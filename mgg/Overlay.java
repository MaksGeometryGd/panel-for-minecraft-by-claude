package mgg;

import android.app.Activity;
import android.content.ClipData;
import android.content.ClipboardManager;
import android.content.Context;
import android.graphics.Color;
import android.graphics.Outline;
import android.graphics.drawable.GradientDrawable;
import android.net.Uri;
import android.os.Handler;
import android.os.Looper;
import android.util.DisplayMetrics;
import android.util.Log;
import android.util.TypedValue;
import android.view.Gravity;
import android.view.MotionEvent;
import android.view.View;
import android.view.ViewGroup;
import android.view.ViewOutlineProvider;
import android.webkit.JavascriptInterface;
import android.webkit.WebResourceRequest;
import android.webkit.WebResourceResponse;
import android.webkit.WebSettings;
import android.webkit.WebView;
import android.webkit.WebViewClient;
import android.widget.FrameLayout;
import android.widget.LinearLayout;
import android.widget.TextView;

import java.io.ByteArrayInputStream;
import java.io.ByteArrayOutputStream;
import java.io.InputStream;
import java.io.OutputStream;
import java.net.InetSocketAddress;
import java.net.Socket;

/**
 * MGG overlay: плавающая кнопка "MGG" поверх игры. По нажатию открывается окно с панелью.
 * Окно можно таскать за шапку, менять размер окна и текста, делать полупрозрачным.
 *
 * Запросы WebView не идут через сеть Android (там запрещён http): страница грузится с
 * вымышленного адреса https://mgg.local, а Java сама достаёт ответы у libmggpanel.so
 * по обычному сокету на 127.0.0.1.
 *
 * Подключение: в smali конструктора MainActivity (после вызова super-конструктора)
 *     invoke-static {v7}, Lmgg/Overlay;->start(Landroid/app/Activity;)V
 */
public final class Overlay {
    static final String TOKEN = "__MGG_TOKEN__";   // подставляется при сборке
    private static final int PORT = 8765;
    static final String HOST = "mgg.local";
    private static final String TAG = "MGG";
    private static final float[] ALPHAS = {1f, 0.8f, 0.6f, 0.4f};

    private static final Handler H = new Handler(Looper.getMainLooper());
    private static Activity cur;
    private static TextView button;
    private static LinearLayout panel;
    private static WebView web;

    // запомненные положения (px от левого верхнего угла) и настройки окна
    private static int bx = -1, by = -1, pnx = -1, pny = -1;
    private static float scale = 1f;
    private static int zoom = 75;
    private static final int PANEL_RADIUS_DP = 16;   // скругление всего окна панели (шапка + webview разом)
    private static int alphaIdx = 0;

    private Overlay() {}

    public static void start(final Activity a) {
        if (a == null) return;
        H.postDelayed(new Runnable() {
            public void run() {
                if (a.isFinishing() || a.isDestroyed()) return;
                try {
                    ensure(a);
                    FMenu.ensure(a);
                } catch (Throwable t) {
                    Log.e(TAG, "overlay: " + t);
                }
                H.postDelayed(this, 3000);   // если игра пересоздала окно, кнопка вернётся
            }
        }, 3000);
    }

    private static int dp(Activity a, int v) {
        return (int) (v * a.getResources().getDisplayMetrics().density + 0.5f);
    }

    private static void remove(View v) {
        if (v != null && v.getParent() instanceof ViewGroup) ((ViewGroup) v.getParent()).removeView(v);
    }

    private static void detach() {
        remove(panel);
        remove(button);
        try {
            if (web != null) web.destroy();
        } catch (Throwable ignored) {
        }
        panel = null;
        button = null;
        web = null;
    }

    private static void ensure(Activity a) {
        if (cur != a) {
            detach();
            cur = a;
        }
        if (button == null) button = makeButton(a);
        if (!button.isAttachedToWindow()) {
            remove(button);
            int sz = dp(a, 46);
            FrameLayout.LayoutParams lp = new FrameLayout.LayoutParams(sz, sz);
            lp.gravity = Gravity.TOP | Gravity.LEFT;
            lp.leftMargin = bx >= 0 ? bx : dp(a, 16);
            lp.topMargin = by >= 0 ? by : dp(a, 96);
            a.addContentView(button, lp);
        }
        if (panel != null && !panel.isAttachedToWindow()) {
            remove(panel);
            a.addContentView(panel, panel.getLayoutParams());
            button.bringToFront();
        }
    }

    private static TextView makeButton(Activity a) {
        TextView t = new TextView(a);
        t.setText("MGG");
        t.setTextColor(Color.WHITE);
        t.setTextSize(TypedValue.COMPLEX_UNIT_SP, 11);
        t.setGravity(Gravity.CENTER);
        GradientDrawable g = new GradientDrawable();
        g.setShape(GradientDrawable.OVAL);
        g.setColor(0xCC3B5BDB);
        t.setBackground(g);
        t.setOnTouchListener(new Mover(a, t, new Runnable() {
            public void run() {
                toggle();
            }
        }));
        return t;
    }

    /** Перемещение view через margin (а не translation) с ограничением по границам экрана. */
    private static void place(View v, int l, int t) {
        if (!(v.getParent() instanceof ViewGroup)) return;
        ViewGroup parent = (ViewGroup) v.getParent();
        int maxL = Math.max(0, parent.getWidth() - v.getWidth());
        int maxT = Math.max(0, parent.getHeight() - v.getHeight());
        l = Math.max(0, Math.min(l, maxL));
        t = Math.max(0, Math.min(t, maxT));
        if (!(v.getLayoutParams() instanceof FrameLayout.LayoutParams)) return;
        FrameLayout.LayoutParams lp = (FrameLayout.LayoutParams) v.getLayoutParams();
        lp.gravity = Gravity.TOP | Gravity.LEFT;
        lp.leftMargin = l;
        lp.topMargin = t;
        v.setLayoutParams(lp);
        if (v == button) {
            bx = l;
            by = t;
        } else {
            pnx = l;
            pny = t;
        }
    }

    /** Тянет target за любой view-ручку; короткое касание без сдвига вызывает tap (если задан). */
    private static final class Mover implements View.OnTouchListener {
        private final View target;
        private final Runnable tap;
        private final int slop;
        private float sx, sy;
        private int startL, startT;
        private boolean moved;

        Mover(Activity a, View target, Runnable tap) {
            this.target = target;
            this.tap = tap;
            this.slop = dp(a, 8);
        }

        public boolean onTouch(View v, MotionEvent e) {
            switch (e.getActionMasked()) {
                case MotionEvent.ACTION_DOWN: {
                    sx = e.getRawX();
                    sy = e.getRawY();
                    moved = false;
                    if (target.getLayoutParams() instanceof FrameLayout.LayoutParams) {
                        FrameLayout.LayoutParams lp = (FrameLayout.LayoutParams) target.getLayoutParams();
                        startL = lp.leftMargin;
                        startT = lp.topMargin;
                    }
                    return true;
                }
                case MotionEvent.ACTION_MOVE: {
                    float dx = e.getRawX() - sx, dy = e.getRawY() - sy;
                    if (!moved && (Math.abs(dx) > slop || Math.abs(dy) > slop)) moved = true;
                    if (moved) place(target, startL + (int) dx, startT + (int) dy);
                    return true;
                }
                case MotionEvent.ACTION_UP:
                    if (!moved && tap != null) tap.run();
                    return true;
                case MotionEvent.ACTION_CANCEL:
                    return true;
                default:
                    return false;
            }
        }
    }

    private static void toggle() {
        Activity a = cur;
        if (a == null) return;
        if (panel == null) buildPanel(a);
        if (panel.getVisibility() != View.VISIBLE) {
            layoutPanel(a);
            panel.setVisibility(View.VISIBLE);
            if (web != null) web.requestFocus();
        } else {
            panel.setVisibility(View.GONE);
        }
        if (button != null) button.bringToFront();
    }

    private static void layoutPanel(Activity a) {
        if (panel == null) return;
        DisplayMetrics m = a.getResources().getDisplayMetrics();
        boolean land = m.widthPixels > m.heightPixels;
        int w = (int) (m.widthPixels * (land ? 0.5f : 0.95f) * scale);
        int h = (int) (m.heightPixels * (land ? 0.75f : 0.5f) * scale);
        w = Math.max(dp(a, 220), Math.min(w, m.widthPixels));
        h = Math.max(dp(a, 160), Math.min(h, m.heightPixels));
        int l = pnx >= 0 ? pnx : dp(a, 8);
        int t = pny >= 0 ? pny : dp(a, 8);
        l = Math.max(0, Math.min(l, m.widthPixels - w));
        t = Math.max(0, Math.min(t, m.heightPixels - h));
        FrameLayout.LayoutParams lp = new FrameLayout.LayoutParams(w, h);
        lp.gravity = Gravity.TOP | Gravity.LEFT;
        lp.leftMargin = l;
        lp.topMargin = t;
        panel.setLayoutParams(lp);
        panel.post(new Runnable() {         // ждём, пока новый размер реально применится, иначе скругление возьмёт старые w/h
            public void run() {
                panel.invalidateOutline();
            }
        });
    }

    private static TextView tb(Activity a, String s, View.OnClickListener l) {
        TextView t = new TextView(a);
        t.setText(s);
        t.setTextColor(Color.WHITE);
        t.setTextSize(TypedValue.COMPLEX_UNIT_SP, 15);
        t.setGravity(Gravity.CENTER);
        t.setOnClickListener(l);
        return t;
    }

    private static void buildPanel(final Activity a) {
        final LinearLayout p = new LinearLayout(a);
        p.setOrientation(LinearLayout.VERTICAL);
        p.setBackgroundColor(0xF2101014);
        p.setClickable(true);                       // касания не проваливаются в игру

        final WebView w = new WebView(a);
        WebSettings s = w.getSettings();
        s.setJavaScriptEnabled(true);
        s.setAllowFileAccess(false);
        s.setAllowContentAccess(false);
        s.setTextZoom(zoom);
        w.setBackgroundColor(Color.BLACK);
        w.addJavascriptInterface(new Bridge(a), "MGGJ");
        w.setWebViewClient(new WebViewClient() {
            @Override
            public WebResourceResponse shouldInterceptRequest(WebView v, WebResourceRequest r) {
                return handle(r);
            }
        });

        // шапка: за название тянем окно, кнопки меняют размер/прозрачность/закрывают
        LinearLayout head = new LinearLayout(a);
        head.setOrientation(LinearLayout.HORIZONTAL);
        head.setBackgroundColor(0xFF1A1D29);           // тот же тон, что и фон страницы (--card): шапка не выделяется отдельной плашкой
        TextView title = new TextView(a);
        title.setText("≡");                            // только значок "потяни", название уже есть в самой панели
        title.setTextColor(0xFF8D92A6);
        title.setTextSize(TypedValue.COMPLEX_UNIT_SP, 15);
        title.setGravity(Gravity.CENTER_VERTICAL);
        title.setPadding(dp(a, 12), 0, 0, 0);
        title.setOnTouchListener(new Mover(a, p, null));
        head.addView(title, new LinearLayout.LayoutParams(0, ViewGroup.LayoutParams.MATCH_PARENT, 1f));

        int bw = dp(a, 36);
        int mp = ViewGroup.LayoutParams.MATCH_PARENT;
        head.addView(tb(a, "A−", new View.OnClickListener() {
            public void onClick(View v) {
                zoom = Math.max(50, zoom - 10);
                w.getSettings().setTextZoom(zoom);
            }
        }), new LinearLayout.LayoutParams(bw, mp));
        head.addView(tb(a, "A+", new View.OnClickListener() {
            public void onClick(View v) {
                zoom = Math.min(160, zoom + 10);
                w.getSettings().setTextZoom(zoom);
            }
        }), new LinearLayout.LayoutParams(bw, mp));
        head.addView(tb(a, "−", new View.OnClickListener() {
            public void onClick(View v) {
                scale = Math.max(0.5f, scale - 0.15f);
                layoutPanel(a);
            }
        }), new LinearLayout.LayoutParams(bw, mp));
        head.addView(tb(a, "+", new View.OnClickListener() {
            public void onClick(View v) {
                scale = Math.min(1.4f, scale + 0.15f);
                layoutPanel(a);
            }
        }), new LinearLayout.LayoutParams(bw, mp));
        head.addView(tb(a, "◐", new View.OnClickListener() {
            public void onClick(View v) {
                alphaIdx = (alphaIdx + 1) % ALPHAS.length;
                p.setAlpha(ALPHAS[alphaIdx]);
            }
        }), new LinearLayout.LayoutParams(bw, mp));
        head.addView(tb(a, "✕", new View.OnClickListener() {
            public void onClick(View v) {
                p.setVisibility(View.GONE);
            }
        }), new LinearLayout.LayoutParams(bw, mp));

        p.addView(head, new LinearLayout.LayoutParams(mp, dp(a, 38)));
        p.addView(w, new LinearLayout.LayoutParams(mp, 0, 1f));
        final float rad = dp(a, PANEL_RADIUS_DP);
        p.setOutlineProvider(new ViewOutlineProvider() {
            @Override
            public void getOutline(View view, Outline outline) {
                outline.setRoundRect(0, 0, view.getWidth(), view.getHeight(), rad);
            }
        });
        p.setClipToOutline(true);
        p.setAlpha(ALPHAS[alphaIdx]);
        p.setVisibility(View.GONE);
        panel = p;
        web = w;
        a.addContentView(p, new FrameLayout.LayoutParams(dp(a, 300), dp(a, 300)));
        w.loadUrl("https://" + HOST + "/?t=" + TOKEN);
        if (button != null) button.bringToFront();
    }

    /** Мост для кнопки «Скопировать результат» (в WebView navigator.clipboard может не работать). */
    public static final class Bridge {
        private final Activity a;

        Bridge(Activity a) {
            this.a = a;
        }

        @JavascriptInterface
        public void openF() {
            FMenu.toggle();
        }

        @JavascriptInterface
        public void copy(final String text) {
            a.runOnUiThread(new Runnable() {
                public void run() {
                    try {
                        ClipboardManager c = (ClipboardManager) a.getSystemService(Context.CLIPBOARD_SERVICE);
                        c.setPrimaryClip(ClipData.newPlainText("mgg", text));
                    } catch (Throwable t) {
                        Log.e(TAG, "copy: " + t);
                    }
                }
            });
        }
    }

    // ------------------------------------------------------------ локальный "прокси" на сокете

    /** Текст ответа панели на путь вроде "/api/uimode?t=..." (для FMenu). Вызывать не из UI-потока. */
    static String getText(String pathAndQuery) {
        try {
            WebResourceResponse r = fetch(pathAndQuery);
            InputStream in = r.getData();
            ByteArrayOutputStream bo = new ByteArrayOutputStream();
            byte[] b = new byte[256];
            int n;
            while ((n = in.read(b)) > 0 && bo.size() < 4096) bo.write(b, 0, n);
            return bo.toString("UTF-8").trim();
        } catch (Throwable t) {
            return "";
        }
    }

    static WebResourceResponse handle(WebResourceRequest r) {
        Uri u = r.getUrl();
        if (u == null || !HOST.equals(u.getHost())) return reply("text/plain", "");
        String pq = u.getEncodedPath();
        if (pq == null || pq.length() == 0) pq = "/";
        String q = u.getEncodedQuery();
        if (q != null) pq += "?" + q;
        return fetch(pq);
    }

    private static WebResourceResponse reply(String mime, String body) {
        try {
            return new WebResourceResponse(mime, "utf-8", new ByteArrayInputStream(body.getBytes("UTF-8")));
        } catch (Exception e) {
            return new WebResourceResponse(mime, "utf-8", new ByteArrayInputStream(new byte[0]));
        }
    }

    private static int indexOf(byte[] a, String needle) {
        byte[] n = needle.getBytes();
        for (int i = 0; i + n.length <= a.length; i++) {
            int k = 0;
            while (k < n.length && a[i + k] == n[k]) k++;
            if (k == n.length) return i;
        }
        return -1;
    }

    private static WebResourceResponse fetch(String pathAndQuery) {
        Socket s = new Socket();
        try {
            s.connect(new InetSocketAddress("127.0.0.1", PORT), 2000);
            s.setSoTimeout(15000);
            OutputStream o = s.getOutputStream();
            o.write(("GET " + pathAndQuery + " HTTP/1.1\r\nHost: 127.0.0.1\r\nConnection: close\r\n\r\n").getBytes("UTF-8"));
            o.flush();
            ByteArrayOutputStream bo = new ByteArrayOutputStream();
            byte[] buf = new byte[8192];
            InputStream in = s.getInputStream();
            int n;
            while ((n = in.read(buf)) > 0) bo.write(buf, 0, n);
            byte[] all = bo.toByteArray();
            int idx = indexOf(all, "\r\n\r\n");
            if (idx < 0) return reply("text/plain", "пустой ответ панели");
            String head = new String(all, 0, idx, "UTF-8");
            String mime = "text/plain";
            for (String line : head.split("\r\n")) {
                if (line.toLowerCase().startsWith("content-type:")) {
                    mime = line.substring(13).trim();
                    int sc = mime.indexOf(';');
                    if (sc > 0) mime = mime.substring(0, sc).trim();
                }
            }
            return new WebResourceResponse(mime, "utf-8", new ByteArrayInputStream(all, idx + 4, all.length - idx - 4));
        } catch (Exception e) {
            return reply("text/plain", "Панель не отвечает (libmggpanel.so не загружена?): " + e);
        } finally {
            try {
                s.close();
            } catch (Exception ignored) {
            }
        }
    }
}
