package mgg;

import android.app.Activity;
import android.content.ClipData;
import android.content.ClipboardManager;
import android.content.Context;
import android.graphics.Color;
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
import android.webkit.JavascriptInterface;
import android.webkit.WebResourceRequest;
import android.webkit.WebResourceResponse;
import android.webkit.WebSettings;
import android.webkit.WebView;
import android.webkit.WebViewClient;
import android.widget.FrameLayout;
import android.widget.TextView;

import java.io.ByteArrayInputStream;
import java.io.ByteArrayOutputStream;
import java.io.InputStream;
import java.io.OutputStream;
import java.net.InetSocketAddress;
import java.net.Socket;

/**
 * MGG overlay: плавающая кнопка "MGG" поверх игры. По нажатию открывается окно с той же панелью,
 * что и в браузере. Запросы WebView не идут через сеть Android (там запрещён http): страница
 * грузится с вымышленного адреса https://mgg.local, а Java сама достаёт ответы у libmggpanel.so
 * по обычному сокету на 127.0.0.1.
 *
 * Подключение: в smali MainActivity.onCreate добавить
 *     invoke-static {p0}, Lmgg/Overlay;->start(Landroid/app/Activity;)V
 */
public final class Overlay {
    private static final String TOKEN = "__MGG_TOKEN__";   // подставляется при сборке
    private static final int PORT = 8765;
    private static final String HOST = "mgg.local";
    private static final String TAG = "MGG";

    private static final Handler H = new Handler(Looper.getMainLooper());
    private static Activity cur;
    private static TextView button;
    private static FrameLayout panel;
    private static WebView web;

    private Overlay() {}

    public static void start(final Activity a) {
        if (a == null) return;
        H.postDelayed(new Runnable() {
            public void run() {
                if (a.isFinishing() || a.isDestroyed()) return;
                try {
                    ensure(a);
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
            FrameLayout.LayoutParams lp = new FrameLayout.LayoutParams(dp(a, 52), dp(a, 52));
            lp.gravity = Gravity.TOP | Gravity.LEFT;
            lp.leftMargin = dp(a, 16);
            lp.topMargin = dp(a, 96);
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
        t.setTextSize(TypedValue.COMPLEX_UNIT_SP, 12);
        t.setGravity(Gravity.CENTER);
        GradientDrawable g = new GradientDrawable();
        g.setShape(GradientDrawable.OVAL);
        g.setColor(0xCC3B5BDB);
        t.setBackground(g);
        t.setOnTouchListener(new Drag(a));
        return t;
    }

    /** Перетаскивание кнопки; короткое касание без сдвига открывает/закрывает панель. */
    private static final class Drag implements View.OnTouchListener {
        private final int slop;
        private float ox, oy, sx, sy;
        private boolean moved;

        Drag(Activity a) {
            slop = dp(a, 8);
        }

        public boolean onTouch(View v, MotionEvent e) {
            switch (e.getActionMasked()) {
                case MotionEvent.ACTION_DOWN:
                    ox = v.getX() - e.getRawX();
                    oy = v.getY() - e.getRawY();
                    sx = e.getRawX();
                    sy = e.getRawY();
                    moved = false;
                    return true;
                case MotionEvent.ACTION_MOVE:
                    if (!moved && (Math.abs(e.getRawX() - sx) > slop || Math.abs(e.getRawY() - sy) > slop)) moved = true;
                    if (moved) {
                        v.setX(e.getRawX() + ox);
                        v.setY(e.getRawY() + oy);
                    }
                    return true;
                case MotionEvent.ACTION_UP:
                    if (!moved) toggle();
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
        DisplayMetrics m = a.getResources().getDisplayMetrics();
        boolean land = m.widthPixels > m.heightPixels;
        int w = land ? (int) (m.widthPixels * 0.6f) : ViewGroup.LayoutParams.MATCH_PARENT;
        int h = (int) (m.heightPixels * (land ? 0.92f : 0.6f));
        FrameLayout.LayoutParams lp = new FrameLayout.LayoutParams(w, h);
        lp.gravity = Gravity.BOTTOM | Gravity.LEFT;
        panel.setLayoutParams(lp);
    }

    private static void buildPanel(Activity a) {
        FrameLayout p = new FrameLayout(a);
        p.setBackgroundColor(0xF2101014);
        p.setClickable(true);                       // касания не проваливаются в игру
        WebView w = new WebView(a);
        WebSettings s = w.getSettings();
        s.setJavaScriptEnabled(true);
        s.setAllowFileAccess(false);
        s.setAllowContentAccess(false);
        w.setBackgroundColor(Color.BLACK);
        w.addJavascriptInterface(new Bridge(a), "MGGJ");
        w.setWebViewClient(new WebViewClient() {
            @Override
            public WebResourceResponse shouldInterceptRequest(WebView v, WebResourceRequest r) {
                return handle(r);
            }
        });
        p.addView(w, new FrameLayout.LayoutParams(ViewGroup.LayoutParams.MATCH_PARENT, ViewGroup.LayoutParams.MATCH_PARENT));
        p.setVisibility(View.GONE);
        panel = p;
        web = w;
        a.addContentView(p, new FrameLayout.LayoutParams(ViewGroup.LayoutParams.MATCH_PARENT, ViewGroup.LayoutParams.MATCH_PARENT));
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

    private static WebResourceResponse handle(WebResourceRequest r) {
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
  
