// PC-меню (страница /pc?fm=1) прямо поверх игры: без рамки и фона, видны только колонки с функциями.
// Касания мимо колонок проходят в игру. Кнопка F (перетаскивается) открывает/закрывает меню.
// Подключение: Overlay.ensure() вызывает FMenu.ensure(activity) каждые 3 с. Кнопка F видна, когда в Settings режим pc (/api/uimode).
package mgg;

import android.annotation.SuppressLint;
import android.app.Activity;
import android.content.ClipData;
import android.content.ClipboardManager;
import android.content.Context;
import android.graphics.Color;
import android.graphics.Typeface;
import android.graphics.drawable.GradientDrawable;
import android.os.Handler;
import android.os.Looper;
import android.util.DisplayMetrics;
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

public final class FMenu {
    private static Activity cur;
    private static Root rootView;
    private static WebView web;
    private static TextView fbView;
    private static Runnable toggleAction;            // тап по F, вызывается и из Overlay.Bridge.openF()
    private static volatile float[] rects = new float[0];   // x,y,w,h в пикселях экрана (по 4 числа на окно), присылает страница

    private FMenu() {}

    /** Контейнер на весь экран: касание забирает только если попало в колонку или в кнопку F, иначе отдаёт игре. */
    private static final class Root extends FrameLayout {
        private boolean grab;
        private final float pad;
        Root(Context c, float pad) { super(c); this.pad = pad; }

        @Override public boolean dispatchTouchEvent(MotionEvent e) {
            if (e.getActionMasked() == MotionEvent.ACTION_DOWN) grab = hit(e.getX(), e.getY());
            if (!grab) return false;
            return super.dispatchTouchEvent(e);
        }

        private boolean hit(float x, float y) {
            TextView f = fbView;
            if (f != null && f.getVisibility() == View.VISIBLE
                    && x >= f.getX() - pad && x <= f.getX() + f.getWidth() + pad
                    && y >= f.getY() - pad && y <= f.getY() + f.getHeight() + pad) return true;
            WebView w = web;
            if (w == null || w.getVisibility() != View.VISIBLE) return false;
            float[] r = rects;
            for (int i = 0; i + 3 < r.length; i += 4)
                if (x >= r[i] - pad && x <= r[i] + r[i + 2] + pad && y >= r[i + 1] - pad && y <= r[i + 1] + r[i + 3] + pad) return true;
            return false;
        }
    }

    /** Мост для страницы: список занятых прямоугольников и копирование журнала. */
    private static final class JS {
        private final Context ctx;
        JS(Context c) { ctx = c; }

        @JavascriptInterface public void rects(String csv) {
            try {
                String[] p = csv.isEmpty() ? new String[0] : csv.split(",");
                float[] r = new float[p.length];
                for (int i = 0; i < p.length; i++) r[i] = Float.parseFloat(p[i]);
                rects = r;
            } catch (Throwable ignored) {}
        }

        @JavascriptInterface public void copy(String t) {
            try { ((ClipboardManager) ctx.getSystemService(Context.CLIPBOARD_SERVICE)).setPrimaryClip(ClipData.newPlainText("mgg", t)); } catch (Throwable ignored) {}
        }
    }

    /** Вызывается из Overlay каждые 3 с: создаёт окно один раз, возвращает его, если игра пересоздала Activity. */
    public static void ensure(final Activity act) {
        if (cur != act) {
            if (rootView != null && rootView.getParent() instanceof ViewGroup) ((ViewGroup) rootView.getParent()).removeView(rootView);
            try { if (web != null) web.destroy(); } catch (Throwable ignored) {}
            web = null; rootView = null; fbView = null; toggleAction = null; rects = new float[0];
            cur = act;
            build(act);
        } else if (rootView != null && !rootView.isAttachedToWindow()) {
            if (rootView.getParent() instanceof ViewGroup) ((ViewGroup) rootView.getParent()).removeView(rootView);
            act.addContentView(rootView, new ViewGroup.LayoutParams(ViewGroup.LayoutParams.MATCH_PARENT, ViewGroup.LayoutParams.MATCH_PARENT));
        }
    }

    /** Открыть/закрыть меню (кнопка PC в панели вызывает это через MGGJ.openF). */
    public static void toggle() {
        final Runnable r = toggleAction;
        if (r != null && cur != null) cur.runOnUiThread(r);
    }

    @SuppressLint({"SetJavaScriptEnabled", "ClickableViewAccessibility"})
    private static void build(final Activity act) {
        final DisplayMetrics dm = act.getResources().getDisplayMetrics();
        final float d = dm.density;

        final Root root = new Root(act, 6 * d);
        act.addContentView(root, new ViewGroup.LayoutParams(ViewGroup.LayoutParams.MATCH_PARENT, ViewGroup.LayoutParams.MATCH_PARENT));
        root.setClipChildren(false);
        root.setClipToPadding(false);
        rootView = root;

        // ---- кнопка F
        final TextView fb = new TextView(act);
        fb.setText("F");
        fb.setTextColor(Color.WHITE);
        fb.setTypeface(Typeface.DEFAULT_BOLD);
        fb.setTextSize(20);
        fb.setGravity(Gravity.CENTER);
        GradientDrawable fg = new GradientDrawable();
        fg.setShape(GradientDrawable.OVAL);
        fg.setColor(0xFFC4262E);
        fg.setStroke((int) (2 * d), 0x66FFFFFF);
        fb.setBackground(fg);
        root.addView(fb, new FrameLayout.LayoutParams((int) (46 * d), (int) (46 * d)));
        fb.setX(12 * d);
        fb.setY(dm.heightPixels * 0.32f);
        fb.setVisibility(View.GONE);
        fbView = fb;

        final String url = "https://" + Overlay.HOST + "/pc?fm=1&t=" + Overlay.TOKEN;

        toggleAction = new Runnable() {
            @Override public void run() {
                if (web == null) {                                   // WebView создаём при первом открытии
                    web = new WebView(act);
                    WebSettings ws = web.getSettings();
                    ws.setJavaScriptEnabled(true);
                    ws.setDomStorageEnabled(true);
                    web.setBackgroundColor(Color.TRANSPARENT);       // прозрачный фон: видна игра
                    web.setVerticalScrollBarEnabled(false);
                    web.setHorizontalScrollBarEnabled(false);
                    web.setOverScrollMode(View.OVER_SCROLL_NEVER);
                    web.addJavascriptInterface(new JS(act), "MGGJ");
                    web.setWebViewClient(new WebViewClient() {
                        @Override public WebResourceResponse shouldInterceptRequest(WebView v, WebResourceRequest r) { return Overlay.handle(r); }
                    });
                    root.addView(web, 0, new FrameLayout.LayoutParams(ViewGroup.LayoutParams.MATCH_PARENT, ViewGroup.LayoutParams.MATCH_PARENT));
                    web.loadUrl(url);
                    return;
                }
                web.setVisibility(web.getVisibility() == View.VISIBLE ? View.GONE : View.VISIBLE);
            }
        };

        final int[] loc = new int[2];
        // перетаскивание и тап по кнопке F
        fb.setOnTouchListener(new View.OnTouchListener() {
            float dx, dy, sx, sy; boolean moved;
            @Override public boolean onTouch(View v, MotionEvent e) {
                switch (e.getActionMasked()) {
                    case MotionEvent.ACTION_DOWN:
                        root.getLocationOnScreen(loc);
                        dx = fb.getX() - (e.getRawX() - loc[0]); dy = fb.getY() - (e.getRawY() - loc[1]);
                        sx = e.getRawX(); sy = e.getRawY(); moved = false;
                        return true;
                    case MotionEvent.ACTION_MOVE:
                        if (Math.abs(e.getRawX() - sx) + Math.abs(e.getRawY() - sy) > 10 * d) moved = true;
                        if (moved) {
                            root.getLocationOnScreen(loc);
                            float nx = e.getRawX() - loc[0] + dx, ny = e.getRawY() - loc[1] + dy;
                            fb.setX(Math.max(0, Math.min(root.getWidth() - fb.getWidth(), nx)));
                            fb.setY(Math.max(0, Math.min(root.getHeight() - fb.getHeight(), ny)));
                        }
                        return true;
                    case MotionEvent.ACTION_UP:
                        if (!moved) toggleAction.run();
                        return true;
                }
                return true;
            }
        });

        // ---- опрос режима: pc = кнопка F видна, off = скрыта
        final Handler ui = new Handler(Looper.getMainLooper());
        Thread th = new Thread(new Runnable() {
            @Override public void run() {
                while (cur == act) {
                    final String r = Overlay.getText("/api/uimode?t=" + Overlay.TOKEN);
                    // не дозвонились до панели (занята/ошибка) -> оставляем как есть, прячем только по явному "off"
                    final int state = "pc".equals(r) ? 1 : "off".equals(r) ? 0 : -1;
                    if (state >= 0) ui.post(new Runnable() {
                        @Override public void run() {
                            fb.setVisibility(state == 1 ? View.VISIBLE : View.GONE);
                            if (state == 0 && web != null) web.setVisibility(View.GONE);
                        }
                    });
                    try { Thread.sleep(2000); } catch (InterruptedException e) { return; }
                }
            }
        }, "mgg-fmenu-poll");
        th.setDaemon(true);
        th.start();
    }
}
