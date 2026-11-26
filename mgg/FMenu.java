// Отдельное окно PC-меню (страница /pc) со своей кнопкой F. Живёт рядом с Overlay в overlay.jar.
// Подключение: Overlay.ensure() вызывает FMenu.ensure(activity) каждые 3 с (см. патч Overlay.java).
// Кнопка F видна, когда в Settings включён режим pc (/api/uimode). Окно: тянуть за красную полосу, размер уголком ◢, ✕ закрывает.
package mgg;

import android.annotation.SuppressLint;
import android.app.Activity;
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
import android.webkit.WebResourceRequest;
import android.webkit.WebResourceResponse;
import android.webkit.WebSettings;
import android.webkit.WebView;
import android.webkit.WebViewClient;
import android.widget.FrameLayout;
import android.widget.LinearLayout;
import android.widget.TextView;


public final class FMenu {
    private static Activity cur;
    private static FrameLayout rootView;
    private static WebView web;
    private static volatile boolean pollOn;
    private static Runnable toggleAction;     // тап по F, вызывается и из Overlay.Bridge.openF()

    private FMenu() {}

    /** Вызывается из Overlay каждые 3 с: создаёт окно один раз, возвращает его, если игра пересоздала Activity. */
    public static void ensure(final Activity act) {
        if (cur != act) {
            if (rootView != null && rootView.getParent() instanceof ViewGroup) ((ViewGroup) rootView.getParent()).removeView(rootView);
            try { if (web != null) web.destroy(); } catch (Throwable ignored) {}
            web = null; rootView = null; toggleAction = null;
            cur = act;
            build(act);
        } else if (rootView != null && !rootView.isAttachedToWindow()) {
            if (rootView.getParent() instanceof ViewGroup) ((ViewGroup) rootView.getParent()).removeView(rootView);
            act.addContentView(rootView, new ViewGroup.LayoutParams(ViewGroup.LayoutParams.MATCH_PARENT, ViewGroup.LayoutParams.MATCH_PARENT));
        }
    }

    /** Открыть/закрыть окно (кнопка PC в панели вызывает это через MGGJ.openF). */
    public static void toggle() {
        final Runnable r = toggleAction;
        if (r != null && cur != null) cur.runOnUiThread(r);
    }

    @SuppressLint({"SetJavaScriptEnabled", "ClickableViewAccessibility"})
    private static void build(final Activity act) {
        final DisplayMetrics dm = act.getResources().getDisplayMetrics();
        final float d = dm.density;
        final int accent = 0xFFC4262E;

        // контейнер на весь экран: сам касания не забирает (нет фона и обработчиков), всё, что вне наших окон, идёт в игру
        final FrameLayout root = new FrameLayout(act);
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
        fg.setColor(accent);
        fg.setStroke((int) (2 * d), 0x66FFFFFF);
        fb.setBackground(fg);
        FrameLayout.LayoutParams fp = new FrameLayout.LayoutParams((int) (46 * d), (int) (46 * d));
        root.addView(fb, fp);
        fb.setX(12 * d);
        fb.setY(dm.heightPixels * 0.32f);
        fb.setVisibility(View.GONE);

        // ---- окно меню
        final FrameLayout menu = new FrameLayout(act);
        GradientDrawable mbg = new GradientDrawable();
        mbg.setColor(0xFF0D0F14);
        mbg.setCornerRadius(10 * d);
        mbg.setStroke((int) d, 0xFF2B3040);
        menu.setBackground(mbg);
        menu.setClipToOutline(true);
        final int mw = (int) (dm.widthPixels * 0.82f), mh = (int) (dm.heightPixels * 0.86f);
        root.addView(menu, new FrameLayout.LayoutParams(mw, mh));
        menu.setX((dm.widthPixels - mw) / 2f);
        menu.setY((dm.heightPixels - mh) / 2f);
        menu.setVisibility(View.GONE);

        // верхняя полоса: тянуть окно + закрыть
        final LinearLayout strip = new LinearLayout(act);
        strip.setOrientation(LinearLayout.HORIZONTAL);
        strip.setBackgroundColor(accent);
        strip.setGravity(Gravity.CENTER_VERTICAL);
        TextView title = new TextView(act);
        title.setText("  ≡  F menu");
        title.setTextColor(Color.WHITE);
        title.setTypeface(Typeface.DEFAULT_BOLD);
        strip.addView(title, new LinearLayout.LayoutParams(0, ViewGroup.LayoutParams.MATCH_PARENT, 1f));
        title.setGravity(Gravity.CENTER_VERTICAL);
        TextView close = new TextView(act);
        close.setText("✕");
        close.setTextColor(Color.WHITE);
        close.setTextSize(16);
        close.setGravity(Gravity.CENTER);
        strip.addView(close, new LinearLayout.LayoutParams((int) (44 * d), ViewGroup.LayoutParams.MATCH_PARENT));
        menu.addView(strip, new FrameLayout.LayoutParams(ViewGroup.LayoutParams.MATCH_PARENT, (int) (30 * d)));

        final String url = "https://" + Overlay.HOST + "/pc?t=" + Overlay.TOKEN;

        // ---- уголок изменения размера
        final TextView grip = new TextView(act);
        grip.setText("◢");
        grip.setTextColor(0xCCFFFFFF);
        grip.setGravity(Gravity.CENTER);
        FrameLayout.LayoutParams gp = new FrameLayout.LayoutParams((int) (30 * d), (int) (30 * d), Gravity.BOTTOM | Gravity.END);
        menu.addView(grip, gp);

        final int[] mloc = new int[2];
        // перетаскивание полосы
        strip.setOnTouchListener(new View.OnTouchListener() {
            float dx, dy;
            @Override public boolean onTouch(View v, MotionEvent e) {
                switch (e.getActionMasked()) {
                    case MotionEvent.ACTION_DOWN: root.getLocationOnScreen(mloc); dx = menu.getX() - (e.getRawX() - mloc[0]); dy = menu.getY() - (e.getRawY() - mloc[1]); return true;
                    case MotionEvent.ACTION_MOVE:
                        root.getLocationOnScreen(mloc);
                        menu.setX(Math.max(-menu.getWidth() * 0.7f, Math.min(root.getWidth() - menu.getWidth() * 0.3f, e.getRawX() - mloc[0] + dx)));
                        menu.setY(Math.max(0, Math.min(root.getHeight() - 30 * d, e.getRawY() - mloc[1] + dy)));
                        return true;
                }
                return true;
            }
        });
        close.setOnClickListener(new View.OnClickListener() {
            @Override public void onClick(View v) { menu.setVisibility(View.GONE); }
        });

        // изменение размера
        grip.setOnTouchListener(new View.OnTouchListener() {
            float sx, sy; int sw, sh;
            @Override public boolean onTouch(View v, MotionEvent e) {
                FrameLayout.LayoutParams lp = (FrameLayout.LayoutParams) menu.getLayoutParams();
                switch (e.getActionMasked()) {
                    case MotionEvent.ACTION_DOWN: sx = e.getRawX(); sy = e.getRawY(); sw = menu.getWidth(); sh = menu.getHeight(); return true;
                    case MotionEvent.ACTION_MOVE:
                        lp.width = (int) Math.max(240 * d, sw + (e.getRawX() - sx));
                        lp.height = (int) Math.max(200 * d, sh + (e.getRawY() - sy));
                        menu.setLayoutParams(lp);
                        return true;
                }
                return true;
            }
        });

        toggleAction = new Runnable() {
            @Override public void run() {
                            if (menu.getVisibility() == View.VISIBLE) { menu.setVisibility(View.GONE); }
                            else {
                                if (web == null) {                       // WebView создаём при первом открытии
                                    web = new WebView(act);
                                    WebSettings ws = web.getSettings();
                                    ws.setJavaScriptEnabled(true);
                                    ws.setDomStorageEnabled(true);
                                    web.setBackgroundColor(0xFF0D0F14);
                                    web.setWebViewClient(new WebViewClient() {
                                        @Override public WebResourceResponse shouldInterceptRequest(WebView v, WebResourceRequest r) { return Overlay.handle(r); }
                                    });
                                    FrameLayout.LayoutParams wp = new FrameLayout.LayoutParams(ViewGroup.LayoutParams.MATCH_PARENT, ViewGroup.LayoutParams.MATCH_PARENT);
                                    wp.topMargin = (int) (30 * d);
                                    menu.addView(web, 0, wp);            // под полосой и уголком
                                    web.loadUrl(url);
                                }
                                menu.setVisibility(View.VISIBLE);
                                menu.bringToFront();
                            }
            }
        };

        final int[] loc = new int[2];
        // перетаскивание и тап по кнопке F
        fb.setOnTouchListener(new View.OnTouchListener() {
            float dx, dy, sx, sy; boolean moved;
            @Override public boolean onTouch(View v, MotionEvent e) {
                switch (e.getActionMasked()) {
                    case MotionEvent.ACTION_DOWN:
                        root.getLocationOnScreen(loc); dx = fb.getX() - (e.getRawX() - loc[0]); dy = fb.getY() - (e.getRawY() - loc[1]); sx = e.getRawX(); sy = e.getRawY(); moved = false; return true;
                    case MotionEvent.ACTION_MOVE:
                        if (Math.abs(e.getRawX() - sx) + Math.abs(e.getRawY() - sy) > 10 * d) moved = true;
                        if (moved) {                              // границы берём у самого root, а не у экрана: иначе кнопка уезжает за край и обрезается
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
                    // не смогли дозвониться до панели (занята/ошибка) -> оставляем как есть, прячем только по явному "off"
                    final int state = "pc".equals(r) ? 1 : "off".equals(r) ? 0 : -1;
                    if (state >= 0) ui.post(new Runnable() {
                        @Override public void run() {
                            fb.setVisibility(state == 1 ? View.VISIBLE : View.GONE);
                            if (state == 0) menu.setVisibility(View.GONE);
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
