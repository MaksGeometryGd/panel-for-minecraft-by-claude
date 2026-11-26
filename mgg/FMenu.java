// Оверлей-кнопка F и окно PC-меню (страница http://127.0.0.1:PORT/pc).
// НЕ ПРОВЕРЕНО на устройстве: Overlay.java я не видел, поэтому класс самодостаточный.
//
// Подключение: там, где у тебя создаётся кнопка MGG (есть Activity игры), добавь одну строку:
//     FMenu.install(activity, 8765, "mgg");     // порт и токен как в сборке (MGG_PORT, MGG_TOKEN)
// Поменяй package на свой.
//
// Как работает:
//  - раз в 2 секунды спрашивает /api/uimode. Режим pc (Settings → Тема → Functions second menu) = кнопка F видна, OFF = скрыта;
//  - кнопку F можно таскать пальцем, короткий тап открывает/закрывает окно меню;
//  - окно двигается за красную верхнюю полосу, размер меняется уголком справа внизу, ✕ закрывает;
//  - внутри окна страница /pc: категории-окна, их тоже можно двигать.
package com.mgg.panel;

import android.annotation.SuppressLint;
import android.app.Activity;
import android.graphics.Color;
import android.graphics.Typeface;
import android.graphics.drawable.GradientDrawable;
import android.net.Uri;
import android.os.Handler;
import android.os.Looper;
import android.util.DisplayMetrics;
import android.view.Gravity;
import android.view.MotionEvent;
import android.view.View;
import android.view.ViewGroup;
import android.webkit.WebSettings;
import android.webkit.WebView;
import android.webkit.WebViewClient;
import android.widget.FrameLayout;
import android.widget.LinearLayout;
import android.widget.TextView;

import java.io.BufferedReader;
import java.io.InputStreamReader;
import java.net.HttpURLConnection;
import java.net.URL;
import java.net.URLEncoder;

public final class FMenu {
    private static boolean started;
    private static WebView web;

    private FMenu() {}

    public static void install(final Activity act, final int port, final String token) {
        act.runOnUiThread(new Runnable() {
            @Override public void run() {
                if (started) return;
                started = true;
                build(act, port, token);
            }
        });
    }

    @SuppressLint({"SetJavaScriptEnabled", "ClickableViewAccessibility"})
    private static void build(final Activity act, final int port, final String token) {
        final DisplayMetrics dm = act.getResources().getDisplayMetrics();
        final float d = dm.density;
        final int accent = 0xFFC4262E;

        // контейнер на весь экран: сам касания не забирает (нет фона и обработчиков), всё, что вне наших окон, идёт в игру
        final FrameLayout root = new FrameLayout(act);
        act.addContentView(root, new ViewGroup.LayoutParams(ViewGroup.LayoutParams.MATCH_PARENT, ViewGroup.LayoutParams.MATCH_PARENT));

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

        final String url = "http://127.0.0.1:" + port + "/pc?t=" + Uri.encode(token);

        // ---- уголок изменения размера
        final TextView grip = new TextView(act);
        grip.setText("◢");
        grip.setTextColor(0xCCFFFFFF);
        grip.setGravity(Gravity.CENTER);
        FrameLayout.LayoutParams gp = new FrameLayout.LayoutParams((int) (30 * d), (int) (30 * d), Gravity.BOTTOM | Gravity.END);
        menu.addView(grip, gp);

        // перетаскивание полосы
        strip.setOnTouchListener(new View.OnTouchListener() {
            float dx, dy;
            @Override public boolean onTouch(View v, MotionEvent e) {
                switch (e.getActionMasked()) {
                    case MotionEvent.ACTION_DOWN: dx = menu.getX() - e.getRawX(); dy = menu.getY() - e.getRawY(); return true;
                    case MotionEvent.ACTION_MOVE:
                        menu.setX(Math.max(-menu.getWidth() * 0.7f, Math.min(dm.widthPixels - menu.getWidth() * 0.3f, e.getRawX() + dx)));
                        menu.setY(Math.max(0, Math.min(dm.heightPixels - 30 * d, e.getRawY() + dy)));
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

        // перетаскивание и тап по кнопке F
        fb.setOnTouchListener(new View.OnTouchListener() {
            float dx, dy, sx, sy; boolean moved;
            @Override public boolean onTouch(View v, MotionEvent e) {
                switch (e.getActionMasked()) {
                    case MotionEvent.ACTION_DOWN:
                        dx = fb.getX() - e.getRawX(); dy = fb.getY() - e.getRawY(); sx = e.getRawX(); sy = e.getRawY(); moved = false; return true;
                    case MotionEvent.ACTION_MOVE:
                        if (Math.abs(e.getRawX() - sx) + Math.abs(e.getRawY() - sy) > 10 * d) moved = true;
                        if (moved) { fb.setX(e.getRawX() + dx); fb.setY(e.getRawY() + dy); }
                        return true;
                    case MotionEvent.ACTION_UP:
                        if (!moved) {
                            if (menu.getVisibility() == View.VISIBLE) { menu.setVisibility(View.GONE); }
                            else {
                                if (web == null) {                       // WebView создаём при первом открытии
                                    web = new WebView(act);
                                    WebSettings ws = web.getSettings();
                                    ws.setJavaScriptEnabled(true);
                                    ws.setDomStorageEnabled(true);
                                    web.setBackgroundColor(0xFF0D0F14);
                                    web.setWebViewClient(new WebViewClient());
                                    FrameLayout.LayoutParams wp = new FrameLayout.LayoutParams(ViewGroup.LayoutParams.MATCH_PARENT, ViewGroup.LayoutParams.MATCH_PARENT);
                                    wp.topMargin = (int) (30 * d);
                                    menu.addView(web, 0, wp);            // под полосой и уголком
                                    web.loadUrl(url);
                                }
                                menu.setVisibility(View.VISIBLE);
                                menu.bringToFront();
                            }
                        }
                        return true;
                }
                return true;
            }
        });

        // ---- опрос режима: pc = кнопка F видна, off = скрыта
        final Handler ui = new Handler(Looper.getMainLooper());
        Thread th = new Thread(new Runnable() {
            @Override public void run() {
                while (true) {
                    boolean pc = false;
                    try {
                        HttpURLConnection c = (HttpURLConnection) new URL("http://127.0.0.1:" + port + "/api/uimode?t=" + URLEncoder.encode(token, "UTF-8")).openConnection();
                        c.setConnectTimeout(1500);
                        c.setReadTimeout(1500);
                        BufferedReader r = new BufferedReader(new InputStreamReader(c.getInputStream()));
                        String l = r.readLine();
                        r.close();
                        pc = l != null && "pc".equals(l.trim());
                    } catch (Exception ignored) {}
                    final boolean show = pc;
                    ui.post(new Runnable() {
                        @Override public void run() {
                            fb.setVisibility(show ? View.VISIBLE : View.GONE);
                            if (!show) menu.setVisibility(View.GONE);
                        }
                    });
                    try { Thread.sleep(2000); } catch (InterruptedException e) { return; }
                }
            }
        });
        th.setDaemon(true);
        th.start();
    }
}
