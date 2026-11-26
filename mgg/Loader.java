package mgg;

import android.app.Activity;
import android.os.Handler;
import android.os.Looper;
import android.util.Log;
import android.widget.Toast;

import dalvik.system.DexClassLoader;

import java.io.ByteArrayOutputStream;
import java.io.File;
import java.io.FileInputStream;
import java.io.FileOutputStream;
import java.io.IOException;
import java.io.InputStream;
import java.io.OutputStream;
import java.lang.reflect.Method;
import java.net.HttpURLConnection;
import java.net.URL;

/**
 * MGG loader: вставляется в APK ОДИН раз и больше не меняется.
 * При запуске игры в фоне проверяет version.txt в релизе "latest" на GitHub; если там новая сборка,
 * скачивает libmggpanel.so и overlay.jar, затем грузит .so и запускает mgg.Overlay из jar.
 * Нет сети: берёт то, что скачано раньше.
 *
 * Подключение: в smali конструктора MainActivity (после super-конструктора)
 *     invoke-static {v7}, Lmgg/Loader;->start(Landroid/app/Activity;)V
 * (вместо старого вызова Lmgg/Overlay;->start и вместо System.loadLibrary("mggpanel"))
 */
public final class Loader {
    private static final String BASE = "https://github.com/__MGG_REPO__/releases/download/latest/";   // подставляется при сборке
    private static final String TAG = "MGG";
    private static boolean started;

    private Loader() {}

    public static synchronized void start(final Activity a) {
        if (a == null || started) return;
        started = true;
        // конструктор Activity ещё не готов (нет контекста), поэтому ждём и работаем в фоне
        new Handler(Looper.getMainLooper()).postDelayed(new Runnable() {
            public void run() {
                new Thread(new Runnable() {
                    public void run() {
                        try {
                            work(a);
                        } catch (Throwable t) {
                            Log.e(TAG, "loader: " + t);
                            toast(a, "ошибка: " + t, true);
                        }
                    }
                }, "mgg-loader").start();
            }
        }, 2000);
    }

    private static void work(final Activity a) throws Exception {
        File base = null;
        for (int i = 0; i < 60 && base == null; i++) {
            try { base = a.getFilesDir(); } catch (Throwable ignore) {}
            if (base == null) Thread.sleep(500);
        }
        if (base == null) return;
        File dir = new File(base, "mgg");
        dir.mkdirs();
        File ver = new File(dir, "version.txt");
        File so = new File(dir, "libmggpanel.so");
        File jar = new File(dir, "overlay.jar");

        String have = readText(ver), want = null;
        try {
            want = fetchText(BASE + "version.txt");
        } catch (Throwable t) {
            Log.w(TAG, "нет связи с GitHub, беру сохранённую сборку: " + t);
            toast(a, "нет связи с GitHub (" + t + "), беру сохранённую сборку", true);
        }
        if (want != null && (!want.equals(have) || !so.exists() || !jar.exists())) {
            toast(a, "качаю обновление…", false);
            File so2 = new File(dir, "libmggpanel.so.tmp");
            File jar2 = new File(dir, "overlay.jar.tmp");
            download(BASE + "libmggpanel.so", so2);
            download(BASE + "overlay.jar", jar2);
            so.delete();            // старые файлы только для чтения: удаляем и кладём новые
            jar.delete();
            if (!so2.renameTo(so) || !jar2.renameTo(jar)) throw new IOException("не удалось переименовать скачанные файлы");
            writeText(ver, want);
            Log.i(TAG, "обновлено до " + want);
        }
        if (!so.exists() || !jar.exists()) { Log.w(TAG, "нечего загружать (нет сети и нет сохранённой сборки)"); toast(a, "нечего загружать: нет сети и нет сохранённой сборки", true); return; }
        so.setReadOnly();
        jar.setReadOnly();          // Android 14+: загружаемый код должен быть только для чтения

        System.load(so.getAbsolutePath());
        ClassLoader cl = new DexClassLoader(jar.getAbsolutePath(), a.getCodeCacheDir().getAbsolutePath(), null, a.getClassLoader());
        Class<?> c = cl.loadClass("mgg.Overlay");
        final Method m = c.getMethod("start", Activity.class);
        String v = want != null ? want : have;
        final String v7 = v == null ? "?" : v.length() > 7 ? v.substring(0, 7) : v;
        a.runOnUiThread(new Runnable() {
            public void run() {
                try {
                    m.invoke(null, a);
                    toast(a, "ok " + v7, false);
                } catch (Throwable t) {
                    Log.e(TAG, "overlay: " + t);
                    toast(a, "overlay: " + t, true);
                }
            }
        });
    }

    private static void toast(final Activity a, final String s, final boolean lng) {
        Log.i(TAG, s);
        new Handler(Looper.getMainLooper()).post(new Runnable() {
            public void run() {
                try {
                    Toast.makeText(a, "MGG: " + s, lng ? Toast.LENGTH_LONG : Toast.LENGTH_SHORT).show();
                } catch (Throwable ignore) {}
            }
        });
    }

    private static HttpURLConnection open(String url) throws IOException {
        HttpURLConnection c = (HttpURLConnection) new URL(url).openConnection();
        c.setConnectTimeout(5000);
        c.setReadTimeout(15000);
        c.setUseCaches(false);
        c.setRequestProperty("User-Agent", "mgg-loader");
        if (c.getResponseCode() != 200) throw new IOException("HTTP " + c.getResponseCode() + " " + url);
        return c;
    }

    private static String fetchText(String url) throws IOException {
        HttpURLConnection c = open(url);
        try {
            InputStream in = c.getInputStream();
            ByteArrayOutputStream bo = new ByteArrayOutputStream();
            byte[] b = new byte[512];
            int n;
            while ((n = in.read(b)) > 0 && bo.size() < 4096) bo.write(b, 0, n);
            in.close();
            return bo.toString("UTF-8").trim();
        } finally {
            c.disconnect();
        }
    }

    private static void download(String url, File out) throws IOException {
        HttpURLConnection c = open(url);
        try {
            InputStream in = c.getInputStream();
            OutputStream os = new FileOutputStream(out);
            byte[] b = new byte[16384];
            int n;
            while ((n = in.read(b)) > 0) os.write(b, 0, n);
            os.close();
            in.close();
        } finally {
            c.disconnect();
        }
        if (out.length() == 0) throw new IOException("пустой файл " + url);
    }

    private static String readText(File f) {
        try {
            FileInputStream in = new FileInputStream(f);
            ByteArrayOutputStream bo = new ByteArrayOutputStream();
            byte[] b = new byte[256];
            int n;
            while ((n = in.read(b)) > 0) bo.write(b, 0, n);
            in.close();
            return bo.toString("UTF-8").trim();
        } catch (Throwable t) {
            return null;
        }
    }

    private static void writeText(File f, String s) throws IOException {
        FileOutputStream os = new FileOutputStream(f);
        os.write(s.getBytes("UTF-8"));
        os.close();
    }
}
