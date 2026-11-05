import base64
import math
import os
import queue
import re
import shlex
import shutil
import struct
import subprocess
import sys
import tempfile
import threading
import time
import tkinter as tk
import urllib.request
import zipfile
import zlib
from tkinter import filedialog, ttk
from tkinter import font as tkfont

FORMATS = {
    "Opus": ("opus", None),
    "MP3(最高音質設定)": ("mp3", "0"),
    "FLAC": ("flac", None),
    "M4A": ("m4a", None),
}
DEFAULT_FORMAT = "MP3(最高音質設定)"

ADV_DEFAULTS = {
    "fmt": "ba",
    "name": "%(title)s.%(ext)s",
    "quality": "既定",
    "rate": "",
    "cookies": "なし",
    "proxy": "",
    "meta": True,
    "thumb": True,
    "playlist": False,
    "extra": "",
}
QUALITIES = ["既定", "0", "2", "5", "9", "320K", "256K", "192K", "128K"]
BROWSERS = ["なし", "chrome", "edge", "firefox", "brave", "opera", "vivaldi"]

BIN_DIR = os.path.join(
    os.environ.get("LOCALAPPDATA", os.path.expanduser("~")), "yt_dlp_gui", "bin"
)
YTDLP_URL = "https://github.com/yt-dlp/yt-dlp/releases/latest/download/yt-dlp.exe"
FFMPEG_URLS = [
    "https://www.gyan.dev/ffmpeg/builds/ffmpeg-release-essentials.zip",
    "https://github.com/BtbN/FFmpeg-Builds/releases/latest/download/ffmpeg-master-latest-win64-gpl.zip",
]

FONT_FILE = os.path.join(os.path.dirname(os.path.abspath(__file__)), "NotoSansJP-Thin.ttf")
FONT_NAME = "Noto Sans JP Thin"
FALLBACK_FONT = "Yu Gothic UI"

BLACK = "#000000"
FIELD = "#0c0c0c"
FG = "#ffffff"
MUTED = "#a8a8a8"
LOG_FG = "#d0d0d0"
ERR = "#ff5c6c"
SELECT = "#4a4a4a"
BAR_FG = "#e6e6e6"

PROGRESS_RE = re.compile(r"\[download\]\s+(\d+(?:\.\d+)?)%")

PANEL_X = 24
PANEL_W = 492
PANEL_LADDER = [492, 524, 541, 550, 554]

BAR_X, BAR_Y, BAR_W, BAR_H = 48, 338, 444, 28
BAR_PAD = 4

STYLES = {
    "panel": dict(fill=(255, 255, 255), a_top=0.12, a_bot=0.07, spec=0.05, rim=0.55, glow=0.05),
    "field": dict(fill=(12, 12, 12), a_top=1.0, a_bot=1.0, spec=0.0, rim=0.30, glow=0.0, inset=True),
    "btn": dict(fill=(255, 255, 255), a_top=0.20, a_bot=0.11, spec=0.06, rim=0.70, glow=0.05),
    "btn_hover": dict(fill=(255, 255, 255), a_top=0.30, a_bot=0.18, spec=0.08, rim=0.85, glow=0.06),
    "btn_off": dict(fill=(255, 255, 255), a_top=0.07, a_bot=0.04, spec=0.02, rim=0.30, glow=0.02),
}
RIM_COLOR = (240, 240, 244)


def _png(w, h, rows):
    raw = b"".join(b"\x00" + bytes(r) for r in rows)

    def chunk(tag, data):
        body = struct.pack(">I", len(data)) + tag + data
        return body + struct.pack(">I", zlib.crc32(tag + data) & 0xFFFFFFFF)

    return (
        b"\x89PNG\r\n\x1a\n"
        + chunk(b"IHDR", struct.pack(">IIBBBBB", w, h, 8, 6, 0, 0, 0))
        + chunk(b"IDAT", zlib.compress(raw, 6))
        + chunk(b"IEND", b"")
    )


def glass_png(w, h, r, st):
    band = 10
    fill = st["fill"]
    inset = st.get("inset", False)

    def px(x, y, v, a_int):
        cx = min(max(x + 0.5, r), w - r)
        cy = min(max(y + 0.5, r), h - r)
        d = math.hypot(x + 0.5 - cx, y + 0.5 - cy) - r
        cov = 0.5 - d
        if cov <= 0:
            return b"\x00\x00\x00\x00"
        cov = min(cov, 1.0)
        depth = max(-d, 0.0)

        prof = max(0.0, 1.0 - depth / 1.7)
        gl = max(0.0, 1.0 - depth / 9.0) ** 2

        diag = ((x + 0.5) / w + v) / 2
        if inset:
            orient = 0.10 + 0.55 * v
        else:
            tl = max(0.0, 1.0 - diag * 2.3)
            br = max(0.0, 1.0 - (1.0 - diag) * 2.3)
            orient = min(1.0, 0.30 + 0.70 * max(tl, 0.75 * br))

        a_rim = st["rim"] * orient * prof
        a_fill = min(1.0, a_int + st["glow"] * orient * gl)
        total = 1.0 - (1.0 - a_fill) * (1.0 - a_rim)
        if total <= 0:
            return b"\x00\x00\x00\x00"
        k_fill = a_fill * (1.0 - a_rim) / total
        k_rim = a_rim / total
        rgb = [min(255, int(fill[i] * k_fill + RIM_COLOR[i] * k_rim + 0.5)) for i in range(3)]
        return bytes((rgb[0], rgb[1], rgb[2], int(total * cov * 255 + 0.5)))

    rows = []
    for y in range(h):
        v = (y + 0.5) / h
        a_int = st["a_top"] + (st["a_bot"] - st["a_top"]) * v
        a_int = min(1.0, a_int + st["spec"] * math.exp(-((v / 0.22) ** 2)))
        inner = bytes((fill[0], fill[1], fill[2], int(a_int * 255 + 0.5)))
        row = bytearray()
        if y < band or y >= h - band:
            for x in range(w):
                row += px(x, y, v, a_int)
        else:
            edge = (r + band) if (y < r or y >= h - r) else band
            edge = min(edge, w // 2)
            for x in range(edge):
                row += px(x, y, v, a_int)
            row += inner * (w - 2 * edge)
            for x in range(w - edge, w):
                row += px(x, y, v, a_int)
        rows.append(row)
    return _png(w, h, rows)


def pick_font_family(root):
    registered = False
    if sys.platform == "win32" and os.path.exists(FONT_FILE):
        try:
            import ctypes

            registered = ctypes.windll.gdi32.AddFontResourceExW(FONT_FILE, 0x10, 0) > 0
        except Exception:
            pass
    if registered or FONT_NAME in tkfont.families(root):
        return FONT_NAME
    return FALLBACK_FONT


def tool_env():
    env = os.environ.copy()
    env["PATH"] = BIN_DIR + os.pathsep + env.get("PATH", "")
    return env


def download_file(url, dest):
    req = urllib.request.Request(url, headers={"User-Agent": "Mozilla/5.0"})
    tmp = dest + ".part"
    with urllib.request.urlopen(req, timeout=60) as r, open(tmp, "wb") as f:
        shutil.copyfileobj(r, f)
    os.replace(tmp, dest)


def show_command(cmd):
    return " ".join('"%s"' % a if (not a or " " in a) else a for a in cmd)


class App(tk.Tk):
    W, H = 540, 540
    ADV_W = 980

    def __init__(self):
        super().__init__()
        self.title("yt_dlp")

        # タイトルバーのアイコン（スクリプトと同じフォルダの yt-dlp.ico）
        icon_path = os.path.join(os.path.dirname(os.path.abspath(__file__)), "yt-dlp.ico")
        try:
            if os.path.isfile(icon_path):
                self.iconbitmap(default=icon_path)
        except tk.TclError:
            # アイコンが未配置、またはTkが形式を読み込めない場合も起動を続行
            pass

        self.geometry(f"{self.W}x{self.H}")
        self.resizable(False, False)
        self.configure(bg=BLACK)

        fam = pick_font_family(self)
        self.f_label = (fam, 10)
        self.f_small = (fam, 9)
        self.f_entry = (fam, 11)
        self.f_btn = (fam, 12)
        self.f_log = (fam, 10)

        self.q = queue.Queue()
        self.running = False
        self.imgs = {}
        self.png_ready = {}
        self.bar_value = 0.0
        self.bar_target = 0.0
        self.bar_error = False
        self.pct_text = ""

        self.advanced = False
        self.adv_shown = False
        self.win_w = float(self.W)
        self.win_target = self.W
        self.cur_h = self.H
        self.anim_id = None
        self.bg_clicks = []
        self.toggles = []

        self.panel_idx = 0
        self.log_want = False
        self.log_busy = False
        self.auto_opened = False

        threading.Thread(target=self.prewarm, daemon=True).start()

        self.setup_styles()
        self.canvas = tk.Canvas(
            self,
            width=self.ADV_W,
            height=PANEL_LADDER[-1] + 48,
            bg=BLACK,
            highlightthickness=0,
            bd=0,
        )
        self.canvas.pack(fill="both", expand=True)
        self.build_ui()
        self.build_adv()
        self.canvas.itemconfigure("adv", state="hidden")
        self.canvas.itemconfigure("logbox", state="hidden")
        self.canvas.bind("<Button-1>", self.on_canvas_click, add="+")

        self.after(50, self.dark_titlebar)
        self.after(100, self.poll_log)
        self.after(30, self.tick_bar)

    def prewarm(self):
        for h in PANEL_LADDER[1:]:
            key = (PANEL_W, h, 26, "panel")
            if key not in self.png_ready:
                self.png_ready[key] = glass_png(key[0], key[1], key[2], STYLES[key[3]])

    def setup_styles(self):
        style = ttk.Style(self)
        try:
            style.theme_use("clam")
        except tk.TclError:
            pass
        style.configure(
            "TCombobox",
            fieldbackground=FIELD, background=FIELD, foreground=FG,
            arrowcolor="#ffffff", bordercolor=FIELD, lightcolor=FIELD, darkcolor=FIELD,
            selectbackground=FIELD, selectforeground=FG, borderwidth=0, padding=4,
        )
        style.map(
            "TCombobox",
            fieldbackground=[("readonly", FIELD)],
            foreground=[("readonly", FG)],
            selectbackground=[("readonly", FIELD)],
            selectforeground=[("readonly", FG)],
            bordercolor=[("focus", FIELD)],
        )
        self.option_add("*TCombobox*Listbox.background", "#161616")
        self.option_add("*TCombobox*Listbox.foreground", FG)
        self.option_add("*TCombobox*Listbox.selectBackground", SELECT)
        self.option_add("*TCombobox*Listbox.selectForeground", "#ffffff")
        self.option_add("*TCombobox*Listbox.font", self.f_entry)

    def dark_titlebar(self):
        if sys.platform != "win32":
            return
        try:
            import ctypes

            self.update_idletasks()
            hwnd = ctypes.windll.user32.GetParent(self.winfo_id())
            dwm = ctypes.windll.dwmapi

            def put(attr, value):
                v = ctypes.c_int(value)
                dwm.DwmSetWindowAttribute(hwnd, attr, ctypes.byref(v), ctypes.sizeof(v))

            put(20, 1)
            put(19, 1)
            put(35, 0x000000)
            put(36, 0xFFFFFF)
            put(34, 0x000000)
        except Exception:
            pass

    def img(self, w, h, r, style):
        key = (w, h, r, style)
        if key not in self.imgs:
            png = self.png_ready.get(key) or glass_png(w, h, r, STYLES[style])
            self.imgs[key] = tk.PhotoImage(data=base64.b64encode(png))
        return self.imgs[key]

    def make_button(self, x, y, w, h, text, command, font=None, tags=()):
        c = self.canvas
        tag = f"btn_{x}_{y}"
        all_tags = (tag,) + tuple(tags)
        r = 12
        btn = {
            "tag": tag,
            "n": self.img(w, h, r, "btn"),
            "h": self.img(w, h, r, "btn_hover"),
            "off": self.img(w, h, r, "btn_off"),
            "locked": False,
        }
        btn["iid"] = c.create_image(x, y, image=btn["n"], anchor="nw", tags=all_tags)
        btn["tid"] = c.create_text(
            x + w / 2, y + h / 2, text=text, fill=FG, font=font or self.f_btn, tags=all_tags
        )

        def on_enter(_e):
            if not btn["locked"]:
                c.itemconfigure(btn["iid"], image=btn["h"])
                c.configure(cursor="hand2")

        def on_leave(_e):
            if not btn["locked"]:
                c.itemconfigure(btn["iid"], image=btn["n"])
            c.configure(cursor="")

        c.tag_bind(tag, "<Enter>", on_enter)
        c.tag_bind(tag, "<Leave>", on_leave)
        c.tag_bind(tag, "<Button-1>", lambda e: command())
        return btn

    def set_button_locked(self, btn, locked, text):
        c = self.canvas
        btn["locked"] = locked
        c.itemconfigure(btn["iid"], image=btn["off"] if locked else btn["n"])
        c.itemconfigure(btn["tid"], text=text, fill=MUTED if locked else FG)
        if locked:
            c.configure(cursor="")

    def place_entry(self, var, x, y, w, h, tags=()):
        e = tk.Entry(
            self.canvas, textvariable=var, bg=FIELD, fg=FG, insertbackground="#ffffff",
            relief="flat", bd=0, highlightthickness=0, font=self.f_entry,
            selectbackground=SELECT, selectforeground="#ffffff",
        )
        self.canvas.create_window(x, y, window=e, anchor="nw", width=w, height=h, tags=tags)
        return e

    def build_ui(self):
        c = self.canvas

        def label(x, y, text):
            c.create_text(x, y, text=text, fill=MUTED, font=self.f_label, anchor="w")

        self.panel_item = c.create_image(
            PANEL_X, 24, image=self.img(PANEL_W, PANEL_LADDER[0], 26, "panel"), anchor="nw"
        )

        label(52, 58, "URL")
        c.create_image(48, 70, image=self.img(444, 40, 10, "field"), anchor="nw")
        self.url_var = tk.StringVar()
        self.place_entry(self.url_var, 60, 75, 420, 30)

        label(52, 128, "保存先")
        c.create_image(48, 140, image=self.img(358, 40, 10, "field"), anchor="nw")
        self.dir_var = tk.StringVar(value=os.path.join(os.path.expanduser("~"), "Downloads"))
        self.place_entry(self.dir_var, 60, 145, 334, 30)
        self.make_button(416, 140, 76, 40, "選択", self.choose_dir)

        label(52, 198, "形式")
        c.create_image(48, 210, image=self.img(444, 40, 10, "field"), anchor="nw")
        self.fmt_var = tk.StringVar(value=DEFAULT_FORMAT)
        combo = ttk.Combobox(
            c, textvariable=self.fmt_var, values=list(FORMATS), state="readonly", font=self.f_entry
        )
        c.create_window(54, 214, window=combo, anchor="nw", width=432, height=32)

        self.main_btn = self.make_button(48, 274, 444, 46, "ダウンロード", self.start)

        c.create_image(
            BAR_X, BAR_Y, image=self.img(BAR_W, BAR_H, BAR_H // 2, "field"), anchor="nw"
        )
        self.bar_line = c.create_line(
            0, 0, 0, 0, width=BAR_H - 2 * BAR_PAD, capstyle="round", fill=BAR_FG, state="hidden"
        )
        self.pct_item = c.create_text(
            BAR_X + BAR_W / 2, BAR_Y + BAR_H + 14, text="0%", fill=MUTED, font=self.f_small
        )

        self.log_btn = self.make_button(48, 396, 444, 34, "", self.toggle_log)
        self.log_tri = c.create_polygon(
            0, 0, 0, 0, 0, 0, fill=MUTED, outline="", tags=(self.log_btn["tag"],)
        )
        c.create_text(
            86, 413, text="ログ", fill=FG, font=self.f_label, anchor="w", tags=(self.log_btn["tag"],)
        )
        self.draw_tri()

        logtags = ("logbox",)
        c.create_image(48, 438, image=self.img(444, 120, 10, "field"), anchor="nw", tags=logtags)
        self.log = tk.Text(
            c, bg=FIELD, fg=LOG_FG, font=self.f_log, relief="flat", bd=0,
            highlightthickness=0, state="disabled", wrap="word", selectbackground=SELECT,
        )
        self.log.tag_configure("error", foreground=ERR)
        c.create_window(60, 448, window=self.log, anchor="nw", width=420, height=100, tags=logtags)

    def draw_tri(self):
        cx, cy = 66, 413
        if self.log_want:
            pts = (cx - 5, cy - 3, cx + 5, cy - 3, cx, cy + 4)
        else:
            pts = (cx - 3, cy - 5, cx + 4, cy, cx - 3, cy + 5)
        self.canvas.coords(self.log_tri, *pts)
        self.canvas.itemconfigure(self.log_tri, fill=FG if self.log_want else MUTED)

    def set_geometry(self):
        self.geometry(f"{int(round(self.win_w))}x{self.cur_h}")

    def apply_panel(self):
        h = PANEL_LADDER[self.panel_idx]
        self.canvas.itemconfigure(self.panel_item, image=self.img(PANEL_W, h, 26, "panel"))
        self.cur_h = h + 48
        self.set_geometry()

    def toggle_log(self):
        self.set_log(not self.log_want)

    def set_log(self, want):
        self.log_want = want
        self.draw_tri()
        self.log_update()

    def log_update(self):
        if self.log_busy:
            return
        target = len(PANEL_LADDER) - 1 if self.log_want else 0
        if self.panel_idx == target:
            self.canvas.itemconfigure("logbox", state="normal" if self.log_want else "hidden")
            return
        self.canvas.itemconfigure("logbox", state="hidden")
        self.log_busy = True
        self.log_step(target)

    def log_step(self, target):
        if self.panel_idx == target:
            self.log_busy = False
            self.log_update()
            return
        self.panel_idx += 1 if target > self.panel_idx else -1
        self.apply_panel()
        self.after(18, lambda: self.log_step(target))

    def adv_label(self, x, y, text):
        return self.canvas.create_text(
            x, y, text=text, fill=MUTED, font=self.f_label, anchor="w", tags=("adv",)
        )

    def adv_entry(self, var, x, y, w):
        self.canvas.create_image(
            x, y, image=self.img(w, 40, 10, "field"), anchor="nw", tags=("adv",)
        )
        return self.place_entry(var, x + 12, y + 5, w - 24, 30, ("adv",))

    def adv_combo(self, var, values, x, y, w):
        c = self.canvas
        c.create_image(x, y, image=self.img(w, 40, 10, "field"), anchor="nw", tags=("adv",))
        combo = ttk.Combobox(
            c, textvariable=var, values=values, state="readonly", font=self.f_entry
        )
        c.create_window(
            x + 6, y + 4, window=combo, anchor="nw", width=w - 12, height=32, tags=("adv",)
        )
        return combo

    def adv_toggle(self, x, y, text, var):
        c = self.canvas
        tag = f"tg_{x}_{y}"
        t = {
            "var": var,
            "off": self.img(24, 24, 8, "field"),
            "on": self.img(24, 24, 8, "btn_hover"),
        }
        t["iid"] = c.create_image(x, y, image=t["off"], anchor="nw", tags=(tag, "adv"))
        t["ck"] = c.create_line(
            x + 6, y + 12, x + 10, y + 17, x + 18, y + 7,
            width=2, fill=FG, capstyle="round", joinstyle="round", tags=(tag, "adv"),
        )
        c.create_text(
            x + 34, y + 12, text=text, fill=FG, font=self.f_label, anchor="w", tags=(tag, "adv")
        )

        def click(_e):
            var.set(not var.get())
            self.refresh_toggles()

        c.tag_bind(tag, "<Button-1>", click)
        c.tag_bind(tag, "<Enter>", lambda e: c.configure(cursor="hand2"))
        c.tag_bind(tag, "<Leave>", lambda e: c.configure(cursor=""))
        self.toggles.append(t)

    def refresh_toggles(self):
        for t in self.toggles:
            on = bool(t["var"].get())
            self.canvas.itemconfigure(t["iid"], image=t["on"] if on else t["off"])
            self.canvas.itemconfigure(
                t["ck"], state="normal" if (on and self.adv_shown) else "hidden"
            )

    def build_adv(self):
        c = self.canvas
        d = ADV_DEFAULTS
        self.adv_fmt = tk.StringVar(value=d["fmt"])
        self.adv_name = tk.StringVar(value=d["name"])
        self.adv_quality = tk.StringVar(value=d["quality"])
        self.adv_rate = tk.StringVar(value=d["rate"])
        self.adv_cookies = tk.StringVar(value=d["cookies"])
        self.adv_proxy = tk.StringVar(value=d["proxy"])
        self.adv_meta = tk.BooleanVar(value=d["meta"])
        self.adv_thumb = tk.BooleanVar(value=d["thumb"])
        self.adv_playlist = tk.BooleanVar(value=d["playlist"])
        self.adv_extra = tk.StringVar(value=d["extra"])

        c.create_image(540, 24, image=self.img(416, 492, 26, "panel"), anchor="nw", tags=("adv",))
        c.create_text(
            566, 54, text="詳細設定", fill=FG, font=self.f_btn, anchor="w", tags=("adv",)
        )
        self.make_button(
            828, 40, 104, 28, "初期値に戻す", self.reset_adv, font=self.f_label, tags=("adv",)
        )

        self.adv_label(568, 88, "フォーマット指定  -f")
        self.adv_entry(self.adv_fmt, 564, 100, 368)

        self.adv_label(568, 160, "ファイル名  -o")
        self.adv_entry(self.adv_name, 564, 172, 368)

        self.adv_label(568, 232, "音質  --audio-quality")
        self.adv_combo(self.adv_quality, QUALITIES, 564, 244, 176)
        self.adv_label(760, 232, "速度制限  -r")
        self.adv_entry(self.adv_rate, 756, 244, 176)

        self.adv_label(568, 304, "cookieの取得元")
        self.adv_combo(self.adv_cookies, BROWSERS, 564, 316, 176)
        self.adv_label(760, 304, "プロキシ  --proxy")
        self.adv_entry(self.adv_proxy, 756, 316, 176)

        self.adv_toggle(566, 376, "メタデータ", self.adv_meta)
        self.adv_toggle(686, 376, "サムネイル", self.adv_thumb)
        self.adv_toggle(806, 376, "プレイリスト", self.adv_playlist)

        self.adv_label(568, 426, "追加の引数")
        self.adv_entry(self.adv_extra, 564, 438, 368)

    def reset_adv(self):
        d = ADV_DEFAULTS
        self.adv_fmt.set(d["fmt"])
        self.adv_name.set(d["name"])
        self.adv_quality.set(d["quality"])
        self.adv_rate.set(d["rate"])
        self.adv_cookies.set(d["cookies"])
        self.adv_proxy.set(d["proxy"])
        self.adv_meta.set(d["meta"])
        self.adv_thumb.set(d["thumb"])
        self.adv_playlist.set(d["playlist"])
        self.adv_extra.set(d["extra"])
        self.refresh_toggles()

    def on_canvas_click(self, e):
        c = self.canvas
        x, y = c.canvasx(e.x), c.canvasy(e.y)
        if c.find_overlapping(x, y, x, y):
            self.bg_clicks = []
            return
        now = time.time()
        self.bg_clicks = [t for t in self.bg_clicks if now - t <= 2.0] + [now]
        if len(self.bg_clicks) >= 5:
            self.bg_clicks = []
            self.toggle_mode()

    def toggle_mode(self):
        self.advanced = not self.advanced
        if self.advanced:
            self.adv_shown = True
            self.canvas.itemconfigure("adv", state="normal")
            self.refresh_toggles()
        self.win_target = self.ADV_W if self.advanced else self.W
        self.animate_window()

    def animate_window(self):
        if self.anim_id is not None:
            self.after_cancel(self.anim_id)
            self.anim_id = None
        diff = self.win_target - self.win_w
        if abs(diff) < 1.5:
            self.win_w = float(self.win_target)
            self.set_geometry()
            if not self.advanced:
                self.adv_shown = False
                self.canvas.itemconfigure("adv", state="hidden")
                self.focus_set()
            self.anim_id = None
            return
        self.win_w += diff * 0.28
        self.set_geometry()
        self.anim_id = self.after(16, self.animate_window)

    def reset_bar(self):
        self.bar_value = 0.0
        self.bar_target = 0.0
        self.bar_error = False

    def tick_bar(self):
        if not self.bar_error:
            diff = self.bar_target - self.bar_value
            if abs(diff) < 0.05:
                self.bar_value = self.bar_target
            else:
                self.bar_value += diff * 0.2
        c = self.canvas
        if self.bar_value <= 0:
            c.itemconfigure(self.bar_line, state="hidden")
        else:
            r = BAR_H // 2
            x0 = BAR_X + r
            x1 = x0 + (BAR_W - 2 * r) * self.bar_value / 100
            cy = BAR_Y + r
            c.coords(self.bar_line, x0, cy, x1, cy)
            c.itemconfigure(
                self.bar_line, state="normal", fill=ERR if self.bar_error else BAR_FG
            )
        shown = 0 if (self.bar_error and self.bar_target == 0) else int(self.bar_value)
        text = f"{shown}%"
        if text != self.pct_text:
            self.pct_text = text
            c.itemconfigure(self.pct_item, text=text)
        self.after(30, self.tick_bar)

    def write_log(self, text, tag=None):
        self.log.configure(state="normal")
        self.log.insert("end", text + "\n", tag)
        self.log.see("end")
        self.log.configure(state="disabled")
        if tag == "error" and not self.auto_opened:
            self.auto_opened = True
            self.set_log(True)

    def poll_log(self):
        try:
            while True:
                item = self.q.get_nowait()
                kind = item[0]
                if kind == "log":
                    self.write_log(item[1], item[2])
                elif kind == "progress":
                    if not self.bar_error:
                        self.bar_target = item[1]
                elif kind == "bar_error":
                    if not self.bar_error:
                        self.bar_error = True
                        if self.bar_value < 2:
                            self.bar_value = 2.0
                elif kind == "done":
                    self.running = False
                    self.set_button_locked(self.main_btn, False, "ダウンロード")
        except queue.Empty:
            pass
        self.after(100, self.poll_log)

    def say(self, text):
        self.q.put(("log", text, None))

    def err(self, text):
        self.q.put(("log", text, "error"))

    def choose_dir(self):
        d = filedialog.askdirectory(initialdir=self.dir_var.get())
        if d:
            self.dir_var.set(d)

    def parse_extra(self):
        s = self.adv_extra.get().strip()
        if not s:
            return []
        tokens = shlex.split(s, posix=False)
        return [
            t[1:-1] if len(t) >= 2 and t[0] == t[-1] and t[0] in "\"'" else t for t in tokens
        ]

    def build_command(self, url, out_dir):
        codec, default_quality = FORMATS[self.fmt_var.get()]
        if not self.advanced:
            cmd = ["yt-dlp", "-f", "ba", "-x", "--audio-format", codec]
            if default_quality:
                cmd += ["--audio-quality", default_quality]
            cmd += [
                "--no-playlist", "--newline",
                "--embed-metadata",
                "--embed-thumbnail",
                "--convert-thumbnails", "jpg",
                "-o", "%(title)s.%(ext)s",
                "-P", out_dir,
                url,
            ]
            return cmd

        cmd = ["yt-dlp", "-f", self.adv_fmt.get().strip() or "ba", "-x", "--audio-format", codec]
        quality = self.adv_quality.get()
        if quality == "既定":
            quality = default_quality
        if quality:
            cmd += ["--audio-quality", quality]
        cmd += ["--yes-playlist" if self.adv_playlist.get() else "--no-playlist", "--newline"]
        if self.adv_meta.get():
            cmd.append("--embed-metadata")
        if self.adv_thumb.get():
            cmd += ["--embed-thumbnail", "--convert-thumbnails", "jpg"]
        cookies = self.adv_cookies.get()
        if cookies and cookies != "なし":
            cmd += ["--cookies-from-browser", cookies]
        rate = self.adv_rate.get().strip()
        if rate:
            cmd += ["-r", rate]
        proxy = self.adv_proxy.get().strip()
        if proxy:
            cmd += ["--proxy", proxy]
        cmd += ["-o", self.adv_name.get().strip() or ADV_DEFAULTS["name"], "-P", out_dir]
        cmd += self.parse_extra()
        cmd.append(url)
        return cmd

    def start(self):
        if self.running:
            return
        self.auto_opened = False
        url = self.url_var.get().strip()
        if not url:
            self.write_log("ERROR(URLが入力されていません)", "error")
            return
        out_dir = self.dir_var.get().strip()
        try:
            cmd = self.build_command(url, out_dir)
        except ValueError:
            self.write_log("ERROR(追加の引数を解釈できません)", "error")
            return
        self.url_var.set("")
        self.reset_bar()
        if self.advanced:
            self.write_log("> " + show_command(cmd))
        self.running = True
        self.set_button_locked(self.main_btn, True, "ダウンロード中...")
        threading.Thread(target=self.run, args=(cmd, out_dir), daemon=True).start()

    def missing_tools(self):
        path = tool_env()["PATH"]
        return [n for n in ("yt-dlp", "ffmpeg") if not shutil.which(n, path=path)]

    def install_ytdlp(self):
        self.say("yt-dlpをダウンロード中...")
        download_file(YTDLP_URL, os.path.join(BIN_DIR, "yt-dlp.exe"))

    def install_ffmpeg(self):
        self.say("ffmpegをダウンロード中(数分かかる場合があります)...")
        last_error = None
        for url in FFMPEG_URLS:
            zip_path = os.path.join(tempfile.gettempdir(), "yt_dlp_gui_ffmpeg.zip")
            try:
                download_file(url, zip_path)
                with zipfile.ZipFile(zip_path) as z:
                    for name in ("ffmpeg.exe", "ffprobe.exe"):
                        member = next(m for m in z.namelist() if m.endswith("/bin/" + name))
                        with z.open(member) as src, open(os.path.join(BIN_DIR, name), "wb") as dst:
                            shutil.copyfileobj(src, dst)
                return
            except Exception as e:
                last_error = e
            finally:
                if os.path.exists(zip_path):
                    os.remove(zip_path)
        raise last_error

    def ensure_tools(self):
        missing = self.missing_tools()
        if not missing:
            return True
        self.err("ERROR(yt-dlpもしくはffmpegが見つかりません。自動でインストールします)")
        if sys.platform != "win32":
            self.err("ERROR(自動インストールはWindowsのみ対応しています)")
            return False
        try:
            os.makedirs(BIN_DIR, exist_ok=True)
            if "yt-dlp" in missing:
                self.install_ytdlp()
            if "ffmpeg" in missing:
                self.install_ffmpeg()
        except Exception as e:
            self.err(f"ERROR(インストールに失敗しました: {e})")
            return False
        self.say("インストール完了")
        return True

    def run(self, cmd, out_dir):
        try:
            if not self.ensure_tools():
                self.q.put(("bar_error",))
                return
            os.makedirs(out_dir, exist_ok=True)
            flags = subprocess.CREATE_NO_WINDOW if sys.platform == "win32" else 0
            proc = subprocess.Popen(
                cmd,
                stdout=subprocess.PIPE,
                stderr=subprocess.STDOUT,
                text=True,
                encoding="utf-8",
                errors="replace",
                env=tool_env(),
                creationflags=flags,
            )
            for line in proc.stdout:
                line = line.rstrip()
                m = PROGRESS_RE.match(line)
                if m:
                    self.q.put(("progress", float(m.group(1)) * 0.95))
                is_err = line.startswith("ERROR")
                if is_err:
                    self.q.put(("bar_error",))
                self.q.put(("log", line, "error" if is_err else None))
            code = proc.wait()
            if code == 0:
                self.q.put(("progress", 100.0))
                self.say("完了")
            else:
                self.q.put(("bar_error",))
                self.err(f"ERROR(終了コード:{code})")
        except Exception as e:
            self.q.put(("bar_error",))
            self.err(f"ERROR({e})")
        finally:
            self.q.put(("done",))


if __name__ == "__main__":
    App().mainloop()
