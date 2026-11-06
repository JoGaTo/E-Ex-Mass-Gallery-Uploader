from http.cookiejar import CookieJar
import io
import importlib
import importlib.util
import json
import mimetypes
import os
import html
import hashlib
import queue
import re
import subprocess
import sys
import tempfile
import traceback
import threading
import time
import tkinter as tk
import tkinter.font as tkfont
import zipfile
from concurrent.futures import ThreadPoolExecutor
from pathlib import Path
from tkinter import filedialog, messagebox, simpledialog, ttk
from urllib.parse import quote, urljoin
import webbrowser

# Python 3.14's Windows platform detection may block in a WMI query while
# CustomTkinter imports darkdetect. Use Python's built-in non-WMI fallback
# just for that import; the rest of the process keeps normal WMI behavior.
if sys.platform == "win32" and sys.version_info >= (3, 14):
    import platform as _platform
    _saved_wmi = getattr(_platform, "_wmi", None)
    try:
        _platform._wmi = None
        import customtkinter as ctk
    finally:
        _platform._wmi = _saved_wmi
else:
    import customtkinter as ctk
import requests
import shutil
from bs4 import BeautifulSoup
from PIL import Image, ImageDraw, ImageEnhance, ImageFilter, ImageFont, ImageOps, ImageTk
from requests.adapters import HTTPAdapter
from urllib3.util.retry import Retry


def _draw_scrollbar_without_nested_events(self, no_color_updates=False):
    """Draw CTk scrollbars without recursively pumping Tk's idle event queue.

    CTkScrollbar._draw calls canvas.update_idletasks(), including from the
    scrollcommand callback. Several textboxes/scrollable frames can recursively
    reenter one another during resize and focus changes. Drawing canvas items
    is sufficient; Tk paints them when the current callback returns.
    This compatibility fix affects this process only, not the installed package.
    """
    super(ctk.CTkScrollbar, self)._draw(no_color_updates)
    start, end = self._get_scrollbar_values_for_minimum_pixel_size()
    recolor = self._draw_engine.draw_rounded_scrollbar(
        self._apply_widget_scaling(self._current_width),
        self._apply_widget_scaling(self._current_height),
        self._apply_widget_scaling(self._corner_radius),
        self._apply_widget_scaling(self._border_spacing), start, end, self._orientation)
    if not no_color_updates or recolor:
        button = self._button_hover_color if self._hover_state else self._button_color
        color = self._apply_appearance_mode(button)
        self._canvas.itemconfig("scrollbar_parts", fill=color, outline=color)
        background = self._bg_color if self._fg_color == "transparent" else self._fg_color
        background = self._apply_appearance_mode(background)
        self._canvas.configure(bg=background)
        self._canvas.itemconfig("border_parts", fill=background, outline=background)


ctk.CTkScrollbar._draw = _draw_scrollbar_without_nested_events

# Optional browser packages are intentionally only detected here. Importing
# PySide6/tkinterweb/pywebview during application startup is expensive and none
# of them is needed until the user actually opens a browser result.
def _module_available(module_name):
    try:
        return importlib.util.find_spec(module_name) is not None
    except Exception:
        return False


HtmlFrame = None
tkhtml_runtime = None
webview = None
HAS_TKINTERWEB = _module_available("tkinterweb")
HAS_TKHTML_RUNTIME = _module_available("tkinterweb_tkhtml")
HAS_PYWEBVIEW = _module_available("webview")
# Checking a dotted module can import its parent package.  Detect the lightweight
# PySide6 package marker here; the isolated browser process validates WebEngine
# only when the feature is actually opened.
HAS_QT_CHROMIUM = _module_available("PySide6")

try:
    from tkinterdnd2 import DND_FILES, TkinterDnD

    HAS_DND = True
    DND_IMPORT_ERROR = None
except ImportError as exc:
    HAS_DND = False
    DND_IMPORT_ERROR = str(exc)

# ==============================================================================
# CONFIGURATION & CONSTANTS
# ==============================================================================
HARDCODED_MEMBER_ID = ""
HARDCODED_PASS_HASH = ""
HARDCODED_IGNEOUS = ""
HARDCODED_SK = ""

USER_AGENT = (
    "Mozilla/5.0 (Windows NT 10.0; Win64; x64) "
    "AppleWebKit/537.36 (KHTML, like Gecko) "
    "Chrome/128.0.0.0 Safari/537.36"
)

# Keep user data beside each executable; the frozen code lives in _internal.
APP_DIR = Path(sys.executable).resolve().parent if getattr(sys, "frozen", False) else Path(__file__).resolve().parent
CONFIG_FILE = APP_DIR / "eh_uploader_config.json"
UI_BUILD_ID = "2r-python314-dnd-2026-11-04"

# The outer window may resize/maximize; the interior keeps one desktop layout with a left queue and right inspector/console stack.
DESKTOP_WINDOW_WIDTH = 1920
DESKTOP_WINDOW_HEIGHT = 1080

QUEUE_STATE_FILE = APP_DIR / "eh_uploader_queue.json"

CATEGORIES = [
    "Doujinshi",
    "Manga",
    "Artist CG",
    "Game CG",
    "Western",
    "Non-H",
    "Image Set",
    "Cosplay",
    "Misc",
]

# Retained for compatibility with the GUI/configuration. The live form is now
# authoritative for the actual submitted category value.
CATEGORY_NUMERIC_MAP = {
    "doujinshi": "2",
    "manga": "3",
    "artist cg": "4",
    "game cg": "5",
    "western": "10",
    "non-h": "9",
    "image set": "7",
    "cosplay": "8",
    "misc": "1",
}

# Sort modes use stable internal keys (first element) paired with the
# English display string (second element). The display string is only a
# fallback; the GUI shows the translated string via tr(SORT_I18N[key]).
SORT_MODES = [
    ("natural", "Natural (1, 2, 10)"),
    ("alpha", "Alphabetical (1, 10, 2)"),
    ("reverse_natural", "Reverse Natural"),
]
SORT_KEYS = [key for key, _ in SORT_MODES]
SORT_I18N = {
    "natural": "sort_natural",
    "alpha": "sort_alpha",
    "reverse_natural": "sort_reverse",
}
SORT_DISPLAY_EN = {key: display for key, display in SORT_MODES}

BOX_STYLE_OPTIONS = [
    ("balanced", "Balanced"),
    ("compact", "Compact"),
    ("readable", "Readable"),
    ("poster", "Poster Focus"),
]

BOX_STYLE_PRESETS = {
    "balanced": {
        "batch_preview_width": 440,
        "batch_preview_wrap": 400,
        "single_preview_size": 300,
        "single_preview_wrap": 310,
        "tree_title_w": 320,
        "tree_jp_w": 180,
        "tree_path_w": 240,
        "action_wrap_threshold": 1100,
    },
    "compact": {
        "batch_preview_width": 360,
        "batch_preview_wrap": 320,
        "single_preview_size": 240,
        "single_preview_wrap": 250,
        "tree_title_w": 260,
        "tree_jp_w": 155,
        "tree_path_w": 190,
        "action_wrap_threshold": 1250,
    },
    "readable": {
        "batch_preview_width": 480,
        "batch_preview_wrap": 440,
        "single_preview_size": 320,
        "single_preview_wrap": 340,
        "tree_title_w": 360,
        "tree_jp_w": 220,
        "tree_path_w": 300,
        "action_wrap_threshold": 980,
    },
    "poster": {
        "batch_preview_width": 520,
        "batch_preview_wrap": 480,
        "single_preview_size": 360,
        "single_preview_wrap": 380,
        "tree_title_w": 300,
        "tree_jp_w": 170,
        "tree_path_w": 200,
        "action_wrap_threshold": 900,
    },
}

VALID_EXTENSIONS = (".jpg", ".jpeg", ".png", ".gif", ".webp")
ARCHIVE_EXTENSIONS = (".zip", ".rar", ".cbz", ".cbr", ".7z")
MAX_GALLERY_IMAGES = 2000
LANCZOS_FILTER = getattr(Image, "Resampling", Image).LANCZOS
ALLER_FONT_FAMILY = "Aller"
INPUT_FONT = (ALLER_FONT_FAMILY, 13)
SMALL_INPUT_FONT = (ALLER_FONT_FAMILY, 11)
MAX_FOLDER_CACHE_ENTRIES = 256
MAX_ARCHIVE_CACHE_ENTRIES = 64
MAX_THUMBNAIL_CACHE_ENTRIES = 160
MAX_PREVIEW_CACHE_ENTRIES = 320
MAX_TRANSLATION_CACHE_ENTRIES = 2500
MAX_COVER_CACHE_ENTRIES = 500
# Cover/thumbnail ranking threshold. Only near-identical covers (exact file or
# near-duplicate artwork) should populate title pickers. Low-confidence text
# hits that score below this are discarded so the UI never offers unrelated
# galleries.
MIN_COVER_SIMILARITY = 75.0

# -----------------------------------------------------------------------------
# Desktop translation / reverse-image search providers
# -----------------------------------------------------------------------------
TITLE_TRANSLATORS = [
    ("Google (Top Web MT)", "google_web"),
    ("Bing (Top Web MT)", "bing_web"),
    ("DeepL (Top Web MT)", "deepl_web"),
    ("Youdao (Web MT)", "youdao_web"),
    ("Sogou (Web MT)", "sogou_web"),
    ("Alibaba (Web MT)", "alibaba_web"),
    ("Lingva Mirror (Web)", "lingva"),
    ("pykakasi (Romanized Fallback)", "pykakasi_eng"),
    ("MyMemory (Free Online)", "mymemory"),
]

ROMAJI_PROVIDERS = [
    ("pykakasi (Hepburn)", "pykakasi"),
    ("pykakasi (Passport)", "pykakasi_passport"),
    ("pykakasi (Kunrei)", "pykakasi_kunrei"),
    ("Accurate Auto (Sudachi/MeCab -> Hepburn)", "auto_accurate"),
    ("SudachiPy + Core", "sudachi"),
    ("MeCab + UniDic-lite", "mecab_unidic"),
    ("Cutlet", "cutlet"),
]

# Label for the OCR-driven multi-source cover search.  Instead of uploading
# the image for reverse search, the cover's visible words are read with OCR
# and every metadata source is searched by text (Google-Translate-image style).
OCR_ALL_SOURCES_LABEL = "All Sources (OCR Cover Text)"
GOOGLE_OCR_TITLE_LABEL = "Google (OCR Title Search)"

METADATA_SOURCES = [
    "E-Hentai / ExHentai",
    "nhentai",
    "HentaiEra",
    "DoujinRepublic",
    "Melonbooks",
    OCR_ALL_SOURCES_LABEL,
    GOOGLE_OCR_TITLE_LABEL,
]

IMAGE_SEARCH_PROVIDERS = [
    ("Google Lens", "google_lens"),
    ("Bing Visual Search", "bing_visual"),
    ("Yandex Images", "yandex_images"),
    ("SauceNAO (SearchNAO)", "saucenao"),
    ("ascii2d", "ascii2d"),
    ("TinEye", "tineye"),
    ("Suruga-ya", "surugaya"),
]

# -----------------------------------------------------------------------------
# Internationalization (i18n)
# -----------------------------------------------------------------------------
# Language code -> human name (shown in its own script in the Language menu).
LANGUAGES = [
    ("en", "English"),
    ("ja", "日本語"),
    ("zh", "中文"),
    ("ko", "한국어"),
    ("es", "Español"),
    ("ru", "Русский"),
    ("pt", "Português"),
]

# String-ID-keyed translation table. Keys are stable identifiers (never
# translated); each value maps a language code to the localized string.
# Data values submitted to E-Hentai (categories, gallery languages, folder
# names, cookie field names) are intentionally NOT part of this table.
TRANSLATIONS = {
    "app_title": {
        "en": "E(x)-Hentai Mass Gallery Creator & Publisher",
        "ja": "E(x)-Hentai 一括ギャラリー作成＆公開",
        "zh": "E(x)-Hentai 批量画廊创建与发布",
        "ko": "E(x)-Hentai 대량 갤러리 생성 및 게시",
        "es": "Creador y Publicador Masivo de Galerías E(x)-Hentai",
        "ru": "Массовое создание и публикация галерей E(x)-Hentai",
        "pt": "Criador e Publicador em Massa de Galerias E(x)-Hentai",
    },
    "file_menu": {
        "en": "File", "ja": "ファイル", "zh": "文件", "ko": "파일",
        "es": "Archivo", "ru": "Файл", "pt": "Arquivo",
    },
    "file_close": {
        "en": "Close", "ja": "閉じる", "zh": "关闭", "ko": "닫기",
        "es": "Cerrar", "ru": "Закрыть", "pt": "Fechar",
    },
    "language_menu": {
        "en": "Language", "ja": "言語", "zh": "语言", "ko": "언어",
        "es": "Idioma", "ru": "Язык", "pt": "Idioma",
    },
    "settings_menu": {
        "en": "Settings", "ja": "設定", "zh": "设置", "ko": "설정",
        "es": "Configuración", "ru": "Настройки", "pt": "Configurações",
    },
    "settings_show_debug": {
        "en": "Show Debug", "ja": "デバッグを表示", "zh": "显示调试", "ko": "디버그 표시",
        "es": "Mostrar depuración", "ru": "Показывать отладку", "pt": "Mostrar depuração",
    },
    "ctx_cut": {
        "en": "Cut", "ja": "切り取り", "zh": "剪切", "ko": "잘라내기",
        "es": "Cortar", "ru": "Вырезать", "pt": "Recortar",
    },
    "ctx_copy": {
        "en": "Copy", "ja": "コピー", "zh": "复制", "ko": "복사",
        "es": "Copiar", "ru": "Копировать", "pt": "Copiar",
    },
    "ctx_paste": {
        "en": "Paste", "ja": "貼り付け", "zh": "粘贴", "ko": "붙여넣기",
        "es": "Pegar", "ru": "Вставить", "pt": "Colar",
    },
    "ctx_delete": {
        "en": "Delete", "ja": "削除", "zh": "删除", "ko": "삭제",
        "es": "Eliminar", "ru": "Удалить", "pt": "Excluir",
    },
    "ctx_select_all": {
        "en": "Select All", "ja": "すべて選択", "zh": "全选", "ko": "모두 선택",
        "es": "Seleccionar todo", "ru": "Выделить всё", "pt": "Selecionar tudo",
    },
    "cred_member_id": {
        "en": "ipb_member_id:", "ja": "ipb_member_id:", "zh": "ipb_member_id:",
        "ko": "ipb_member_id:", "es": "ipb_member_id:", "ru": "ipb_member_id:", "pt": "ipb_member_id:",
    },
    "cred_pass_hash": {
        "en": "ipb_pass_hash:", "ja": "ipb_pass_hash:", "zh": "ipb_pass_hash:",
        "ko": "ipb_pass_hash:", "es": "ipb_pass_hash:", "ru": "ipb_pass_hash:", "pt": "ipb_pass_hash:",
    },
    "cred_igneous": {
        "en": "igneous:", "ja": "igneous:", "zh": "igneous:",
        "ko": "igneous:", "es": "igneous:", "ru": "igneous:", "pt": "igneous:",
    },
    "cred_use_exhentai": {
        "en": "Use ExHentai", "ja": "ExHentaiを使用", "zh": "使用 ExHentai", "ko": "ExHentai 사용",
        "es": "Usar ExHentai", "ru": "Использовать ExHentai", "pt": "Usar ExHentai",
    },
    "cred_load_cookie": {
        "en": "Load Cookie File", "ja": "Cookieファイルを読み込む", "zh": "加载 Cookie 文件", "ko": "Cookie 파일 불러오기",
        "es": "Cargar archivo de cookies", "ru": "Загрузить файл cookie", "pt": "Carregar arquivo de cookies",
    },
    "cred_validate_session": {
        "en": "Validate Session", "ja": "セッションを検証", "zh": "验证会话", "ko": "세션 검증",
        "es": "Validar sesión", "ru": "Проверить сессию", "pt": "Validar sessão",
    },
    "cred_member_id_ph": {
        "en": "1234567", "ja": "1234567", "zh": "1234567", "ko": "1234567",
        "es": "1234567", "ru": "1234567", "pt": "1234567",
    },
    "cred_pass_hash_ph": {
        "en": "abcdef0123456789...", "ja": "abcdef0123456789...", "zh": "abcdef0123456789...", "ko": "abcdef0123456789...",
        "es": "abcdef0123456789...", "ru": "abcdef0123456789...", "pt": "abcdef0123456789...",
    },
    "cred_igneous_ph": {
        "en": "optional / exhentai cookie", "ja": "任意 / exhentai cookie", "zh": "可选 / exhentai cookie", "ko": "선택 / exhentai cookie",
        "es": "opcional / cookie exhentai", "ru": "необязательно / cookie exhentai", "pt": "opcional / cookie exhentai",
    },
    "cred_cookie_path_ph": {
        "en": "Path to cookies.txt or folder", "ja": "cookies.txt またはフォルダのパス", "zh": "cookies.txt 或文件夹路径", "ko": "cookies.txt 또는 폴더 경로",
        "es": "Ruta a cookies.txt o carpeta", "ru": "Путь к cookies.txt или папке", "pt": "Caminho para cookies.txt ou pasta",
    },
    "tab_batch": {
        "en": "Batch Queue Uploader", "ja": "一括キューアップローダー", "zh": "批量队列上传器", "ko": "일괄 대기열 업로더",
        "es": "Cargador de cola por lotes", "ru": "Пакетный загрузчик очереди", "pt": "Carregador de fila em lote",
    },
    "tab_single": {
        "en": "Single Gallery Creation", "ja": "単一ギャラリー作成", "zh": "单个画廊创建", "ko": "단일 갤러리 생성",
        "es": "Creación de galería única", "ru": "Создание одной галереи", "pt": "Criação de galeria única",
    },
    "btn_add_folders": {
        "en": "+ Add Folders...", "ja": "+ フォルダを追加...", "zh": "+ 添加文件夹...", "ko": "+ 폴더 추가...",
        "es": "+ Añadir carpetas...", "ru": "+ Добавить папки...", "pt": "+ Adicionar pastas...",
    },
    "btn_add_root_dir": {
        "en": "+ Add Root Dir...", "ja": "+ ルートディレクトリを追加...", "zh": "+ 添加根目录...", "ko": "+ 루트 디렉터리 추가...",
        "es": "+ Añadir dir. raíz...", "ru": "+ Добавить корневой каталог...", "pt": "+ Adicionar dir. raiz...",
    },
    "btn_remove_selected": {
        "en": "Remove Selected", "ja": "選択を削除", "zh": "移除所选", "ko": "선택 항목 제거",
        "es": "Eliminar seleccionados", "ru": "Удалить выбранные", "pt": "Remover selecionados",
    },
    "btn_clear_all": {
        "en": "Clear All", "ja": "すべて消去", "zh": "全部清除", "ko": "모두 지우기",
        "es": "Borrar todo", "ru": "Очистить всё", "pt": "Limpar tudo",
    },
    "btn_sync_form": {
        "en": "Sync Form", "ja": "フォームを同期", "zh": "同步表单", "ko": "폼 동기화",
        "es": "Sincronizar formulario", "ru": "Синхронизировать форму", "pt": "Sincronizar formulário",
    },
    "btn_start_batch": {
        "en": "Start Batch Upload Queue", "ja": "一括アップロードを開始", "zh": "开始批量上传队列", "ko": "일괄 업로드 대기열 시작",
        "es": "Iniciar cola de carga por lotes", "ru": "Запустить очередь пакетной загрузки", "pt": "Iniciar fila de upload em lote",
    },
    "lbl_cat": {
        "en": "Cat:", "ja": "カテゴリ:", "zh": "分类:", "ko": "카테고리:",
        "es": "Cat.:", "ru": "Кат.:", "pt": "Cat.:",
    },
    "lbl_lang": {
        "en": "Lang:", "ja": "言語:", "zh": "语言:", "ko": "언어:",
        "es": "Idioma:", "ru": "Язык:", "pt": "Idioma:",
    },
    "lbl_folder": {
        "en": "Folder:", "ja": "フォルダ:", "zh": "文件夹:", "ko": "폴더:",
        "es": "Carpeta:", "ru": "Папка:", "pt": "Pasta:",
    },
    "lbl_sort": {
        "en": "Sort:", "ja": "並び順:", "zh": "排序:", "ko": "정렬:",
        "es": "Ord.:", "ru": "Сорт.:", "pt": "Ord.:",
    },
    "chk_publish": {
        "en": "Publish", "ja": "公開", "zh": "发布", "ko": "게시",
        "es": "Publicar", "ru": "Опубликовать", "pt": "Publicar",
    },
    "chk_unlisted": {
        "en": "Unlisted", "ja": "非公開", "zh": "不列出", "ko": "미공개",
        "es": "No listado", "ru": "Без каталога", "pt": "Não listado",
    },
    "lbl_speed_batch": {
        "en": "Batch:", "ja": "一括数:", "zh": "批量:", "ko": "배치:",
        "es": "Lote:", "ru": "Пакет:", "pt": "Lote:",
    },
    "lbl_speed_workers": {
        "en": "Workers:", "ja": "ワーカー:", "zh": "线程:", "ko": "워커:",
        "es": "Hilos:", "ru": "Потоки:", "pt": "Processos:",
    },
    "lbl_speed_delay": {
        "en": "Delay:", "ja": "遅延:", "zh": "延迟:", "ko": "지연:",
        "es": "Retraso:", "ru": "Задержка:", "pt": "Atraso:",
    },
    "lbl_speed_secs": {
        "en": "s", "ja": "s", "zh": "s", "ko": "s",
        "es": "s", "ru": "с", "pt": "s",
    },
    "hint_dnd_on": {
        "en": "Drag & Drop folders into table", "ja": "フォルダをドラッグ＆ドロップ", "zh": "拖放文件夹到表格", "ko": "폴더를 표로 드래그 앤 드롭",
        "es": "Arrastra y suelta carpetas a la tabla", "ru": "Перетащите папки в таблицу", "pt": "Arraste e solte pastas na tabela",
    },
    "hint_dnd_off": {
        "en": "(Install 'tkinterdnd2' to enable drag & drop)",
        "ja": "('tkinterdnd2'をインストールしてドラッグ＆ドロップを有効化)",
        "zh": "(安装 'tkinterdnd2' 以启用拖放)",
        "ko": "('tkinterdnd2' 설치로 드래그 앤 드롭 활성화)",
        "es": "(Instala 'tkinterdnd2' para activar arrastrar y soltar)",
        "ru": "(Установите 'tkinterdnd2' для включения перетаскивания)",
        "pt": "(Instale 'tkinterdnd2' para ativar arrastar e soltar)",
    },
    "col_title_en": {
        "en": "English Title", "ja": "英語タイトル", "zh": "英文标题", "ko": "영어 제목",
        "es": "Título en inglés", "ru": "Английское название", "pt": "Título em inglês",
    },
    "col_title_jp": {
        "en": "Japanese Title (Optional)", "ja": "日本語タイトル(任意)", "zh": "日文标题(可选)", "ko": "일본어 제목(선택)",
        "es": "Título en japonés (opcional)", "ru": "Японское название (необязательно)", "pt": "Título em japonês (opcional)",
    },
    "col_images": {
        "en": "Images", "ja": "画像数", "zh": "图片", "ko": "이미지",
        "es": "Imágenes", "ru": "Изображения", "pt": "Imagens",
    },
    "col_status": {
        "en": "Status", "ja": "ステータス", "zh": "状态", "ko": "상태",
        "es": "Estado", "ru": "Статус", "pt": "Status",
    },
    "col_path": {
        "en": "Directory Path", "ja": "ディレクトリパス", "zh": "目录路径", "ko": "디렉터리 경로",
        "es": "Ruta del directorio", "ru": "Путь к каталогу", "pt": "Caminho do diretório",
    },
    "cover_preview": {
        "en": "Cover Preview", "ja": "カバープレビュー", "zh": "封面预览", "ko": "표지 미리보기",
        "es": "Vista previa de la portada", "ru": "Предпросмотр обложки", "pt": "Pré-visualização da capa",
    },
    "selected_titles": {
        "en": "Selected Gallery Titles", "ja": "選択中のギャラリータイトル", "zh": "已选画廊标题", "ko": "선택된 갤러리 제목",
        "es": "Títulos de galería seleccionados", "ru": "Названия выбранных галерей", "pt": "Títulos de galeria selecionados",
    },
    "lbl_en_title": {
        "en": "English Title:", "ja": "英語タイトル:", "zh": "英文标题:", "ko": "영어 제목:",
        "es": "Título en inglés:", "ru": "Английское название:", "pt": "Título em inglês:",
    },
    "lbl_jp_title": {
        "en": "Japanese Title (Optional):", "ja": "日本語タイトル(任意):", "zh": "日文标题(可选):", "ko": "일본어 제목(선택):",
        "es": "Título en japonés (opcional):", "ru": "Японское название (необязательно):", "pt": "Título em japonês (opcional):",
    },
    "cover_select_hint": {
        "en": "Select a folder\nto edit titles & preview",
        "ja": "フォルダを選択して\nタイトル編集＆プレビュー",
        "zh": "选择文件夹以\n编辑标题和预览",
        "ko": "폴더를 선택하여\n제목 편집 및 미리보기",
        "es": "Selecciona una carpeta\npara editar títulos y previsualizar",
        "ru": "Выберите папку\nдля редактирования и предпросмотра",
        "pt": "Selecione uma pasta\npara editar títulos e pré-visualizar",
    },
    "cover_no_preview": {
        "en": "No preview\navailable", "ja": "プレビューなし", "zh": "无可用\n预览", "ko": "미리보기 없음",
        "es": "Sin vista previa\ndisponible", "ru": "Нет предпросмотра", "pt": "Sem pré-visualização\ndisponível",
    },
    "single_jp_title": {
        "en": "Japanese Title:", "ja": "日本語タイトル:", "zh": "日文标题:", "ko": "일본어 제목:",
        "es": "Título en japonés:", "ru": "Японское название:", "pt": "Título em japonês:",
    },
    "single_en_title": {
        "en": "English Title:", "ja": "英語タイトル:", "zh": "英文标题:", "ko": "영어 제목:",
        "es": "Título en inglés:", "ru": "Английское название:", "pt": "Título em inglês:",
    },
    "single_category": {
        "en": "Category:", "ja": "カテゴリ:", "zh": "分类:", "ko": "카테고리:",
        "es": "Categoría:", "ru": "Категория:", "pt": "Categoria:",
    },
    "single_language": {
        "en": "Language:", "ja": "言語:", "zh": "语言:", "ko": "언어:",
        "es": "Idioma:", "ru": "Язык:", "pt": "Idioma:",
    },
    "single_gallery_folder": {
        "en": "Gallery Folder:", "ja": "ギャラリーフォルダ:", "zh": "画廊文件夹:", "ko": "갤러리 폴더:",
        "es": "Carpeta de galería:", "ru": "Папка галереи:", "pt": "Pasta da galeria:",
    },
    "single_sort_order": {
        "en": "Image Sort Order:", "ja": "画像並び順:", "zh": "图片排序顺序:", "ko": "이미지 정렬 순서:",
        "es": "Orden de imágenes:", "ru": "Порядок сортировки:", "pt": "Ordem das imagens:",
    },
    "single_image_folder": {
        "en": "Image Folder:", "ja": "画像フォルダ:", "zh": "图片文件夹:", "ko": "이미지 폴더:",
        "es": "Carpeta de imágenes:", "ru": "Папка изображений:", "pt": "Pasta de imagens:",
    },
    "btn_browse": {
        "en": "Browse...", "ja": "参照...", "zh": "浏览...", "ko": "찾아보기...",
        "es": "Examinar...", "ru": "Обзор...", "pt": "Procurar...",
    },
    "chk_autopublish": {
        "en": "Auto-Publish immediately after upload", "ja": "アップロード後すぐに自動公開", "zh": "上传后立即自动发布", "ko": "업로드 후 즉시 자동 게시",
        "es": "Auto-publicar tras la carga", "ru": "Автопубликация после загрузки", "pt": "Auto-publicar após o upload",
    },
    "chk_unlisted_gallery": {
        "en": "Unlisted Gallery", "ja": "非公開ギャラリー", "zh": "不列出的画廊", "ko": "미공개 갤러리",
        "es": "Galería no listada", "ru": "Галерея без каталога", "pt": "Galeria não listada",
    },
    "single_no_folder": {
        "en": "No folder selected", "ja": "フォルダ未選択", "zh": "未选择文件夹", "ko": "폴더 미선택",
        "es": "Ninguna carpeta seleccionada", "ru": "Папка не выбрана", "pt": "Nenhuma pasta selecionada",
    },
    "btn_create_upload": {
        "en": "Create & Upload Gallery", "ja": "ギャラリー作成＆アップロード", "zh": "创建并上传画廊", "ko": "갤러리 생성 및 업로드",
        "es": "Crear y subir galería", "ru": "Создать и загрузить галерею", "pt": "Criar e enviar galeria",
    },
    "log_title": {
        "en": "Process Console Log", "ja": "プロセスコンソールログ", "zh": "进程控制台日志", "ko": "프로세스 콘솔 로그",
        "es": "Registro de consola", "ru": "Журнал консоли", "pt": "Registro do console",
    },
    "sort_natural": {
        "en": "Natural (1, 2, 10)", "ja": "自然順(1, 2, 10)", "zh": "自然排序(1, 2, 10)", "ko": "자연순(1, 2, 10)",
        "es": "Natural (1, 2, 10)", "ru": "Естественный (1, 2, 10)", "pt": "Natural (1, 2, 10)",
    },
    "sort_alpha": {
        "en": "Alphabetical (1, 10, 2)", "ja": "アルファベット順(1, 10, 2)", "zh": "字母序(1, 10, 2)", "ko": "알파벳순(1, 10, 2)",
        "es": "Alfabético (1, 10, 2)", "ru": "Алфавитный (1, 10, 2)", "pt": "Alfabético (1, 10, 2)",
    },
    "sort_reverse": {
        "en": "Reverse Natural", "ja": "逆自然順", "zh": "反向自然排序", "ko": "역자연순",
        "es": "Natural inverso", "ru": "Обратный естественный", "pt": "Natural inverso",
    },
    "msg_cookie_not_found": {
        "en": "Cookie file not found", "ja": "Cookieファイルが見つかりません", "zh": "未找到 Cookie 文件", "ko": "Cookie 파일을 찾을 수 없습니다",
        "es": "Archivo de cookies no encontrado", "ru": "Файл cookie не найден", "pt": "Arquivo de cookies não encontrado",
    },
    "msg_cookie_not_found_body": {
        "en": "Please enter a valid path to a cookies.txt export or folder containing one.",
        "ja": "cookies.txt エクスポートまたはフォルダの有効なパスを入力してください。",
        "zh": "请输入有效的 cookies.txt 导出路径或包含它的文件夹。",
        "ko": "cookies.txt 내보내기 또는 폴더의 올바른 경로를 입력하세요.",
        "es": "Introduce una ruta válida a un archivo cookies.txt o carpeta que lo contenga.",
        "ru": "Укажите правильный путь к файлу cookies.txt или папке.",
        "pt": "Insira um caminho válido para um arquivo cookies.txt ou pasta que o contenha.",
    },
    "msg_cookie_error": {
        "en": "Cookie file error", "ja": "Cookieファイルエラー", "zh": "Cookie 文件错误", "ko": "Cookie 파일 오류",
        "es": "Error de archivo de cookies", "ru": "Ошибка файла cookie", "pt": "Erro de arquivo de cookies",
    },
    "msg_busy": {
        "en": "Busy", "ja": "ビジー", "zh": "忙碌", "ko": "사용 중",
        "es": "Ocupado", "ru": "Занято", "pt": "Ocupado",
    },
    "msg_busy_validate": {
        "en": "Wait for the current upload process to finish before validating the session.",
        "ja": "セッション検証前に現在のアップロード処理が完了するのをお待ちください。",
        "zh": "请等待当前上传流程完成后再验证会话。",
        "ko": "세션을 검증하기 전에 현재 업로드 처리가 완료될 때까지 기다리세요.",
        "es": "Espera a que termine el proceso de carga actual antes de validar la sesión.",
        "ru": "Дождитесь завершения текущей загрузки перед проверкой сессии.",
        "pt": "Aguarde o processo de upload atual terminar antes de validar a sessão.",
    },
    "msg_busy_running": {
        "en": "An upload process is already running.", "ja": "アップロード処理が既に実行中です。", "zh": "已有上传流程正在运行。", "ko": "업로드 처리가 이미 실행 중입니다.",
        "es": "Ya hay un proceso de carga en ejecución.", "ru": "Процесс загрузки уже выполняется.", "pt": "Um processo de upload já está em execução.",
    },
    "msg_folder_missing": {
        "en": "Selected image folder does not exist.", "ja": "選択された画像フォルダは存在しません。", "zh": "所选图片文件夹不存在。", "ko": "선택된 이미지 폴더가 존재하지 않습니다.",
        "es": "La carpeta de imágenes seleccionada no existe.", "ru": "Выбранная папка с изображениями не существует.", "pt": "A pasta de imagens selecionada não existe.",
    },
    "msg_error": {
        "en": "Error", "ja": "エラー", "zh": "错误", "ko": "오류",
        "es": "Error", "ru": "Ошибка", "pt": "Erro",
    },
    "msg_empty_queue": {
        "en": "Empty Queue", "ja": "キューが空です", "zh": "队列为空", "ko": "대기열이 비었습니다",
        "es": "Cola vacía", "ru": "Очередь пуста", "pt": "Fila vazia",
    },
    "msg_empty_queue_body": {
        "en": "Please add or drag & drop folders into the queue first.",
        "ja": "まずフォルダをキューに追加またはドラッグ＆ドロップしてください。",
        "zh": "请先将文件夹添加或拖放到队列中。",
        "ko": "먼저 폴더를 대기열에 추가하거나 드래그 앤 드롭하세요.",
        "es": "Añade o arrastra y suelta carpetas a la cola primero.",
        "ru": "Сначала добавьте или перетащите папки в очередь.",
        "pt": "Adicione ou arraste e solte pastas na fila primeiro.",
    },
    "msg_no_images": {
        "en": "No Valid Images", "ja": "有効な画像がありません", "zh": "无有效图片", "ko": "유효한 이미지 없음",
        "es": "Sin imágenes válidas", "ru": "Нет подходящих изображений", "pt": "Sem imagens válidas",
    },
    "msg_no_images_body": {
        "en": "None of the queued folders contain valid images.",
        "ja": "キュー内のフォルダに有効な画像がありません。",
        "zh": "队列中的文件夹均不包含有效图片。",
        "ko": "대기열의 폴더에 유효한 이미지가 없습니다.",
        "es": "Ninguna carpeta en cola contiene imágenes válidas.",
        "ru": "Ни одна папка в очереди не содержит подходящих изображений.",
        "pt": "Nenhuma pasta na fila contém imagens válidas.",
    },
    "status_queued": {
        "en": "Queued", "ja": "待機中", "zh": "已排队", "ko": "대기 중",
        "es": "En cola", "ru": "В очереди", "pt": "Na fila",
    },
    "status_paused": {
        "en": "Paused", "ja": "一時停止", "zh": "已暂停", "ko": "일시 중지",
        "es": "Pausado", "ru": "Приостановлено", "pt": "Pausado",
    },
    "status_no_images": {
        "en": "No Images Found", "ja": "画像が見つかりません", "zh": "未找到图片", "ko": "이미지 없음",
        "es": "Sin imágenes", "ru": "Нет изображений", "pt": "Sem imagens",
    },
    "status_creating": {
        "en": "Creating Draft...", "ja": "ドラフト作成中...", "zh": "创建草稿中...", "ko": "초안 생성 중...",
        "es": "Creando borrador...", "ru": "Создание черновика...", "pt": "Criando rascunho...",
    },
    "status_uploading": {
        "en": "Uploading", "ja": "アップロード中", "zh": "上传中", "ko": "업로드 중",
        "es": "Subiendo", "ru": "Загрузка", "pt": "Enviando",
    },
    "status_publishing": {
        "en": "Publishing...", "ja": "公開中...", "zh": "发布中...", "ko": "게시 중...",
        "es": "Publicando...", "ru": "Публикация...", "pt": "Publicando...",
    },
    "status_published": {
        "en": "Published", "ja": "公開済み", "zh": "已发布", "ko": "게시됨",
        "es": "Publicado", "ru": "Опубликовано", "pt": "Publicado",
    },
    "status_draft_saved": {
        "en": "Draft Saved", "ja": "ドラフト保存済み", "zh": "草稿已保存", "ko": "초안 저장됨",
        "es": "Borrador guardado", "ru": "Черновик сохранён", "pt": "Rascunho salvo",
    },
    "status_error": {
        "en": "Error", "ja": "エラー", "zh": "错误", "ko": "오류",
        "es": "Error", "ru": "Ошибка", "pt": "Erro",
    },
    "btn_pause_selected": {
        "en": "Pause Selected", "ja": "選択中を停止", "zh": "暂停所选", "ko": "선택 항목 일시중지",
        "es": "Pausar seleccionados", "ru": "Приостановить выбранные", "pt": "Pausar selecionados",
    },
    "btn_resume_selected": {
        "en": "Resume Selected", "ja": "選択中を再開", "zh": "恢复所选", "ko": "선택 항목 재개",
        "es": "Reanudar seleccionados", "ru": "Возобновить выбранные", "pt": "Retomar selecionados",
    },
    "btn_pause_all": {
        "en": "Pause All", "ja": "すべて停止", "zh": "全部暂停", "ko": "모두 일시중지",
        "es": "Pausar todo", "ru": "Приостановить всё", "pt": "Pausar tudo",
    },
    "btn_resume_all": {
        "en": "Resume All", "ja": "すべて再開", "zh": "全部恢复", "ko": "모두 재개",
        "es": "Reanudar todo", "ru": "Возобновить всё", "pt": "Retomar tudo",
    },
    "btn_view_draft_preview": {
        "en": "View Draft Images", "ja": "ドラフト画像を見る", "zh": "查看草稿图片", "ko": "초안 이미지 보기",
        "es": "Ver imágenes del borrador", "ru": "Просмотр изображений черновика", "pt": "Ver imagens do rascunho",
    },
    "preview_sort": {
        "en": "Sort:", "ja": "並び順:", "zh": "排序:", "ko": "정렬:",
        "es": "Orden:", "ru": "Сортировка:", "pt": "Ordenar:",
    },
    "preview_page": {
        "en": "Page:", "ja": "ページ:", "zh": "页:", "ko": "페이지:",
        "es": "Página:", "ru": "Страница:", "pt": "Página:",
    },
    "preview_no_images": {
        "en": "No images available for preview.", "ja": "プレビュー可能な画像がありません。", "zh": "没有可预览的图片。", "ko": "미리보기할 이미지가 없습니다.",
        "es": "No hay imágenes disponibles para previsualizar.", "ru": "Нет изображений для предпросмотра.", "pt": "Nenhuma imagem disponível para pré-visualização.",
    },
}

ctk.set_appearance_mode("Dark")
ctk.set_default_color_theme("dark-blue")

# This build intentionally uses hard square geometry everywhere.  Update the
# CustomTkinter theme defaults as well as the explicit widget values below so
# dialogs and dynamically-created controls do not silently reintroduce rounding.
try:
    for _theme_widget in (
        "CTkButton", "CTkEntry", "CTkFrame", "CTkLabel", "CTkComboBox",
        "CTkOptionMenu", "CTkCheckBox", "CTkTextbox", "CTkScrollableFrame",
        "CTkProgressBar", "CTkSegmentedButton", "CTkSlider",
    ):
        _section = ctk.ThemeManager.theme.get(_theme_widget, {})
        if isinstance(_section, dict) and "corner_radius" in _section:
            _section["corner_radius"] = 0
except Exception:
    pass


# ==============================================================================
# HELPER FUNCTIONS
# ==============================================================================
def create_eh_app_icon(icon_path: str | os.PathLike | None = None):
    """Generate a phoenix-style red/orange/yellow icon if missing."""
    target = Path(icon_path) if icon_path is not None else ((APP_DIR / "eh_app_icon.ico"))

    if target.exists():
        return str(target)

    try:
        icon = Image.new("RGBA", (256, 256), (0, 0, 0, 0))
        draw = ImageDraw.Draw(icon)

        red = (222, 52, 33, 255)
        orange = (246, 128, 32, 255)
        yellow = (255, 210, 74, 255)
        ember = (255, 240, 180, 255)

        # Wings
        draw.polygon([(18, 150), (108, 72), (126, 130), (70, 200), (20, 185)], fill=orange)
        draw.polygon([(238, 150), (148, 72), (130, 130), (186, 200), (236, 185)], fill=orange)

        # Body + tail flame
        draw.polygon([(98, 186), (128, 78), (158, 186), (128, 232)], fill=red)
        draw.polygon([(112, 206), (128, 176), (144, 206), (128, 246)], fill=yellow)

        # Crest / inner glow
        draw.polygon([(110, 95), (128, 56), (146, 95), (128, 112)], fill=yellow)
        draw.ellipse((108, 118, 148, 158), fill=ember)

        try:
            font = ImageFont.truetype("arial.ttf", 32)
        except Exception:
            font = ImageFont.load_default()

        text = "PHX"
        bbox = draw.textbbox((0, 0), text, font=font)
        text_w = bbox[2] - bbox[0]
        text_h = bbox[3] - bbox[1]
        x = (256 - text_w) / 2
        y = 204 - (text_h / 2)
        draw.text((x, y), text, font=font, fill=(45, 20, 10, 220))

        target.parent.mkdir(parents=True, exist_ok=True)
        icon.save(target, format="ICO")
        return str(target)
    except Exception:
        return ""


def natural_sort_key(filename):
    key = []
    for token in re.split(r"(\d+)", str(filename)):
        if token.isdigit():
            key.append((0, int(token)))
        else:
            key.append((1, token.lower()))
    return key


def _normalize_sort_key(sort_mode):
    """Map a sort value (internal key OR English display string) to a stable
    internal sort key. Translated display strings should be converted by the
    GUI via _sort_display_to_key() before reaching this helper.
    """
    if not sort_mode:
        return "natural"
    s = str(sort_mode).strip()
    if s in SORT_KEYS:
        return s
    # Legacy English display strings from older config files.
    for key, display in SORT_MODES:
        if s == display:
            return key
    low = s.lower()
    if "reverse" in low:
        return "reverse_natural"
    if "alpha" in low:
        return "alpha"
    return "natural"


def _sort_image_paths(paths, sort_mode="natural"):
    if not paths:
        return []

    key = _normalize_sort_key(sort_mode)
    ordered = list(paths)

    if key == "reverse_natural":
        ordered.sort(key=lambda p: natural_sort_key(os.path.basename(p)), reverse=True)
    elif key == "alpha":
        ordered.sort(key=lambda p: os.path.basename(p).lower())
    else:
        ordered.sort(key=lambda p: natural_sort_key(os.path.basename(p)))

    return ordered


def _is_valid_image_name(name):
    return str(name).lower().endswith(VALID_EXTENSIONS)


_FOLDER_SCAN_CACHE = {}
_ARCHIVE_IMAGE_CACHE = {}


def _bounded_cache_set(cache, key, value, max_entries):
    """Insert into an insertion-ordered dict and evict its oldest entries."""
    cache.pop(key, None)
    cache[key] = value
    while len(cache) > max(1, int(max_entries)):
        try:
            cache.pop(next(iter(cache)))
        except (StopIteration, KeyError):
            break


def _directory_snapshot_key(folder_path):
    """Cheap directory-listing fingerprint.

    The previous implementation enumerated and stat'ed every child merely to
    decide whether the cached enumeration could be used, and then enumerated
    the same directory a second time on a miss. Directory mtime/ctime are the
    correct invalidation signals for a filename listing and make repeated
    selections effectively constant-time.
    """
    try:
        folder_path = os.path.abspath(folder_path)
        stat = os.stat(folder_path)

        # A directory timestamp by itself is not a reliable listing cache key.
        # In particular, Windows copy/move tools can preserve the directory
        # timestamp while adding files.  That previously left an empty result
        # cached even though the folder had since received images.  Include a
        # cheap fingerprint of the entry names so additions/removals/renames
        # invalidate the cache without stat'ing every image.
        with os.scandir(folder_path) as entries:
            names = tuple(sorted(os.path.normcase(entry.name) for entry in entries))
        return (
            folder_path,
            stat.st_mtime_ns,
            stat.st_ctime_ns,
            len(names),
            hash(names),
        )
    except OSError:
        return (os.path.abspath(folder_path), 0, 0)


def _archive_cache_key(archive_path):
    try:
        st = os.stat(archive_path)
        return (os.path.abspath(archive_path), st.st_mtime_ns, st.st_size)
    except OSError:
        return (os.path.abspath(archive_path), 0, 0)


def _resolve_archive_extractor():
    candidates = []
    for exe in ("7z", "7za", "7zr", "unrar", "rar"):
        resolved = shutil.which(exe)
        if resolved:
            candidates.append(resolved)

    if os.name == "nt":
        candidate_dirs = [
            r"C:\Program Files\7-Zip",
            r"C:\Program Files (x86)\7-Zip",
            r"C:\Program Files\WinRAR",
            r"C:\Program Files (x86)\WinRAR",
        ]
        for base in candidate_dirs:
            for exe in ("7z.exe", "7za.exe", "7zr.exe", "unrar.exe", "rar.exe"):
                full = os.path.join(base, exe)
                if os.path.isfile(full):
                    candidates.append(full)

    seen = set()
    ordered = []
    for path in candidates:
        norm = os.path.normcase(os.path.normpath(path))
        if norm not in seen:
            ordered.append(path)
            seen.add(norm)
    return ordered


def _get_archive_tooling_error_message(archive_name):
    extractors = _resolve_archive_extractor()
    if not extractors:
        return (
            f"RAR extraction tool missing: install 7-Zip or WinRAR and ensure 7z.exe/unrar.exe is available. "
            f"Archive: {archive_name}"
        )
    return f"RAR extraction failed for {archive_name}; verify the archive is valid and not password-protected."


def _extract_archive_images(archive_path, temp_root):
    cache_key = _archive_cache_key(archive_path)
    if cache_key in _ARCHIVE_IMAGE_CACHE:
        return list(_ARCHIVE_IMAGE_CACHE[cache_key]), None

    if not os.path.isfile(archive_path):
        return [], "archive missing"

    archive_name = os.path.basename(archive_path)
    lower_name = archive_name.lower()
    extract_dir = os.path.join(temp_root, f"extract_{os.path.splitext(archive_name)[0]}")
    os.makedirs(extract_dir, exist_ok=True)

    try:
        if lower_name.endswith(".zip") or lower_name.endswith(".cbz"):
            with zipfile.ZipFile(archive_path, "r") as archive:
                archive.extractall(extract_dir)
        elif lower_name.endswith(".rar") or lower_name.endswith(".cbr"):
            rarextracted = False
            last_error = None
            try:
                import rarfile

                with rarfile.RarFile(archive_path, "r") as archive:
                    archive.extractall(extract_dir)
                rarextracted = True
            except Exception as exc:
                last_error = exc

            if not rarextracted:
                executables = _resolve_archive_extractor()
                for extractor in executables:
                    try:
                        if os.path.basename(extractor).lower() in {"7z.exe", "7za.exe", "7zr.exe"}:
                            subprocess.run(
                                [extractor, "x", "-y", archive_path, f"-o{extract_dir}"],
                                check=True,
                                stdout=subprocess.DEVNULL,
                                stderr=subprocess.DEVNULL,
                            )
                        elif os.path.basename(extractor).lower() in {"unrar.exe", "rar.exe"}:
                            subprocess.run(
                                [extractor, "x", "-y", archive_path, extract_dir],
                                check=True,
                                stdout=subprocess.DEVNULL,
                                stderr=subprocess.DEVNULL,
                            )
                        else:
                            continue
                        rarextracted = True
                        break
                    except Exception as exc:
                        last_error = exc

            if not rarextracted:
                tool_error = _get_archive_tooling_error_message(archive_name)
                if last_error is not None:
                    return [], f"rar extract failed: {last_error}. {tool_error}"
                return [], f"rar extract failed: {tool_error}"
        elif lower_name.endswith(".7z"):
            executables = _resolve_archive_extractor()
            extracted_ok = False
            last_error = None
            for extractor in executables:
                try:
                    if os.path.basename(extractor).lower() in {"7z.exe", "7za.exe", "7zr.exe"}:
                        subprocess.run(
                            [extractor, "x", "-y", archive_path, f"-o{extract_dir}"],
                            check=True,
                            stdout=subprocess.DEVNULL,
                            stderr=subprocess.DEVNULL,
                        )
                        extracted_ok = True
                        break
                except Exception as exc:
                    last_error = exc
            if not extracted_ok:
                if last_error is not None:
                    return [], f"7z extract failed: {last_error}. Install 7-Zip and ensure 7z.exe is available."
                return [], "7z extract failed: no 7-Zip binary found. Install 7-Zip and ensure 7z.exe is available."
        else:
            return [], f"unsupported archive type: {archive_name}"
    except Exception as exc:
        return [], f"archive extract failed: {exc}"

    images = []
    for root, _, files in os.walk(extract_dir):
        for filename in files:
            if _is_valid_image_name(filename):
                images.append(os.path.join(root, filename))
    if not images:
        return [], f"archive extracted but no valid image files found in {archive_name}"

    cached_images = _sort_image_paths(images, "natural")
    _bounded_cache_set(
        _ARCHIVE_IMAGE_CACHE,
        cache_key,
        cached_images,
        MAX_ARCHIVE_CACHE_ENTRIES,
    )
    return cached_images, None


def get_sorted_image_files(folder_path, sort_mode="natural"):
    try:
        if os.path.isfile(folder_path) and str(folder_path).lower().endswith(ARCHIVE_EXTENSIONS):
            temp_root = os.path.join(
                tempfile.gettempdir(),
                f"eh_archive_{abs(hash(os.path.abspath(folder_path)))}",
            )
            os.makedirs(temp_root, exist_ok=True)
            images, _error = _extract_archive_images(folder_path, temp_root)
            return _sort_image_paths(images, sort_mode)
        if not os.path.isdir(folder_path):
            return []

        cache_key = (_directory_snapshot_key(folder_path), sort_mode)
        if cache_key in _FOLDER_SCAN_CACHE:
            return list(_FOLDER_SCAN_CACHE[cache_key])

        direct = []
        archive_paths = []
        with os.scandir(folder_path) as entries:
            for entry in entries:
                lower = entry.name.lower()
                if _is_valid_image_name(entry.name):
                    direct.append(os.path.join(folder_path, entry.name))
                elif lower.endswith(ARCHIVE_EXTENSIONS):
                    archive_paths.append(os.path.join(folder_path, entry.name))

        if direct:
            result = _sort_image_paths(direct, sort_mode)
            _bounded_cache_set(
                _FOLDER_SCAN_CACHE,
                cache_key,
                list(result),
                MAX_FOLDER_CACHE_ENTRIES,
            )
            return result

        if not archive_paths:
            _bounded_cache_set(
                _FOLDER_SCAN_CACHE,
                cache_key,
                [],
                MAX_FOLDER_CACHE_ENTRIES,
            )
            return []

        temp_root = os.path.join(tempfile.gettempdir(), f"eh_gallery_{abs(hash(os.path.abspath(folder_path)))}")
        os.makedirs(temp_root, exist_ok=True)

        extracted = []
        errors = []
        for archive in sorted(archive_paths, key=lambda p: natural_sort_key(os.path.basename(p))):
            images, err = _extract_archive_images(archive, temp_root)
            if err:
                errors.append(f"{os.path.basename(archive)}: {err}")
            extracted.extend(images)

        if not extracted:
            if errors:
                print(f"[Archive scan] no valid images extracted: {'; '.join(errors)}")
            _bounded_cache_set(
                _FOLDER_SCAN_CACHE,
                cache_key,
                [],
                MAX_FOLDER_CACHE_ENTRIES,
            )
            return []

        result = _sort_image_paths(extracted, sort_mode)
        _bounded_cache_set(
            _FOLDER_SCAN_CACHE,
            cache_key,
            list(result),
            MAX_FOLDER_CACHE_ENTRIES,
        )
        return result
    except Exception:
        return []


def get_sorted_image_files_with_debug(folder_path, sort_mode="natural"):
    try:
        if os.path.isfile(folder_path) and str(folder_path).lower().endswith(ARCHIVE_EXTENSIONS):
            temp_root = os.path.join(
                tempfile.gettempdir(),
                f"eh_archive_{abs(hash(os.path.abspath(folder_path)))}",
            )
            os.makedirs(temp_root, exist_ok=True)
            images, error = _extract_archive_images(folder_path, temp_root)
            if error:
                return [], [error]
            return _sort_image_paths(images, sort_mode), []
        if not os.path.isdir(folder_path):
            return [], [f"Folder or archive not found: {folder_path}"]

        direct = []
        archive_paths = []
        with os.scandir(folder_path) as entries:
            for entry in entries:
                lower = entry.name.lower()
                if _is_valid_image_name(entry.name):
                    direct.append(os.path.join(folder_path, entry.name))
                elif lower.endswith(ARCHIVE_EXTENSIONS):
                    archive_paths.append(os.path.join(folder_path, entry.name))

        if direct:
            return _sort_image_paths(direct, sort_mode), []

        if not archive_paths:
            return [], [f"No supported image or archive files found in {folder_path}"]

        temp_root = os.path.join(tempfile.gettempdir(), f"eh_gallery_{abs(hash(os.path.abspath(folder_path)))}")
        os.makedirs(temp_root, exist_ok=True)

        extracted = []
        errors = []
        for archive in sorted(archive_paths, key=lambda p: natural_sort_key(os.path.basename(p))):
            images, err = _extract_archive_images(archive, temp_root)
            if err:
                errors.append(f"{os.path.basename(archive)}: {err}")
            extracted.extend(images)

        if not extracted:
            return [], errors or [f"No valid images found in {folder_path}"]

        return _sort_image_paths(extracted, sort_mode), errors
    except Exception as exc:
        return [], [f"Folder scan failed: {exc}"]


def get_first_image_path(folder_path, sort_mode="natural"):
    files = get_sorted_image_files(folder_path, sort_mode)
    return files[0] if files else None


def count_images_in_folder(folder_path):
    try:
        return len(get_sorted_image_files(folder_path, "natural"))
    except Exception:
        return 0


# ==============================================================================
# BACKEND CLASS
# ==============================================================================
# Client-side limits for the restored direct multipart upload path.
UPLOAD_MAX_REQUEST_FILES = 15
UPLOAD_MAX_WORKERS = 20


class EHentaiBackend:
    _gallery_metadata_cache = {}
    _gallery_metadata_cache_lock = threading.RLock()
    # The site can reject two publication transitions made at the same time,
    # even when the uploads themselves used independent sessions.  Batch
    # workers may upload concurrently, but publication must be serialized.
    _publish_lock = threading.Lock()
    _gallery_metadata_cache_max = 300
    _image_lookup_cache = {}
    _image_lookup_cache_lock = threading.RLock()
    _image_lookup_cache_max = 120

    def __init__(self, cookies=None, log_fn=print, cookie_file="cookies.txt", use_ex=False, save_cookie_file=True):
        self.log = log_fn
        self.session = requests.Session()
        self.use_ex = use_ex
        self._tos_checked_at = 0.0
        # When False (worker sessions in the concurrent batch pool),
        # save_session_to_cookie_file becomes a no-op so concurrent workers
        # never race on / clobber the shared cookies.txt file.
        self.save_cookie_file = save_cookie_file

        self.session.headers.update({
            "User-Agent": USER_AGENT,
            "Accept": (
                "text/html,application/xhtml+xml,application/xml;q=0.9,"
                "image/avif,*/*;q=0.8"
            ),
            "Accept-Language": "en-US,en;q=0.5",
            "Connection": "keep-alive",
            "Upgrade-Insecure-Requests": "1",
            "Sec-Fetch-Dest": "document",
            "Sec-Fetch-Mode": "navigate",
            "Sec-Fetch-Site": "none",
            "Sec-Fetch-User": "?1",
        })

        # Reuse a larger connection pool for thumbnail/title probes. Retry only
        # idempotent reads; gallery creation and file uploads must never be
        # replayed automatically.
        retry = Retry(
            total=2,
            connect=2,
            read=2,
            other=0,
            status=2,
            backoff_factor=0.35,
            status_forcelist=(429, 500, 502, 503, 504),
            allowed_methods=frozenset({"GET", "HEAD"}),
            raise_on_status=False,
        )
        adapter = HTTPAdapter(
            pool_connections=8,
            pool_maxsize=16,
            max_retries=retry,
            pool_block=False,
        )
        self.session.mount("https://", adapter)
        self.session.mount("http://", adapter)

        self.base_url = "https://upload.e-hentai.org"
        self.manage_url = f"{self.base_url}/managegallery"
        self.eh_url = "https://e-hentai.org"

        cookie_path = APP_DIR / cookie_file
        if cookie_path.exists():
            self._load_netscape_cookie_file(cookie_path)
        else:
            self.log(
                f"No '{cookie_file}' found; using GUI/manual authentication fields."
            )

        self._load_manual_cookies(cookies)
        self._log_cookie_inventory()

    def _load_netscape_cookie_file(self, cookie_path):
        """
        Load a Netscape-format cookie export while preserving the original
        cookie domains. This avoids collapsing host-specific cookies onto
        .e-hentai.org.
        """
        self.log(
            f"Found '{cookie_path.name}'. Parsing Netscape format with original domains..."
        )
        loaded = 0
        skipped = 0
        seen = set()

        try:
            with open(cookie_path, "r", encoding="utf-8", errors="replace") as f:
                for raw in f:
                    line = raw.rstrip("\r\n")

                    if not line or line.startswith("#") or line.startswith("HTTP"):
                        continue

                    parts = line.split("\t")
                    if len(parts) < 7:
                        skipped += 1
                        continue

                    (
                        domain,
                        include_subdomains,
                        path,
                        secure,
                        expiration,
                        name,
                        value,
                    ) = parts[:7]

                    domain = domain.strip()
                    path = path.strip() or "/"
                    name = name.strip()

                    if not domain or not name:
                        skipped += 1
                        continue

                    cookie_domain = domain

                    key = (cookie_domain.lower(), path, name)
                    if key in seen:
                        skipped += 1
                        continue
                    seen.add(key)

                    secure_bool = secure.strip().upper() == "TRUE"

                    try:
                        expires = int(expiration) if expiration.strip() else None
                    except ValueError:
                        expires = None

                    self._remove_cookie(cookie_domain, path, name)

                    self.session.cookies.set(
                        name=name,
                        value=value,
                        domain=cookie_domain,
                        path=path,
                    )

                    for cookie in self.session.cookies:
                        if (
                            cookie.name == name
                            and cookie.domain == cookie_domain
                            and cookie.path == path
                        ):
                            cookie.secure = secure_bool
                            if expires is not None:
                                cookie.expires = expires
                            break

                    loaded += 1

            self.log(
                f"Successfully loaded {loaded} cookies from '{cookie_path.name}'."
            )

            if skipped:
                self.log(
                    f"[Debug] Skipped {skipped} duplicate/malformed cookie rows."
                )

        except Exception as exc:
            raise RuntimeError(
                f"Failed parsing Netscape cookie file '{cookie_path}': {exc}"
            ) from exc

    def _remove_cookie(self, domain, path, name):
        doomed = []

        for cookie in self.session.cookies:
            if (
                cookie.domain == domain
                and cookie.path == path
                and cookie.name == name
            ):
                doomed.append((cookie.domain, cookie.path, cookie.name))

        for d, p, n in doomed:
            try:
                self.session.cookies.clear(domain=d, path=p, name=n)
            except KeyError:
                pass

    def save_session_to_cookie_file(self, cookie_path=None):
        """Persist the current authenticated session to a Netscape cookies.txt file."""
        if not getattr(self, "save_cookie_file", True):
            self.log("[Debug] Cookie-file writing disabled for this session (worker).")
            return None
        path = Path(cookie_path) if cookie_path else APP_DIR / "cookies.txt"
        target_hosts = {"e-hentai.org", "upload.e-hentai.org", "exhentai.org"}

        relevant = []
        seen = set()

        for cookie in self.session.cookies:
            domain = (cookie.domain or "").lower()
            if not domain:
                continue
            if not any(host in domain for host in ("e-hentai.org", "exhentai.org")):
                continue

            key = (cookie.domain, cookie.path, cookie.name)
            if key in seen:
                continue
            seen.add(key)

            relevant.append(
                (
                    cookie.domain,
                    cookie.domain.startswith("."),
                    cookie.path or "/",
                    bool(cookie.secure),
                    int(cookie.expires) if cookie.expires is not None else 0,
                    cookie.name,
                    cookie.value,
                )
            )

        try:
            with open(path, "w", encoding="utf-8", newline="") as fh:
                for domain, include_subdomains, path, secure, expires, name, value in sorted(
                    relevant,
                    key=lambda item: (item[0], item[2], item[5]),
                ):
                    if domain not in target_hosts and not domain.startswith("."):
                        base = domain
                    else:
                        base = domain
                    fh.write(
                        f"{base}\t"
                        f"{'TRUE' if include_subdomains else 'FALSE'}\t"
                        f"{path}\t"
                        f"{'TRUE' if secure else 'FALSE'}\t"
                        f"{expires}\t"
                        f"{name}\t"
                        f"{value}\n"
                    )

            self.log(f"[Debug] Saved current E-Hentai session to {path}")
            return str(path)
        except Exception as exc:
            self.log(f"[Debug] Failed to save cookie session file: {exc}")
            return None

    def _log_cookie_inventory(self):
        names = sorted({cookie.name for cookie in self.session.cookies})

        self.log(
            "[Debug] Active session cookie names: "
            + (", ".join(names) if names else "NONE")
        )

        for host in (
            "e-hentai.org",
            "upload.e-hentai.org",
            "exhentai.org",
        ):
            temp = requests.Session()
            temp.cookies.update(self.session.cookies)

            prepared = temp.prepare_request(
                requests.Request("GET", f"https://{host}/")
            )

            header = prepared.headers.get("Cookie", "")
            sent = []

            if header:
                sent = [
                    part.split("=", 1)[0]
                    for part in header.split("; ")
                    if "=" in part
                ]

            self.log(
                f"[Debug] Cookies sent to {host}: "
                f"{', '.join(sorted(set(sent))) if sent else 'NONE'}"
            )

    def _load_manual_cookies(self, cookies):
        manual = {
            "ipb_member_id": HARDCODED_MEMBER_ID,
            "ipb_pass_hash": HARDCODED_PASS_HASH,
            "ipb_session_id": "",
            "igneous": HARDCODED_IGNEOUS,
            "sk": HARDCODED_SK,
        }

        if cookies:
            for key, value in cookies.items():
                if value:
                    manual[key] = value

        for key, value in manual.items():
            if not value:
                continue

            if key in {
                "ipb_member_id",
                "ipb_pass_hash",
                "ipb_session_id",
                "sk",
                "star",
                "yay",
            }:
                domain = ".e-hentai.org"
            elif key == "igneous":
                domain = ".exhentai.org" if self.use_ex else ".e-hentai.org"
            else:
                domain = ".e-hentai.org"

            self._remove_cookie(domain, "/", key)

            self.session.cookies.set(
                key,
                str(value),
                domain=domain,
                path="/",
            )

    def ensure_tos_accepted(self):
        """
        Validate the authenticated browser session first, then verify the
        uploader ToS state.
        """
        if time.monotonic() - self._tos_checked_at < 300:
            return True

        self.log("Performing authentication & uploader ToS check...")

        home = self.session.get(
            f"{self.eh_url}/home.php",
            headers={"Referer": f"{self.eh_url}/"},
            timeout=30,
            allow_redirects=True,
        )
        home.raise_for_status()

        home_text = home.text.lower()

        login_indicators = (
            "login.php",
            "ipb_login_form",
            'name="username"',
            'name="password"',
            "please log in",
            "you are not logged in",
            "you are not signed in",
        )

        cookie_names = {cookie.name.lower() for cookie in self.session.cookies}
        has_auth_cookie = any(
            name in cookie_names for name in {"ipb_member_id", "ipb_pass_hash", "igneous", "sk", "ipb_session_id"}
        )

        if (
            ("login" in home.url.lower() or any(marker in home_text for marker in login_indicators))
            and not has_auth_cookie
        ):
            raise RuntimeError(
                "E-Hentai account session was not authenticated. "
                "The cookie export does not contain a valid login session "
                "for e-hentai.org."
            )

        if (
            "login" in home.url.lower()
            or ("log in" in home_text and "logout" not in home_text)
            or any(marker in home_text for marker in login_indicators)
        ):
            raise RuntimeError(
                "E-Hentai account session was not authenticated. "
                f"Final URL: {home.url}. "
                "The stored cookies/session appear stale or expired."
            )

        final_url_lower = home.url.lower()

        if any(marker in final_url_lower for marker in ("/login", "login.php")):
            raise RuntimeError(
                f"E-Hentai account session is not authenticated. "
                f"Final URL: {home.url}"
            )

        if any(marker in home_text for marker in login_indicators):
            raise RuntimeError(
                f"E-Hentai account session is not authenticated. "
                f"Final URL: {home.url}"
            )

        self.log(
            f"Primary E-Hentai account session check passed. Final URL: {home.url}"
        )

        resp = self.session.get(
            f"{self.manage_url}?act=new",
            headers={"Referer": f"{self.eh_url}/home.php"},
            timeout=30,
            allow_redirects=True,
        )
        resp.raise_for_status()

        self.log(f"[Debug] Uploader URL: {resp.url}")

        lower = resp.text.lower()

        if "just a moment" in lower or "cf-mitigated" in lower:
            raise RuntimeError(
                "Cloudflare challenge detected on upload.e-hentai.org. "
                "A browser session/cookie export cannot bypass a challenge by itself."
            )

        tos_required = (
            "you must agree to abide by the terms of service" in lower
            or "you must agree to the terms of service" in lower
            or "terms of service agreement" in lower
        )

        if not tos_required:
            self.log(
                "Uploader ToS check passed: "
                "the creation page is not showing the ToS gate."
            )
            self._tos_checked_at = time.monotonic()
            self.save_session_to_cookie_file()
            return True

        self.log(
            "Uploader ToS gate detected. "
            "Attempting the site's ToS acknowledgement endpoint..."
        )

        candidates = [
            f"{self.eh_url}/tok2.php",
            f"{self.base_url}/tok2.php",
        ]

        accepted = False

        for endpoint in candidates:
            try:
                r = self.session.post(
                    endpoint,
                    data={"tosagree": "1", "act": "tos"},
                    headers={
                        "Referer": resp.url,
                        "Origin": self.eh_url,
                    },
                    timeout=20,
                    allow_redirects=True,
                )

                if r.ok:
                    verify = self.session.get(
                        f"{self.manage_url}?act=new",
                        headers={"Referer": endpoint},
                        timeout=30,
                        allow_redirects=True,
                    )

                    verify_lower = verify.text.lower()

                    if (
                        "you must agree to abide by the terms of service"
                        not in verify_lower
                        and "you must agree to the terms of service"
                        not in verify_lower
                    ):
                        accepted = True
                        self.log(
                            f"Uploader ToS accepted and verified via {endpoint}."
                        )
                        break

            except requests.RequestException as exc:
                self.log(
                    f"[Debug] ToS endpoint failed: {endpoint} ({exc})"
                )

        if accepted:
            self._tos_checked_at = time.monotonic()
            self.save_session_to_cookie_file()
            return True

        raise RuntimeError(
            "The E-Hentai account is authenticated, but upload.e-hentai.org "
            "still requires uploader ToS acceptance. Open the Create New "
            "Gallery page in your browser, click the site's 'agree to the "
            "Terms of Service' control once, then export the updated "
            "cookies.txt and rerun the uploader."
        )

    @staticmethod
    def parse_gallery_title_metadata(html_text):
        """Parse English/Japanese title fields from a gallery page's HTML."""
        soup = BeautifulSoup(html_text, "html.parser")
        result = {"english": [], "japanese": []}
        seen = set()

        jp_re = re.compile(r"[\u3040-\u30ff\u3400-\u4dbf\u4e00-\u9fff]")

        def add_value(kind, value):
            if value is None:
                return
            text = html.unescape(str(value)).strip()
            text = re.sub(r"\s+", " ", text).strip(" \r\n\t\u200b")
            if not text:
                return
            if text in seen:
                return
            seen.add(text)
            result[kind].append(text)

        def classify_from_text(raw):
            text = re.sub(r"\s*[-–—|]\s*(?:E-Hentai|ExHentai|E-Hentai Galleries|ExHentai Galleries).*$", "", raw, flags=re.I)
            text = text.strip()
            if not text:
                return None
            if jp_re.search(text):
                return "japanese"
            if re.search(r"[A-Za-z]", text):
                return "english"
            return None

        for selector in [
            'meta[property="og:title"]',
            'meta[name="twitter:title"]',
            'meta[property="twitter:title"]',
        ]:
            for tag in soup.select(selector):
                content = (tag.get("content") or "").strip()
                if not content:
                    continue
                kind = classify_from_text(content)
                if kind:
                    add_value(kind, content)

        title_tag = soup.find("title")
        if title_tag:
            text = title_tag.get_text(" ", strip=True)
            kind = classify_from_text(text)
            if kind:
                add_value(kind, text)

        for node_id, kind in (("gn", "english"), ("gj", "japanese")):
            el = soup.find(attrs={"id": node_id})
            if el is not None:
                node_text = el.get_text(" ", strip=True)
                if node_text:
                    add_value(kind, node_text)

        for selector in ["#gn", "#gj", "div#gn", "div#gj"]:
            for el in soup.select(selector):
                text = el.get_text(" ", strip=True)
                if not text:
                    continue
                kind = "english" if "gn" in selector else "japanese"
                add_value(kind, text)

        if not result["english"] and not result["japanese"]:
            for node in soup.find_all(string=True):
                text = str(node).strip()
                if not text or len(text) < 2:
                    continue
                kind = classify_from_text(text)
                if kind:
                    add_value(kind, text)

        return result

    def fetch_gallery_title_metadata(self, gallery_url):
        """Fetch exact English/Japanese titles, preferring the gallery API.

        HappyPanda resolves the gallery URL first and then asks E-Hentai's
        metadata API for ``title`` and ``title_jpn``. That is both faster and
        less fragile than scraping display markup, so HTML parsing is retained
        only as a compatibility fallback.
        """
        if not gallery_url:
            raise ValueError("No gallery URL supplied.")

        normalized = gallery_url.strip()
        if not re.match(r"^https?://", normalized, flags=re.I):
            normalized = f"https://{normalized}"

        gallery_match = re.search(
            r"/g/(\d+)/([A-Za-z0-9]+)/?",
            normalized,
            flags=re.I,
        )
        cache_key = normalized.rstrip("/")
        with self._gallery_metadata_cache_lock:
            cached = self._gallery_metadata_cache.get(cache_key)
            if isinstance(cached, dict):
                return {
                    "english": list(cached.get("english", [])),
                    "japanese": list(cached.get("japanese", [])),
                    "url": cached.get("url", normalized),
                }

        if gallery_match:
            gid = int(gallery_match.group(1))
            token = gallery_match.group(2)
            payload = {
                "method": "gdata",
                "gidlist": [[gid, token]],
                "namespace": 1,
            }
            api_urls = []
            if self.use_ex or "exhentai.org" in normalized.lower():
                api_urls.append("https://exhentai.org/api.php")
            api_urls.extend(
                [
                    "https://api.e-hentai.org/api.php",
                    "https://e-hentai.org/api.php",
                ]
            )
            for api_url in dict.fromkeys(api_urls):
                try:
                    response = self.session.post(
                        api_url,
                        json=payload,
                        headers={
                            "Accept": "application/json",
                            "Content-Type": "application/json",
                            "Referer": normalized,
                        },
                        timeout=30,
                    )
                    response.raise_for_status()
                    body = response.json()
                    galleries = body.get("gmetadata", []) if isinstance(body, dict) else []
                    gallery = galleries[0] if galleries else {}
                    if gallery and not gallery.get("error"):
                        title_en = html.unescape(str(gallery.get("title") or "")).strip()
                        title_jp = html.unescape(str(gallery.get("title_jpn") or "")).strip()
                        title_en = re.sub(r"\s+", " ", title_en)
                        title_jp = re.sub(r"\s+", " ", title_jp)
                        result = {
                            "english": [title_en] if title_en else [],
                            "japanese": [title_jp] if title_jp else [],
                            "url": normalized,
                        }
                        if result["english"] or result["japanese"]:
                            with self._gallery_metadata_cache_lock:
                                _bounded_cache_set(
                                    self._gallery_metadata_cache,
                                    cache_key,
                                    result,
                                    self._gallery_metadata_cache_max,
                                )
                            return result
                except Exception as exc:
                    self.log(f"[Metadata API] {api_url} failed; using fallback if needed: {exc}")

        resp = self.session.get(normalized, timeout=30, allow_redirects=True)
        resp.raise_for_status()

        parsed = self.parse_gallery_title_metadata(resp.text)
        result = {
            "english": list(dict.fromkeys(parsed.get("english", []))),
            "japanese": list(dict.fromkeys(parsed.get("japanese", []))),
            "url": resp.url,
        }
        with self._gallery_metadata_cache_lock:
            _bounded_cache_set(
                self._gallery_metadata_cache,
                cache_key,
                result,
                self._gallery_metadata_cache_max,
            )
        return result

    def search_gallery_matches_by_text_list(self, query_text, max_pages=4):
        """Search E-Hentai/ExHentai by text and return every direct gallery match.

        Each result carries ``title``, ``url`` and (when the current result
        display mode exposes one) a ``thumb`` URL so callers can rank
        candidates against a local cover image.  ``_search_gallery_matches_by_text``
        keeps its best-match behavior for existing callers; new multi-source
        flows use this list variant.
        """
        query = str(query_text or "").strip()
        if not query:
            return []

        self.ensure_tos_accepted()
        bases = ["https://exhentai.org", "https://e-hentai.org"] if self.use_ex else ["https://e-hentai.org"]
        seen = set()
        results = []

        for base in bases:
            for page_idx in range(max_pages):
                page = page_idx + 1
                url = f"{base}/?f_search={quote(query)}"
                if page > 1:
                    url = f"{url}&page={page - 1}"
                try:
                    resp = self.session.get(
                        url,
                        headers={
                            "Referer": f"{base}/",
                            "Accept": "text/html,application/xhtml+xml,application/xml;q=0.9,*/*;q=0.8",
                            "User-Agent": USER_AGENT,
                        },
                        timeout=30,
                        allow_redirects=True,
                    )
                    resp.raise_for_status()
                except Exception as exc:
                    self.log(f"[E/Ex text search] {base} page {page} failed: {exc}")
                    continue

                soup = BeautifulSoup(resp.text, "html.parser")
                for a in soup.select("a[href*='/g/']"):
                    href = (a.get("href") or "").strip()
                    if not href:
                        continue
                    match = re.search(r"/g/(\d+)/([^/?#]+)", href)
                    if not match:
                        continue
                    gallery_url = urljoin(resp.url, href.split("#", 1)[0])
                    if gallery_url in seen:
                        continue
                    seen.add(gallery_url)

                    title = ""
                    glink = a.find_parent(["div", "td", "tr", "li"])
                    if glink is not None:
                        for candidate in [glink.select_one("div.glink"), glink.select_one(".glink"), glink.select_one(".glname")]:
                            if candidate is not None:
                                title = candidate.get_text(" ", strip=True)
                                if title:
                                    break
                    if not title:
                        title = a.get_text(" ", strip=True)
                    title = re.sub(r"\s+", " ", str(title or "")).strip(" -")

                    thumb = ""
                    node = a
                    for _ in range(7):
                        if node is None or getattr(node, "name", None) in (None, "body", "html", "[document]"):
                            break
                        image_node = node.select_one("img") if hasattr(node, "select_one") else None
                        if image_node is not None:
                            src = (image_node.get("data-src") or image_node.get("src") or "").strip()
                            if src and not src.startswith("data:"):
                                thumb = urljoin(resp.url, src)
                                break
                        styled = node.select_one("[style*='url']") if hasattr(node, "select_one") else None
                        if styled is not None:
                            thumb_match = re.search(r"url\((['\"]?)([^)'\"]+)\1\)", styled.get("style", ""), re.I)
                            if thumb_match:
                                thumb = urljoin(resp.url, thumb_match.group(2).strip())
                                break
                        node = getattr(node, "parent", None)

                    if title and title.lower() not in {"next", "prev", "search", "show more"}:
                        results.append({"title": title, "url": gallery_url, "thumb": thumb, "similarity": 0.0})

                low = " ".join(s for s in soup.stripped_strings if s).lower()
                if re.search(r"no results|no hits|nothing found", low, flags=re.I):
                    break
                if len(results) >= 12:
                    break
            if len(results) >= 12:
                break

        return results

    def _search_gallery_matches_by_text(self, query_text, max_pages=4):
        """Search E-Hentai/ExHentai by text and return the best direct gallery matches."""
        query = str(query_text or "").strip()
        if not query:
            return {}

        self.ensure_tos_accepted()
        bases = ["https://exhentai.org", "https://e-hentai.org"] if self.use_ex else ["https://e-hentai.org"]
        seen = set()
        results = []

        for base in bases:
            for page_idx in range(max_pages):
                page = page_idx + 1
                url = f"{base}/?f_search={quote(query)}"
                if page > 1:
                    url = f"{url}&page={page - 1}"
                try:
                    resp = self.session.get(
                        url,
                        headers={
                            "Referer": f"{base}/",
                            "Accept": "text/html,application/xhtml+xml,application/xml;q=0.9,*/*;q=0.8",
                            "User-Agent": USER_AGENT,
                        },
                        timeout=30,
                        allow_redirects=True,
                    )
                    resp.raise_for_status()
                except Exception as exc:
                    self.log(f"[E/Ex text search] {base} page {page} failed: {exc}")
                    continue

                soup = BeautifulSoup(resp.text, "html.parser")
                for a in soup.select("a[href*='/g/']"):
                    href = (a.get("href") or "").strip()
                    if not href:
                        continue
                    match = re.search(r"/g/(\d+)/([^/?#]+)", href)
                    if not match:
                        continue
                    gallery_url = urljoin(resp.url, href.split("#", 1)[0])
                    if gallery_url in seen:
                        continue
                    seen.add(gallery_url)

                    title = ""
                    glink = a.find_parent(["div", "td", "tr", "li"])
                    if glink is not None:
                        for candidate in [glink.select_one("div.glink"), glink.select_one(".glink"), glink.select_one(".glname")]:
                            if candidate is not None:
                                title = candidate.get_text(" ", strip=True)
                                if title:
                                    break
                    if not title:
                        title = a.get_text(" ", strip=True)
                    title = re.sub(r"\s+", " ", str(title or "")).strip(" -")
                    if title and title.lower() not in {"next", "prev", "search", "show more"}:
                        results.append({"title": title, "url": gallery_url})

                low = " ".join(s for s in soup.stripped_strings if s).lower()
                if re.search(r"no results|no hits|nothing found", low, flags=re.I):
                    break
                if len(results) >= 12:
                    break
            if len(results) >= 12:
                break

        if not results:
            return {}

        best = results[0]
        try:
            metadata = self.fetch_gallery_title_metadata(best["url"])
            english = metadata.get("english") or [best["title"]]
            japanese = metadata.get("japanese") or [best["title"]]
            return {
                "title_en": english[0],
                "title_jp": japanese[0] if japanese else best["title"],
                "url": best["url"],
            }
        except Exception:
            return {"title_en": best["title"], "title_jp": best["title"], "url": best["url"]}

    def search_gallery_matches_by_image(self, image_path, max_pages=8):
        """Find galleries by uploading the cover to E/Ex image lookup.

        This mirrors HappyPanda's reliable color-image path: multipart POST the
        actual cover as ``sfile`` with ``fs_similar=1``. A SHA-1 URL search is
        retained only as an exact-file fallback.
        """
        if not image_path or not os.path.isfile(image_path):
            raise ValueError("No cover image path was provided.")

        def build_signature(path_or_bytes):
            try:
                source = io.BytesIO(path_or_bytes) if isinstance(path_or_bytes, (bytes, bytearray)) else path_or_bytes
                with Image.open(source) as opened:
                    image = ImageOps.exif_transpose(opened).convert("L")
                    image.thumbnail((64, 64), LANCZOS_FILTER)
                    canvas = Image.new("L", (64, 64), 255)
                    canvas.paste(image, ((64 - image.width) // 2, (64 - image.height) // 2))
                    return canvas.tobytes()
            except Exception:
                return b""

        def similarity_pct(left, right):
            if not left or not right:
                return 0.0
            count = min(len(left), len(right))
            if not count:
                return 0.0
            delta = sum(abs(left[index] - right[index]) for index in range(count))
            return max(0.0, 100.0 * (1.0 - delta / (255.0 * count)))

        target_signature = build_signature(image_path)
        digest = hashlib.sha1()
        with open(image_path, "rb") as image_file:
            for chunk in iter(lambda: image_file.read(1024 * 1024), b""):
                digest.update(chunk)
        exact_sha1 = digest.hexdigest()

        lookup_cache_key = (bool(self.use_ex), exact_sha1)
        with self._image_lookup_cache_lock:
            cached_matches = self._image_lookup_cache.get(lookup_cache_key)
            if isinstance(cached_matches, list):
                self.log("[Image Lookup] Reusing cached cover-search results.")
                return [dict(item) for item in cached_matches[:25]]

        self.ensure_tos_accepted()
        matches = []
        seen_urls = set()
        thumbnail_scores = {}

        def gallery_links(soup, base_url):
            local_seen = set()
            for link in soup.select("a[href*='/g/']"):
                href = (link.get("href") or "").replace("&amp;", "&").strip()
                found = re.search(r"/g/(\d+)/([A-Za-z0-9]+)", href)
                if not found:
                    continue
                url = urljoin(base_url, href.split("#", 1)[0])
                if url in local_seen:
                    continue
                local_seen.add(url)
                yield link, url

        def containing_result(link):
            row = link.find_parent("tr")
            if row is not None:
                return row
            node = link
            for _ in range(6):
                node = getattr(node, "parent", None)
                if node is None:
                    break
                if getattr(node, "name", None) in {"div", "li", "td"}:
                    if node.select_one(".glink, .glname, img, [style*='url']"):
                        return node
            return link.parent

        def result_title(link, container, fallback=""):
            title_node = None
            if container is not None:
                title_node = container.select_one(".glink, .glname, .it5")
            title = title_node.get_text(" ", strip=True) if title_node else link.get_text(" ", strip=True)
            title = re.sub(r"\s+", " ", title or fallback).strip(" -")
            if title.lower() in {"next", "prev", "search", "show more", ">", "<"}:
                return fallback
            return title

        def result_thumbnail(container, base_url):
            if container is None:
                return ""
            image_node = container.select_one("img")
            if image_node is not None:
                src = (image_node.get("data-src") or image_node.get("src") or "").strip()
                if src:
                    return urljoin(base_url, src)
            for styled in container.select("[style*='url']"):
                match = re.search(r"url\((['\"]?)([^)'\"]+)\1\)", styled.get("style", ""), re.I)
                if match:
                    return urljoin(base_url, match.group(2).strip())
            return ""

        def add_results(html_text, response_url):
            soup = BeautifulSoup(html_text or "", "html.parser")
            added = 0

            direct = re.search(r"/g/(\d+)/([A-Za-z0-9]+)", response_url or "")
            if direct and response_url not in seen_urls:
                title_node = soup.select_one("#gn, .glink") or soup.find("title")
                title = title_node.get_text(" ", strip=True) if title_node else response_url
                normalized = response_url.split("?", 1)[0].rstrip("/") + "/"
                seen_urls.add(normalized)
                matches.append({"title": title, "url": normalized, "similarity": 100.0, "thumb": ""})
                added += 1

            for link, gallery_url in gallery_links(soup, response_url):
                if gallery_url in seen_urls:
                    continue
                container = containing_result(link)
                title = result_title(link, container, fallback=gallery_url)
                thumbnail = result_thumbnail(container, response_url)
                score = 0.0
                container_text = container.get_text(" ", strip=True) if container is not None else ""
                percent = re.search(r"(\d{1,3}(?:\.\d+)?)\s*%", container_text)
                if percent:
                    score = min(100.0, float(percent.group(1)))
                if thumbnail:
                    if thumbnail not in thumbnail_scores:
                        local_score = 0.0
                        try:
                            thumb_response = self.session.get(
                                thumbnail,
                                headers={"Referer": response_url},
                                timeout=15,
                            )
                            thumb_response.raise_for_status()
                            local_score = similarity_pct(
                                target_signature,
                                build_signature(thumb_response.content),
                            )
                        except Exception as exc:
                            self.log(f"[Image Lookup] Thumbnail ranking skipped: {exc}")
                        thumbnail_scores[thumbnail] = local_score
                    score = max(score, thumbnail_scores[thumbnail])
                seen_urls.add(gallery_url)
                matches.append(
                    {
                        "title": title,
                        "url": gallery_url,
                        "similarity": round(score, 2),
                        "thumb": thumbnail,
                    }
                )
                added += 1
            return added, soup

        lookup_endpoints = []
        if self.use_ex:
            lookup_endpoints.append("https://exhentai.org/upload/image_lookup.php/")
        lookup_endpoints.append("https://upload.e-hentai.org/image_lookup.php/")

        last_error = None
        for endpoint in dict.fromkeys(lookup_endpoints):
            for attempt in range(1, 4):
                try:
                    self.log(f"[Image Lookup] Uploading cover for similarity search: {endpoint}")
                    with open(image_path, "rb") as image_file:
                        mime_type = mimetypes.guess_type(image_path)[0] or "application/octet-stream"
                        response = self.session.post(
                            endpoint,
                            files={
                                "sfile": (
                                    os.path.basename(image_path),
                                    image_file,
                                    mime_type,
                                )
                            },
                            data={"fs_similar": "1", "fs_exp": "1"},
                            headers={
                                "Referer": endpoint,
                                "Origin": endpoint.split("/upload", 1)[0],
                            },
                            timeout=90,
                            allow_redirects=True,
                        )
                    if response.status_code == 429:
                        raise requests.HTTPError("image lookup rate limited", response=response)
                    response.raise_for_status()
                    lower = response.text.lower()
                    if "please wait a bit longer between each file search" in lower:
                        if attempt < 3:
                            time.sleep(5 * attempt)
                            continue
                    added, _soup = add_results(response.text, response.url)
                    if added:
                        break
                    if "exhentai.org" in endpoint and any(
                        marker in lower
                        for marker in (
                            "sad panda",
                            "access denied",
                            "please stand by while we check your browser",
                        )
                    ):
                        break
                    # A successful no-hit response should fall through to the
                    # public E-Hentai endpoint or the exact hash fallback.
                    break
                except Exception as exc:
                    last_error = exc
                    if attempt < 3:
                        delay = 5 * attempt
                        self.log(f"[Image Lookup] Attempt {attempt} failed; retrying in {delay}s: {exc}")
                        time.sleep(delay)
                        continue
                    self.log(f"[Image Lookup] Endpoint failed: {endpoint}: {exc}")
            if matches:
                break

        if not matches:
            search_bases = ["https://exhentai.org", "https://e-hentai.org"] if self.use_ex else ["https://e-hentai.org"]
            for base in search_bases:
                try:
                    exact_url = f"{base}/?f_shash={exact_sha1}&fs_exp=1"
                    self.log(f"[Image Lookup] Trying exact-file SHA-1 fallback: {exact_url}")
                    response = self.session.get(
                        exact_url,
                        headers={"Referer": f"{base}/"},
                        timeout=30,
                        allow_redirects=True,
                    )
                    response.raise_for_status()
                    added, _soup = add_results(response.text, response.url)
                    if added:
                        break
                except Exception as exc:
                    last_error = exc
                    self.log(f"[Image Lookup] Exact hash fallback failed: {exc}")

        matches.sort(
            key=lambda item: float(item.get("similarity") or 0.0),
            reverse=True,
        )
        # Keep only near-identical covers. Weak text/thumbnail hits create the
        # "unrelated gallery" problem the title picker used to show.
        high_conf = [
            item for item in matches
            if float(item.get("similarity") or 0.0) >= MIN_COVER_SIMILARITY
        ]
        if matches and not high_conf:
            best = float(matches[0].get("similarity") or 0.0)
            self.log(
                f"[Image Lookup] Discarded {len(matches)} low-confidence match(es); "
                f"best score was {best:.1f}% (need >= {MIN_COVER_SIMILARITY:.0f}%)."
            )
        matches = high_conf
        if not matches and last_error is not None:
            self.log(f"[Image Lookup] No matches returned; last error: {last_error}")
        result = matches[:25]
        if result:
            with self._image_lookup_cache_lock:
                _bounded_cache_set(
                    self._image_lookup_cache,
                    lookup_cache_key,
                    [dict(item) for item in result],
                    self._image_lookup_cache_max,
                )
        return result

    def get_creation_schema(self, refresh=False):
        resp = self.session.get(
            f"{self.manage_url}?act=new", headers={"Referer": self.manage_url}, timeout=30,
        )
        resp.raise_for_status()
        _, controls = self._creation_form_controls(BeautifulSoup(resp.text, "html.parser"))
        return {
            key: {"name": control.get("name"), "options": [
                (option.get_text(" ", strip=True), option.get("value", option.get_text(" ", strip=True)))
                for option in control.find_all("option")
                if not option.has_attr("disabled")
                and not (option.parent.name == "optgroup" and option.parent.has_attr("disabled"))
            ]}
            for key, control in controls.items()
        }

    def _resolve_gallery_token(self, gid):
        """Best-effort lookup of the live gallery token for an existing draft/edit page."""
        if gid in (None, "", "0"):
            return None

        candidate_urls = [
            f"{self.manage_url}?act=edit&gid={gid}",
            f"{self.manage_url}?gid={gid}",
            f"{self.manage_url}?ulgid={gid}",
        ]

        cookie_names = sorted({cookie.name for cookie in self.session.cookies})

        for url in candidate_urls:
            try:
                self.log(f"[Debug] Resolving edit-page token for gid={gid} via {url}")
                self.log(
                    "[Debug] Active cookie names for token lookup: "
                    + (", ".join(cookie_names) if cookie_names else "NONE")
                )
                resp = self.session.get(
                    url,
                    headers={"Referer": self.manage_url, "Origin": self.base_url},
                    timeout=30,
                    allow_redirects=True,
                )
                resp.raise_for_status()
            except requests.RequestException as exc:
                self.log(f"[Debug] Token lookup request failed for {url}: {exc}")
                continue

            html = resp.text or ""
            page_snippet = re.sub(r"\s+", " ", html[:1600])

            if "login.php" in resp.url.lower() or "please log in" in html.lower() or "you are not logged in" in html.lower():
                self.log(f"[Debug] Edit page is not authenticated for gid={gid}; final URL={resp.url}")
                self.log(f"[Debug] Edit page snippet: {page_snippet[:500]}")
                continue

            for pattern in (
                r"(?:[?&])token=([A-Za-z0-9]+)",
                r"['\"]token['\"]\s*:\s*['\"]([A-Za-z0-9]+)['\"]",
                r"(?:[?&])gid=(\d+)(?:[&#]|&|$)[^\n]*?[?&]token=([A-Za-z0-9]+)",
                r"(?:[?&])token=([^&#\s\"']+)",
            ):
                match = re.search(pattern, html, re.I)
                if match:
                    token = match.group(1) if match.lastindex == 1 else match.group(2)
                    if token and token not in {"0", "None"}:
                        self.log(f"[Debug] Resolved edit token for gid={gid}: {token}")
                        return token

            soup = BeautifulSoup(html, "html.parser")
            token_input = soup.find("input", {"name": "token"}) or soup.find("input", {"name": "gallerytoken"})
            if token_input and token_input.get("value"):
                token = token_input.get("value")
                if token and token not in {"0", "None"}:
                    self.log(f"[Debug] Found hidden token input for gid={gid}: {token}")
                    return token

            for tag in soup.find_all(["a", "form", "script", "meta"]):
                for attr in ("href", "action", "content"):
                    value = tag.get(attr, "")
                    if not value:
                        continue
                    m = re.search(r"(?:[?&])token=([A-Za-z0-9]+)", value, re.I)
                    if m:
                        token = m.group(1)
                        if token and token not in {"0", "None"}:
                            self.log(f"[Debug] Found token in markup for gid={gid}: {token}")
                            return token

            self.log(f"[Debug] No token discovered on {url}; final URL={resp.url}")
            self.log(f"[Debug] Edit page snippet: {page_snippet[:800]}")

        self.log(f"[Debug] Failed to resolve any live gallery token for gid={gid}.")
        return None

    def create_gallery(
        self,
        title_en,
        title_jp="",
        category="Doujinshi",
        language="Japanese",
        folder="Unsorted",
        unlisted=True,
        language_type="Official / Textless",
        ai_generated=False,
    ):
        """Create a gallery using the live E-Hentai create form."""
        form_url = f"{self.manage_url}?act=new"

        resp_get = self.session.get(
            form_url,
            headers={
                "Referer": f"{self.eh_url}/home.php",
                "Accept": (
                    "text/html,application/xhtml+xml,application/xml;q=0.9,"
                    "image/avif,*/*;q=0.8"
                ),
            },
            timeout=30,
            allow_redirects=True,
        )
        resp_get.raise_for_status()

        soup = BeautifulSoup(resp_get.text, "html.parser")
        form, creation_controls = self._creation_form_controls(soup)

        action = form.get("action") or form_url
        target_url = urljoin(resp_get.url, action)
        method = (form.get("method") or "post").lower()

        payload = {}

        def add_field(name, value):
            if name:
                payload[name] = value

        def set_select_by_text(select, desired_text):
            desired = " ".join(str(desired_text or "").split()).casefold()
            options = [option for option in select.find_all("option")
                       if not option.has_attr("disabled")
                       and not (option.parent.name == "optgroup" and option.parent.has_attr("disabled"))]
            matches = [option for option in options
                       if " ".join(option.get_text(" ", strip=True).split()).casefold() == desired]
            if not matches:
                matches = [option for option in options if str(option.get("value", "")) == str(desired_text)]
            name = select.get("name")
            if not name or select.has_attr("disabled") or len(matches) != 1:
                raise RuntimeError(
                    f"Saved choice {desired_text!r} is unavailable or ambiguous for "
                    f"{name or 'a required gallery field'}. Sync the form and choose a valid value for this gallery."
                )
            option = matches[0]
            payload[name] = option.get("value", option.get_text(" ", strip=True))

        for element in form.find_all(["input", "select", "textarea"]):
            name = element.get("name")
            if not name or element.has_attr("disabled"):
                continue

            tag_name = element.name.lower()
            if tag_name == "input":
                input_type = (element.get("type") or "text").lower()
                if input_type in {"submit", "button", "image", "reset", "file"}:
                    continue
                if input_type in {"checkbox", "radio"}:
                    if element.has_attr("checked"):
                        add_field(name, element.get("value", "on"))
                    continue
                add_field(name, element.get("value", ""))
            elif tag_name == "textarea":
                add_field(name, element.get_text(" ", strip=True))
            elif tag_name == "select":
                options = element.find_all("option")
                selected = [opt for opt in options if opt.has_attr("selected")]
                if not selected and options:
                    selected = [options[0]]
                if element.has_attr("multiple"):
                    add_field(name, [opt.get("value", "") for opt in selected])
                else:
                    add_field(name, selected[0].get("value", "") if selected else "")

        set_select_by_text(creation_controls["category"], category)
        set_select_by_text(creation_controls["lang"], language)
        set_select_by_text(creation_controls["folder"], folder)

        language_types = {"Official / Textless": "0", "Translated": "1", "Rewrite": "2"}
        if language_type not in language_types:
            raise RuntimeError(f"Unknown language type: {language_type!r}. Choose a valid language type.")
        if not isinstance(ai_generated, bool):
            raise RuntimeError("AI-generated must be a boolean selection.")
        radios = form.find_all("input", attrs={"name": "langtype", "type": "radio"})
        if radios:
            expected = language_types[language_type]
            if not any(r.get("value") == expected and not r.has_attr("disabled") for r in radios):
                raise RuntimeError("The selected language type is unavailable in the live form.")
            payload["langtype"] = expected
        elif language_type != "Official / Textless":
            raise RuntimeError("The live form does not expose the requested language type.")
        ai_control = form.find("input", attrs={"name": "aigen", "type": "checkbox"})
        payload.pop("aigen", None)
        if ai_generated:
            if ai_control is None or ai_control.has_attr("disabled"):
                raise RuntimeError("The live form does not expose the AI-generated checkbox.")
            payload["aigen"] = ai_control.get("value", "on")

        title_en_field = None
        for name in ("gname_en", "title_en", "title"):
            if form.find(attrs={"name": name}):
                title_en_field = name
                break
        if title_en_field:
            payload[title_en_field] = title_en.strip() or "Untitled Gallery"
        else:
            payload["gname_en"] = title_en.strip() or "Untitled Gallery"

        title_jp_field = None
        for name in ("gname_jp", "title_jp", "jtitle"):
            if form.find(attrs={"name": name}):
                title_jp_field = name
                break
        if title_jp_field:
            payload[title_jp_field] = title_jp.strip()

        if unlisted:
            unlisted_input = form.find("input", {"name": "unlisted", "type": "checkbox"})
            if unlisted_input:
                payload["unlisted"] = unlisted_input.get("value", "1")
            else:
                generic_unlisted = form.find("input", {"name": "unlisted"})
                if generic_unlisted:
                    payload["unlisted"] = generic_unlisted.get("value", "1")
        else:
            payload.pop("unlisted", None)

        payload.setdefault("MAX_FILE_SIZE", "1258291200")
        payload.setdefault("do_save", "1")
        payload.setdefault("ulcomment", "")
        payload.setdefault("foldername", "")
        payload["tos"] = "1"

        request_headers = {
            "Referer": resp_get.url,
            "Origin": self.base_url,
            "Accept": (
                "text/html,application/xhtml+xml,application/xml;q=0.9,*/*;q=0.8"
            ),
        }

        if method == "get":
            post_resp = self.session.get(
                target_url,
                params=payload,
                headers=request_headers,
                timeout=30,
                allow_redirects=True,
            )
        else:
            request_headers["Content-Type"] = "application/x-www-form-urlencoded"
            post_resp = self.session.post(
                target_url,
                data=payload,
                headers=request_headers,
                timeout=30,
                allow_redirects=True,
            )

        post_resp.raise_for_status()

        gid_val = None
        token_val = None
        draft_identifier = False
        urls_to_check = [post_resp.url, *(r.url for r in post_resp.history)]

        for u in urls_to_check:
            if not u:
                continue
            decoded = u.replace("&amp;", "&")

            patterns = [
                r"(?:[?&])gid=(\d+)(?:[&#])token=([a-f0-9]+)",
                r"(?:[?&])gid=(\d+)(?:[&#])token=([^&#]+)",
            ]
            for pattern in patterns:
                match = re.search(pattern, decoded, re.I)
                if match:
                    gid_val, token_val = match.group(1), match.group(2)
                    break
            if not gid_val:
                ulgid_match = re.search(r"(?:[?&])ulgid=(\d+)", decoded, re.I)
                if ulgid_match:
                    gid_val = ulgid_match.group(1)
                    draft_identifier = True
            if gid_val and token_val:
                break

        if not gid_val:
            res_soup = BeautifulSoup(post_resp.text, "html.parser")
            gid_input = res_soup.find("input", {"name": "gid"}) or res_soup.find("input", {"name": "ulgid"})
            if gid_input:
                gid_val = gid_input.get("value")
                if str(gid_input.get("name") or "").lower() == "ulgid":
                    draft_identifier = True
            token_input = res_soup.find("input", {"name": "token"})
            if token_input:
                token_val = token_input.get("value")

        # A freshly created gallery is a DRAFT identified by its ulgid (the
        # "upload gallery id") — this is what the creation redirect carries
        # (e.g. managegallery?ulgid=2450422). The public gid+token used in
        # e-hentai.org/g/{gid}/{token}/ URLs are NOT exposed on the draft page
        # and are not needed to upload images: uploads go through the live
        # #uploadform on managegallery?ulgid=... (field name 'files[]'). So a
        # missing token is normal here, not an error.
        if draft_identifier:
            # ulgid and public gid are different identifier spaces. Looking up
            # an edit token by treating an ulgid as a public gid can target an
            # unrelated gallery and makes auto-publish operate on the wrong URL.
            token_val = None
        elif not token_val and gid_val:
            token_val = self._resolve_gallery_token(gid_val)
            if token_val:
                self.log(f"[Debug] Resolved live gallery token for gid={gid_val}: {token_val}")
            else:
                self.log(
                    f"[Debug] No gallery token exposed for ulgid={gid_val}. "
                    "This is normal for an unpublished draft; image uploads use "
                    "the ulgid + the live #uploadform, not a token."
                )

        if not gid_val:
            try:
                debug_file = APP_DIR / "eh_gallery_create_response.html"
                debug_file.write_text(post_resp.text, encoding="utf-8", errors="replace")
                self.log(f"[Debug] Server response saved to: {debug_file}")
            except Exception:
                pass
            raise RuntimeError(
                "Server rejected gallery creation. "
                f"HTTP {post_resp.status_code}. Final URL: {post_resp.url}."
            )

        # Save the draft creation response for diagnosis.
        try:
            debug_file = APP_DIR / "eh_gallery_draft_page.html"
            debug_file.write_text(post_resp.text, encoding="utf-8", errors="replace")
            self.log(f"[Debug] Draft creation response saved to: {debug_file}")
        except Exception:
            pass

        token_val = token_val or None
        self.log(f"[Debug] create_gallery returned ulgid={gid_val}, token={token_val}")
        return gid_val, token_val

    def _gallery_worker_target(self, gid, token=None):
        gid = str(gid)
        token = (token or "").strip()

        if token and token not in {"0", "None"}:
            upload_url = f"{self.base_url}/galleryworker.php?gid={gid}&token={token}"
            referer_url = f"{self.manage_url}?act=edit&gid={gid}&token={token}"
        else:
            upload_url = f"{self.base_url}/galleryworker.php?gid={gid}"
            referer_url = f"{self.manage_url}?act=edit&gid={gid}"

        return upload_url, referer_url

    def upload_file(self, *args, **kwargs):
        """
        Upload a single image to an existing gallery draft by submitting the
        gallery's live #uploadform. E-Hentai accepts image uploads only through
        the managegallery upload form (file field name 'files[]'); it does NOT
        accept posts to galleryworker.php. So the endpoint, the file input
        name, and the hidden fields are read from the live form rather than
        hardcoded.
        """
        gid = kwargs.get("gid") or kwargs.get("ulgid")
        token = kwargs.get("token", "")
        file_path = (
            kwargs.get("file_path")
            or kwargs.get("filepath")
            or kwargs.get("file")
        )

        if len(args) >= 4:
            gid, token, file_path, _ = args[:4]
        elif len(args) == 3:
            gid, token, file_path = args
        elif len(args) == 2:
            gid, file_path = args
        elif len(args) == 1 and isinstance(args[0], (str, Path)):
            file_path = args[0]

        if gid is None:
            for arg in args:
                if isinstance(arg, (str, int)) and not isinstance(arg, bool):
                    if not (
                        isinstance(arg, (str, Path))
                        and Path(str(arg)).exists()
                    ):
                        gid = arg
                        break

        if file_path is None:
            for arg in args:
                if isinstance(arg, (str, Path)):
                    candidate = Path(arg)
                    if candidate.exists() and candidate.is_file():
                        file_path = candidate
                        break

        if gid is None or file_path is None:
            raise ValueError(
                f"Could not resolve valid gid ({gid}) or file_path "
                f"({file_path}) from args={args}, kwargs={kwargs}"
            )

        start_index = kwargs.get("file_start_index", kwargs.get("file_index"))
        if start_index is None and len(args) >= 4:
            start_index = args[3]
        return self.upload_files(str(gid), [Path(file_path)], start_index)

    def _count_uploaded_files(self, html_text):
        """Best-effort count of images already uploaded to a draft, parsed from
        the managegallery page HTML. Used only for post-upload verification.
        """
        if not html_text:
            return 0
        text = html_text
        count = 0
        for pattern in (
            r"files? uploaded so far[^0-9]*(\d+)",
            r"(\d+)\s+files? uploaded",
            r"uploaded\s+images?\s*[:\-]?\s*(\d+)",
        ):
            match = re.search(pattern, text, re.I)
            if match:
                try:
                    count = max(count, int(match.group(1)))
                except ValueError:
                    pass
        try:
            soup = BeautifulSoup(text, "html.parser")
            for cell in soup.find_all(["td", "th"]):
                label = re.sub(r"\s+", " ", cell.get_text(" ", strip=True))
                if re.fullmatch(r"Uploaded Files\s*:", label, flags=re.I):
                    value_cell = cell.find_next_sibling(["td", "th"])
                    if value_cell is not None:
                        found = re.search(r"\d+", value_cell.get_text(" ", strip=True))
                        if found:
                            count = max(count, int(found.group(0)))
            for script in soup.find_all("script"):
                pages_match = re.search(r"\bvar\s+pages\s*=\s*(\d+)", script.get_text(" ", strip=False), re.I)
                if pages_match:
                    count = max(count, int(pages_match.group(1)))
            image_cells = soup.select("div[id^='cell_']")
            if image_cells:
                count = max(count, len(image_cells))
            uploaded = [
                img
                for img in soup.find_all("img")
                if "g/" in (img.get("src") or "")
                or "thumb" in (img.get("src") or "").lower()
            ]
            if uploaded:
                count = max(count, len(uploaded))
        except Exception:
            pass
        return count

    @staticmethod
    def _upload_count_from_page(html_text):
        """Use explicit server counters, not arbitrary thumbnail/logo counts.

        Missing markup means unknown, NOT zero. This is especially important
        when deciding whether an interrupted POST actually completed.
        """
        counts = []
        soup = BeautifulSoup(html_text or "", "html.parser")
        text = soup.get_text(" ", strip=True)
        for pattern in (
            r"files? uploaded so far[^0-9]*(\d+)",
            r"(\d+)\s+files? uploaded",
            r"uploaded\s+images?\s*[:\-]?\s*(\d+)",
        ):
            for match in re.finditer(pattern, text, re.I):
                counts.append(int(match.group(1)))
        for cell in soup.find_all(["td", "th"]):
            label = re.sub(r"\s+", " ", cell.get_text(" ", strip=True))
            if re.fullmatch(r"Uploaded Files\s*:?", label, flags=re.I):
                value_cell = cell.find_next_sibling(["td", "th"])
                found = re.search(r"\d[\d,]*", value_cell.get_text(" ", strip=True)) if value_cell is not None else None
                if found:
                    counts.append(int(found.group(0).replace(",", "")))
        for script in soup.find_all("script"):
            match = re.search(r"\b(?:var|let|const)\s+pages\s*=\s*(\d+)",
                              script.get_text(" ", strip=False), re.I)
            if match:
                counts.append(int(match.group(1)))
        return max(counts) if counts else None

    def _wait_for_uploaded_count(self, page_url, expected_count, timeout=90):
        """Wait only when server-side image processing is still catching up."""
        deadline = time.monotonic() + max(1, timeout)
        last_count = 0
        delay = 0.75
        last_response = None
        while time.monotonic() < deadline:
            last_response = self.session.get(
                page_url,
                headers={"Referer": self.manage_url, "Origin": self.base_url},
                timeout=30,
                allow_redirects=True,
            )
            last_response.raise_for_status()
            last_count = self._count_uploaded_files(last_response.text)
            if last_count >= expected_count:
                return last_response, last_count
            time.sleep(delay)
            delay = min(4.0, delay * 1.45)
        raise RuntimeError(
            "E-Hentai did not finish processing the uploaded images before "
            f"the verification timeout (expected at least {expected_count}, "
            f"server reports {last_count}). The gallery was left as a draft."
        )

    def upload_files(self, ulgid, file_paths, file_start_index=1):
        """
        Upload one caller-selected image batch in a multipart POST using the
        proven request path from the earlier performance/cache build.

        The live upload form supplies the endpoint, file field, and hidden
        values. HTTP 429/5xx and transport failures are retried with exponential
        backoff up to three attempts, matching that build's behavior.
        """
        ulgid = str(ulgid)
        file_paths = [Path(p) for p in file_paths if p]
        if not file_paths:
            return None

        page_url = f"{self.manage_url}?ulgid={ulgid}"
        page_resp = self.session.get(
            page_url,
            headers={
                "Referer": self.manage_url,
                "Origin": self.base_url,
            },
            timeout=30,
            allow_redirects=True,
        )
        page_resp.raise_for_status()

        soup = BeautifulSoup(page_resp.text, "html.parser")
        form = soup.find("form", {"id": "uploadform"}) or soup.find("form")
        if form is None:
            raise RuntimeError(
                f"No upload form found on {page_resp.url}. The gallery "
                f"draft for ulgid={ulgid} may not exist or the session is stale."
            )

        action = form.get("action") or page_resp.url
        target_url = urljoin(page_resp.url, action)
        file_input = form.find("input", {"type": "file"})
        file_field_name = (
            (file_input.get("name") if file_input else "") or "files[]"
        )

        data = {}
        for hidden in form.find_all("input", {"type": "hidden"}):
            name = hidden.get("name")
            if name:
                data[name] = hidden.get("value", "")

        before_count = self._count_uploaded_files(page_resp.text)
        self.log(
            f"[Debug] upload_files ulgid={ulgid} -> {target_url} "
            f"field={file_field_name!r} files={len(file_paths)} "
            f"hidden={sorted(data.keys())}"
        )

        max_retries = 3
        backoff = 2
        response = None

        for attempt in range(1, max_retries + 1):
            opened_files = []
            files_payload = []
            try:
                for file_path in file_paths:
                    mime_type, _ = mimetypes.guess_type(str(file_path))
                    mime_type = mime_type or "application/octet-stream"
                    file_handle = open(file_path, "rb")
                    opened_files.append(file_handle)
                    files_payload.append(
                        (file_field_name, (file_path.name, file_handle, mime_type))
                    )

                try:
                    response = self.session.post(
                        target_url,
                        files=files_payload,
                        data=data,
                        headers={
                            "Referer": page_resp.url,
                            "Origin": self.base_url,
                        },
                        timeout=120,
                        allow_redirects=True,
                    )
                finally:
                    for file_handle in opened_files:
                        try:
                            file_handle.close()
                        except Exception:
                            pass

                status = response.status_code
                snippet = re.sub(r"\s+", " ", response.text[:1200])
                if status == 429 or status >= 500:
                    self.log(
                        f"[Debug] upload_files HTTP {status} "
                        f"(attempt {attempt}/{max_retries}): {snippet}"
                    )
                    if attempt < max_retries:
                        time.sleep(backoff)
                        backoff *= 2
                        continue
                    response.raise_for_status()

                if status >= 400:
                    self.log(
                        f"[Debug] upload_files {status} {response.url}\n{snippet}"
                    )
                response.raise_for_status()

                expected_count = before_count + len(file_paths)
                _verify, after_count = self._wait_for_uploaded_count(
                    page_url,
                    expected_count,
                    timeout=90,
                )
                self.log(
                    f"[Debug] Verified upload: draft files "
                    f"{before_count} -> {after_count} "
                    f"(expected at least {expected_count})."
                )
                return response

            except requests.HTTPError as exc:
                code = exc.response.status_code if exc.response is not None else None
                if (
                    code == 429 or (code is not None and code >= 500)
                ) and attempt < max_retries:
                    self.log(
                        f"[Debug] upload_files HTTP {code}; retrying in "
                        f"{backoff}s (attempt {attempt}/{max_retries})."
                    )
                    time.sleep(backoff)
                    backoff *= 2
                    continue
                raise
            except requests.RequestException as exc:
                if attempt < max_retries:
                    self.log(
                        f"[Debug] upload_files network error: {exc}; "
                        f"retrying in {backoff}s "
                        f"(attempt {attempt}/{max_retries})."
                    )
                    time.sleep(backoff)
                    backoff *= 2
                    continue
                raise

        return response

    def publish_gallery(self, gid, token=None, expected_files=None):
        with self._publish_lock:
            return self._publish_gallery_unlocked(gid, token, expected_files)

    def _publish_gallery_unlocked(self, gid, token=None, expected_files=None):
        """Publish and prove that E-Hentai made the gallery public.

        A 200 response is not success: the site also returns HTTP 200 when the
        draft is not ready or when it shows an error page. The live draft page
        puts its actual action in ``input#publishbutton``'s ``onclick`` and adds
        ``from=gallery``. Follow that action, then poll the manage page until it
        exposes a public /g/{gid}/{token}/ URL and reports the gallery visible.
        """
        identifier = str(gid).strip()
        live_token = (token or "").strip()
        if not identifier:
            raise ValueError("No gallery identifier was supplied for publishing.")

        is_existing_public = live_token not in {"", "0", "None"}
        if is_existing_public:
            manage_page_url = (
                f"{self.manage_url}?act=edit&gid={identifier}&token={live_token}"
            )
        else:
            manage_page_url = f"{self.manage_url}?ulgid={identifier}"

        def inspect(response):
            page = response.text or ""
            soup = BeautifulSoup(page, "html.parser")
            public_url = ""
            # A successful publish may redirect directly to the public gallery.
            # Such a page does not necessarily contain a link to itself, so the
            # old link-only check could report failure after a real publication.
            if re.search(r"/g/\d+/[A-Za-z0-9]+/?", response.url or ""):
                public_url = (response.url or "").split("?", 1)[0]
            for link in soup.find_all("a", href=True):
                href = urljoin(response.url, link.get("href", ""))
                if re.search(r"/g/\d+/[A-Za-z0-9]+/?", href):
                    public_url = href.split("?", 1)[0]
                    break

            visible = False
            posted = False
            for row in soup.select("td#d tr"):
                cells = [
                    re.sub(r"\s+", " ", cell.get_text(" ", strip=True))
                    for cell in row.find_all("td")
                ]
                if len(cells) < 2:
                    continue
                label = cells[0].lower()
                value = cells[1].lower()
                if "visible" in label:
                    visible = value.startswith("yes")
                elif "date posted" in label:
                    posted = bool(value and "not published" not in value)

            unpublished_markers = (
                "not published yet",
                "no (unpublished)",
                "gallery must be published first",
            )
            still_unpublished = any(marker in page.lower() for marker in unpublished_markers)
            # "Visible" can legitimately be No for private/unlisted, expunged,
            # or newly screened galleries.  Date Posted plus a public gallery
            # identifier is the durable publication signal.
            published = bool(public_url and posted and not still_unpublished)

            publish_url = ""
            publish_button = soup.select_one("input#publishbutton, button#publishbutton")
            publish_enabled = publish_button is not None and not publish_button.has_attr("disabled")
            if publish_button is not None:
                onclick = html.unescape(publish_button.get("onclick", ""))
                match = re.search(
                    r"(?:document\.)?location(?:\.href)?\s*=\s*['\"]([^'\"]*act=publish[^'\"]*)",
                    onclick,
                    flags=re.I,
                )
                if match:
                    publish_url = urljoin(response.url, match.group(1))

            if not publish_url:
                for tag in soup.find_all(["a", "form"]):
                    value = tag.get("href" if tag.name == "a" else "action", "")
                    value = html.unescape(value or "")
                    if "act=publish" in value.lower():
                        publish_url = urljoin(response.url, value)
                        break

            errors = []
            for node in soup.select("#e, .error, .errors, p.e"):
                message = re.sub(r"\s+", " ", node.get_text(" ", strip=True))
                if message and message not in errors:
                    errors.append(message)

            # Some uploader errors are plain paragraphs rather than elements
            # carrying an error class. Preserve the useful server explanation.
            for node in soup.find_all(["p", "div", "td"]):
                message = re.sub(r"\s+", " ", node.get_text(" ", strip=True))
                low = message.lower()
                if (
                    message
                    and len(message) <= 500
                    and any(marker in low for marker in (
                        "cannot publish",
                        "could not publish",
                        "publish limit",
                        "rate limit",
                        "try again later",
                        "wait before",
                    ))
                    and message not in errors
                ):
                    errors.append(message)

            return {
                "published": published,
                "public_url": public_url,
                "uploaded": self._count_uploaded_files(page),
                "publish_url": publish_url,
                "publish_enabled": publish_enabled,
                "errors": errors,
            }

        def fetch_manage_page(referer=None):
            response = self.session.get(
                manage_page_url,
                headers={"Referer": referer or self.manage_url},
                timeout=30,
                allow_redirects=True,
            )
            response.raise_for_status()
            return response

        def verified_result(response):
            state = inspect(response)
            if not state["published"]:
                return None
            gallery_match = re.search(
                r"/g/(\d+)/([A-Za-z0-9]+)",
                state["public_url"],
                flags=re.I,
            )
            result = {
                "response": response,
                "gallery_url": state["public_url"],
                "gid": gallery_match.group(1) if gallery_match else identifier,
                "token": gallery_match.group(2) if gallery_match else live_token,
            }
            self.log(f"[Publish] Verified public gallery: {result['gallery_url']}")
            return result

        # Wait for the live publish control. This is normally immediate because
        # upload_files already verifies each chunk, but it covers the site's
        # asynchronous post-processing window.
        deadline = time.monotonic() + 90
        delay = 0.75
        ready_response = None
        ready_state = None
        while time.monotonic() < deadline:
            ready_response = fetch_manage_page()
            already_published = verified_result(ready_response)
            if already_published:
                return already_published
            ready_state = inspect(ready_response)
            enough_files = (
                ready_state["uploaded"] >= int(expected_files)
                if expected_files is not None
                else ready_state["uploaded"] > 0
            )
            if is_existing_public or (
                enough_files
                and ready_state["publish_enabled"]
                and ready_state["publish_url"]
            ):
                break
            time.sleep(delay)
            delay = min(4.0, delay * 1.45)

        if ready_response is None or ready_state is None:
            raise RuntimeError("Could not load the gallery manage page before publishing.")
        if not is_existing_public and ready_state["uploaded"] <= 0:
            raise RuntimeError(
                "E-Hentai still reports an empty gallery, so it was left as a draft."
            )
        if expected_files is not None and ready_state["uploaded"] < int(expected_files):
            raise RuntimeError(
                "E-Hentai has not finished processing all uploaded files "
                f"({ready_state['uploaded']}/{int(expected_files)}); the gallery "
                "was left as a draft instead of being falsely marked Published."
            )

        if is_existing_public:
            publish_url = (
                f"{self.manage_url}?act=publish&gid={identifier}"
                f"&token={live_token}&from=gallery"
            )
        else:
            publish_url = ready_state["publish_url"] or (
                f"{self.manage_url}?ulgid={identifier}&act=publish&from=gallery"
            )

        self.log(f"[Publish] Following the live gallery publish action: {publish_url}")
        publish_response = self.session.get(
            publish_url,
            headers={"Referer": ready_response.url, "Origin": self.base_url},
            timeout=45,
            allow_redirects=True,
        )
        publish_response.raise_for_status()

        immediate = verified_result(publish_response)
        if immediate:
            return immediate

        # Publication can take a moment to become visible. Poll semantic state,
        # not merely HTTP status.
        verification_deadline = time.monotonic() + 60
        delay = 1.0
        last_response = publish_response
        while time.monotonic() < verification_deadline:
            time.sleep(delay)
            delay = min(5.0, delay * 1.4)
            last_response = fetch_manage_page(referer=publish_url)
            result = verified_result(last_response)
            if result:
                return result

        final_state = inspect(last_response)
        detail = "; ".join(final_state.get("errors", [])[:3])
        if not detail:
            detail = (
                f"server still reports {final_state['uploaded']} uploaded files "
                "without a visible public gallery URL"
            )
        raise RuntimeError(
            "E-Hentai did not confirm publication. The gallery remains a draft: "
            + detail
        )

    @staticmethod
    def _creation_form_controls(soup):
        """Find the gallery form, not a preceding navigation/search form."""
        aliases = {
            "category": ("category", "cat", "gallery_category"),
            "lang": ("langtag", "language", "lang", "gallery_language"),
            "folder": ("folderid", "folder", "gallery_folder", "galleryfolder"),
        }
        candidates = []
        for form in soup.find_all("form"):
            controls = {}
            for key, names in aliases.items():
                for select in form.find_all("select"):
                    identity = {str(select.get("name") or "").lower(),
                                str(select.get("id") or "").lower()}
                    if identity.intersection(names):
                        controls[key] = select
                        break
                if key not in controls:
                    labels = {"category": {"category"}, "lang": {"language"},
                              "folder": {"gallery folder", "folder"}}[key]
                    for label in form.find_all("label"):
                        if label.get_text(" ", strip=True).rstrip(":").strip().lower() in labels:
                            control = (form.find("select", id=label.get("for"))
                                       if label.get("for") else label.find("select"))
                            if control is not None:
                                controls[key] = control
                                break
            title = form.find(attrs={"name": re.compile(r"^(gname_en|title_en|title)$", re.I)})
            if title is not None and "category" in controls:
                candidates.append((len(controls), form, controls))
        if not candidates:
            raise RuntimeError("The live Create New Gallery form was not recognized. "
                               "Check your session and Sync again; no gallery was created.")
        _, form, controls = max(candidates, key=lambda entry: entry[0])
        missing = {"category", "lang", "folder"} - controls.keys()
        if missing:
            raise RuntimeError("The server form is missing supported controls: "
                               + ", ".join(sorted(missing)) + ". No gallery was created.")
        return form, controls



def _find_chromium_executable():
    env = os.environ
    candidates = [
        os.path.join(env.get("ProgramFiles", r"C:\Program Files"), "Google", "Chrome", "Application", "chrome.exe"),
        os.path.join(env.get("ProgramFiles(x86)", r"C:\Program Files (x86)"), "Google", "Chrome", "Application", "chrome.exe"),
        os.path.join(env.get("LOCALAPPDATA", ""), "Google", "Chrome", "Application", "chrome.exe"),
        os.path.join(env.get("ProgramFiles", r"C:\Program Files"), "Microsoft", "Edge", "Application", "msedge.exe"),
        os.path.join(env.get("ProgramFiles(x86)", r"C:\Program Files (x86)"), "Microsoft", "Edge", "Application", "msedge.exe"),
        shutil.which("chrome") or "",
        shutil.which("msedge") or "",
        shutil.which("chromium") or "",
        shutil.which("google-chrome") or "",
        shutil.which("google-chrome-stable") or "",
    ]
    for path in candidates:
        if path and os.path.isfile(path):
            return path
    return ""


def _chromium_dump_html(url, timeout=50, log_fn=None):
    """Load a URL with installed Chrome/Edge and return the rendered HTML.

    DoujinRepublic 404s Python/curl clients (203-byte nginx stub) while the
    same URL loads in a real browser. Headless Chromium uses the same TLS
    stack as the user's browser.
    """
    exe = _find_chromium_executable()
    if not exe:
        raise RuntimeError(
            "DoujinRepublic blocks non-browser HTTP clients. Install Chrome or Edge, then retry."
        )
    tmpdir = tempfile.mkdtemp(prefix="dr_chrome_")
    try:
        cmd = [
            exe,
            "--headless=new",
            "--disable-gpu",
            "--disable-extensions",
            "--no-first-run",
            "--no-default-browser-check",
            f"--user-data-dir={tmpdir}",
            "--dump-dom",
            url,
        ]
        startupinfo = None
        creationflags = 0
        if os.name == "nt":
            startupinfo = subprocess.STARTUPINFO()
            startupinfo.dwFlags |= subprocess.STARTF_USESHOWWINDOW
            creationflags = getattr(subprocess, "CREATE_NO_WINDOW", 0)
        if log_fn:
            log_fn(f"[DoujinRepublic] Fetching via Chromium: {url}")
        proc = subprocess.run(
            cmd,
            capture_output=True,
            timeout=timeout,
            startupinfo=startupinfo,
            creationflags=creationflags,
        )
        html = (proc.stdout or b"").decode("utf-8", errors="replace")
        if not html.strip():
            html = (proc.stderr or b"").decode("utf-8", errors="replace")
        if len(html) < 1500 or re.search(r"<title>\s*404 not found\s*</title>", html, re.I):
            raise RuntimeError(
                "DoujinRepublic returned no usable HTML through Chromium. "
                "Open the site once in Chrome/Edge, then retry."
            )
        return html
    except subprocess.TimeoutExpired as exc:
        raise RuntimeError(f"Chromium timed out loading {url}") from exc
    finally:
        shutil.rmtree(tmpdir, ignore_errors=True)


def _windows_powershell_exe():
    sysroot = os.environ.get("SystemRoot", r"C:\Windows")
    exe = os.path.join(sysroot, "System32", "WindowsPowerShell", "v1.0", "powershell.exe")
    if os.path.isfile(exe):
        return exe
    return shutil.which("powershell") or ""


_WINDOWS_OCR_PS1 = r"""
param([Parameter(Mandatory=$true)][string]$ImagePath, [string]$Lang = 'ja')
$ErrorActionPreference = 'Stop'
[Console]::OutputEncoding = New-Object System.Text.UTF8Encoding $false
$OutputEncoding = [Console]::OutputEncoding
Add-Type -AssemblyName System.Runtime.WindowsRuntime | Out-Null
$asTaskGeneric = [System.WindowsRuntimeSystemExtensions].GetMethods() | Where-Object {
    $_.Name -eq 'AsTask' -and $_.IsGenericMethod -and $_.GetParameters().Count -eq 1 -and $_.GetParameters()[0].ParameterType.Name -like 'IAsyncOperation*'
} | Select-Object -First 1
if ($null -eq $asTaskGeneric) {
    throw 'Windows Runtime AsTask helper was not found.'
}
function Await-WinRT($WinRtTask, [Type]$ResultType) {
    $asTask = $asTaskGeneric.MakeGenericMethod($ResultType)
    $netTask = $asTask.Invoke($null, @($WinRtTask))
    $netTask.Wait(-1) | Out-Null
    return $netTask.Result
}
[Windows.Globalization.Language,Windows.Foundation,ContentType=WindowsRuntime] | Out-Null
[Windows.Media.Ocr.OcrEngine,Windows.Foundation,ContentType=WindowsRuntime] | Out-Null
[Windows.Storage.StorageFile,Windows.Storage,ContentType=WindowsRuntime] | Out-Null
[Windows.Graphics.Imaging.BitmapDecoder,Windows.Graphics.Imaging,ContentType=WindowsRuntime] | Out-Null
[Windows.Storage.FileAccessMode,Windows.Storage,ContentType=WindowsRuntime] | Out-Null
$language = New-Object Windows.Globalization.Language $Lang
$engine = [Windows.Media.Ocr.OcrEngine]::TryCreateFromLanguage($language)
if (-not $engine) {
    $engine = [Windows.Media.Ocr.OcrEngine]::TryCreateFromUserProfileLanguages()
}
if (-not $engine) { throw "Windows OCR engine is unavailable" }
$file = Await-WinRT ([Windows.Storage.StorageFile]::GetFileFromPathAsync($ImagePath)) ([Windows.Storage.StorageFile])
$stream = Await-WinRT ($file.OpenAsync([Windows.Storage.FileAccessMode]::Read)) ([Windows.Storage.Streams.IRandomAccessStream])
$decoder = Await-WinRT ([Windows.Graphics.Imaging.BitmapDecoder]::CreateAsync($stream)) ([Windows.Graphics.Imaging.BitmapDecoder])
$bitmap = Await-WinRT ($decoder.GetSoftwareBitmapAsync()) ([Windows.Graphics.Imaging.SoftwareBitmap])
$result = Await-WinRT ($engine.RecognizeAsync($bitmap)) ([Windows.Media.Ocr.OcrResult])
[Console]::Out.Write(($result.Text | Out-String).TrimEnd())
"""

_WINDOWS_OCR_REGIONS_PS1 = r"""
param([Parameter(Mandatory=$true)][string]$ImagePath, [string]$Lang = 'ja')
$ErrorActionPreference = 'Stop'
[Console]::OutputEncoding = New-Object System.Text.UTF8Encoding $false
$OutputEncoding = [Console]::OutputEncoding
Add-Type -AssemblyName System.Runtime.WindowsRuntime | Out-Null
$asTaskGeneric = [System.WindowsRuntimeSystemExtensions].GetMethods() | Where-Object {
    $_.Name -eq 'AsTask' -and $_.IsGenericMethod -and $_.GetParameters().Count -eq 1 -and $_.GetParameters()[0].ParameterType.Name -like 'IAsyncOperation*'
} | Select-Object -First 1
if ($null -eq $asTaskGeneric) { throw 'Windows Runtime AsTask helper was not found.' }
function Await-WinRT($WinRtTask, [Type]$ResultType) {
    $asTask = $asTaskGeneric.MakeGenericMethod($ResultType)
    $netTask = $asTask.Invoke($null, @($WinRtTask))
    $netTask.Wait(-1) | Out-Null
    return $netTask.Result
}
[Windows.Globalization.Language,Windows.Foundation,ContentType=WindowsRuntime] | Out-Null
[Windows.Media.Ocr.OcrEngine,Windows.Foundation,ContentType=WindowsRuntime] | Out-Null
[Windows.Storage.StorageFile,Windows.Storage,ContentType=WindowsRuntime] | Out-Null
[Windows.Graphics.Imaging.BitmapDecoder,Windows.Graphics.Imaging,ContentType=WindowsRuntime] | Out-Null
[Windows.Storage.FileAccessMode,Windows.Storage,ContentType=WindowsRuntime] | Out-Null
$language = New-Object Windows.Globalization.Language $Lang
$engine = [Windows.Media.Ocr.OcrEngine]::TryCreateFromLanguage($language)
if (-not $engine) { $engine = [Windows.Media.Ocr.OcrEngine]::TryCreateFromUserProfileLanguages() }
if (-not $engine) { throw 'Windows OCR engine is unavailable' }
$file = Await-WinRT ([Windows.Storage.StorageFile]::GetFileFromPathAsync($ImagePath)) ([Windows.Storage.StorageFile])
$stream = Await-WinRT ($file.OpenAsync([Windows.Storage.FileAccessMode]::Read)) ([Windows.Storage.Streams.IRandomAccessStream])
$decoder = Await-WinRT ([Windows.Graphics.Imaging.BitmapDecoder]::CreateAsync($stream)) ([Windows.Graphics.Imaging.BitmapDecoder])
$bitmap = Await-WinRT ($decoder.GetSoftwareBitmapAsync()) ([Windows.Graphics.Imaging.SoftwareBitmap])
$result = Await-WinRT ($engine.RecognizeAsync($bitmap)) ([Windows.Media.Ocr.OcrResult])
$items = New-Object System.Collections.ArrayList
foreach ($line in $result.Lines) {
    $words = @($line.Words)
    if ($words.Count -lt 1) { continue }
    $left = [double]::PositiveInfinity
    $top = [double]::PositiveInfinity
    $right = [double]::NegativeInfinity
    $bottom = [double]::NegativeInfinity
    foreach ($word in $words) {
        $r = $word.BoundingRect
        if ($r.X -lt $left) { $left = $r.X }
        if ($r.Y -lt $top) { $top = $r.Y }
        if (($r.X + $r.Width) -gt $right) { $right = $r.X + $r.Width }
        if (($r.Y + $r.Height) -gt $bottom) { $bottom = $r.Y + $r.Height }
    }
    $null = $items.Add([PSCustomObject]@{
        text = [string]$line.Text
        x = [double]$left
        y = [double]$top
        w = [double]($right - $left)
        h = [double]($bottom - $top)
    })
}
[Console]::Out.Write((ConvertTo-Json -InputObject @($items) -Compress -Depth 4))
"""



def _split_ocr_text_candidates(full_text):
    japanese = []
    english = []
    seen = set()

    def add(value, bucket):
        cleaned = re.sub(r"\s+", " ", str(value or "")).strip(" -_|,\t")
        if len(cleaned) < 2 or cleaned in seen:
            return
        seen.add(cleaned)
        bucket.append(cleaned)

    for line in str(full_text or "").splitlines():
        line = re.sub(r"\s+", " ", line).strip()
        if not line:
            continue
        if re.search(r"[\u3040-\u30ff\u3400-\u4dbf\u4e00-\u9fff]", line):
            add(line, japanese)
        elif re.search(r"[A-Za-z]", line):
            add(line, english)
        for token in re.findall(
            r"[\u3040-\u30ff\u3400-\u9fff]{2,}|[A-Za-z0-9][A-Za-z0-9'_-]{1,}",
            line,
        ):
            if re.search(r"[\u3040-\u30ff\u3400-\u4dbf\u4e00-\u9fff]", token):
                add(token, japanese)
            elif re.search(r"[A-Za-z]", token):
                add(token, english)
    return japanese, english


def _ocr_image_windows(image_path, langs=("ja", "en"), log_fn=None):
    """Read cover text with Windows.Media.Ocr (better CJK than Tesseract)."""
    if os.name != "nt":
        raise RuntimeError("Windows OCR is only available on Windows.")
    exe = _windows_powershell_exe()
    if not exe:
        raise RuntimeError("Windows PowerShell was not found for OCR.")
    png_path = os.path.abspath(image_path)
    tmp_png = None
    script_path = None
    try:
        handle = tempfile.NamedTemporaryFile(prefix="win_ocr_", suffix=".png", delete=False)
        tmp_png = handle.name
        handle.close()
        with Image.open(png_path) as raw:
            img = ImageOps.exif_transpose(raw).convert("RGB")
            max_side = 2600
            if max(img.size) > max_side:
                img.thumbnail((max_side, max_side), LANCZOS_FILTER)
            if min(img.size) < 80:
                img = img.resize((img.width * 3, img.height * 3), LANCZOS_FILTER)
            img.save(tmp_png, "PNG")
        png_path = tmp_png
        script = tempfile.NamedTemporaryFile(prefix="win_ocr_", suffix=".ps1", delete=False)
        script_path = script.name
        script.close()
        Path(script_path).write_text(_WINDOWS_OCR_PS1, encoding="utf-8-sig")
        chunks = []
        for lang in langs:
            if log_fn:
                log_fn(f"[OCR] Windows OCR ({lang}): {png_path}")
            proc = subprocess.run(
                [
                    exe,
                    "-NoProfile",
                    "-ExecutionPolicy",
                    "Bypass",
                    "-File",
                    script_path,
                    "-ImagePath",
                    png_path,
                    "-Lang",
                    lang,
                ],
                capture_output=True,
                timeout=45,
            )
            out = (proc.stdout or b"").decode("utf-8", errors="replace").strip()
            if proc.returncode != 0 and not out:
                err = (proc.stderr or b"").decode("utf-8", errors="replace").strip()
                raise RuntimeError(err or f"Windows OCR failed for {lang}")
            if out:
                chunks.append(out)
        merged = _tighten_cjk_ocr_text("\n".join(dict.fromkeys(chunks)))
        if not merged.strip():
            raise RuntimeError("Windows OCR returned no text.")
        return merged
    finally:
        for extra in (tmp_png, script_path):
            if extra:
                try:
                    os.remove(extra)
                except Exception:
                    pass



def _tighten_cjk_ocr_text(text):
    return re.sub(
        r"(?<=[\u3040-\u30ff\u3400-\u9fff])\s+(?=[\u3040-\u30ff\u3400-\u9fff])",
        "",
        str(text or ""),
    )


def _ocr_image_gemini(image_path, api_key, log_fn=None):
    """Read cover text with the Gemini free-tier vision API.

    Google Cloud Vision OCR is billed and is not used. Gemini Flash on
    Google AI Studio is the free alternative.
    """
    import base64

    api_key = str(api_key or "").strip()
    if not api_key:
        raise RuntimeError("No Gemini API key is configured.")
    buf = io.BytesIO()
    with Image.open(image_path) as raw:
        img = ImageOps.exif_transpose(raw).convert("RGB")
        img.thumbnail((1600, 1600), LANCZOS_FILTER)
        img.save(buf, format="JPEG", quality=85)
    payload = {
        "contents": [{
            "parts": [
                {
                    "text": (
                        "Transcribe every printed word on this manga/doujin cover. "
                        "Keep original Japanese and English. One text block per line. "
                        "No translation, no commentary, no markdown."
                    )
                },
                {
                    "inline_data": {
                        "mime_type": "image/jpeg",
                        "data": base64.b64encode(buf.getvalue()).decode("ascii"),
                    }
                },
            ]
        }],
        "generationConfig": {"temperature": 0, "maxOutputTokens": 1024},
    }
    last_error = None
    for model in (
        "gemini-2.5-flash",
        "gemini-2.0-flash",
        "gemini-2.0-flash-lite",
        "gemini-flash-latest",
    ):
        url = f"https://generativelanguage.googleapis.com/v1beta/models/{model}:generateContent"
        try:
            if log_fn:
                log_fn(f"[OCR] Gemini OCR ({model})")
            response = requests.post(url, params={"key": api_key}, json=payload, timeout=60)
            if response.status_code in {404, 429}:
                last_error = f"{model}: HTTP {response.status_code}"
                continue
            if response.status_code >= 400:
                detail = ""
                try:
                    detail = str((response.json().get("error") or {}).get("message") or "")
                except Exception:
                    detail = (response.text or "")[:240]
                last_error = detail or f"{model}: HTTP {response.status_code}"
                if response.status_code in {401, 403}:
                    break
                continue
            body = response.json() if response.content else {}
            parts = (((body.get("candidates") or [{}])[0].get("content") or {}).get("parts") or [])
            text = "\n".join(str(part.get("text") or "") for part in parts).strip()
            text = _tighten_cjk_ocr_text(text)
            if text:
                return text
            last_error = f"{model} returned no text"
        except Exception as exc:
            last_error = exc
            continue
    raise RuntimeError(f"Gemini OCR failed: {last_error}")


_PADDLE_OCR_ENGINE = None
_PADDLE_OCR_KIND = ""


def _load_paddle_ocr_engine(log_fn=None):
    global _PADDLE_OCR_ENGINE, _PADDLE_OCR_KIND
    if _PADDLE_OCR_ENGINE is not None:
        return _PADDLE_OCR_ENGINE, _PADDLE_OCR_KIND
    try:
        from paddleocr import PaddleOCR
        try:
            engine = PaddleOCR(use_angle_cls=True, lang="japan", show_log=False)
        except TypeError:
            engine = PaddleOCR(lang="japan")
        _PADDLE_OCR_ENGINE, _PADDLE_OCR_KIND = engine, "paddleocr"
        if log_fn:
            log_fn("[OCR] Loaded PaddleOCR (japan)")
        return _PADDLE_OCR_ENGINE, _PADDLE_OCR_KIND
    except Exception as exc:
        if log_fn:
            log_fn(f"[OCR] Full PaddleOCR package not available: {exc}")
    try:
        from rapidocr_onnxruntime import RapidOCR
        engine = RapidOCR()
        _PADDLE_OCR_ENGINE, _PADDLE_OCR_KIND = engine, "rapidocr"
        if log_fn:
            log_fn("[OCR] Loaded PaddleOCR models via RapidOCR")
        return _PADDLE_OCR_ENGINE, _PADDLE_OCR_KIND
    except Exception as exc:
        raise RuntimeError(
            "PaddleOCR is not installed. Use Settings > Cover OCR to install RapidOCR (Paddle models)."
        ) from exc


def _parse_paddle_ocr_lines(raw):
    if raw is None:
        return []
    if hasattr(raw, "rec_texts"):
        return [str(item).strip() for item in (raw.rec_texts or []) if str(item).strip()]
    rows = raw[0] if isinstance(raw, tuple) else raw
    if rows is None:
        return []
    if isinstance(rows, dict):
        values = rows.get("rec_texts") or rows.get("texts") or []
        return [str(item).strip() for item in values if str(item).strip()]
    texts = []
    for item in rows or []:
        if item is None:
            continue
        if isinstance(item, str):
            if item.strip():
                texts.append(item.strip())
            continue
        if isinstance(item, (list, tuple)) and len(item) >= 2:
            payload = item[1]
            if isinstance(payload, str):
                if payload.strip():
                    texts.append(payload.strip())
            elif isinstance(payload, (list, tuple)) and payload:
                value = str(payload[0]).strip()
                if value:
                    texts.append(value)
    return texts


def _ocr_image_paddle(image_path, log_fn=None):
    """Read cover text with PaddleOCR, or RapidOCR running Paddle PP-OCR models."""
    import numpy as np

    engine, kind = _load_paddle_ocr_engine(log_fn)
    if log_fn:
        log_fn(f"[OCR] PaddleOCR ({kind})")
    with Image.open(image_path) as raw:
        arr = np.array(ImageOps.exif_transpose(raw).convert("RGB"))
    if kind == "paddleocr":
        if hasattr(engine, "ocr"):
            try:
                raw_result = engine.ocr(arr, cls=True)
            except TypeError:
                raw_result = engine.ocr(arr)
        else:
            raw_result = engine.predict(arr)
    else:
        raw_result = engine(arr)
    lines = _parse_paddle_ocr_lines(raw_result)
    text = _tighten_cjk_ocr_text("\n".join(lines))
    if not text.strip():
        raise RuntimeError("PaddleOCR returned no text.")
    return text




def _manual_ocr_crop_text(crop_image, target="japanese", log_fn=None):
    """OCR one user-drawn crop without relying on pre-detected text boxes.

    The crop is enlarged and tried through a few conservative preprocessing
    variants.  Recognition stays local: Rapid/Paddle first, Windows OCR next,
    then Tesseract when installed.  The highest-scoring non-empty result is
    returned together with the engine/variant that produced it.
    """
    target = "english" if str(target).lower().startswith("en") else "japanese"
    src = ImageOps.exif_transpose(crop_image).convert("RGB")
    if src.width < 2 or src.height < 2:
        raise RuntimeError("The marquee is too small to OCR.")

    # OCR engines are substantially better on small cover lettering after
    # enlargement.  Cap the result so a large marquee does not explode memory.
    shortest = max(1, min(src.size))
    scale = max(1.0, min(4.0, 280.0 / shortest))
    max_side = max(src.size) * scale
    if max_side > 3000:
        scale *= 3000.0 / max_side
    new_size = (max(2, int(src.width * scale)), max(2, int(src.height * scale)))
    enlarged = src.resize(new_size, LANCZOS_FILTER) if new_size != src.size else src.copy()

    gray = ImageOps.grayscale(enlarged)
    contrast = ImageOps.autocontrast(gray, cutoff=1)
    contrast = ImageEnhance.Contrast(contrast).enhance(1.35)
    sharpened = contrast.filter(ImageFilter.UnsharpMask(radius=1.2, percent=170, threshold=2))

    # Two variants are normally enough and avoid turning stylized characters
    # into thresholding artifacts.  Tesseract additionally gets a binary pass.
    variants = [
        ("color", enlarged),
        ("contrast", sharpened.convert("RGB")),
    ]
    threshold_level = 150
    binary = sharpened.point(lambda px: 255 if px >= threshold_level else 0).convert("RGB")

    candidates = []
    seen = set()

    def add(text, engine, variant):
        value = _tighten_cjk_ocr_text(str(text or ""))
        value = re.sub(r"[ \t]+", " ", value)
        value = re.sub(r"\n{3,}", "\n\n", value).strip()
        if not value or value in seen:
            return
        seen.add(value)
        candidates.append((value, engine, variant))

    temp_paths = []
    try:
        # RapidOCR / PaddleOCR tends to be strongest for mixed Japanese/Latin
        # cover typography, so try it on both useful variants.
        for variant_name, img in variants:
            try:
                f = tempfile.NamedTemporaryFile(prefix="manual_marquee_", suffix=".png", delete=False)
                path = f.name
                f.close()
                temp_paths.append(path)
                img.save(path, "PNG")
                add(_ocr_image_paddle(path, log_fn=log_fn), "Paddle/RapidOCR", variant_name)
            except Exception as exc:
                if log_fn:
                    log_fn(f"[Manual OCR] Paddle/RapidOCR {variant_name} pass unavailable: {exc}")

        # Windows OCR is useful on systems where the appropriate language pack
        # is installed.  Prefer the user's currently selected destination.
        if os.name == "nt":
            langs = ("en",) if target == "english" else ("ja",)
            for variant_name, img in variants:
                try:
                    f = tempfile.NamedTemporaryFile(prefix="manual_marquee_win_", suffix=".png", delete=False)
                    path = f.name
                    f.close()
                    temp_paths.append(path)
                    img.save(path, "PNG")
                    add(_ocr_image_windows(path, langs=langs, log_fn=log_fn), "Windows OCR", variant_name)
                except Exception as exc:
                    if log_fn:
                        log_fn(f"[Manual OCR] Windows OCR {variant_name} pass unavailable: {exc}")

        # Tesseract fallback. Try line/block segmentation because a marquee may
        # contain one word, one line, or a compact multi-line title fragment.
        try:
            import pytesseract
            _configure_pytesseract_binary(pytesseract)
            lang = "eng" if target == "english" else "jpn+eng"
            tess_variants = variants + [("binary", binary)]
            for variant_name, img in tess_variants:
                for psm in (6, 7, 11):
                    try:
                        text = pytesseract.image_to_string(
                            img,
                            lang=lang,
                            config=f"--psm {psm} -c preserve_interword_spaces=1",
                        )
                        add(text, f"Tesseract psm {psm}", variant_name)
                    except Exception:
                        continue
        except Exception as exc:
            if log_fn:
                log_fn(f"[Manual OCR] Tesseract fallback unavailable: {exc}")

    finally:
        for path in temp_paths:
            try:
                os.remove(path)
            except Exception:
                pass

    if not candidates:
        raise RuntimeError(
            "No OCR engine returned text for that marquee. Try drawing a slightly "
            "larger rectangle around the characters, or zoom in and select again."
        )

    def score(item):
        text, engine, _variant = item
        compact = re.sub(r"\s+", "", text)
        cjk = len(re.findall(r"[\u3040-\u30ff\u3400-\u9fff]", text))
        latin = len(re.findall(r"[A-Za-z]", text))
        digits = len(re.findall(r"[0-9]", text))
        symbols = max(0, len(compact) - cjk - latin - digits)
        # Destination choice is a recognition hint, not a filter: punctuation
        # and mixed-script titles remain intact.
        if target == "japanese":
            language_bonus = cjk * 5.0 + latin * 0.8
        else:
            language_bonus = latin * 3.0 + cjk * 0.5
        engine_bonus = 2.0 if engine.startswith("Paddle") else (1.0 if engine.startswith("Windows") else 0.0)
        return language_bonus + digits + symbols * 0.8 + len(compact) * 0.35 + engine_bonus

    best = max(candidates, key=score)
    if log_fn:
        log_fn(
            f"[Manual OCR] Marquee recognized with {best[1]} ({best[2]}): "
            f"{best[0][:180]}"
        )
    return best[0], best[1], best[2], [item[0] for item in sorted(candidates, key=score, reverse=True)]


def _ocr_polygon_bbox(points):
    clean = []
    for point in points or []:
        try:
            clean.append((float(point[0]), float(point[1])))
        except Exception:
            continue
    if not clean:
        return None
    xs = [pt[0] for pt in clean]
    ys = [pt[1] for pt in clean]
    return (min(xs), min(ys), max(xs), max(ys))


def _looks_like_ocr_polygon(value):
    if not isinstance(value, (list, tuple)) or len(value) < 4:
        return False
    good = 0
    for point in value[:8]:
        if not isinstance(point, (list, tuple)) or len(point) < 2:
            return False
        try:
            float(point[0]); float(point[1])
            good += 1
        except Exception:
            return False
    return good >= 4


def _normalize_ocr_confidence(value):
    try:
        score = float(value)
    except Exception:
        return 0.0
    if score <= 1.0:
        score *= 100.0
    return max(0.0, min(100.0, score))


def _parse_ocr_regions(raw):
    """Return text + polygon regions from PaddleOCR/RapidOCR result variants."""
    regions = []

    def seq(value):
        if value is None:
            return []
        try:
            return list(value)
        except Exception:
            return []

    def first_present(*values):
        for value in values:
            if value is not None:
                return value
        return None

    def add_region(poly, text, score=0):
        value = re.sub(r"\s+", " ", str(text or "")).strip()
        if not value or not _looks_like_ocr_polygon(poly):
            return
        clean_poly = [(float(pt[0]), float(pt[1])) for pt in poly]
        bbox = _ocr_polygon_bbox(clean_poly)
        if bbox is None:
            return
        regions.append({
            "text": value,
            "confidence": _normalize_ocr_confidence(score),
            "polygon": clean_poly,
            "bbox": bbox,
        })

    def parse_object(obj):
        if obj is None:
            return

        texts = getattr(obj, "rec_texts", None)
        if texts is not None:
            polys = first_present(
                getattr(obj, "rec_polys", None),
                getattr(obj, "dt_polys", None),
                getattr(obj, "polys", None),
            )
            scores = first_present(getattr(obj, "rec_scores", None), getattr(obj, "scores", None))
            text_list, poly_list, score_list = seq(texts), seq(polys), seq(scores)
            for idx, text in enumerate(text_list):
                if idx < len(poly_list):
                    add_region(poly_list[idx], text, score_list[idx] if idx < len(score_list) else 0)
            return

        if isinstance(obj, dict):
            texts = first_present(obj.get("rec_texts"), obj.get("texts"))
            polys = first_present(obj.get("rec_polys"), obj.get("dt_polys"), obj.get("polys"), obj.get("boxes"))
            scores = first_present(obj.get("rec_scores"), obj.get("scores"))
            text_list, poly_list, score_list = seq(texts), seq(polys), seq(scores)
            if text_list and poly_list:
                for idx, text in enumerate(text_list):
                    if idx < len(poly_list):
                        add_region(poly_list[idx], text, score_list[idx] if idx < len(score_list) else 0)
                return
            for value in obj.values():
                if isinstance(value, (dict, list, tuple)):
                    parse_object(value)
            return

        if isinstance(obj, tuple) and len(obj) == 2 and isinstance(obj[0], (list, tuple)):
            parse_object(obj[0])
            return

        if isinstance(obj, (list, tuple)):
            if len(obj) >= 2 and _looks_like_ocr_polygon(obj[0]):
                payload = obj[1]
                if isinstance(payload, str):
                    add_region(obj[0], payload, obj[2] if len(obj) > 2 else 0)
                    return
                if isinstance(payload, (list, tuple)) and payload:
                    text = payload[0] if isinstance(payload[0], str) else ""
                    score = payload[1] if len(payload) > 1 else 0
                    if text:
                        add_region(obj[0], text, score)
                        return
            for item in obj:
                parse_object(item)

    parse_object(raw)

    deduped = []
    seen = set()
    for region in regions:
        x1, y1, x2, y2 = region["bbox"]
        key = (region["text"], round(x1 / 4), round(y1 / 4), round(x2 / 4), round(y2 / 4))
        if key in seen:
            continue
        seen.add(key)
        deduped.append(region)
    deduped.sort(key=lambda item: (item["bbox"][1], item["bbox"][0]))
    return deduped


def _configure_pytesseract_binary(pytesseract_module):
    tess = shutil.which("tesseract")
    if tess:
        pytesseract_module.pytesseract.tesseract_cmd = tess
        return tess
    if os.name == "nt":
        alt = os.environ.get("TESSERACT_CMD") or os.environ.get("TESSERACT_PATH")
        candidates = [
            alt,
            r"C:\\Program Files\\Tesseract-OCR\\tesseract.exe",
            r"C:\\Program Files (x86)\\Tesseract-OCR\\tesseract.exe",
        ]
        for candidate in candidates:
            if candidate and os.path.exists(candidate):
                pytesseract_module.pytesseract.tesseract_cmd = candidate
                return candidate
    raise RuntimeError("Tesseract is not installed or not on PATH.")


def _detect_manual_ocr_regions(image_path, log_fn=None):
    """Detect selectable OCR regions for the Lens-style manual OCR popup.

    RapidOCR/PaddleOCR is preferred because it supplies line polygons. Tesseract
    is the fallback and its word boxes are grouped into readable line regions.
    Coordinates are always returned in the original EXIF-corrected image space.
    """
    path = os.path.abspath(str(image_path or ""))
    if not path or not os.path.isfile(path):
        raise RuntimeError("The cover image could not be found.")

    with Image.open(path) as raw:
        original = ImageOps.exif_transpose(raw).convert("RGB")
        original_w, original_h = original.size
        max_dim = max(original_w, original_h)
        process_scale = min(1.0, 2200.0 / max_dim) if max_dim else 1.0
        if process_scale < 1.0:
            process_img = original.resize(
                (max(1, int(original_w * process_scale)), max(1, int(original_h * process_scale))),
                LANCZOS_FILTER,
            )
        else:
            process_img = original.copy()

    errors = []

    # Best interactive result: line polygons from Paddle/RapidOCR.
    try:
        import numpy as np
        engine, kind = _load_paddle_ocr_engine(log_fn)
        arr = np.array(process_img)
        if kind == "paddleocr":
            if hasattr(engine, "ocr"):
                try:
                    raw_result = engine.ocr(arr, cls=True)
                except TypeError:
                    raw_result = engine.ocr(arr)
            else:
                raw_result = engine.predict(arr)
        else:
            raw_result = engine(arr)
        regions = _parse_ocr_regions(raw_result)
        if regions:
            if process_scale != 1.0:
                inverse = 1.0 / process_scale
                for region in regions:
                    region["polygon"] = [(x * inverse, y * inverse) for x, y in region["polygon"]]
                    region["bbox"] = _ocr_polygon_bbox(region["polygon"])
            for region in regions:
                region["engine"] = "RapidOCR" if kind == "rapidocr" else "PaddleOCR"
            if log_fn:
                log_fn(f"[Manual OCR] {len(regions)} selectable region(s) detected with {regions[0]['engine']}.")
            return regions
        errors.append(f"{kind}: no regions")
    except Exception as exc:
        errors.append(f"Paddle/RapidOCR: {exc}")
        if log_fn:
            log_fn(f"[Manual OCR] Paddle/RapidOCR region detection unavailable: {exc}")

    # Windows.Media.Ocr supplies line bounding boxes without extra Python wheels.
    if os.name == "nt":
        tmp_png = None
        script_path = None
        try:
            exe = _windows_powershell_exe()
            if not exe:
                raise RuntimeError("Windows PowerShell was not found.")
            handle = tempfile.NamedTemporaryFile(prefix="manual_ocr_", suffix=".png", delete=False)
            tmp_png = handle.name
            handle.close()
            process_img.save(tmp_png, "PNG")
            script = tempfile.NamedTemporaryFile(prefix="manual_ocr_", suffix=".ps1", delete=False)
            script_path = script.name
            script.close()
            Path(script_path).write_text(_WINDOWS_OCR_REGIONS_PS1, encoding="utf-8-sig")

            all_regions = []
            for lang in ("ja", "en"):
                proc = subprocess.run(
                    [
                        exe, "-NoProfile", "-ExecutionPolicy", "Bypass",
                        "-File", script_path, "-ImagePath", tmp_png, "-Lang", lang,
                    ],
                    capture_output=True,
                    timeout=45,
                )
                out = (proc.stdout or b"").decode("utf-8", errors="replace").strip()
                if proc.returncode != 0 and not out:
                    err = (proc.stderr or b"").decode("utf-8", errors="replace").strip()
                    raise RuntimeError(err or f"Windows OCR failed for {lang}")
                if not out:
                    continue
                parsed = json.loads(out)
                if isinstance(parsed, dict):
                    parsed = [parsed]
                inverse = 1.0 / process_scale if process_scale else 1.0
                for item in parsed or []:
                    text = _tighten_cjk_ocr_text(str(item.get("text") or "")).strip()
                    if not text:
                        continue
                    x = float(item.get("x") or 0) * inverse
                    y = float(item.get("y") or 0) * inverse
                    w = float(item.get("w") or 0) * inverse
                    h = float(item.get("h") or 0) * inverse
                    if w <= 0 or h <= 0:
                        continue
                    poly = [(x, y), (x + w, y), (x + w, y + h), (x, y + h)]
                    all_regions.append({
                        "text": text,
                        "confidence": 0.0,
                        "polygon": poly,
                        "bbox": _ocr_polygon_bbox(poly),
                        "engine": "Windows OCR",
                    })

            deduped = []
            seen = set()
            for region in sorted(all_regions, key=lambda item: (item["bbox"][1], item["bbox"][0])):
                x1, y1, x2, y2 = region["bbox"]
                key = (region["text"], round(x1 / 6), round(y1 / 6), round(x2 / 6), round(y2 / 6))
                if key in seen:
                    continue
                seen.add(key)
                deduped.append(region)
            if deduped:
                if log_fn:
                    log_fn(f"[Manual OCR] {len(deduped)} selectable region(s) detected with Windows OCR.")
                return deduped
            errors.append("Windows OCR: no regions")
        except Exception as exc:
            errors.append(f"Windows OCR: {exc}")
            if log_fn:
                log_fn(f"[Manual OCR] Windows OCR region detection unavailable: {exc}")
        finally:
            for extra in (tmp_png, script_path):
                if extra:
                    try:
                        os.remove(extra)
                    except Exception:
                        pass

    # Fallback: Tesseract word boxes grouped into lines.
    try:
        import pytesseract
        from pytesseract import Output
        _configure_pytesseract_binary(pytesseract)
        data = pytesseract.image_to_data(
            process_img,
            config="--psm 11 -c preserve_interword_spaces=1",
            lang="jpn+eng",
            output_type=Output.DICT,
        )
        groups = {}
        count = len(data.get("text", []))
        for i in range(count):
            text = str(data.get("text", [""])[i] or "").strip()
            if not text:
                continue
            try:
                conf = float(data.get("conf", [0])[i])
            except Exception:
                conf = 0.0
            if conf < 12:
                continue
            key = (
                data.get("block_num", [0] * count)[i],
                data.get("par_num", [0] * count)[i],
                data.get("line_num", [0] * count)[i],
            )
            left = float(data.get("left", [0] * count)[i])
            top = float(data.get("top", [0] * count)[i])
            width = float(data.get("width", [0] * count)[i])
            height = float(data.get("height", [0] * count)[i])
            group = groups.setdefault(key, {"tokens": [], "boxes": [], "scores": []})
            group["tokens"].append(text)
            group["boxes"].append((left, top, left + width, top + height))
            group["scores"].append(conf)

        regions = []
        inverse = 1.0 / process_scale if process_scale else 1.0
        for group in groups.values():
            if not group["tokens"]:
                continue
            line = _tighten_cjk_ocr_text(" ".join(group["tokens"]))
            x1 = min(box[0] for box in group["boxes"])
            y1 = min(box[1] for box in group["boxes"])
            x2 = max(box[2] for box in group["boxes"])
            y2 = max(box[3] for box in group["boxes"])
            poly = [
                (x1 * inverse, y1 * inverse),
                (x2 * inverse, y1 * inverse),
                (x2 * inverse, y2 * inverse),
                (x1 * inverse, y2 * inverse),
            ]
            regions.append({
                "text": line,
                "confidence": sum(group["scores"]) / max(1, len(group["scores"])),
                "polygon": poly,
                "bbox": _ocr_polygon_bbox(poly),
                "engine": "Tesseract",
            })
        regions.sort(key=lambda item: (item["bbox"][1], item["bbox"][0]))
        if regions:
            if log_fn:
                log_fn(f"[Manual OCR] {len(regions)} selectable region(s) detected with Tesseract.")
            return regions
        errors.append("Tesseract: no regions")
    except Exception as exc:
        errors.append(f"Tesseract: {exc}")
        if log_fn:
            log_fn(f"[Manual OCR] Tesseract region detection unavailable: {exc}")

    detail = " | ".join(errors[-3:])
    raise RuntimeError(
        "No OCR engine with selectable-region support is available. "
        "Install RapidOCR from Settings > Cover OCR, or install Tesseract + pytesseract."
        + (f"\n\nDetails: {detail}" if detail else "")
    )



class AlternateTitleMetadataBackend:
    """Search nhentai or HentaiEra and rank candidate covers locally.

    Neither site offers E/Ex's upload-a-cover lookup.  Candidate discovery uses
    the current title/folder name, then thumbnail similarity keeps the UI useful
    when several title matches are returned.
    """

    _search_cache = {}
    _search_cache_lock = threading.RLock()
    _search_cache_max = 120

    def __init__(self, source, query_text, log_fn=print):
        self.source = str(source or "").strip().lower()
        self.query_text = re.sub(r"\s+", " ", str(query_text or "")).strip()
        self.log = log_fn
        self.session = requests.Session()
        self.session.headers.update({
            "User-Agent": USER_AGENT,
            "Accept": "application/json,text/html,application/xhtml+xml,*/*;q=0.8",
            "Accept-Language": "en-US,en;q=0.7",
        })
        retry = Retry(
            total=2,
            connect=2,
            read=2,
            status=2,
            backoff_factor=0.35,
            status_forcelist=(429, 500, 502, 503, 504),
            allowed_methods=frozenset({"GET", "HEAD"}),
            raise_on_status=False,
        )
        adapter = HTTPAdapter(pool_connections=6, pool_maxsize=12, max_retries=retry)
        self.session.mount("https://", adapter)
        self._metadata_by_url = {}

    @staticmethod
    def _image_signature(path_or_bytes):
        try:
            source = io.BytesIO(path_or_bytes) if isinstance(path_or_bytes, (bytes, bytearray)) else path_or_bytes
            with Image.open(source) as opened:
                image = ImageOps.exif_transpose(opened).convert("L")
                image.thumbnail((64, 64), LANCZOS_FILTER)
                canvas = Image.new("L", (64, 64), 255)
                canvas.paste(image, ((64 - image.width) // 2, (64 - image.height) // 2))
                return canvas.tobytes()
        except Exception:
            return b""

    @staticmethod
    def _similarity(left, right):
        if not left or not right:
            return 0.0
        count = min(len(left), len(right))
        delta = sum(abs(left[index] - right[index]) for index in range(count))
        return max(0.0, 100.0 * (1.0 - delta / (255.0 * max(1, count))))

    def _query_variants(self):
        values = []

        def add(value):
            clean = re.sub(r"\s+", " ", str(value or "")).strip(" -_|,")
            if clean and clean.casefold() not in {item.casefold() for item in values}:
                values.append(clean)

        add(self.query_text)
        for bracketed in re.findall(r"\[([^\]]+)\]", self.query_text):
            bracketed = re.sub(r"[()]", " ", bracketed)
            if not re.search(r"^(english|japanese|chinese|translated|digital)$", bracketed.strip(), re.I):
                add(bracketed)
        stripped = re.sub(r"\[[^\]]+\]|\([^)]*\)", " ", self.query_text)
        add(stripped)
        tokens = re.findall(r"[A-Za-z0-9][A-Za-z0-9'_-]{4,}|[\u3040-\u30ff\u3400-\u9fff]{2,}", stripped)
        if tokens:
            token = max(tokens, key=len)
            add(re.sub(r"(?<=[a-z])(?=[A-Z])", " ", token))
        return values[:4]

    def _nhentai_search(self, query):
        response = self.session.get(
            "https://nhentai.net/api/v2/search",
            params={"query": query, "sort": "date", "page": 1},
            headers={"Referer": "https://nhentai.net/"},
            timeout=30,
        )
        response.raise_for_status()
        body = response.json()
        rows = body.get("result", []) if isinstance(body, dict) else []
        results = []
        for row in rows[:25]:
            gallery_id = row.get("id")
            if not gallery_id:
                continue
            gallery_url = f"https://nhentai.net/g/{gallery_id}/"
            title_en = re.sub(r"\s+", " ", str(row.get("english_title") or "")).strip()
            title_jp = re.sub(r"\s+", " ", str(row.get("japanese_title") or "")).strip()
            thumb_path = str(row.get("thumbnail") or "").lstrip("/")
            thumb = f"https://t1.nhentai.net/{thumb_path}" if thumb_path else ""
            self._metadata_by_url[gallery_url] = {
                "english": [title_en] if title_en else [],
                "japanese": [title_jp] if title_jp else [],
                "url": gallery_url,
            }
            results.append({
                "title": title_en or title_jp or f"nhentai #{gallery_id}",
                "url": gallery_url,
                "thumb": thumb,
                "thumb_path": thumb_path,
                "similarity": 0.0,
            })
        return results

    def _hentaiera_search(self, query):
        response = self.session.get(
            "https://hentaiera.com/search/",
            params={"key": query},
            headers={"Referer": "https://hentaiera.com/"},
            timeout=30,
        )
        response.raise_for_status()
        soup = BeautifulSoup(response.text, "html.parser")
        by_url = {}
        for link in soup.select("a[href*='/gallery/']"):
            href = urljoin(response.url, link.get("href", "")).split("?", 1)[0]
            if not re.search(r"hentaiera\.com/gallery/\d+/?$", href, re.I):
                continue
            entry = by_url.setdefault(href, {"title": "", "url": href, "thumb": "", "similarity": 0.0})
            image = link.select_one("img")
            if image is not None:
                src = image.get("data-src") or image.get("src") or ""
                if src:
                    entry["thumb"] = urljoin(response.url, src)
                alt = re.sub(r"\s+", " ", str(image.get("alt") or "")).strip()
                if alt and not entry["title"]:
                    entry["title"] = alt
            text = re.sub(r"\s+", " ", link.get_text(" ", strip=True)).strip()
            if text and len(text) > len(entry["title"]):
                entry["title"] = text
        return [item for item in by_url.values() if item["title"]][:25]

    def _doujinrepublic_search(self, query):
        """Search DoujinRepublic product listings by title text.

        Product pages look like ``/product/product_page_2000858521.html``.
        The public search form is ``/product/text_search.html``; parameter
        names vary, so a few common keys are tried until one returns products.
        """
        last_error = None
        response = None
        soup = None
        for params in (
            {"q": query},
            {"keyword": query},
            {"search_word": query},
            {"word": query},
        ):
            try:
                response = self.session.get(
                    "https://doujinrepublic.com/product/text_search.html",
                    params=params,
                    headers={"Referer": "https://doujinrepublic.com/"},
                    timeout=30,
                )
                if response.status_code == 404 or (
                    len(response.text or "") < 1500
                    and re.search(r"404 not found", response.text or "", re.I)
                ):
                    last_error = requests.HTTPError(
                        f"404 for {response.url}",
                        response=response,
                    )
                    break
                response.raise_for_status()
                soup = BeautifulSoup(response.text, "html.parser")
                break
            except Exception as exc:
                last_error = exc
                continue
        if soup is None or response is None:
            try:
                search_url = (
                    "https://doujinrepublic.com/product/text_search.html"
                    f"?q={quote(query)}"
                )
                html = _chromium_dump_html(search_url, log_fn=self.log)
                soup = BeautifulSoup(html, "html.parser")

                class _DrResp:
                    url = search_url

                response = _DrResp()
            except Exception as exc:
                raise RuntimeError(
                    f"DoujinRepublic search failed: {last_error or exc}"
                ) from (last_error or exc)

        by_url = {}
        for link in soup.select("a[href*='/product/product_page_']"):
            href = urljoin(response.url, link.get("href", "")).split("?", 1)[0]
            if not re.search(r"/product/product_page_\d+\.html$", href, re.I):
                continue
            entry = by_url.setdefault(
                href,
                {"title": "", "url": href, "thumb": "", "similarity": 0.0},
            )
            image = link.select_one("img")
            if image is not None:
                src = image.get("data-src") or image.get("src") or ""
                if src and not str(src).startswith("data:"):
                    entry["thumb"] = urljoin(response.url, src)
                alt = re.sub(r"\s+", " ", str(image.get("alt") or "")).strip()
                if alt and not entry["title"]:
                    entry["title"] = alt
            text = re.sub(r"\s+", " ", link.get_text(" ", strip=True)).strip()
            if text and len(text) > len(entry["title"]):
                entry["title"] = text
            aria = re.sub(
                r"(?i)^see item:\s*",
                "",
                re.sub(r"\s+", " ", str(link.get("aria-label") or "")).strip(),
            ).strip()
            if aria and len(aria) > len(entry["title"]):
                entry["title"] = aria
        for node in soup.select("[data-title-default]"):
            title = re.sub(r"\s+", " ", str(node.get("data-title-default") or "")).strip()
            if not title:
                continue
            parent = node.find_parent("a", href=True)
            href = ""
            if parent is not None:
                href = urljoin(response.url, parent.get("href", "")).split("?", 1)[0]
            if not re.search(r"/product/product_page_\d+\.html$", href, re.I):
                sibling = None
                if node.parent is not None:
                    sibling = node.parent.select_one("a[href*='/product/product_page_']")
                if sibling is not None:
                    href = urljoin(response.url, sibling.get("href", "")).split("?", 1)[0]
            if not re.search(r"/product/product_page_\d+\.html$", href, re.I):
                continue
            entry = by_url.setdefault(
                href,
                {"title": "", "url": href, "thumb": "", "similarity": 0.0},
            )
            if len(title) > len(entry["title"]):
                entry["title"] = title
        return [item for item in by_url.values() if item["title"]][:25]


    def _ensure_melonbooks_adult(self):
        """Auto-accept Melonbooks age gate via AUTH_ADULT cookie."""
        try:
            self.session.cookies.set("AUTH_ADULT", "1", domain=".melonbooks.co.jp", path="/")
            self.session.cookies.set("AUTH_ADULT", "1", domain="www.melonbooks.co.jp", path="/")
        except Exception:
            pass
        try:
            self.session.get(
                "https://www.melonbooks.co.jp/",
                headers={"Referer": "https://www.melonbooks.co.jp/"},
                timeout=20,
                allow_redirects=True,
            )
        except Exception as exc:
            self.log(f"[Melonbooks] Adult cookie warm-up skipped: {exc}")

    def _melonbooks_search(self, query):
        """Search melonbooks.co.jp product listings by title text."""
        self._ensure_melonbooks_adult()
        query = re.sub(r"\s+", " ", str(query or "")).strip()
        if not query:
            return []
        search_url = (
            "https://www.melonbooks.co.jp/search/search.php"
            f"?name={quote(query)}&text_type=all"
        )
        response = self.session.get(
            search_url,
            headers={
                "Referer": "https://www.melonbooks.co.jp/",
                "Accept": "text/html,application/xhtml+xml,application/xml;q=0.9,*/*;q=0.8",
            },
            timeout=30,
            allow_redirects=True,
        )
        response.raise_for_status()
        html = response.text or ""
        if "AUTH_ADULT" in html.upper() and "成年" in html and "confirm" in html.lower():
            self._ensure_melonbooks_adult()
            response = self.session.get(
                search_url,
                headers={"Referer": "https://www.melonbooks.co.jp/"},
                timeout=30,
                allow_redirects=True,
            )
            response.raise_for_status()
            html = response.text or ""
        soup = BeautifulSoup(html, "html.parser")
        by_url = {}
        for a in soup.select("a[href*='product_id='], a[href*='/detail/detail.php']"):
            href = (a.get("href") or "").strip()
            if not href:
                continue
            href = urljoin(response.url, href.split("#", 1)[0])
            if "product_id=" not in href and "/detail/detail.php" not in href:
                continue
            href = href.split("&", 1)[0] if "product_id=" in href else href
            title = a.get_text(" ", strip=True)
            if not title:
                parent = a.find_parent(["div", "li", "td", "tr"])
                if parent is not None:
                    title_node = parent.select_one(".title, .product-title, h2, h3, p")
                    if title_node is not None:
                        title = title_node.get_text(" ", strip=True)
            title = re.sub(r"\s+", " ", str(title or "")).strip()
            if not title or len(title) < 2:
                continue
            low = title.lower()
            if low in {"詳細", "detail", "カート", "cart", "buy"}:
                continue
            thumb = ""
            node = a
            for _ in range(6):
                if node is None:
                    break
                img = node.select_one("img") if hasattr(node, "select_one") else None
                if img is not None:
                    src = (img.get("data-src") or img.get("src") or "").strip()
                    if src and not src.startswith("data:"):
                        thumb = urljoin(response.url, src)
                        break
                node = getattr(node, "parent", None)
            entry = by_url.setdefault(
                href,
                {"title": "", "url": href, "thumb": "", "similarity": 0.0},
            )
            if len(title) > len(entry["title"]):
                entry["title"] = title
            if thumb and not entry["thumb"]:
                entry["thumb"] = thumb
        results = [item for item in by_url.values() if item["title"]][:25]
        self.log(f"[Melonbooks] {len(results)} product candidate(s) for: {query}")
        return results

    def search_text_matches(self, query):
        """Run a single text search and return raw candidate matches.

        Unlike ``search_gallery_matches_by_image`` this ignores the
        constructor's ``query_text`` and performs no thumbnail scoring, so it
        can be reused for arbitrary OCR-derived queries.
        """
        query = re.sub(r"\s+", " ", str(query or "")).strip()
        if not query:
            return []
        if self.source == "nhentai":
            return self._nhentai_search(query)
        if self.source == "hentaiera":
            return self._hentaiera_search(query)
        if self.source == "doujinrepublic":
            return self._doujinrepublic_search(query)
        if self.source in {"melonbooks", "melon books"}:
            return self._melonbooks_search(query)
        raise ValueError(f"Unsupported metadata source: {self.source}")

    def _thumbnail_score(self, item, target_signature):
        urls = []
        if self.source == "nhentai" and item.get("thumb_path"):
            urls.extend(
                f"https://t{index}.nhentai.net/{item['thumb_path']}"
                for index in range(1, 5)
            )
        elif item.get("thumb"):
            urls.append(item["thumb"])
        for url in urls:
            try:
                response = self.session.get(url, headers={"Referer": item["url"]}, timeout=12)
                response.raise_for_status()
                signature = self._image_signature(response.content)
                if signature:
                    return self._similarity(target_signature, signature)
            except Exception:
                continue
        return 0.0

    def search_gallery_matches_by_image(self, image_path, max_pages=1):
        if not image_path or not os.path.isfile(image_path):
            raise ValueError("No cover image path was provided.")
        if not self.query_text:
            raise ValueError("Enter a title or use a named gallery folder before searching this source.")
        digest = hashlib.sha1()
        with open(image_path, "rb") as handle:
            for chunk in iter(lambda: handle.read(1024 * 1024), b""):
                digest.update(chunk)
        cache_key = (self.source, self.query_text.casefold(), digest.hexdigest())
        with self._search_cache_lock:
            cached = self._search_cache.get(cache_key)
            if isinstance(cached, dict):
                self._metadata_by_url.update(cached.get("metadata", {}))
                return [dict(item) for item in cached.get("matches", [])]

        matches = []
        last_error = None
        for query in self._query_variants():
            try:
                self.log(f"[{self.source}] Searching title candidates for: {query}")
                if self.source == "nhentai":
                    matches = self._nhentai_search(query)
                elif self.source == "hentaiera":
                    matches = self._hentaiera_search(query)
                elif self.source == "doujinrepublic":
                    matches = self._doujinrepublic_search(query)
                elif self.source in {"melonbooks", "melon books"}:
                    matches = self._melonbooks_search(query)
                else:
                    raise ValueError(f"Unsupported metadata source: {self.source}")
                if matches:
                    break
            except Exception as exc:
                last_error = exc
                self.log(f"[{self.source}] Candidate search failed: {exc}")
        if not matches and last_error is not None:
            raise RuntimeError(f"{self.source} search failed: {last_error}") from last_error

        target = self._image_signature(image_path)
        candidates_to_score = matches[:16]
        if target and candidates_to_score:
            with ThreadPoolExecutor(max_workers=min(6, len(candidates_to_score))) as pool:
                scores = list(pool.map(lambda item: self._thumbnail_score(item, target), candidates_to_score))
            for item, score in zip(candidates_to_score, scores):
                item["similarity"] = round(score, 2)
        matches.sort(key=lambda item: float(item.get("similarity") or 0.0), reverse=True)
        high_conf = [
            item for item in matches
            if float(item.get("similarity") or 0.0) >= MIN_COVER_SIMILARITY
        ]
        if matches and not high_conf:
            best = float(matches[0].get("similarity") or 0.0)
            self.log(
                f"[{self.source}] Discarded {len(matches)} low-confidence match(es); "
                f"best score was {best:.1f}% (need >= {MIN_COVER_SIMILARITY:.0f}%)."
            )
        matches = high_conf
        result = matches[:25]
        if result:
            with self._search_cache_lock:
                _bounded_cache_set(
                    self._search_cache,
                    cache_key,
                    {
                        "matches": [dict(item) for item in result],
                        "metadata": dict(self._metadata_by_url),
                    },
                    self._search_cache_max,
                )
        return result

    @staticmethod
    def _split_shop_titles(full_title):
        full_title = re.sub(r"\s+", " ", str(full_title or "")).strip()
        if not full_title:
            return "", ""
        jp_parts = [
            part.strip()
            for part in re.split(r"\s*[|/]\s*", full_title)
            if re.search(r"[\u3040-\u30ff\u3400-\u9fff]", part)
        ]
        title_jp = " | ".join(jp_parts)
        paren = re.search(r"\(([^)]*[A-Za-z][^)]*)\)\s*$", full_title)
        if paren and not re.search(r"[\u3040-\u30ff\u3400-\u9fff]", paren.group(1)):
            return paren.group(1).strip(), re.sub(r"\([^)]*\)\s*$", "", full_title).strip() or title_jp
        if not re.search(r"[\u3040-\u30ff\u3400-\u9fff]", full_title):
            return full_title, title_jp
        return full_title, title_jp or full_title

    def fetch_gallery_title_metadata(self, gallery_url):
        cached = self._metadata_by_url.get(gallery_url)
        if isinstance(cached, dict):
            return {key: list(value) if isinstance(value, list) else value for key, value in cached.items()}

        if self.source == "nhentai":
            match = re.search(r"/g/(\d+)", gallery_url)
            if not match:
                raise ValueError("Invalid nhentai gallery URL.")
            response = self.session.get(
                f"https://nhentai.net/api/v2/galleries/{match.group(1)}",
                headers={"Referer": gallery_url},
                timeout=30,
            )
            response.raise_for_status()
            body = response.json()
            titles = body.get("title", {}) if isinstance(body, dict) else {}
            title_en = re.sub(r"\s+", " ", str(titles.get("english") or titles.get("pretty") or "")).strip()
            title_jp = re.sub(r"\s+", " ", str(titles.get("japanese") or "")).strip()
        elif self.source == "doujinrepublic" or "doujinrepublic.com" in str(gallery_url).lower():
            html = ""
            try:
                response = self.session.get(
                    gallery_url,
                    headers={"Referer": "https://doujinrepublic.com/"},
                    timeout=30,
                )
                html = response.text or ""
                if int(getattr(response, "status_code", 0) or 0) == 404 or (
                    len(html) < 1500 and re.search(r"404 not found", html, re.I)
                ):
                    html = ""
            except Exception as exc:
                self.log(f"[DoujinRepublic] Direct HTTP failed, using Chromium: {exc}")
                html = ""
            if not html:
                html = _chromium_dump_html(gallery_url, log_fn=self.log)
            soup = BeautifulSoup(html, "html.parser")
            heading = soup.select_one("#product_title, h1")
            full_title = re.sub(r"\s+", " ", heading.get_text(" ", strip=True) if heading else "").strip()
            table_title = ""
            for row in soup.select("tr"):
                cells = row.find_all(["th", "td"])
                if len(cells) < 2:
                    continue
                label = re.sub(r"\s+", " ", cells[0].get_text(" ", strip=True)).strip().casefold()
                if label in {"title", "タイトル"}:
                    table_title = re.sub(r"\s+", " ", cells[1].get_text(" ", strip=True)).strip()
                    break
            if not full_title:
                og = soup.select_one("meta[property='og:title']")
                if og is not None:
                    full_title = re.sub(r"\s+", " ", str(og.get("content") or "")).strip()
            if not full_title and soup.title:
                full_title = re.sub(
                    r"\s+[-|]\s+DoujinRepublic\s*$",
                    "",
                    soup.title.get_text(" ", strip=True),
                    flags=re.I,
                )
            title_en, title_jp = self._split_shop_titles(full_title)
            if table_title:
                title_jp = table_title
        elif self.source in {"melonbooks", "melon books"} or "melonbooks.co.jp" in str(gallery_url).lower():
            self._ensure_melonbooks_adult()
            response = self.session.get(
                gallery_url,
                headers={"Referer": "https://www.melonbooks.co.jp/"},
                timeout=30,
                allow_redirects=True,
            )
            response.raise_for_status()
            soup = BeautifulSoup(response.text or "", "html.parser")
            heading = (
                soup.select_one("h1.page-header")
                or soup.select_one("h1")
                or soup.select_one(".page-header")
                or soup.select_one("[itemprop='name']")
            )
            full_title = re.sub(r"\s+", " ", heading.get_text(" ", strip=True) if heading else "").strip()
            if not full_title and soup.title:
                full_title = re.sub(
                    r"\s*[-|]\s*メロンブックス.*$",
                    "",
                    soup.title.get_text(" ", strip=True),
                    flags=re.I,
                )
            title_en, title_jp = self._split_shop_titles(full_title)
            if not title_jp and re.search(r"[぀-ヿ㐀-鿿]", full_title):
                title_jp = full_title
        else:
            response = self.session.get(gallery_url, headers={"Referer": "https://hentaiera.com/"}, timeout=30)
            response.raise_for_status()
            soup = BeautifulSoup(response.text, "html.parser")
            heading = soup.select_one("h1")
            full_title = re.sub(r"\s+", " ", heading.get_text(" ", strip=True) if heading else "").strip()
            full_title = re.sub(r"^Report\s+", "", full_title, flags=re.I)
            if not full_title and soup.title:
                full_title = re.sub(r"\s+-\s+HentaiEra\s*$", "", soup.title.get_text(" ", strip=True), flags=re.I)
            title_en, title_jp = self._split_shop_titles(full_title)
        result = {
            "english": [title_en] if title_en else [],
            "japanese": [title_jp] if title_jp else [],
            "url": gallery_url,
        }
        self._metadata_by_url[gallery_url] = result
        return result


class OcrCoverTitleSearchBackend:
    """Search every metadata source by the text OCR reads from the cover.

    This is the Google-Translate-image style flow: instead of uploading the
    cover for a reverse image search, the cover's visible words are extracted
    locally and each site (E-Hentai/ExHentai, nhentai, HentaiEra) is searched
    by text. Candidate covers are still downloaded and ranked against the
    local cover so the picker stays visually ordered.
    """

    _ocr_search_cache = {}
    _ocr_search_cache_lock = threading.RLock()
    _ocr_search_cache_max = 60

    def __init__(self, ehentai_backend, ocr_fn, log_fn=print):
        if not callable(ocr_fn):
            raise ValueError("An OCR callback (ocr_fn) is required.")
        self.ehentai = ehentai_backend
        self.ocr_fn = ocr_fn
        self.log = log_fn
        self._alt_backends = {
            "nhentai": AlternateTitleMetadataBackend("nhentai", "", log_fn=log_fn),
            "hentaiera": AlternateTitleMetadataBackend("hentaiera", "", log_fn=log_fn),
            "doujinrepublic": AlternateTitleMetadataBackend("doujinrepublic", "", log_fn=log_fn),
            "melonbooks": AlternateTitleMetadataBackend("melonbooks", "", log_fn=log_fn),
        }

    @staticmethod
    def _query_variants(jp_words, en_words, limit=None):
        """Build search queries from every OCR fragment on the cover.

        The full Japanese and English strings are tried first, then each
        extracted word so every token is searched.
        """
        variants = []

        def add(value):
            clean = re.sub(r"\s+", " ", str(value or "")).strip(" -_|,")
            if len(clean) < 2:
                return
            if clean.casefold() not in {item.casefold() for item in variants}:
                variants.append(clean)

        jp = [str(word).strip() for word in jp_words or [] if str(word or "").strip()]
        en = [str(word).strip() for word in en_words or [] if str(word or "").strip()]
        if jp:
            add(" ".join(jp))
        if en:
            add(" ".join(en))
        for word in jp + en:
            add(word)
        if limit:
            return variants[: int(limit)]
        return variants

    def _search_ehentai_text_matches(self, query, max_pages=1):
        list_fn = getattr(self.ehentai, "search_gallery_matches_by_text_list", None)
        if callable(list_fn):
            try:
                rows = list_fn(query, max_pages=max_pages) or []
                return [dict(item) for item in rows if isinstance(item, dict)]
            except Exception as exc:
                self.log(f"[OCR Search] E/Ex list search failed: {exc}")

        single_fn = getattr(self.ehentai, "_search_gallery_matches_by_text", None)
        if callable(single_fn):
            one = single_fn(query, max_pages=max_pages)
            if isinstance(one, dict) and one.get("url"):
                return [
                    {
                        "title": one.get("title_en") or one.get("title_jp") or one.get("url", ""),
                        "url": one.get("url", ""),
                        "similarity": float(one.get("similarity") or 0.0),
                        "thumb": one.get("thumb", ""),
                    }
                ]
        return []

    def _search_alt_text_matches(self, backend, source_key, query):
        direct_fn = getattr(backend, "search_text_matches", None)
        if callable(direct_fn):
            try:
                rows = direct_fn(query) or []
                return [dict(item) for item in rows if isinstance(item, dict)]
            except Exception:
                pass

        if source_key == "nhentai":
            return backend._nhentai_search(query)
        if source_key == "hentaiera":
            return backend._hentaiera_search(query)
        if source_key == "doujinrepublic":
            return backend._doujinrepublic_search(query)
        if source_key == "melonbooks":
            return backend._melonbooks_search(query)
        return []

    def _thumbnail_score(self, item, target_signature):
        if not target_signature:
            return 0.0
        urls = []
        session = self.ehentai.session
        if item.get("thumb_path"):
            urls.extend(
                f"https://t{index}.nhentai.net/{item['thumb_path']}"
                for index in range(1, 5)
            )
            session = self._alt_backends["nhentai"].session
        elif item.get("thumb"):
            urls.append(item["thumb"])
            if "hentaiera.com" in str(item.get("url", "")).lower():
                session = self._alt_backends["hentaiera"].session
            elif "doujinrepublic.com" in str(item.get("url", "")).lower():
                session = self._alt_backends["doujinrepublic"].session
            elif "melonbooks.co.jp" in str(item.get("url", "")).lower():
                session = self._alt_backends["melonbooks"].session
        for url in urls:
            try:
                response = session.get(
                    url,
                    headers={"Referer": item.get("url") or "https://e-hentai.org/"},
                    timeout=12,
                )
                response.raise_for_status()
                signature = AlternateTitleMetadataBackend._image_signature(response.content)
                if signature:
                    return AlternateTitleMetadataBackend._similarity(target_signature, signature)
            except Exception:
                continue
        return 0.0

    def search_gallery_matches_by_image(self, image_path, max_pages=1):
        if not image_path or not os.path.isfile(image_path):
            raise ValueError("No cover image path was provided.")

        jp_words, en_words = self.ocr_fn(image_path)
        queries = self._query_variants(jp_words, en_words)
        if not queries:
            raise RuntimeError("OCR did not find any readable title text on that cover.")
        self.log(
            f"[OCR Search] {len(jp_words)} JP / {len(en_words)} EN OCR words, "
            f"{len(queries)} search queries: {' | '.join(queries)}"
        )

        digest = hashlib.sha1()
        with open(image_path, "rb") as handle:
            for chunk in iter(lambda: handle.read(1024 * 1024), b""):
                digest.update(chunk)
        cache_key = (
            bool(getattr(self.ehentai, "use_ex", False)),
            digest.hexdigest(),
            "all-words",
        )
        with self._ocr_search_cache_lock:
            cached = self._ocr_search_cache.get(cache_key)
            if isinstance(cached, list):
                self.log("[OCR Search] Reusing cached multi-source results.")
                return [dict(item) for item in cached]

        matches = []
        seen_urls = set()

        def absorb(items, source_label):
            for item in items or []:
                url = str(item.get("url") or "").strip()
                if not url or url in seen_urls:
                    continue
                seen_urls.add(url)
                entry = dict(item)
                entry["source"] = source_label
                matches.append(entry)

        for query in queries:
            try:
                self.log(f"[OCR Search] E-Hentai/ExHentai text search: {query}")
                found = self._search_ehentai_text_matches(query, max_pages=max_pages)
            except Exception as exc:
                self.log(f"[OCR Search] E/Ex search failed for {query!r}: {exc}")
                found = []
            if found:
                absorb(found, "E-Hentai / ExHentai")

        for source_key, source_label in (
            ("nhentai", "nhentai"),
            ("hentaiera", "HentaiEra"),
            ("doujinrepublic", "DoujinRepublic"),
            ("melonbooks", "Melonbooks"),
        ):
            backend = self._alt_backends[source_key]
            for query in queries:
                try:
                    self.log(f"[OCR Search] {source_label} text search: {query}")
                    found = self._search_alt_text_matches(backend, source_key, query)
                except Exception as exc:
                    self.log(f"[OCR Search] {source_label} search failed for {query!r}: {exc}")
                    found = []
                if found:
                    absorb(found, source_label)

        if not matches:
            raise RuntimeError(
                "No gallery on E/Ex, nhentai, HentaiEra, DoujinRepublic or Melonbooks matched the cover text. Tried: "
                + "; ".join(queries)
            )

        target_signature = AlternateTitleMetadataBackend._image_signature(image_path)
        candidates_to_score = matches[:80]
        if target_signature and candidates_to_score:
            with ThreadPoolExecutor(max_workers=min(8, len(candidates_to_score))) as pool:
                scores = list(pool.map(lambda item: self._thumbnail_score(item, target_signature), candidates_to_score))
            for item, score in zip(candidates_to_score, scores):
                item["similarity"] = round(score, 2)

        matches.sort(key=lambda item: float(item.get("similarity") or 0.0), reverse=True)
        high_conf = [
            item for item in matches
            if float(item.get("similarity") or 0.0) >= MIN_COVER_SIMILARITY
        ]
        if matches and not high_conf:
            best = float(matches[0].get("similarity") or 0.0)
            self.log(
                f"[OCR Search] Discarded {len(matches)} low-confidence match(es); "
                f"best score was {best:.1f}% (need >= {MIN_COVER_SIMILARITY:.0f}%)."
            )
        matches = high_conf
        result = matches[:40]
        with self._ocr_search_cache_lock:
            _bounded_cache_set(
                self._ocr_search_cache,
                cache_key,
                [dict(item) for item in result],
                self._ocr_search_cache_max,
            )
        return result

    def fetch_gallery_title_metadata(self, gallery_url):
        low = str(gallery_url or "").lower()
        if "nhentai.net" in low:
            return self._alt_backends["nhentai"].fetch_gallery_title_metadata(gallery_url)
        if "hentaiera.com" in low:
            return self._alt_backends["hentaiera"].fetch_gallery_title_metadata(gallery_url)
        if "doujinrepublic.com" in low:
            return self._alt_backends["doujinrepublic"].fetch_gallery_title_metadata(gallery_url)
        if "melonbooks.co.jp" in low:
            return self._alt_backends["melonbooks"].fetch_gallery_title_metadata(gallery_url)
        return self.ehentai.fetch_gallery_title_metadata(gallery_url)


# ==============================================================================
# GUI APPLICATION
# ==============================================================================
BaseAppClass = ctk.CTk

if HAS_DND:

    class CTkWithDnD(ctk.CTk, TkinterDnD.DnDWrapper):
        def __init__(self, *args, **kwargs):
            super().__init__(*args, **kwargs)
            self._dnd_error = None
            try:
                self.TkdndVersion = TkinterDnD._require(self)
                self._dnd_available = True
            except Exception as exc:
                self._dnd_available = False
                self._dnd_error = f"Could not load tkinterdnd2: {exc}"

    BaseAppClass = CTkWithDnD


class EHentaiUploaderApp(BaseAppClass):
    def __init__(self):
        super().__init__()
        if not hasattr(self, "_dnd_available"):
            self._dnd_available = False
            self._dnd_error = f"tkinterdnd2 is unavailable: {DND_IMPORT_ERROR}"

        # Prefer the requested Aller face for editable fields.  The distributed
        # app does not bundle the commercial font; an installed Allerta or
        # Segoe UI is used until Aller is installed on the machine.
        try:
            available_fonts = {name.lower(): name for name in tkfont.families(self)}
        except Exception:
            available_fonts = {}
        self.input_font_family = available_fonts.get(
            "aller",
            available_fonts.get("allerta", "Segoe UI"),
        )
        self.input_font = (self.input_font_family, 13)
        self.small_input_font = (self.input_font_family, 11)
        try:
            ctk.ThemeManager.theme["CTkFont"]["family"] = self.input_font_family
        except Exception:
            pass

        # i18n state (set before any widget is built so tr() works at build).
        self.lang_code = "en"
        self._i18n_widgets = []
        self._tab_labels = {}

        # Debug toggle (Feature 3). Default ON; gated in self.log().
        self.debug_enabled = tk.BooleanVar(value=True)

        # Faster-upload speed settings (Feature 2). Bound to spinboxes later.
        self.batch_size_var = tk.IntVar(value=UPLOAD_MAX_REQUEST_FILES)
        self.workers_var = tk.IntVar(value=UPLOAD_MAX_WORKERS)
        self.delay_var = tk.DoubleVar(value=0.5)

        self.title(f"{self.tr('app_title')}  [{UI_BUILD_ID}]")

        icon_path = create_eh_app_icon()
        if icon_path:
            try:
                self.iconbitmap(icon_path)
            except Exception:
                pass

        try:
            self.geometry(f"{DESKTOP_WINDOW_WIDTH}x{DESKTOP_WINDOW_HEIGHT}")
            self.minsize(1360, 760)
            self.resizable(True, True)
            self.state("zoomed")
        except Exception:
            self.geometry(f"{DESKTOP_WINDOW_WIDTH}x{DESKTOP_WINDOW_HEIGHT}")

        try:
            self.update_idletasks()
            self.wm_attributes("-fullscreen", False)
        except Exception:
            pass

        self.log_queue = queue.Queue()
        self.after(
            100,
            self._poll_log_queue,
        )

        self.batch_queue_items = {}
        self._queue_state_lock = threading.RLock()
        self._cache_lock = threading.RLock()
        self._cache_save_timer = None
        self.current_preview_image = None
        self.current_preview_path = None
        self.batch_preview_path = None
        self.single_preview_path = None
        self._cover_hover_window = None
        self._cover_hover_image = None
        self._cover_hover_after_id = None
        self._header_redrawers = []
        self._main_split_drag_start = None
        self._right_split_drag_start = None
        self._thumbnail_cache = {}
        self._preview_pil_cache = {}
        self._row_status_cache = {}
        self._last_batch_preview_key = None
        self._batch_preview_after_id = None
        self._last_preview_render = {}
        self._last_queue_save_ts = 0.0
        self._browser_unavailable_logged = False
        self._title_cache = {"translations": {}, "cover_metadata": {}}
        self._cache_path = (APP_DIR / "eh_uploader_cache.json")
        self._ocr_install_prompted = False
        self._ocr_install_in_progress = False
        self._load_startup_cache()
        self._log_expanded = True
        self._ui_theme = "dark"
        self._box_style = "balanced"
        self._box_style_after_id = None
        self._hotkeys_enabled = True
        self.translation_settings = {
            "lingva_mirror": "https://lingva.ml",
            "mymemory_email": "",
            "gemini_api_key": "",
            "sudachi_dictionary": "core",
            "sudachi_split_mode": "B",
            "mecab_dictionary": "auto",
        }
        self.open_automation_result_in_app_var = tk.BooleanVar(value=False)
        self.metadata_source_var = tk.StringVar(value=METADATA_SOURCES[0])
        self.is_processing = False
        self.batch_pause_all_event = threading.Event()
        self.batch_pause_all_event.set()
        self.batch_pause_flags = {}
        self.batch_pause_events = {}

        self.grid_columnconfigure(0, weight=1)
        self.grid_columnconfigure(1, weight=0)
        self.grid_rowconfigure(0, weight=0)
        self.grid_rowconfigure(1, weight=0)
        self.grid_rowconfigure(2, weight=1)

        self._build_menu_bar()
        self._build_context_menu()
        self._configure_treeview_style()
        self._build_credentials_frame()
        self._build_resizable_layout()
        self._build_tab_view()
        self._build_browser_sidebar()
        self._build_log_frame()
        if not self._dnd_available:
            self.log(f"[Drag & drop] {self._dnd_error}. Python: {sys.executable}")
        self._bind_global_hotkeys()

        self._load_config()
        self._load_persistent_queue()
        # Re-render all translated text now that config may have changed the
        # language and debug flag.
        self._set_language(self.lang_code)
        self._theme_var.set(self._ui_theme)
        self._apply_ui_theme()
        if self.input_font_family.lower() != "aller":
            self.log(
                f"[Font] Aller is not installed; using {self.input_font_family}. "
                "Install Aller and restart to use it automatically."
            )

        try:
            self._bind_responsive_layout()
        except Exception:
            pass
        self.protocol(
            "WM_DELETE_WINDOW",
            self._on_closing,
        )

    # ------------------------------------------------------------------
    # Embedded browser sidebar
    # ------------------------------------------------------------------
    def _build_resizable_layout(self):
        self.app_body = ctk.CTkFrame(self, fg_color='#0a0a0a', corner_radius=0)
        self.app_body.grid(row=2, column=0, columnspan=2, sticky='nsew')
        self.app_body.grid_rowconfigure(0, weight=1)
        self.app_body.grid_columnconfigure(0, weight=1)
        self.main_horizontal_pane = tk.PanedWindow(self.app_body, orient='horizontal',
            sashwidth=7, sashpad=0, bd=0, relief='flat', bg='#665632', opaqueresize=True)
        self.main_horizontal_pane.grid(row=0, column=0, sticky='nsew')
        self.left_pane_frame = ctk.CTkFrame(self.main_horizontal_pane, fg_color='#090909', corner_radius=0)
        self.left_pane_frame.grid_rowconfigure(0, weight=1)
        self.left_pane_frame.grid_columnconfigure(0, weight=1)
        self.right_pane_frame = ctk.CTkFrame(self.main_horizontal_pane, width=520, fg_color='#11110f', corner_radius=0)
        self.right_pane_frame.grid_rowconfigure(0, weight=1)
        self.right_pane_frame.grid_columnconfigure(0, weight=1)
        self.main_horizontal_pane.add(self.left_pane_frame, minsize=720, stretch='always')
        self.main_horizontal_pane.add(self.right_pane_frame, minsize=360, width=520, stretch='never')
        self.main_vertical_pane = tk.PanedWindow(self.right_pane_frame, orient='vertical',
            sashwidth=7, sashpad=0, bd=0, relief='flat', bg='#665632', opaqueresize=True)
        self.main_vertical_pane.grid(row=0, column=0, sticky='nsew')
        self.inspector_slot = ctk.CTkFrame(self.main_vertical_pane, fg_color='#11110f', corner_radius=0)
        self.log_slot = ctk.CTkFrame(self.main_vertical_pane, fg_color='#11110f', corner_radius=0)
        for frame in (self.inspector_slot, self.log_slot):
            frame.grid_columnconfigure(0, weight=1)
            frame.grid_rowconfigure(0, weight=1)
            frame.grid_propagate(False)
        self.main_vertical_pane.add(self.inspector_slot, minsize=220, height=480, stretch='always')
        self.main_vertical_pane.add(self.log_slot, minsize=110, height=190, stretch='never')
        # Retain aliases for older styling code; native panes own pointer capture,
        # sash limits and drag geometry without an application Configure loop.
        self.main_split_grip = self.main_horizontal_pane
        self.right_split_grip = self.main_vertical_pane
        self.top_pane_frame = self.left_pane_frame
        self.bottom_pane_frame = self.log_slot
        self._sidebar_visible = False
        self._right_top_target = 480
        self.main_horizontal_pane.bind('<ButtonRelease-1>', self._remember_batch_inspector_sash, add='+')
        self.main_vertical_pane.bind('<ButtonRelease-1>', self._remember_batch_inspector_sash, add='+')

    def _begin_main_split_drag(self, event):
        self._main_split_drag_start = (int(event.x_root), int(self.right_pane_frame.winfo_width()))
        self.main_split_grip.grab_set()

    def _drag_main_split(self, event):
        if not self._main_split_drag_start:
            return
        start_x, start_width = self._main_split_drag_start
        total = max(1, int(self.app_body.winfo_width()))
        max_right = max(390, min(900, total - 766))
        self._pending_right_width = max(390, min(start_width - (int(event.x_root) - start_x), max_right))
        if getattr(self, '_split_frame_after', None) is None:
            self._split_frame_after = self.after(16, self._flush_split_geometry)

    def _end_main_split_drag(self, event=None):
        if self._main_split_drag_start is None:
            return
        if event is not None:
            self._drag_main_split(event)
        self._finish_split_drag(self.main_split_grip)
        self._main_split_drag_start = None

    def _begin_right_split_drag(self, event):
        self._right_split_drag_start = (int(event.y_root), int(self.right_split_grip.winfo_y()))
        self.right_split_grip.grab_set()

    def _drag_right_split(self, event):
        if self._right_split_drag_start is None or not getattr(self, '_log_expanded', True):
            return
        start_y, start_top = self._right_split_drag_start
        height = max(1, int(self.right_pane_frame.winfo_height()))
        maximum = max(280, height - 156)
        self._pending_right_top = max(280, min(start_top + int(event.y_root) - start_y, maximum))
        if getattr(self, '_split_frame_after', None) is None:
            self._split_frame_after = self.after(16, self._flush_split_geometry)

    def _end_right_split_drag(self, event=None):
        if self._right_split_drag_start is None:
            return
        if event is not None:
            self._drag_right_split(event)
        self._finish_split_drag(self.right_split_grip)
        self._right_split_drag_start = None

    def _reset_layout_sashes(self):
        self._apply_layout_state({'right_pane_width': 520, 'right_top_height': 480})
        self._save_config()

    def _initialize_batch_inspector_sash_once(self):
        # Construction already sets the default. Never overwrite restored geometry.
        return

    def _get_layout_state(self):
        state = {}
        try:
            state['right_pane_width'] = self.right_pane_frame.winfo_width()
            if str(self.inspector_slot) in tuple(map(str, self.main_vertical_pane.panes())):
                state['right_top_height'] = self.main_vertical_pane.sash_coord(0)[1]
            else:
                state['right_top_height'] = self._right_top_target
            state['queue_columns'] = list(self._batch_tree_visible_columns())
            state['queue_column_widths'] = {name: int(self.batch_tree.column(name, 'width'))
                                            for name in self.batch_tree.cget('columns')}
        except (AttributeError, tk.TclError):
            pass
        return state

    def _apply_layout_state(self, state):
        if not isinstance(state, dict):
            return
        try:
            columns = list(self.batch_tree.cget('columns'))
            order = state.get('queue_columns', [])
            if isinstance(order, list) and len(order) == len(columns) and set(order) == set(columns):
                self.batch_tree['displaycolumns'] = tuple(order)
            widths = state.get('queue_column_widths', {})
            if isinstance(widths, dict):
                for name, value in widths.items():
                    if name in columns and isinstance(value, (int, float)):
                        self.batch_tree.column(name, width=max(70, min(900, int(value))))
            width = state.get('right_pane_width', 520)
            top = state.get('right_top_height', 480)
            if isinstance(width, (int, float)):
                width = max(360, min(int(width), 900))
                total = self.main_horizontal_pane.winfo_width()
                self.main_horizontal_pane.sash_place(0, max(720, total - width - 7), 0)
            if isinstance(top, (int, float)):
                self._right_top_target = max(220, min(int(top), 900))
                if str(self.inspector_slot) in tuple(map(str, self.main_vertical_pane.panes())):
                    height = self.main_vertical_pane.winfo_height()
                    self.main_vertical_pane.sash_place(0, 0, max(220, min(self._right_top_target, height - 117)))
        except (AttributeError, tk.TclError):
            pass

    def _remember_batch_inspector_sash(self, event=None):
        if getattr(self, '_native_layout_save_after', None) is not None:
            self.after_cancel(self._native_layout_save_after)
        def save():
            self._native_layout_save_after = None
            self._save_config()
        self._native_layout_save_after = self.after(150, save)

    def _browser_default_url(self, tab_key):
        if tab_key == "image":
            return "https://www.google.com/imghp?hl=en&ogbl"
        if tab_key == "metadata":
            return "https://www.suruga-ya.jp/"
        return self._build_ehentai_search_url()

    def _browser_mode_text(self):
        if getattr(self, "_embedded_browser_enabled", False):
            return "Embedded mode active"
        if HAS_QT_CHROMIUM:
            return "Qt Chromium mode active"
        if HAS_PYWEBVIEW:
            return "WebView2 mode active"
        return "Fallback mode"

    def _browser_current_tab_key(self):
        if hasattr(self, "browser_tabview"):
            try:
                return self.browser_tabview.get() or "image"
            except Exception:
                pass
        if hasattr(self, "_browser_fallback_tab_var"):
            try:
                return self._browser_fallback_tab_var.get() or "image"
            except Exception:
                pass
        return "image"

    def _browser_set_mode_banner(self, detail=""):
        if not hasattr(self, "browser_mode_var"):
            return
        mode = self._browser_mode_text()
        suffix = f" | {detail}" if detail else ""
        self.browser_mode_var.set(f"Browser: {mode}{suffix}")

    def _browser_should_open_external(self, tab_key):
        # Never short-circuit the popup pipeline.  _browser_open_url will try
        # Qt Chromium, then WebView2, then an Edge app window, and only then the
        # normal system browser.
        return False

    def _browser_open_url(self, tab_key, url, title=None):
        if self._browser_should_open_external(tab_key):
            webbrowser.open(url)
            self._browser_set_mode_banner(f"{tab_key}: external")
            return False
        if self._open_qt_chromium_url(tab_key, url, title=title):
            self._browser_set_mode_banner(f"{tab_key}: Qt Chromium")
            self._browser_url_for_tab(tab_key, url)
            return True
        opened = self._open_embedded_browser(tab_key, url, title=title)
        if opened:
            self._browser_set_mode_banner(f"{tab_key}: embedded")
            return True
        if self._open_webview_url(url, title=title):
            self._browser_set_mode_banner(f"{tab_key}: WebView2 fallback")
            return True
        if self._open_edge_app_url(url):
            self._browser_set_mode_banner(f"{tab_key}: Edge app fallback")
            return True
        webbrowser.open(url)
        self._browser_set_mode_banner(f"{tab_key}: external fallback")
        return False

    def _open_qt_chromium_url(self, tab_key, url, title=None):
        # A frozen executable is not a Python interpreter for the -c child.
        if getattr(sys, "frozen", False) or not HAS_QT_CHROMIUM:
            return False
        if not hasattr(self, "_qt_browser_processes"):
            self._qt_browser_processes = {}

        old_proc = self._qt_browser_processes.get(tab_key)
        if old_proc is not None:
            try:
                if old_proc.poll() is None:
                    old_proc.terminate()
            except Exception:
                pass

        script = (
            "import sys\n"
            "from PySide6.QtWidgets import QApplication\n"
            "from PySide6.QtCore import QUrl\n"
            "from PySide6.QtWebEngineWidgets import QWebEngineView\n"
            "url = sys.argv[1]\n"
            "title = sys.argv[2] if len(sys.argv) > 2 else 'Qt Browser'\n"
            "app = QApplication(sys.argv)\n"
            "view = QWebEngineView()\n"
            "view.setWindowTitle(title)\n"
            "view.resize(1300, 900)\n"
            "view.load(QUrl(url))\n"
            "view.show()\n"
            "sys.exit(app.exec())\n"
        )

        try:
            proc = subprocess.Popen([sys.executable, "-c", script, str(url), str(title or "Uploader Browser")])
            self._qt_browser_processes[tab_key] = proc
            return True
        except Exception as exc:
            self.log(f"[Browser] Qt Chromium launch failed: {exc}")
            return False

    def _build_browser_unavailable_notice(self, parent, reason):
        detail = str(reason or "Unknown reason")
        try:
            tcl_ver = str(self.tk.call("info", "patchlevel"))
        except Exception:
            tcl_ver = "unknown"
        py_ver = sys.version.split()[0]
        text = (
            "Embedded browser unavailable\n"
            "Tkhtml runtime is missing or incompatible.\n"
            "Search actions will use WebView2/native fallback when available.\n\n"
            f"Runtime: Python {py_ver}, Tcl/Tk {tcl_ver}\n"
            "Tip: Install pywebview to use Edge WebView2 fallback on Python 3.14.\n\n"
            f"Reason: {detail[:220]}"
        )
        ctk.CTkLabel(
            parent,
            text=text,
            justify="center",
            text_color="gray",
            wraplength=300,
        ).pack(expand=True, padx=16, pady=24)

    def _ensure_tkhtml_loaded(self):
        global tkhtml_runtime
        if getattr(self, "_tkhtml_loaded", False):
            return True

        # Fast path: Tk already has a discoverable Tkhtml package.
        try:
            self.tk.call("package", "require", "Tkhtml")
            self._tkhtml_loaded = True
            self._tkhtml_load_note = "package"
            return True
        except Exception:
            pass

        if not HAS_TKHTML_RUNTIME:
            self._tkhtml_load_error = "tkinterweb_tkhtml is not installed in this interpreter"
            return False

        if tkhtml_runtime is None:
            try:
                tkhtml_runtime = importlib.import_module("tkinterweb_tkhtml")
            except Exception as exc:
                self._tkhtml_load_error = f"tkinterweb_tkhtml could not be imported: {exc}"
                return False

        # Fallback path: direct binary load (works when package index is not discoverable).
        try:
            tkhtml_file, version, _experimental = tkhtml_runtime.get_tkhtml_file()
            tkhtml_runtime.load_tkhtml_file(self, tkhtml_file)
            self._tkhtml_loaded = True
            self._tkhtml_load_note = f"dll:{version}"
            return True
        except Exception as exc:
            try:
                tcl_ver = str(self.tk.call("info", "patchlevel"))
            except Exception:
                tcl_ver = "unknown"
            py_ver = sys.version.split()[0]
            self._tkhtml_load_error = f"{type(exc).__name__}: {exc} (Python {py_ver}, Tcl/Tk {tcl_ver})"
            return False

    def _create_html_frame_safe(self, parent):
        global HtmlFrame
        if HtmlFrame is None and HAS_TKINTERWEB:
            try:
                HtmlFrame = importlib.import_module("tkinterweb").HtmlFrame
            except Exception as exc:
                if not self._browser_unavailable_logged:
                    self.log(f"[Browser] tkinterweb could not be imported: {exc}")
        try:
            if HtmlFrame is None:
                raise RuntimeError("tkinterweb is not installed")
            browser = HtmlFrame(parent, horizontal_scrollbar=True)
            return browser
        except Exception:
            pass

        try:
            if not self._ensure_tkhtml_loaded():
                raise RuntimeError(getattr(self, "_tkhtml_load_error", "Tkhtml could not be loaded"))
            browser = HtmlFrame(parent, horizontal_scrollbar=True)
            return browser
        except Exception as exc:
            if not self._browser_unavailable_logged:
                self.log(f"[Browser] Embedded browser disabled (Tkhtml unavailable/incompatible): {exc}")
                self._browser_unavailable_logged = True
            return None

    def _open_webview_url(self, url, title=None):
        global webview
        if not HAS_PYWEBVIEW:
            return False
        if webview is None:
            try:
                webview = importlib.import_module("webview")
            except Exception as exc:
                self.log(f"[Browser] pywebview could not be imported: {exc}")
                return False
        try:
            win_title = str(title or "Uploader Browser")

            def open_window():
                webview.create_window(win_title, url=url, width=1280, height=900)
                webview.start(gui="edgechromium")

            threading.Thread(target=open_window, daemon=True).start()
            return True
        except Exception as exc:
            self.log(f"[Browser] WebView2 fallback failed: {exc}")
            return False

    def _open_edge_app_url(self, url):
        edge_candidates = [
            shutil.which("msedge"),
            r"C:\Program Files (x86)\Microsoft\Edge\Application\msedge.exe",
            r"C:\Program Files\Microsoft\Edge\Application\msedge.exe",
        ]
        edge_exe = next((p for p in edge_candidates if p and os.path.exists(p)), "")
        if not edge_exe:
            return False
        try:
            subprocess.Popen([edge_exe, f"--app={url}"])
            return True
        except Exception as exc:
            self.log(f"[Browser] Edge app fallback failed: {exc}")
            return False

    def _build_webview_fallback_panel(self):
        panel = ctk.CTkFrame(self.browser_sidebar, fg_color="transparent")
        panel.pack(fill="both", expand=True, padx=12, pady=(6, 10))
        ctk.CTkLabel(
            panel,
            text="Qt Chromium browser mode. Select a tab and open the URL to load search results for that scope.",
            justify="left",
            text_color="gray",
            wraplength=320,
        ).pack(anchor="w", pady=(0, 10))

        self._browser_fallback_tab_var = tk.StringVar(value="image")
        row = ctk.CTkFrame(panel, fg_color="transparent")
        row.pack(fill="x", pady=(0, 8))
        ctk.CTkRadioButton(row, text="Image", variable=self._browser_fallback_tab_var, value="image").pack(side="left", padx=(0, 8))
        ctk.CTkRadioButton(row, text="Metadata", variable=self._browser_fallback_tab_var, value="metadata").pack(side="left", padx=(0, 8))
        ctk.CTkRadioButton(row, text="E/Ex", variable=self._browser_fallback_tab_var, value="ehentai").pack(side="left", padx=(0, 0))

        ctk.CTkButton(
            panel,
            text="Open Current Tab URL",
            command=lambda: self._browser_open_url(self._browser_current_tab_key(), self.browser_url_var.get().strip(), "Browser"),
        ).pack(anchor="e")

    def _can_relaunch_in_python_312(self):
        if getattr(sys, "frozen", False):
            return False
        if hasattr(self, "_py312_available"):
            return self._py312_available
        self._py312_available = False
        self._py312_exe = ""
        try:
            probe = subprocess.run(
                ["py", "-3.12", "-c", "import sys; print(sys.executable)"],
                capture_output=True,
                text=True,
                timeout=6,
            )
            if probe.returncode == 0:
                self._py312_available = True
                self._py312_exe = (probe.stdout or "").strip().splitlines()[-1].strip()
        except Exception:
            pass
        return self._py312_available

    def _relaunch_in_python_312(self):
        script_path = str(Path(__file__).resolve())
        cwd = str(Path(__file__).resolve().parent)
        try:
            subprocess.Popen(["py", "-3.12", script_path], cwd=cwd)
            self.log("[Browser] Relaunching app with Python 3.12 for embedded browser mode...")
            self.destroy()
        except Exception as exc:
            messagebox.showwarning(
                "Embedded Browser",
                f"Could not relaunch with Python 3.12:\n\n{exc}\n\nRun manually:\npy -3.12 \"{script_path}\"",
                parent=self,
            )

    def _maybe_add_browser_relaunch_button(self):
        if getattr(self, "_embedded_browser_enabled", False):
            return
        if hasattr(self, "browser_relaunch_btn") and self.browser_relaunch_btn is not None:
            return
        try:
            tcl_ver = str(self.tk.call("info", "patchlevel"))
        except Exception:
            tcl_ver = ""
        if not tcl_ver.startswith("9"):
            return
        if not self._can_relaunch_in_python_312():
            return
        if not hasattr(self, "browser_mode_row"):
            return

        label = "Relaunch 3.12"
        if self._py312_exe:
            label = "Relaunch 3.12 (embedded)"

        self.browser_relaunch_btn = ctk.CTkButton(
            self.browser_mode_row,
            text=label,
            width=168,
            command=self._relaunch_in_python_312,
        )
        self.browser_relaunch_btn.pack(side="right", padx=(8, 0))

    def _build_browser_sidebar(self):
        """Initialize browser state without creating a docked in-app sidebar."""
        self._embedded_browser_enabled = False
        self._browser_tab_map = {}
        self._sidebar_visible = False
        self.browser_mode_var = tk.StringVar(value="Browser: popup window mode")
        self.browser_url_var = tk.StringVar(value="https://lens.google.com/")
        self._browser_fallback_tab_var = tk.StringVar(value="image")
        self.browser_external_vars = {
            "image": tk.BooleanVar(value=False),
            "metadata": tk.BooleanVar(value=False),
            "ehentai": tk.BooleanVar(value=False),
        }
        # Compatibility attributes expected by a few old helper paths.
        self.browser_sidebar = None
        self.browser_mode_row = None
        self.browser_mode_label = None
        self.browser_home_btn = None
        self.browser_refresh_btn = None
        self.browser_open_btn = None

    def _build_ehentai_search_url(self, query=""):
        base = "https://exhentai.org" if self.use_ex_var.get() else "https://e-hentai.org"
        if not str(query or "").strip():
            return base
        return f"{base}/?f_search={quote(str(query).strip())}"

    def _browser_url_for_tab(self, tab_key, url=None):
        if not hasattr(self, "browser_url_var"):
            return
        if url:
            self.browser_url_var.set(url)
            return
        home_url = self._browser_default_url(tab_key)
        self.browser_url_var.set(home_url)

    def _browser_home_current_tab(self):
        tab_key = self._browser_current_tab_key()
        home_url = self._browser_default_url(tab_key)
        self._browser_open_url(tab_key, home_url, title="Home")

    def _browser_refresh_current_tab(self):
        tab_key = self._browser_current_tab_key()
        current = self.browser_url_var.get().strip() if hasattr(self, "browser_url_var") else ""
        if current:
            self._browser_open_url(tab_key, current, title="Refresh")

    def _browser_open_current_url(self):
        tab_key = self._browser_current_tab_key()
        url = self.browser_url_var.get().strip() if hasattr(self, "browser_url_var") else ""
        if not url:
            return
        self._browser_open_url(tab_key, url, title="Manual Open")

    def _open_embedded_browser(self, tab_key, url, title=None):
        # Intentionally disabled: the UI no longer reserves space for an embedded
        # browser.  _browser_open_url continues to Qt/WebView2/Edge popups.
        return False

    def tr(self, key):
        entry = TRANSLATIONS.get(key)
        if not entry:
            return key
        return entry.get(self.lang_code) or entry.get("en") or key

    def _reg(self, widget, key, attr="text"):
        """Register a widget for re-rendering on language change."""
        self._i18n_widgets.append((widget, key, attr))
        try:
            if attr == "text":
                widget.configure(text=self.tr(key))
            elif attr == "placeholder_text":
                widget.configure(placeholder_text=self.tr(key))
        except Exception:
            pass
        return widget

    def _sort_display_to_key(self, display):
        if not display:
            return "natural"
        s = str(display)
        for k in SORT_KEYS:
            if s == self.tr(SORT_I18N[k]):
                return k
        if s in SORT_KEYS:
            return s
        return _normalize_sort_key(s)

    def _sort_values(self):
        return [self.tr(SORT_I18N[k]) for k in SORT_KEYS]

    def _set_language(self, code):
        if code not in [c for c, _ in LANGUAGES]:
            code = "en"
        self.lang_code = code

        try:
            if hasattr(self, "_lang_var"):
                self._lang_var.set(code)
        except Exception:
            pass

        try:
            self.title(f"{self.tr('app_title')}  [{UI_BUILD_ID}]")
        except Exception:
            pass

        # Menu bar labels.
        self._apply_menu_labels()

        # Context menu labels.
        self._apply_context_menu_labels()

        # Registered widgets (labels / buttons / checkboxes / entry placeholders).
        for widget, key, attr in self._i18n_widgets:
            try:
                if attr == "text":
                    widget.configure(text=self.tr(key))
                elif attr == "placeholder_text":
                    widget.configure(placeholder_text=self.tr(key))
            except Exception:
                pass

        try:
            if hasattr(self, "_log_header_label"):
                self._log_header_label.configure(text=self.tr("log_title") + ("  ▲" if self._log_expanded else "  ▼"))
        except Exception:
            pass

        # Tab display names.
        self._apply_tab_labels()

        # Treeview headings.
        self._apply_tree_headings()

        # Sort combo display values (internal keys stay stable).
        self._apply_sort_combos()
        self._apply_batch_compact_labels()

        try:
            self._save_config()
        except Exception:
            pass

    def _build_menu_bar(self):
        """Build command menus plus the charcoal HTML-style visible menu row."""
        self._menu = tk.Menu(self)

        self._file_menu = tk.Menu(self._menu, tearoff=0)
        self._menu.add_cascade(label=self.tr("file_menu"), menu=self._file_menu)
        self._file_menu.add_command(label="Load Cookie File", command=self._load_cookie_export_path)
        self._file_menu.add_separator()
        self._file_menu.add_command(label=self.tr("file_close"), command=self._on_closing)

        self._lang_menu = tk.Menu(self._menu, tearoff=0)
        self._menu.add_cascade(label=self.tr("language_menu"), menu=self._lang_menu)
        self._lang_var = tk.StringVar(value=self.lang_code)
        for code, native in LANGUAGES:
            self._lang_menu.add_radiobutton(
                label=native, value=code, variable=self._lang_var,
                command=lambda c=code: self._set_language(c),
            )

        self._settings_menu = tk.Menu(self._menu, tearoff=0)
        self._menu.add_cascade(label=self.tr("settings_menu"), menu=self._settings_menu)
        self._settings_menu.add_checkbutton(
            label=self.tr("settings_show_debug"), variable=self.debug_enabled,
        )
        self._theme_menu = tk.Menu(self._settings_menu, tearoff=0)
        self._settings_menu.add_cascade(label="Theme", menu=self._theme_menu)
        self._theme_var = tk.StringVar(value=self._ui_theme)
        for theme_key, theme_label in (
            ("dark", "Onyx / Charcoal / Gold (Default)"),
            ("ehentai", "E-Hentai / Crimson Parchment"),
            ("winter", "Winter / Frost Slate")
        ):
            self._theme_menu.add_radiobutton(
                label=theme_label, value=theme_key, variable=self._theme_var,
                command=lambda t=theme_key: self._set_ui_theme(t),
            )

        # Legacy size presets now affect Single Gallery only; Batch geometry is
        # fixed by the approved layout.
        self._box_style_menu = tk.Menu(self._settings_menu, tearoff=0)
        self._settings_menu.add_cascade(label="Single Preview Size", menu=self._box_style_menu)
        self._box_style_var = tk.StringVar(value=self._box_style)
        for style_key, style_label in BOX_STYLE_OPTIONS:
            self._box_style_menu.add_radiobutton(
                label=style_label, value=style_key, variable=self._box_style_var,
                command=lambda s=style_key: self._set_box_style(s),
            )
        self._settings_menu.add_checkbutton(
            label="Open automation results in popup browser",
            variable=self.open_automation_result_in_app_var,
            command=self._save_config,
        )
        self._settings_menu.add_command(label="Upload Speed", command=self._open_upload_speed_settings)
        self._settings_menu.add_command(label="Cover OCR (Gemini / PaddleOCR)", command=self._open_ocr_settings)
        self._settings_menu.add_command(label="Close Image Search Browsers", command=self._close_image_search_browsers)
        self._settings_menu.add_separator()
        self._settings_menu.add_command(label="Keyboard Shortcuts", command=self._show_hotkeys)

        self._help_menu = tk.Menu(self._menu, tearoff=0)
        self._menu.add_cascade(label="Help", menu=self._help_menu)
        self._help_menu.add_command(label="Keyboard Shortcuts", command=self._show_hotkeys)

        # Hide the platform menu bar: it cannot match the approved charcoal row.
        try:
            self.config(menu="")
        except Exception:
            pass

        self.custom_menubar = ctk.CTkFrame(
            self, fg_color="#111111", corner_radius=0, height=32, border_width=0,
        )
        self.custom_menubar.grid(row=0, column=0, columnspan=2, sticky="ew")
        self.custom_menubar.grid_propagate(False)

        def make_menu_button(label, menu):
            holder = {"button": None}
            def show_menu():
                self._post_popup_menu(holder["button"], menu)
            btn = ctk.CTkButton(
                self.custom_menubar, text=label, command=show_menu,
                width=72, height=28, corner_radius=0,
                fg_color="transparent", hover_color="#1c1c1c",
                text_color="#9a9a9a", border_width=0,
                font=(self.input_font_family, 11),
            )
            holder["button"] = btn
            btn.pack(side="left", padx=(6, 0), pady=2)
            return btn

        self.file_menu_btn = make_menu_button(self.tr("file_menu"), self._file_menu)
        self.language_menu_btn = make_menu_button(self.tr("language_menu"), self._lang_menu)
        self.settings_menu_btn = make_menu_button(self.tr("settings_menu"), self._settings_menu)
        self.help_menu_btn = make_menu_button("Help", self._help_menu)

    def _post_popup_menu(self, anchor_widget, menu):
        if anchor_widget is None:
            return
        try:
            x = anchor_widget.winfo_rootx()
            y = anchor_widget.winfo_rooty() + anchor_widget.winfo_height()
            menu.tk_popup(x, y)
        finally:
            try:
                menu.grab_release()
            except Exception:
                pass

    def _open_upload_speed_settings(self):
        dialog = ctk.CTkToplevel(self)
        dialog.title("Upload Speed")
        dialog.geometry("460x260")
        dialog.transient(self)
        dialog.grab_set()

        row = ctk.CTkFrame(dialog, fg_color="transparent")
        row.pack(fill="x", padx=14, pady=(14, 6))
        ctk.CTkLabel(row, text="Batch Size", width=110, anchor="w").pack(side="left")
        tk.Spinbox(row, from_=1, to=UPLOAD_MAX_REQUEST_FILES, width=8, textvariable=self.batch_size_var).pack(side="left", padx=(0, 8))

        row2 = ctk.CTkFrame(dialog, fg_color="transparent")
        row2.pack(fill="x", padx=14, pady=6)
        ctk.CTkLabel(row2, text=f"Workers (1-{UPLOAD_MAX_WORKERS})", width=110, anchor="w").pack(side="left")
        tk.Spinbox(row2, from_=1, to=UPLOAD_MAX_WORKERS, width=8, textvariable=self.workers_var).pack(side="left", padx=(0, 8))

        row3 = ctk.CTkFrame(dialog, fg_color="transparent")
        row3.pack(fill="x", padx=14, pady=6)
        ctk.CTkLabel(row3, text="Delay (seconds)", width=110, anchor="w").pack(side="left")
        tk.Spinbox(row3, from_=0, to=5, increment=0.5, width=8, format="%.1f", textvariable=self.delay_var).pack(side="left", padx=(0, 8))

        ctk.CTkLabel(
            dialog,
            text=(
                f"Direct multipart uploads: up to {UPLOAD_MAX_REQUEST_FILES} files per request; "
                f"up to {UPLOAD_MAX_WORKERS} gallery workers."
            ),
            anchor="w", justify="left", wraplength=420,
        ).pack(fill="x", padx=14, pady=(6, 0))

        ctk.CTkButton(dialog, text="Save", command=lambda: (self._save_config(), dialog.destroy())).pack(anchor="e", padx=14, pady=(10, 12))

    def _close_image_search_browsers(self, show_message=True):
        closed = 0
        for driver in list(getattr(self, "_selenium_image_drivers", [])):
            try:
                driver.quit()
                closed += 1
            except Exception:
                pass
        self._selenium_image_drivers = []

        cleaned = 0
        for profile_dir in list(getattr(self, "_selenium_image_profiles", [])):
            try:
                if profile_dir and os.path.isdir(profile_dir):
                    shutil.rmtree(profile_dir, ignore_errors=True)
                    cleaned += 1
            except Exception:
                pass
        self._selenium_image_profiles = []

        self.log(f"[Image Search] Closed {closed} browser session(s); cleaned {cleaned} temporary profile(s).")
        if show_message:
            messagebox.showinfo("Image Search Browsers", f"Closed {closed} browser session(s).\nCleaned {cleaned} temporary profile(s).")

    def _bind_global_hotkeys(self):
        self.bind_all("<Control-s>", lambda e: (self._save_config(), "break")[1], add="+")
        self.bind_all("<Control-Shift-l>", lambda e: (self._toggle_log_panel(), "break")[1], add="+")
        self.bind_all("<Control-Shift-t>", lambda e: (self._cycle_ui_theme(), "break")[1], add="+")

    def _show_hotkeys(self):
        messagebox.showinfo(
            "Keyboard Shortcuts",
            "Global:\n"
            "Ctrl+S  Save configuration\n"
            "Ctrl+Shift+L  Expand/collapse console log\n"
            "Ctrl+Shift+T  Cycle theme\n\n"
            "Draft Images:\n"
            "Home  Top\n"
            "End  Bottom\n"
            "Page Up  Scroll up one viewport\n"
            "Page Down  Scroll down one viewport\n"
            "Mouse Wheel  Fast vertical scrolling\n"
            "Left mouse drag  Reorder cards",
            parent=self,
        )

    def _toggle_log_panel(self):
        self._log_expanded = not self._log_expanded
        if self._log_expanded:
            self.log_textbox.grid()
            self.main_vertical_pane.paneconfigure(self.log_slot, minsize=110, height=190)
        else:
            self.log_textbox.grid_remove()
            self.main_vertical_pane.paneconfigure(self.log_slot, minsize=44, height=44)
            if str(self.inspector_slot) in tuple(map(str, self.main_vertical_pane.panes())):
                self.main_vertical_pane.sash_place(0, 0, self.main_vertical_pane.winfo_height() - 51)
        self._log_header_label.configure(text=self.tr('log_title') + ('  ▲' if self._log_expanded else '  ▼'))

    def _cycle_ui_theme(self):
        order = ["dark", "ehentai", "winter"]
        try:
            idx = order.index(self._ui_theme)
        except ValueError:
            idx = 0
        self._set_ui_theme(order[(idx + 1) % len(order)])

    def _set_box_style(self, style):
        if style not in BOX_STYLE_PRESETS:
            style = "balanced"
        self._box_style = style
        try:
            self._box_style_var.set(style)
        except Exception:
            pass
        self._apply_box_style()
        try:
            self._save_config()
        except Exception:
            pass

    def _queue_box_style_refresh(self, _event=None):
        if _event is not None:
            size = (int(_event.width), int(_event.height))
            if size == getattr(self, '_single_tab_last_size', None):
                return
            self._single_tab_last_size = size
        if self._box_style_after_id is not None:
            self.after_cancel(self._box_style_after_id)
        self._box_style_after_id = self.after(80, self._apply_box_style)

    def _apply_box_style(self):
        self._box_style_after_id = None
        if not hasattr(self, 'single_preview_label'):
            return
        style = BOX_STYLE_PRESETS.get(self._box_style, BOX_STYLE_PRESETS['balanced'])
        size = int(style['single_preview_size'])
        tab_width = int(self.single_tab_root.winfo_width())
        if tab_width > 10:
            size = max(180, min(size, int(tab_width * 0.44)))
        signature = (size, int(style['single_preview_wrap']))
        if signature == getattr(self, '_single_preview_size_signature', None):
            return
        self._single_preview_size_signature = signature
        self._single_thumbnail_size = (size, size)
        self.single_preview_frame.configure(width=size + 20, height=size + 58)
        self.single_preview_label.configure(width=size, height=size,
                                            wraplength=max(170, min(signature[1], size - 10)))
        self._refresh_single_preview()

    def _bind_responsive_layout(self):
        """Apply the fixed desktop layout once; window-size reflow is disabled."""
        self._responsive_mode = "wide"
        self._responsive_last_width = DESKTOP_WINDOW_WIDTH
        self.after(200, self._apply_responsive_layout)

    def _on_root_configure_responsive(self, event=None):
        if event is not None and event.widget is not self:
            return
        try:
            width = int(self.winfo_width())
        except Exception:
            width = 0
        # Ignore focus/activation Configure noise when width did not change.
        if width and width == getattr(self, "_responsive_last_width", None):
            return
        self._responsive_last_width = width
        if getattr(self, "_responsive_after_id", None):
            try:
                self.after_cancel(self._responsive_after_id)
            except Exception:
                pass
        self._responsive_after_id = self.after(80, self._apply_responsive_layout)

    def _responsive_breakpoint(self, width=None):
        # Retain this helper for legacy callers, but the application now has a
        # single fixed desktop arrangement rather than responsive breakpoints.
        return "wide"

    def _set_browser_sidebar_visible(self, visible):
        # Browser/search results intentionally use separate popup windows.
        self._sidebar_visible = False

    def _set_batch_inspector_mode(self, mode):
        # The queue owns its persisted column order; layout must never reset it.
        self._batch_inspector_mode = 'desktop'

    def _apply_responsive_layout(self, event=None):
        self._responsive_after_id = None
        mode = self._responsive_breakpoint()
        previous = getattr(self, "_responsive_mode", None)
        self._responsive_mode = mode

        self._set_browser_sidebar_visible(False)
        self._set_batch_inspector_mode(mode)

        # Credentials: one HTML-like row on desktop, 2-column grid when narrow.
        try:
            holders = getattr(self, "_credential_holders", [])
            if mode == "narrow" and len(holders) >= 4:
                for i, holder in enumerate(holders[:4]):
                    holder.grid(row=i // 2, column=i % 2, padx=4, pady=5, sticky="ew")
                for col in range(2):
                    self.credentials_frame.grid_columnconfigure(col, weight=1, uniform="cred_narrow")
                for col in range(2, 6):
                    self.credentials_frame.grid_columnconfigure(col, weight=0, uniform="")
                self.use_ex_checkbox.grid(row=2, column=0, padx=8, pady=(2, 8), sticky="w")
                self.validate_session_btn.grid(row=2, column=1, padx=8, pady=(2, 8), sticky="e")
            else:
                for i, holder in enumerate(holders[:4]):
                    holder.grid(row=0, column=i, padx=(12 if i == 0 else 4, 4), pady=8, sticky="ew")
                for col in range(4):
                    self.credentials_frame.grid_columnconfigure(col, weight=1, uniform="cred")
                self.credentials_frame.grid_columnconfigure(4, weight=0, uniform="")
                self.credentials_frame.grid_columnconfigure(5, weight=0, uniform="")
                self.use_ex_checkbox.grid(row=0, column=4, padx=(8, 4), pady=(23, 8), sticky="s")
                self.validate_session_btn.grid(row=0, column=5, padx=(4, 12), pady=(23, 8), sticky="s")
            self.cookie_load_btn.grid_remove()
        except Exception:
            pass

        self._reflow_batch_toolbar()
        self._reflow_batch_action_buttons()

        if mode != previous:
            try:
                self.log(f"[UI] HTML layout -> {mode} ({self.winfo_width()}px) [{UI_BUILD_ID}]")
            except Exception:
                pass
            try:
                self.title(f"{self.tr('app_title')}  [{UI_BUILD_ID} · {mode}]")
            except Exception:
                pass

    def _apply_batch_compact_labels(self):
        """Use short action labels so the batch uploader spends space on content."""
        labels = {
            "en": ("+ Folders", "+ Root", "+ Archives", "Pause", "Resume", "Pause all", "Resume all", "Resume queue", "Remove", "Clear", "Sync", "Start batch", "Translate", "Fetch", "E/Ex"),
            "ja": ("+ フォルダ", "+ ルート", "+ 書庫", "停止", "再開", "全停止", "全再開", "キュー再開", "削除", "全消去", "同期", "一括開始", "翻訳", "取得", "E/Ex"),
            "zh": ("+ 文件夹", "+ 根目录", "+ 压缩包", "暂停", "恢复", "全暂停", "全恢复", "恢复队列", "移除", "清空", "同步", "开始批量", "翻译", "获取", "E/Ex"),
            "ko": ("+ 폴더", "+ 루트", "+ 압축", "일시정지", "재개", "전체 정지", "전체 재개", "큐 재개", "제거", "초기화", "동기화", "일괄 시작", "번역", "가져오기", "E/Ex"),
            "es": ("+ Carpetas", "+ Raíz", "+ Archivos", "Pausar", "Seguir", "Pausar todo", "Seguir todo", "Seguir cola", "Quitar", "Vaciar", "Sync", "Iniciar lote", "Traducir", "Obtener", "E/Ex"),
            "ru": ("+ Папки", "+ Корень", "+ Архивы", "Пауза", "Продолжить", "Стоп все", "Пуск все", "Возобн. очередь", "Удалить", "Очистить", "Синхр.", "Старт пакета", "Перевод", "Получить", "E/Ex"),
            "pt": ("+ Pastas", "+ Raiz", "+ Arquivos", "Pausar", "Retomar", "Pausar tudo", "Retomar tudo", "Retomar fila", "Remover", "Limpar", "Sincr.", "Iniciar lote", "Traduzir", "Buscar", "E/Ex"),
        }
        values = labels.get(getattr(self, "lang_code", "en"), labels["en"])
        names = (
            "add_folder_btn", "add_root_btn", "add_archive_btn",
            "batch_pause_selected_btn", "batch_resume_selected_btn",
            "batch_pause_all_btn", "batch_resume_all_btn", "batch_resume_queue_btn",
            "batch_remove_action_btn", "batch_clear_action_btn", "batch_sync_action_btn",
            "batch_start_btn", "batch_translate_btn", "batch_cover_title_btn",
            "batch_fetch_metadata_btn",
        )
        for name, label in zip(names, values):
            widget = getattr(self, name, None)
            if widget is not None:
                try:
                    widget.configure(text=label)
                except Exception:
                    pass

    def _reflow_batch_action_buttons(self, event=None):
        """Implement the HTML queue-actions row, including its flexible spacer."""
        if not hasattr(self, "batch_action_frame"):
            return
        f = self.batch_action_frame
        try:
            width = int(f.winfo_width() or self.winfo_width() or 1)
        except Exception:
            width = 1400
        mode = "wide" if width >= 1100 else "medium" if width >= 760 else "narrow"
        layout_key = (mode, getattr(self, "lang_code", "en"))
        if getattr(self, "_batch_action_layout_key", None) == layout_key:
            return
        self._batch_action_layout_key = layout_key

        controls = [
            self.batch_queue_label, self.batch_action_sep,
            *getattr(self, "_batch_action_widgets", []),
        ]
        for widget in controls:
            try:
                widget.grid_forget()
            except Exception:
                pass
        for col in range(12):
            try:
                f.grid_columnconfigure(col, weight=0, minsize=0)
            except Exception:
                pass

        if mode == "wide":
            # Exact desktop structure:
            # Queue | pause controls + Resume Queue | remove/clear | grow | sync/start
            self.batch_queue_label.grid(row=0, column=0, padx=(6, 2), pady=(2, 4), sticky="w")
            left = [
                self.batch_pause_selected_btn, self.batch_resume_selected_btn,
                self.batch_pause_all_btn, self.batch_resume_all_btn,
                self.batch_resume_queue_btn,
            ]
            for i, widget in enumerate(left, start=1):
                widget.grid(row=0, column=i, padx=2, pady=(2, 4), sticky="w")
            self.batch_action_sep.grid(row=0, column=6, padx=4, pady=(3, 5), sticky="ns")
            self.batch_remove_action_btn.grid(row=0, column=7, padx=2, pady=(2, 4), sticky="w")
            self.batch_clear_action_btn.grid(row=0, column=8, padx=2, pady=(2, 4), sticky="w")
            f.grid_columnconfigure(9, weight=1, minsize=8)
            self.batch_sync_action_btn.grid(row=0, column=10, padx=2, pady=(2, 4), sticky="e")
            self.batch_start_btn.grid(row=0, column=11, padx=(2, 6), pady=(2, 4), sticky="e")
        elif mode == "medium" or width >= 760:
            # Same semantic grouping, wrapped like the HTML medium mockup.
            first = [
                self.batch_pause_selected_btn, self.batch_resume_selected_btn,
                self.batch_pause_all_btn, self.batch_resume_all_btn,
                self.batch_remove_action_btn, self.batch_clear_action_btn,
            ]
            for i, widget in enumerate(first):
                widget.grid(row=0, column=i, padx=(10 if i == 0 else 3, 3), pady=(0, 4), sticky="w")
            f.grid_columnconfigure(6, weight=1)
            self.batch_resume_queue_btn.grid(row=1, column=0, columnspan=2, padx=10, pady=(0, 9), sticky="w")
            self.batch_sync_action_btn.grid(row=1, column=5, padx=3, pady=(0, 9), sticky="e")
            self.batch_start_btn.grid(row=1, column=6, padx=(3, 10), pady=(0, 9), sticky="e")
        else:
            labels = ["Pause", "Resume", "Pause All", "Resume All"]
            for widget, label in zip(
                [self.batch_pause_selected_btn, self.batch_resume_selected_btn,
                 self.batch_pause_all_btn, self.batch_resume_all_btn], labels,
            ):
                try:
                    widget.configure(text=label)
                except Exception:
                    pass
            self.batch_remove_action_btn.configure(text="Remove")
            self.batch_clear_action_btn.configure(text="Clear")
            grid_items = [
                self.batch_pause_selected_btn, self.batch_resume_selected_btn,
                self.batch_pause_all_btn, self.batch_resume_all_btn,
                self.batch_remove_action_btn, self.batch_clear_action_btn,
            ]
            for i, widget in enumerate(grid_items):
                col = i % 3
                row = i // 3
                f.grid_columnconfigure(col, weight=1)
                widget.grid(row=row, column=col, padx=(8 if col == 0 else 3, 3), pady=3, sticky="ew")
            self.batch_resume_queue_btn.grid(row=2, column=1, padx=3, pady=(3, 8), sticky="ew")
            self.batch_start_btn.configure(text="Start")
            self.batch_sync_action_btn.grid(row=2, column=0, padx=(8, 3), pady=(3, 8), sticky="ew")
            self.batch_start_btn.grid(row=2, column=2, padx=(3, 8), pady=(3, 8), sticky="ew")

        self._apply_batch_compact_labels()

    def _reflow_batch_toolbar(self, event=None):
        """Implement the HTML toolbar as one desktop row, wrapping only below it."""
        if not hasattr(self, "batch_ctrl_frame"):
            return
        f = self.batch_ctrl_frame
        try:
            width = int(f.winfo_width() or self.winfo_width() or 1)
        except Exception:
            width = 1400
        mode = "wide" if width >= 1180 else "medium" if width >= 760 else "narrow"
        layout_key = (mode, getattr(self, "lang_code", "en"))
        if getattr(self, "_batch_toolbar_layout_key", None) == layout_key:
            return
        self._batch_toolbar_layout_key = layout_key

        for widget in getattr(self, "_batch_toolbar_widgets", []):
            try:
                widget.grid_forget()
            except Exception:
                pass
        for col in range(12):
            try:
                f.grid_columnconfigure(col, weight=0, minsize=0)
            except Exception:
                pass

        widgets = getattr(self, "_batch_toolbar_widgets", [])
        if mode == "wide":
            for col, widget in enumerate(widgets):
                widget.grid(row=0, column=col, padx=(6 if col == 0 else 2, 2), pady=(5, 3), sticky="w")
            f.grid_columnconfigure(len(widgets), weight=1)
        elif mode == "medium" or width >= 700:
            first = widgets[:5]
            second = widgets[5:]
            for col, widget in enumerate(first):
                widget.grid(row=0, column=col, padx=(10 if col == 0 else 3, 3), pady=(8, 3), sticky="w")
            for col, widget in enumerate(second):
                widget.grid(row=1, column=col, padx=(10 if col == 0 else 3, 3), pady=(3, 6), sticky="w")
        else:
            for index, widget in enumerate(widgets):
                if widget is self.batch_toolbar_sep:
                    continue
                slot = index if index < 3 else index - 1
                widget.grid(row=slot // 3, column=slot % 3, padx=6, pady=4, sticky="w")
            for col in range(3):
                f.grid_columnconfigure(col, weight=1)

    def _install_theme_header_background(self, frame):
        """Paint the active theme's square-edged gradient and signature header pattern."""
        canvas = tk.Canvas(frame, bd=0, highlightthickness=0, takefocus=0)
        canvas.place(x=0, y=0, relwidth=1, relheight=1)
        def _rgb(value):
            value = str(value or "#000000").lstrip("#")
            if len(value) != 6:
                value = "000000"
            return tuple(int(value[i:i + 2], 16) for i in (0, 2, 4))

        def _mix(a, b, t):
            return tuple(round(a[i] + (b[i] - a[i]) * t) for i in range(3))

        def _hex(rgb):
            return "#%02x%02x%02x" % rgb

        paint_state = {'signature': None, 'after': None}
        def redraw(_event=None):
            paint_state['after'] = None
            try:
                p = self._theme_palette()
                signature = (int(frame.winfo_width()), int(frame.winfo_height()), tuple(sorted(p.items())))
                if signature == paint_state['signature']:
                    return
                paint_state['signature'] = signature
                canvas.configure(bg=p["header_left"])
                canvas.delete("all")
                w = max(1, int(frame.winfo_width()))
                h = max(1, int(frame.winfo_height()))
                left = _rgb(p["header_left"])
                middle = _rgb(p["header_mid"])
                right = _rgb(p["header_right"])
                segments = 36
                for idx in range(segments):
                    t0 = idx / segments
                    x0 = round(w * t0)
                    x1 = round(w * (idx + 1) / segments) + 1
                    if t0 <= 0.52:
                        color = _mix(left, middle, t0 / 0.52)
                    else:
                        color = _mix(middle, right, (t0 - 0.52) / 0.48)
                    canvas.create_rectangle(x0, 0, x1, h, fill=_hex(color), outline="")

                pattern = p.get("header_pattern", "diagonal")
                hatch = p["header_hatch"]
                hatch2 = p["header_hatch2"]
                if pattern == "chevron":
                    step = 30
                    for x in range(-h, w + h, step):
                        canvas.create_line(x, h, x + h // 2, h // 2, fill=hatch, width=1)
                        canvas.create_line(x + h // 2, h // 2, x + h, h, fill=hatch2, width=1)
                    # Reversed chevrons add a woven print effect unique to E-Hentai.
                    for x in range(-h + step // 2, w + h, step * 2):
                        canvas.create_line(x, 0, x + h // 2, h // 2, fill=hatch2, width=1)
                        canvas.create_line(x + h // 2, h // 2, x + h, 0, fill=hatch, width=1)
                elif pattern == "frost":
                    # Fine crossing diagonals form an icy diamond lattice.
                    for x in range(-h, w + h, 26):
                        canvas.create_line(x, h, x + h, 0, fill=hatch, width=1)
                    for x in range(-h, w + h, 52):
                        canvas.create_line(x, 0, x + h, h, fill=hatch2, width=1)
                    for x in range(12, w, 78):
                        canvas.create_oval(x, max(3, h // 2 - 1), x + 2, max(5, h // 2 + 1), fill=hatch2, outline="")
                else:
                    # Onyx: etched diagonal metal/glass lines with a second sparse gold pass.
                    for x in range(-h, w + h, 22):
                        canvas.create_line(x, h, x + h, 0, fill=hatch, width=1)
                    for x in range(-h + 11, w + h, 44):
                        canvas.create_line(x, h, x + h, 0, fill=hatch2, width=1)

                canvas.create_line(0, 0, w, 0, fill=p["header_hatch"], width=1)
                canvas.create_line(0, h - 1, w, h - 1, fill=p["header_edge"], width=1)
            except Exception:
                pass

        def schedule_redraw(_event=None):
            if paint_state['after'] is not None:
                self.after_cancel(paint_state['after'])
            paint_state['after'] = self.after(32, redraw)

        canvas.bind("<Configure>", schedule_redraw, add="+")
        if not hasattr(self, "_header_redrawers"):
            self._header_redrawers = []
        self._header_redrawers.append(redraw)
        self.after_idle(redraw)
        return canvas

    # Old helper name retained so plugins/older code paths still work.
    def _install_onyx_gold_header_background(self, frame):
        return self._install_theme_header_background(frame)

    def _refresh_theme_headers(self):
        for redraw in list(getattr(self, "_header_redrawers", [])):
            try:
                redraw()
            except Exception:
                pass


    def _theme_palette(self, theme=None):
        theme = theme or self._ui_theme
        palettes = {
            "dark": {
                "root": "#090909", "elev": "#11110f", "panel": "#171612",
                "soft": "#211f19", "hover": "#302a1d", "border": "#3a3326",
                "border_strong": "#6f5b2e", "text": "#e8e1d2", "muted": "#a89e86",
                "selected": "#40361f", "log": "#080807", "primary": "#c6a65a", "primary_text": "#090909",
                "danger_bg": "#1b1711", "danger_hover": "#2b2418",
                "danger_border": "#7c6534", "danger_text": "#d7b86a",
                "frame": "#11110f", "input": "#211f19", "accent": "#8d7336",
                "accent2": "#c6a65a", "canvas": "#090909",
                "header_left": "#090908", "header_mid": "#3d321d", "header_right": "#151410",
                "header_hatch": "#4c4026", "header_hatch2": "#7f6833", "header_edge": "#a4873e",
                "header_text": "#e0c46d", "header_subtext": "#927d50", "header_pattern": "diagonal",
                "queue_bg": "#0f0f0d", "queue_alt": "#17150f", "queue_heading": "#201d15",
                "queue_heading_text": "#e0c46d", "queue_selected": "#44371d",
                "queue_selected_text": "#fff1c5", "queue_grid": "#3d3423", "queue_rail": "#c6a65a",
                "queue_tagline": "ONYX MATRIX / LIVE QUEUE",
            },
            "ehentai": {
                "root": "#e8dfcd", "elev": "#d9cdb9", "panel": "#f2e8d5",
                "soft": "#fbf2e2", "hover": "#ddc8ad", "border": "#9d7d63",
                "border_strong": "#6e3d2c", "text": "#271711", "muted": "#6e4e3f",
                "selected": "#dbc3a5", "log": "#241815", "primary": "#9e3b23", "primary_text": "#fff5e9",
                "danger_bg": "#ead4c8", "danger_hover": "#dfbeb0",
                "danger_border": "#8b3725", "danger_text": "#6d2415",
                "frame": "#d9cdb9", "input": "#fff8ea", "accent": "#9e3b23",
                "accent2": "#6f2618", "canvas": "#e1d5c1",
                "header_left": "#2a1110", "header_mid": "#7a291c", "header_right": "#3b1612",
                "header_hatch": "#a5573d", "header_hatch2": "#d0a06e", "header_edge": "#d4a563",
                "header_text": "#fff1d7", "header_subtext": "#e0b88b", "header_pattern": "chevron",
                "queue_bg": "#fff8ea", "queue_alt": "#f0e3cf", "queue_heading": "#6a261c",
                "queue_heading_text": "#fff0d7", "queue_selected": "#c6936b",
                "queue_selected_text": "#28130c", "queue_grid": "#b99372", "queue_rail": "#9e3b23",
                "queue_tagline": "CRIMSON ARCHIVE / LIVE QUEUE",
            },
            "winter": {
                "root": "#0c1722", "elev": "#122131", "panel": "#182a3b",
                "soft": "#203548", "hover": "#29465f", "border": "#36566e",
                "border_strong": "#6fa7c8", "text": "#e8f5ff", "muted": "#9ab4c7",
                "selected": "#274a62", "log": "#09121b", "primary": "#8bd3f7", "primary_text": "#07131d",
                "danger_bg": "#342331", "danger_hover": "#4a2e40",
                "danger_border": "#9b6687", "danger_text": "#f0bfd8",
                "frame": "#122131", "input": "#172b3c", "accent": "#4d91b7",
                "accent2": "#8bd3f7", "canvas": "#0c1722",
                "header_left": "#081522", "header_mid": "#215778", "header_right": "#0d2639",
                "header_hatch": "#3d7696", "header_hatch2": "#8ec9e8", "header_edge": "#a6e3ff",
                "header_text": "#e9f8ff", "header_subtext": "#94bdd1", "header_pattern": "frost",
                "queue_bg": "#0f1c28", "queue_alt": "#142635", "queue_heading": "#17364b",
                "queue_heading_text": "#bfe9ff", "queue_selected": "#24516b",
                "queue_selected_text": "#f5fbff", "queue_grid": "#31566c", "queue_rail": "#8bd3f7",
                "queue_tagline": "FROST GRID / LIVE QUEUE",
            },
        }
        return palettes.get(theme, palettes["dark"])

    def _apply_ui_theme(self):
        """Apply colors only.  Theme changes never modify layout geometry."""
        p = self._theme_palette()
        try:
            self.configure(fg_color=p["root"])
        except Exception:
            pass

        def visit(widget):
            try:
                cls = widget.__class__.__name__
                try:
                    widget.configure(corner_radius=0)
                except Exception:
                    pass
                if cls in {"CTkFrame", "CTkScrollableFrame"}:
                    current = ""
                    try:
                        current = str(widget.cget("fg_color") or "").lower()
                    except Exception:
                        pass
                    if current != "transparent":
                        widget.configure(fg_color=p["elev"])
                elif cls == "CTkLabel":
                    widget.configure(text_color=p["text"])
                elif cls == "CTkButton":
                    widget.configure(
                        fg_color=p["soft"], hover_color=p["hover"],
                        text_color=p["text"], border_color=p["border"],
                    )
                elif cls == "CTkEntry":
                    widget.configure(
                        fg_color=p["root"], text_color=p["text"], border_color=p["border"],
                    )
                elif cls == "CTkTextbox":
                    widget.configure(
                        fg_color=p["root"], text_color=p["text"], border_color=p["border"],
                    )
                elif cls == "CTkComboBox":
                    widget.configure(
                        fg_color=p["soft"], button_color=p["soft"],
                        button_hover_color=p["hover"], text_color=p["text"],
                        border_color=p["border"],
                    )
                elif cls == "CTkCheckBox":
                    widget.configure(
                        text_color=p["text"], fg_color=p["primary"],
                        hover_color=p["hover"], checkmark_color=p["primary_text"],
                        border_color=p["border_strong"],
                    )
            except Exception:
                pass
            try:
                for child in widget.winfo_children():
                    visit(child)
            except Exception:
                pass

        visit(self)
        self._apply_html_layout_theme(p)
        self._configure_treeview_style(p)
        self._configure_batch_queue_style(p)
        self._refresh_theme_headers()
        try:
            self.context_menu.configure(
                bg=p["elev"], fg=p["text"], activebackground=p["hover"], activeforeground=p["text"],
            )
        except Exception:
            pass
        try:
            self._theme_var.set(self._ui_theme)
        except Exception:
            pass
        try:
            self._save_config()
        except Exception:
            pass

    def _apply_html_layout_theme(self, p=None):
        """Reassert semantic surface/button colors after the generic theme pass."""
        p = p or self._theme_palette()
        for name, key in (
            ("custom_menubar", "elev"), ("credentials_frame", "panel"),
            ("app_body", "root"), ("left_pane_frame", "root"), ("right_pane_frame", "panel"),
            ("tab_shell", "root"), ("app_tab_bar", "elev"),
            ("tab_content_host", "root"), ("batch_tab", "root"),
            ("batch_ctrl_frame", "root"), ("batch_action_frame", "root"),
            ("batch_main_content", "root"), ("batch_tree_frame", "panel"),
            ("batch_preview_box", "panel"), ("batch_inspector_body", "panel"),
            ("_log_frame", "log"), ("_log_header_frame", "log"),
        ):
            widget = getattr(self, name, None)
            if widget is not None:
                try:
                    widget.configure(fg_color=p[key])
                except Exception:
                    pass

        # Menubar text is intentionally muted until hover.
        for btn_name in ("file_menu_btn", "language_menu_btn", "settings_menu_btn", "help_menu_btn"):
            btn = getattr(self, btn_name, None)
            if btn is not None:
                try:
                    btn.configure(
                        fg_color="transparent", hover_color=p["soft"],
                        text_color=p["muted"], border_width=0,
                    )
                except Exception:
                    pass

        # Credential captions use the same muted uppercase-ish visual hierarchy as HTML.
        for holder in getattr(self, "_credential_holders", []):
            try:
                for child in holder.winfo_children():
                    if child.__class__.__name__ == "CTkLabel":
                        child.configure(text_color=p["muted"])
            except Exception:
                pass

        # Toolbar field captions are muted; combo contents remain normal text.
        for group_name in ("batch_cat_group", "batch_lang_group", "batch_folder_group", "batch_sort_group"):
            group = getattr(self, group_name, None)
            if group is None:
                continue
            try:
                for child in group.winfo_children():
                    if child.__class__.__name__ == "CTkLabel":
                        child.configure(text_color=p["muted"])
            except Exception:
                pass

        for btn_name in (
            "batch_pause_selected_btn", "batch_resume_selected_btn",
            "batch_pause_all_btn", "batch_resume_all_btn",
        ):
            btn = getattr(self, btn_name, None)
            if btn is not None:
                try:
                    btn.configure(
                        fg_color=p["elev"], hover_color=p["hover"], text_color=p["muted"],
                        border_width=1, border_color=p["border"],
                    )
                except Exception:
                    pass

        for btn_name in ("batch_remove_action_btn", "batch_clear_action_btn"):
            btn = getattr(self, btn_name, None)
            if btn is not None:
                try:
                    btn.configure(
                        fg_color=p["danger_bg"], hover_color=p["danger_hover"],
                        text_color=p["danger_text"], border_width=1,
                        border_color=p["danger_border"],
                    )
                except Exception:
                    pass

        btn = getattr(self, "batch_sync_action_btn", None)
        if btn is not None:
            try:
                btn.configure(
                    fg_color="transparent", hover_color=p["hover"], text_color=p["text"],
                    border_width=1, border_color=p["border"],
                )
            except Exception:
                pass
        btn = getattr(self, "batch_start_btn", None)
        if btn is not None:
            try:
                btn.configure(
                    fg_color=p["primary"], hover_color=p["hover"],
                    text_color=p["primary_text"], border_width=1,
                    border_color=p["primary"],
                )
            except Exception:
                pass

        for btn_name in ("add_folder_btn", "add_root_btn"):
            btn = getattr(self, btn_name, None)
            if btn is not None:
                try:
                    btn.configure(
                        fg_color=p["soft"], hover_color=p["hover"], text_color=p["text"],
                        border_width=1, border_color=p["border_strong"],
                    )
                except Exception:
                    pass

        try:
            self.batch_preview_label.configure(fg_color=p["elev"], text_color=p["muted"])
            self.batch_inspector_heading.configure(text_color=p["primary"])
            self.batch_en_label.configure(text_color=p["muted"])
            self.batch_jp_label.configure(text_color=p["muted"])
            self.batch_queue_label.configure(text_color=p["primary"])
            self._log_header_label.configure(text_color=p["primary"])
            self._log_debug_label.configure(text_color=p["muted"])
            self.log_textbox.configure(fg_color=p["log"], text_color=p["muted"])
        except Exception:
            pass
        self._update_custom_tab_styles()

    def _set_ui_theme(self, theme):
        if theme not in {"dark", "ehentai", "winter"}:
            theme = "dark"
        self._ui_theme = theme
        self._apply_ui_theme()

    def _apply_menu_labels(self):
        try:
            if getattr(self, "_menu", None):
                self._menu.entryconfig(0, label=self.tr("file_menu"))
                self._menu.entryconfig(1, label=self.tr("language_menu"))
                self._menu.entryconfig(2, label=self.tr("settings_menu"))
                self._file_menu.entryconfig(2, label=self.tr("file_close"))
                self._settings_menu.entryconfig(0, label=self.tr("settings_show_debug"))
        except Exception:
            pass
        try:
            self.file_menu_btn.configure(text=self.tr("file_menu"))
            self.language_menu_btn.configure(text=self.tr("language_menu"))
            self.settings_menu_btn.configure(text=self.tr("settings_menu"))
        except Exception:
            pass

    def _apply_context_menu_labels(self):
        labels = {
            0: self.tr("ctx_cut"),
            1: self.tr("ctx_copy"),
            2: self.tr("ctx_paste"),
            3: self.tr("ctx_delete"),
            7: self.tr("ctx_select_all"),
        }
        for idx, lbl in labels.items():
            try:
                self.context_menu.entryconfig(idx, label=lbl)
            except Exception:
                pass

    def _apply_tab_labels(self):
        self._tab_labels["batch"] = self.tr("tab_batch")
        self._tab_labels["single"] = self.tr("tab_single")
        try:
            self.batch_tab_btn.configure(text=self._tab_labels["batch"])
            self.single_tab_btn.configure(text=self._tab_labels["single"])
            self._update_custom_tab_styles()
        except Exception:
            pass

    def _rename_tab(self, old_name, new_name):
        # Compatibility shim.  Custom tabs use stable internal keys, so only the
        # visible labels need to change.
        try:
            if old_name == self._tab_labels.get("batch"):
                self.batch_tab_btn.configure(text=new_name)
            elif old_name == self._tab_labels.get("single"):
                self.single_tab_btn.configure(text=new_name)
        except Exception:
            pass

    def _apply_tree_headings(self):
        headings = {
            "title_en": self.tr("col_title_en"),
            "title_jp": self.tr("col_title_jp"),
            "image_count": self.tr("col_images"),
            "status": self.tr("col_status"),
            "path": self.tr("col_path"),
        }
        for col, label in headings.items():
            try:
                self.batch_tree.heading(col, text=label)
            except Exception:
                pass

    def _apply_sort_combos(self):
        values = self._sort_values()
        for combo in (getattr(self, "batch_sort_combo", None), getattr(self, "single_sort_combo", None)):
            if combo is None:
                continue
            try:
                current_key = self._sort_display_to_key(combo.get())
                combo.configure(values=values)
                combo.set(self.tr(SORT_I18N.get(current_key, "sort_natural")))
            except Exception:
                try:
                    combo.configure(values=values)
                except Exception:
                    pass

    def _build_context_menu(self):
        self.context_menu = tk.Menu(
            self,
            tearoff=0,
            bg="#2b2b2b",
            fg="white",
            activebackground="#1f538d",
            activeforeground="white",
        )

        self.context_menu.add_command(
            label=self.tr("ctx_cut"),
            command=self._ctx_cut,
        )

        self.context_menu.add_command(
            label=self.tr("ctx_copy"),
            command=self._ctx_copy,
        )

        self.context_menu.add_command(
            label=self.tr("ctx_paste"),
            command=self._ctx_paste,
        )

        self.context_menu.add_command(
            label=self.tr("ctx_delete"),
            command=self._ctx_delete,
        )

        self.context_menu.add_separator()

        self.context_menu.add_command(
            label="Rename Directory",
            command=self._ctx_rename_directory,
        )

        self.context_menu.add_separator()

        self.context_menu.add_command(
            label=self.tr("ctx_select_all"),
            command=self._ctx_select_all,
        )

        self.context_menu_widget = None

    def _show_context_menu(self, event):
        self.context_menu_widget = event.widget

        # Directory renaming only makes sense when this particular field holds
        # an existing directory.  Password/title fields no longer offer a
        # misleading destructive action.
        directory_state = "disabled"
        try:
            value = str(self.context_menu_widget.get()).strip()
            if value and os.path.isdir(os.path.normpath(value)):
                directory_state = "normal"
        except Exception:
            pass
        try:
            self.context_menu.entryconfig(5, state=directory_state)
        except Exception:
            pass

        try:
            self.context_menu_widget.focus_set()
            self.context_menu.tk_popup(
                event.x_root,
                event.y_root,
            )
        finally:
            self.context_menu.grab_release()

    def _bind_context_menu(self, widget):
        target = getattr(
            widget,
            "_entry",
            getattr(
                widget,
                "_textbox",
                widget,
            ),
        )

        target.bind(
            "<Button-3>",
            self._show_context_menu,
        )

        target.bind(
            "<Button-2>",
            self._show_context_menu,
        )

        # Keep cut/copy/paste/select-all consistent across CTk and Tk widgets.
        target.bind("<Control-x>", lambda e: (e.widget.event_generate("<<Cut>>"), "break")[1])
        target.bind("<Control-c>", lambda e: (e.widget.event_generate("<<Copy>>"), "break")[1])
        target.bind("<Control-v>", lambda e: (e.widget.event_generate("<<Paste>>"), "break")[1])
        target.bind("<Control-a>", lambda e: (e.widget.event_generate("<<SelectAll>>"), "break")[1])
        target.bind("<Control-X>", lambda e: (e.widget.event_generate("<<Cut>>"), "break")[1])
        target.bind("<Control-C>", lambda e: (e.widget.event_generate("<<Copy>>"), "break")[1])
        target.bind("<Control-V>", lambda e: (e.widget.event_generate("<<Paste>>"), "break")[1])
        target.bind("<Control-A>", lambda e: (e.widget.event_generate("<<SelectAll>>"), "break")[1])

    def _apply_input_fonts_recursive(self, root):
        """Apply Aller (or the installed fallback) to editable text controls."""
        try:
            children = root.winfo_children()
        except Exception:
            return
        for child in children:
            try:
                if isinstance(child, (ctk.CTkEntry, ctk.CTkTextbox, tk.Entry, tk.Text)):
                    child.configure(font=self.input_font)
                elif isinstance(child, (ttk.Entry, ttk.Spinbox)):
                    child.configure(font=self.input_font)
            except Exception:
                pass
            self._apply_input_fonts_recursive(child)

    def _prompt_text_dialog(self, title, prompt, initial_value=""):
        dialog = ctk.CTkToplevel(self)
        dialog.title(title)
        dialog.geometry("560x140")
        dialog.minsize(420, 140)
        dialog.transient(self)
        dialog.grab_set()

        ctk.CTkLabel(dialog, text=prompt, anchor="w", justify="left").pack(fill="x", padx=12, pady=(12, 4))
        entry = ctk.CTkEntry(dialog, font=self.input_font)
        entry.pack(fill="x", padx=12, pady=(0, 8))
        entry.insert(0, str(initial_value or ""))
        self._bind_context_menu(entry)
        entry.focus_set()
        entry.select_range(0, "end")

        result = {"value": None}

        def accept():
            result["value"] = entry.get()
            dialog.destroy()

        def cancel():
            dialog.destroy()

        buttons = ctk.CTkFrame(dialog, fg_color="transparent")
        buttons.pack(fill="x", padx=12, pady=(0, 10))
        ctk.CTkButton(buttons, text="Cancel", width=90, command=cancel).pack(side="right", padx=(6, 0))
        ctk.CTkButton(buttons, text="OK", width=90, command=accept).pack(side="right")

        dialog.bind("<Return>", lambda _e: accept())
        dialog.bind("<Escape>", lambda _e: cancel())
        dialog.wait_window(dialog)
        return result["value"]

    def _compose_title_cell(self, title_en, title_jp):
        # Japanese has its own column; repeating it here obscures long titles.
        return str(title_en or "").strip() or str(title_jp or "").strip() or "(untitled)"

    def _status_icon(self, status_key):
        icons = {
            "status_queued": "!",
            "status_paused": "||",
            "status_no_images": "!",
            "status_creating": "..",
            "status_uploading": "^^",
            "status_publishing": "!!",
            "status_published": "OK",
            "status_draft_saved": "DR",
            "status_error": "X",
        }
        return icons.get(status_key, "!")

    def _ctx_cut(self):
        if self.context_menu_widget:
            self.context_menu_widget.event_generate(
                "<<Cut>>"
            )

    def _ctx_copy(self):
        if self.context_menu_widget:
            self.context_menu_widget.event_generate(
                "<<Copy>>"
            )

    def _ctx_paste(self):
        if self.context_menu_widget:
            self.context_menu_widget.event_generate(
                "<<Paste>>"
            )

    def _ctx_delete(self):
        if self.context_menu_widget:
            try:
                self.context_menu_widget.event_generate("<<Clear>>")
            except Exception:
                pass

    def _rename_folder_path_widget(self, widget):
        if widget is None:
            return

        try:
            text = widget.get().strip()
        except Exception:
            text = ""

        if not text:
            messagebox.showwarning("Rename Directory", "Select a directory path first.", parent=self)
            return

        source_dir = os.path.normpath(text)
        if not os.path.isdir(source_dir):
            messagebox.showwarning("Rename Directory", f"Not a valid directory: {source_dir}", parent=self)
            return

        parent_dir = os.path.dirname(source_dir) or os.getcwd()
        current_name = os.path.basename(source_dir)
        new_name = self._prompt_text_dialog(
            "Rename Directory",
            f"New name for: {current_name}",
            initial_value=current_name,
        )
        if new_name is None:
            return

        cleaned = str(new_name).strip()
        if not cleaned or cleaned in {".", ".."}:
            messagebox.showwarning("Rename Directory", "Please enter a valid new directory name.", parent=self)
            return

        target_dir = os.path.join(parent_dir, cleaned)
        if os.path.exists(target_dir):
            messagebox.showwarning("Rename Directory", f"A directory named '{cleaned}' already exists.", parent=self)
            return

        try:
            os.rename(source_dir, target_dir)
            if hasattr(widget, "get"):
                try:
                    widget.delete(0, "end")
                    widget.insert(0, target_dir)
                except Exception:
                    try:
                        widget.set(target_dir)
                    except Exception:
                        pass
            self.log(f"[Directory Rename] Renamed '{source_dir}' -> '{target_dir}'")
        except Exception as exc:
            messagebox.showerror("Rename Directory", f"Rename failed:\n\n{exc}", parent=self)

    def _ctx_rename_directory(self):
        self._rename_folder_path_widget(self.context_menu_widget)

    def _ctx_select_all(self):
        if self.context_menu_widget:
            self.context_menu_widget.event_generate(
                "<<SelectAll>>"
            )

    def _configure_treeview_style(self, palette=None):
        style = ttk.Style()
        try:
            style.theme_use("clam")
        except Exception:
            pass
        p = palette or self._theme_palette()
        style.configure(
            "Treeview",
            background=p["root"], foreground=p["text"], fieldbackground=p["root"],
            rowheight=30, borderwidth=0, relief="flat",
            font=(self.input_font_family, 10),
        )
        style.configure(
            "Treeview.Heading",
            background=p["panel"], foreground=p["primary"], relief="flat",
            borderwidth=0, font=(self.input_font_family, 9, "bold"),
        )
        style.map(
            "Treeview",
            background=[("selected", p["selected"])],
            foreground=[("selected", p["text"])],
        )
        style.map("Treeview.Heading", background=[("active", p["hover"])])

    def _configure_batch_queue_style(self, palette=None):
        """Give the queue a theme-specific matrix/list treatment."""
        if not hasattr(self, "batch_tree"):
            return
        p = palette or self._theme_palette()
        style = ttk.Style(self)
        try:
            style.theme_use("clam")
        except Exception:
            pass
        style.configure(
            "Queue.Treeview",
            background=p["queue_bg"], fieldbackground=p["queue_bg"],
            foreground=p["text"], rowheight=30, borderwidth=0, relief="flat",
            font=(self.input_font_family, 11),
        )
        style.configure(
            "Queue.Treeview.Heading",
            background=p["queue_heading"], foreground=p["queue_heading_text"],
            relief="flat", borderwidth=0, padding=(12, 10),
            font=(self.input_font_family, 10, "bold"),
        )
        style.map(
            "Queue.Treeview",
            background=[("selected", p["queue_selected"])],
            foreground=[("selected", p["queue_selected_text"])],
        )
        style.map(
            "Queue.Treeview.Heading",
            background=[("active", p["hover"])],
            foreground=[("active", p["queue_heading_text"])],
        )
        self.batch_tree.tag_configure("queue_even", background=p["queue_bg"])
        self.batch_tree.tag_configure("queue_odd", background=p["queue_alt"])
        self.batch_tree.tag_configure("status_queued", foreground=p["text"])
        self.batch_tree.tag_configure("status_paused", foreground=p["accent"])
        self.batch_tree.tag_configure("status_no_images", foreground=p["danger_text"])
        self.batch_tree.tag_configure("status_creating", foreground=p["primary"])
        self.batch_tree.tag_configure("status_uploading", foreground=p["primary"])
        self.batch_tree.tag_configure("status_publishing", foreground=p["accent2"])
        self.batch_tree.tag_configure("status_error", foreground=p["danger_text"])
        self.batch_tree.tag_configure("status_published", foreground=p["accent2"])
        self.batch_tree.tag_configure("status_draft_saved", foreground=p["text"])
        for widget_name, color_key in (
            ("batch_queue_accent_rail", "queue_rail"),
            ("batch_queue_summary_bar", "queue_heading"),
        ):
            widget = getattr(self, widget_name, None)
            if widget is not None:
                try:
                    widget.configure(fg_color=p[color_key])
                except Exception:
                    pass
        try:
            self.batch_tree_frame.configure(border_color=p["border_strong"])
            self.batch_preview_box.configure(border_color=p["border_strong"])
            self._log_frame.configure(border_color=p["border_strong"])
            self.main_split_grip.configure(bg=p["queue_rail"])
            self.right_split_grip.configure(bg=p["queue_rail"])
            self.batch_split_pane.configure(bg=p["root"])
            self.batch_preview_label.configure(border_color=p["border_strong"], fg_color=p["elev"], text_color=p["muted"])
            self.log_textbox.configure(border_color=p["border_strong"], fg_color=p["log"], text_color=p["muted"])
        except Exception:
            pass
        try:
            self.batch_queue_heading.configure(text_color=p["header_text"])
            self.batch_queue_glass_note.configure(text="Toolbar: defaults for new galleries · Select a row to edit its settings", text_color=p["header_subtext"])
            self.batch_inspector_heading.configure(text_color=p["header_text"])
            self._log_header_label.configure(text_color=p["header_text"])
            self._log_debug_label.configure(text_color=p["header_subtext"])
            self.batch_queue_counter.configure(text_color=p["queue_heading_text"])
            self.batch_queue_scroll_hint.configure(text_color=p["muted"])
        except Exception:
            pass

    def _build_credentials_frame(self):
        frame = ctk.CTkFrame(
            self, fg_color="#161616", border_width=0, corner_radius=0,
        )
        self.credentials_frame = frame
        frame.grid(row=1, column=0, columnspan=2, padx=0, pady=0, sticky="ew")

        for col in range(4):
            frame.grid_columnconfigure(col, weight=1, uniform="cred")
        frame.grid_columnconfigure(4, weight=0)
        frame.grid_columnconfigure(5, weight=0)

        self._credential_holders = []

        def field(col, label_key, placeholder_key, *, show=None):
            holder = ctk.CTkFrame(frame, fg_color="transparent", corner_radius=0)
            self._credential_holders.append(holder)
            holder.grid(row=0, column=col, padx=(12 if col == 0 else 4, 4), pady=8, sticky="ew")
            label = self._reg(
                ctk.CTkLabel(
                    holder, text="", anchor="w", height=14,
                    font=(self.input_font_family, 9), text_color="#9a9a9a",
                ),
                label_key,
            )
            label.pack(fill="x", pady=(0, 2))
            entry = ctk.CTkEntry(
                holder, placeholder_text="", show=show, font=self.small_input_font,
                height=30, corner_radius=0, fg_color="#0a0a0a",
                border_color="#2a2a2a", border_width=1,
            )
            self._reg(entry, placeholder_key, "placeholder_text")
            entry.pack(fill="x")
            self._bind_context_menu(entry)
            return entry

        self.member_id_entry = field(0, "cred_member_id", "cred_member_id_ph")
        self.pass_hash_entry = field(1, "cred_pass_hash", "cred_pass_hash_ph", show="*")
        self.igneous_entry = field(2, "cred_igneous", "cred_igneous_ph", show="*")

        cookie_holder = ctk.CTkFrame(frame, fg_color="transparent", corner_radius=0)
        self._credential_holders.append(cookie_holder)
        cookie_holder.grid(row=0, column=3, padx=4, pady=8, sticky="ew")
        ctk.CTkLabel(
            cookie_holder, text="COOKIE PATH", anchor="w", height=14,
            font=(self.input_font_family, 9), text_color="#9a9a9a",
        ).pack(fill="x", pady=(0, 2))
        self.cookie_file_entry = ctk.CTkEntry(
            cookie_holder, placeholder_text="", font=self.small_input_font,
            height=30, corner_radius=0, fg_color="#0a0a0a",
            border_color="#2a2a2a", border_width=1,
        )
        self._reg(self.cookie_file_entry, "cred_cookie_path_ph", "placeholder_text")
        self.cookie_file_entry.pack(fill="x")
        self._bind_context_menu(self.cookie_file_entry)

        self.use_ex_var = ctk.BooleanVar(value=False)
        self.use_ex_checkbox = self._reg(
            ctk.CTkCheckBox(
                frame, text="", variable=self.use_ex_var, width=96,
                checkbox_width=16, checkbox_height=16, corner_radius=0,
                fg_color="#f0f0f0", hover_color="#d0d0d0",
                checkmark_color="#0a0a0a", border_color="#3d3d3d",
            ),
            "cred_use_exhentai",
        )
        self.use_ex_checkbox.grid(row=0, column=4, padx=(8, 4), pady=(23, 8), sticky="s")

        # Retain this widget for old code but keep it out of the HTML row.  The
        # same command is available from File > Load Cookie File.
        self.cookie_load_btn = self._reg(
            ctk.CTkButton(frame, text="", width=1, height=1, command=self._load_cookie_export_path),
            "cred_load_cookie",
        )
        self.cookie_load_btn.grid_remove()

        self.validate_session_btn = self._reg(
            ctk.CTkButton(
                frame, text="", width=98, height=30, command=self._validate_session,
                fg_color="#1c1c1c", hover_color="#242424", border_width=1,
                border_color="#3d3d3d", corner_radius=0,
            ),
            "cred_validate_session",
        )
        self.validate_session_btn.grid(row=0, column=5, padx=(4, 12), pady=(23, 8), sticky="s")

    def _resolve_cookie_file(self):
        raw = self.cookie_file_entry.get().strip()

        if not raw:
            default_path = APP_DIR / "cookies.txt"
            return default_path if default_path.exists() else None

        candidate = Path(raw).expanduser()
        if candidate.is_dir():
            preferred_names = [
                "cookies.txt",
                "cookie.txt",
                "eh_cookies.txt",
                "e-hentai-cookies.txt",
                "exhentai-cookies.txt",
            ]
            for name in preferred_names:
                path = candidate / name
                if path.exists():
                    return path
            for child in sorted(candidate.iterdir()):
                if child.is_file() and child.suffix.lower() == ".txt":
                    return child
            return None

        if candidate.is_file():
            return candidate

        return None

    def _load_cookie_export_path(self):
        cookie_path = self._resolve_cookie_file()
        if not cookie_path:
            messagebox.showerror(
                self.tr("msg_cookie_not_found"),
                self.tr("msg_cookie_not_found_body"),
            )
            return

        try:
            self.cookie_file_entry.delete(0, "end")
            self.cookie_file_entry.insert(0, str(cookie_path))
            self._populate_credentials_from_cookie_file(cookie_path)
            self._save_config()
            self.log(f"Loaded cookie export from: {cookie_path}")
        except Exception as exc:
            self.log(f"Failed loading cookie export: {exc}")
            messagebox.showerror(self.tr("msg_cookie_error"), str(exc))

    def _populate_credentials_from_cookie_file(self, cookie_path):
        if not cookie_path:
            return

        try:
            with open(cookie_path, "r", encoding="utf-8", errors="replace") as handle:
                lines = handle.read().splitlines()
        except OSError as exc:
            raise RuntimeError(f"Could not read cookie export: {exc}") from exc

        values = {}
        for line in lines:
            line = line.strip()
            if not line or line.startswith("#"):
                continue

            if "\t" in line:
                parts = line.split("\t")
                if len(parts) >= 7:
                    name = parts[5].strip()
                    value = parts[6].strip()
                    if name:
                        values[name] = value
                continue

            if "=" in line and not line.startswith("http"):
                name, value = line.split("=", 1)
                name = name.strip()
                value = value.strip()
                if name:
                    values[name] = value

        def set_entry(entry_widget, key, default=""):
            value = values.get(key, default)
            if value:
                entry_widget.delete(0, "end")
                entry_widget.insert(0, value)

        set_entry(self.member_id_entry, "ipb_member_id")
        set_entry(self.pass_hash_entry, "ipb_pass_hash")
        set_entry(self.igneous_entry, "igneous")

        if not self.igneous_entry.get().strip() and values.get("igneous"):
            self.igneous_entry.insert(0, values["igneous"])

        if values.get("ipb_session_id"):
            self.log("[Debug] Loaded ipb_session_id from cookie export.")

    def _build_tab_view(self):
        self.tabs = None  # legacy CTkTabview intentionally removed
        self.tab_shell = ctk.CTkFrame(
            self.left_pane_frame, fg_color="#0a0a0a", corner_radius=0, border_width=0,
        )
        self.tab_shell.grid(row=0, column=0, sticky="nsew")
        self.tab_shell.grid_rowconfigure(1, weight=1)
        self.tab_shell.grid_columnconfigure(0, weight=1)

        self.app_tab_bar = ctk.CTkFrame(
            self.tab_shell, fg_color="#111111", corner_radius=0, height=42,
        )
        self.app_tab_bar.grid(row=0, column=0, sticky="ew")
        self.app_tab_bar.grid_propagate(False)

        self.batch_tab_btn = ctk.CTkButton(
            self.app_tab_bar, text=self.tr("tab_batch"), command=lambda: self._show_app_tab("batch"),
            width=160, height=34, corner_radius=0, fg_color="#0a0a0a",
            hover_color="#1c1c1c", text_color="#f0f0f0",
            border_width=1, border_color="#2a2a2a",
            font=(self.input_font_family, 11, "bold"),
        )
        self.batch_tab_btn.pack(side="left", padx=(10, 2), pady=(8, 0))

        self.single_tab_btn = ctk.CTkButton(
            self.app_tab_bar, text=self.tr("tab_single"), command=lambda: self._show_app_tab("single"),
            width=160, height=34, corner_radius=0, fg_color="transparent",
            hover_color="#1c1c1c", text_color="#9a9a9a", border_width=0,
            font=(self.input_font_family, 11),
        )
        self.single_tab_btn.pack(side="left", padx=2, pady=(8, 0))

        self.tab_content_host = ctk.CTkFrame(
            self.tab_shell, fg_color="#0a0a0a", corner_radius=0, border_width=0,
        )
        self.tab_content_host.grid(row=1, column=0, sticky="nsew")
        self.tab_content_host.grid_rowconfigure(0, weight=1)
        self.tab_content_host.grid_columnconfigure(0, weight=1)

        self.batch_tab = ctk.CTkFrame(self.tab_content_host, fg_color="#0a0a0a", corner_radius=0)
        self.single_tab = ctk.CTkFrame(self.tab_content_host, fg_color="#0a0a0a", corner_radius=0)
        self.batch_tab.grid(row=0, column=0, sticky="nsew")
        self.single_tab.grid(row=0, column=0, sticky="nsew")
        self.single_tab.grid_remove()

        self._active_tab_key = "batch"
        self._tab_labels["batch"] = self.tr("tab_batch")
        self._tab_labels["single"] = self.tr("tab_single")

        self._build_batch_tab()
        self._build_single_tab()
        self._update_custom_tab_styles()

    def _show_app_tab(self, key):
        key = 'single' if key == 'single' else 'batch'
        if key == getattr(self, '_active_tab_key', None):
            return
        self._active_tab_key = key
        if key == 'batch':
            self.single_tab.grid_remove()
            self.batch_tab.grid()
            if str(self.inspector_slot) not in tuple(map(str, self.main_vertical_pane.panes())):
                self.main_vertical_pane.add(self.inspector_slot, before=self.log_slot, minsize=220,
                                            height=self._right_top_target, stretch='always')
            if not self._log_expanded:
                self.main_vertical_pane.paneconfigure(self.log_slot, minsize=44, height=44)
        else:
            self.batch_tab.grid_remove()
            self.single_tab.grid()
            if str(self.inspector_slot) in tuple(map(str, self.main_vertical_pane.panes())):
                self._right_top_target = self.main_vertical_pane.sash_coord(0)[1]
                self.main_vertical_pane.forget(self.inspector_slot)
        self._update_custom_tab_styles()

    def _update_custom_tab_styles(self):
        active = getattr(self, "_active_tab_key", "batch")
        p = self._theme_palette()
        for key, btn in (
            ("batch", getattr(self, "batch_tab_btn", None)),
            ("single", getattr(self, "single_tab_btn", None)),
        ):
            if btn is None:
                continue
            try:
                if key == active:
                    btn.configure(
                        fg_color=p["root"], text_color=p["text"],
                        border_width=1, border_color=p["border_strong"],
                    )
                else:
                    btn.configure(
                        fg_color="transparent", text_color=p["muted"], border_width=0,
                    )
            except Exception:
                pass

    def _build_batch_tab(self):
        tab = self.batch_tab
        tab.grid_columnconfigure(0, weight=1)
        tab.grid_rowconfigure(0, weight=0)  # toolbar
        tab.grid_rowconfigure(1, weight=0)  # queue actions
        tab.grid_rowconfigure(2, weight=1)  # table + inspector

        # --------------------------- Toolbar ---------------------------
        toolbar = ctk.CTkFrame(tab, fg_color="#0a0a0a", corner_radius=0, border_width=0)
        self.batch_ctrl_frame = toolbar
        toolbar.grid(row=0, column=0, sticky="ew", padx=0, pady=0)

        self.add_folder_btn = ctk.CTkButton(
            toolbar, text="+ Folders", width=84, height=24,
            command=self._add_batch_folders,
            fg_color="#1c1c1c", hover_color="#242424",
            border_width=1, border_color="#3d3d3d", corner_radius=0,
            font=(self.input_font_family, 9),
        )
        self.add_root_btn = ctk.CTkButton(
            toolbar, text="+ Root", width=72, height=24,
            command=self._add_batch_root_dir,
            fg_color="#1c1c1c", hover_color="#242424",
            border_width=1, border_color="#3d3d3d", corner_radius=0,
            font=(self.input_font_family, 9),
        )
        self.add_archive_btn = ctk.CTkButton(
            toolbar, text="+ Archives", width=86, height=24,
            command=self._add_batch_archives,
            fg_color="#211f19", hover_color="#302a1d", text_color="#d7b86a",
            border_width=1, border_color="#6f5b2e", corner_radius=0,
            font=(self.input_font_family, 9),
        )
        self.batch_toolbar_sep = ctk.CTkFrame(
            toolbar, width=1, height=22, fg_color="#2a2a2a", corner_radius=0,
        )

        def make_select_group(label_key, values, width, *, command=None):
            group = ctk.CTkFrame(toolbar, fg_color="transparent", corner_radius=0)
            label = self._reg(
                ctk.CTkLabel(
                    group, text="", text_color="#9a9a9a",
                    font=(self.input_font_family, 9),
                ),
                label_key,
            )
            label.pack(side="left", padx=(0, 3))
            combo = ctk.CTkComboBox(
                group, values=values, width=width, height=26, command=command,
                fg_color="#1c1c1c", border_color="#2a2a2a",
                button_color="#1c1c1c", button_hover_color="#242424",
            )
            combo.pack(side="left")
            return group, combo

        self.batch_cat_group, self.batch_cat_combo = make_select_group(
            "lbl_cat", CATEGORIES, 96,
        )
        self.batch_lang_group, self.batch_lang_combo = make_select_group(
            "lbl_lang", ["Japanese", "No Text", "English"], 132,
        )
        self.batch_lang_combo.set("Japanese")

        self.batch_folder_group, self.batch_folder_combo = make_select_group(
            "lbl_folder", ["Unsorted"], 110,
        )
        self._bind_context_menu(self.batch_folder_combo)
        self.batch_folder_combo.set("Unsorted")

        self.batch_sort_group, self.batch_sort_combo = make_select_group(
            "lbl_sort", self._sort_values(), 124,
            command=lambda _: self._refresh_batch_preview(),
        )
        self.batch_sort_combo.set(self.tr("sort_natural"))

        self.batch_publish_var = ctk.BooleanVar(value=True)
        self.batch_publish_checkbox = self._reg(
            ctk.CTkCheckBox(
                toolbar, text="", variable=self.batch_publish_var,
                checkbox_width=16, checkbox_height=16, corner_radius=0,
            ),
            "chk_publish",
        )
        self.batch_unlisted_var = ctk.BooleanVar(value=False)
        self.batch_unlisted_checkbox = self._reg(
            ctk.CTkCheckBox(
                toolbar, text="", variable=self.batch_unlisted_var,
                checkbox_width=16, checkbox_height=16, corner_radius=0,
            ),
            "chk_unlisted",
        )

        # Old controls retained as hidden compatibility objects only.
        self.remove_selected_btn = ctk.CTkButton(toolbar, text="", width=1, height=1, command=self._remove_selected_batch)
        self.clear_all_btn = ctk.CTkButton(toolbar, text="", width=1, height=1, command=self._clear_batch_queue)
        self.batch_sync_toolbar_btn = self._reg(
            ctk.CTkButton(toolbar, text="", width=1, height=1, command=self._sync_server_form),
            "btn_sync_form",
        )

        self._batch_toolbar_widgets = [
            self.add_folder_btn, self.add_root_btn, self.add_archive_btn, self.batch_toolbar_sep,
            self.batch_cat_group, self.batch_lang_group, self.batch_folder_group,
            self.batch_sort_group, self.batch_publish_checkbox, self.batch_unlisted_checkbox,
        ]
        toolbar.bind("<Configure>", self._reflow_batch_toolbar, add="+")

        # ------------------------ Queue actions ------------------------
        actions = ctk.CTkFrame(tab, fg_color="#0a0a0a", corner_radius=0, border_width=0)
        self.batch_action_frame = actions
        actions.grid(row=1, column=0, sticky="ew", padx=0, pady=0)

        self.batch_queue_label = ctk.CTkLabel(
            actions, text="QUEUE", text_color="#d7b86a",
            font=(self.input_font_family, 9),
        )
        self.batch_action_sep = ctk.CTkFrame(
            actions, width=1, height=22, fg_color="#2a2a2a", corner_radius=0,
        )

        def muted_action(i18n_key, command):
            return self._reg(
                ctk.CTkButton(
                    actions, text="", command=command, width=82, height=24, corner_radius=0,
                    fg_color="#141414", hover_color="#242424", text_color="#9a9a9a",
                    border_width=1, border_color="#2a2a2a",
                    font=(self.input_font_family, 9),
                ),
                i18n_key,
            )

        self.batch_pause_selected_btn = muted_action("btn_pause_selected", self._pause_selected_batch)
        self.batch_resume_selected_btn = muted_action("btn_resume_selected", self._resume_selected_batch)
        self.batch_pause_all_btn = muted_action("btn_pause_all", self._pause_all_batch)
        self.batch_resume_all_btn = muted_action("btn_resume_all", self._resume_all_batch)
        self.batch_resume_queue_btn = ctk.CTkButton(
            actions, text="Resume Queue", command=self._resume_batch_queue,
            width=88, height=24, corner_radius=0, fg_color="#211f19", hover_color="#302a1d",
            text_color="#d7b86a", border_width=1, border_color="#7c6534",
            font=(self.input_font_family, 9, "bold"),
        )

        self.batch_remove_action_btn = ctk.CTkButton(
            actions, text="Remove Selected", command=self._remove_selected_batch,
            width=58, height=24, corner_radius=0, fg_color="#1b1711", hover_color="#2b2418",
            text_color="#d7b86a", border_width=1, border_color="#7c6534",
            font=(self.input_font_family, 9),
        )
        self.batch_clear_action_btn = ctk.CTkButton(
            actions, text="Clear All", command=self._clear_batch_queue,
            width=58, height=24, corner_radius=0, fg_color="#1b1711", hover_color="#2b2418",
            text_color="#d7b86a", border_width=1, border_color="#7c6534",
            font=(self.input_font_family, 9),
        )
        self.batch_sync_action_btn = self._reg(
            ctk.CTkButton(
                actions, text="", command=self._sync_server_form,
                width=58, height=24, corner_radius=0, fg_color="transparent", hover_color="#242424",
                text_color="#f0f0f0", border_width=1, border_color="#2a2a2a",
                font=(self.input_font_family, 9),
            ),
            "btn_sync_form",
        )
        self.batch_start_btn = self._reg(
            ctk.CTkButton(
                actions, text="", command=self._start_batch_upload,
                width=92, height=24, corner_radius=0, fg_color="#c6a65a", hover_color="#d5b86f",
                text_color="#090909", border_width=1, border_color="#c6a65a",
                font=(self.input_font_family, 10, "bold"),
            ),
            "btn_start_batch",
        )

        # Hidden compatibility control; Draft Preview remains accessible from the
        # queue right-click menu and is not part of the approved action strip.
        self.batch_preview_draft_btn = self._reg(
            ctk.CTkButton(actions, text="", command=self._show_selected_draft_preview, state="disabled"),
            "btn_view_draft_preview",
        )
        self.batch_preview_draft_btn.grid_remove()
        self.batch_dnd_hint_label = self._reg(
            ctk.CTkLabel(actions, text="", text_color="#666666"),
            "hint_dnd_on" if HAS_DND else "hint_dnd_off",
        )
        self.batch_dnd_hint_label.grid_remove()

        self._batch_action_widgets = [
            self.batch_pause_selected_btn, self.batch_resume_selected_btn,
            self.batch_pause_all_btn, self.batch_resume_all_btn, self.batch_resume_queue_btn,
            self.batch_remove_action_btn, self.batch_clear_action_btn,
            self.batch_sync_action_btn, self.batch_start_btn,
        ]
        actions.bind("<Configure>", self._reflow_batch_action_buttons, add="+")

        # ---------------------- Table + inspector ----------------------
        main_content = ctk.CTkFrame(tab, fg_color="#0a0a0a", corner_radius=0, border_width=0)
        self.batch_main_content = main_content
        main_content.grid(row=2, column=0, sticky="nsew", padx=0, pady=0)
        main_content.grid_rowconfigure(0, weight=1)
        main_content.grid_columnconfigure(0, weight=1)

        self.batch_split_pane = tk.PanedWindow(
            main_content, orient="horizontal", sashrelief="flat", sashwidth=0,
            showhandle=False, bd=0, bg="#090909",
        )
        self.batch_split_pane.grid(row=0, column=0, sticky="nsew")
        self._batch_inspector_sash_initialized = True
        self._batch_inspector_user_moved = False

        # Glass-like queue shell: a layered charcoal surface, crisp gold edge,
        # and patterned metal/glass header.  Tk does not offer per-widget alpha,
        # so the translucent effect is expressed with layered low-contrast tones.
        tree_frame = ctk.CTkFrame(
            self.batch_split_pane, fg_color="#171612", corner_radius=0,
            border_width=1, border_color="#6f5b2e",
        )
        self.batch_tree_frame = tree_frame
        tree_frame.grid_rowconfigure(2, weight=1)
        tree_frame.grid_columnconfigure(0, weight=0, minsize=3)
        tree_frame.grid_columnconfigure(1, weight=1)

        queue_header = ctk.CTkFrame(
            tree_frame, fg_color="#11100d", corner_radius=0, height=54, border_width=0,
        )
        self.batch_queue_header = queue_header
        queue_header.grid(row=0, column=0, columnspan=2, sticky="ew")
        queue_header.grid_propagate(False)
        queue_header.grid_columnconfigure(0, weight=1)
        self._install_theme_header_background(queue_header)
        self.batch_queue_heading = ctk.CTkLabel(
            queue_header, text="Gallery queue", height=24, anchor="w", text_color="#d7b86a",
            font=(self.input_font_family, 17, "bold"),
        )
        self.batch_queue_heading.grid(row=0, column=0, padx=12, pady=3, sticky="w")
        self.batch_queue_glass_note = ctk.CTkLabel(
            queue_header, text="Toolbar: defaults for new galleries · Select a row to edit its settings", height=16, anchor="w", text_color="#88764b",
            font=(self.input_font_family, 11),
        )
        self.batch_queue_glass_note.grid(row=1, column=0, padx=12, pady=(0, 5), sticky="w")
        self.batch_queue_reset_columns_btn = ctk.CTkButton(
            queue_header, text="Reset columns", width=100, height=28,
            command=self._reset_batch_tree_columns, font=(self.input_font_family, 11),
        )
        self.batch_queue_reset_columns_btn.grid(row=0, column=1, rowspan=2, padx=12, sticky="e")

        # A hard accent rail and telemetry ribbon make the queue read as a live
        # work surface instead of a stock table wrapped in a decorative box.
        self.batch_queue_accent_rail = ctk.CTkFrame(
            tree_frame, width=3, fg_color="#c6a65a", corner_radius=0, border_width=0,
        )
        self.batch_queue_accent_rail.grid(row=1, column=0, rowspan=2, sticky="ns")

        self.batch_queue_summary_bar = ctk.CTkFrame(
            tree_frame, height=34, fg_color="#201d15", corner_radius=0, border_width=0,
        )
        self.batch_queue_summary_bar.grid(row=1, column=1, sticky="ew")
        self.batch_queue_summary_bar.grid_propagate(False)
        self.batch_queue_summary_bar.grid_columnconfigure(1, weight=1)
        self.batch_queue_counter = ctk.CTkLabel(
            self.batch_queue_summary_bar, text="0 items", anchor="w",
            font=(self.input_font_family, 11, "bold"), text_color="#e0c46d",
        )
        self.batch_queue_counter.grid(row=0, column=0, padx=(9, 8), pady=2, sticky="w")
        self.batch_queue_scroll_hint = ctk.CTkLabel(
            tree_frame,
            text="Drag a heading to reorder · Drag its edge to resize · Double-click its edge to fit",
            anchor="w", font=(self.input_font_family, 11), text_color="#a89e86",
        )
        self.batch_queue_scroll_hint.grid(row=4, column=1, padx=12, pady=7, sticky="ew")

        columns = ("title_en", "title_jp", "image_count", "status", "path")
        self.batch_tree = ttk.Treeview(
            tree_frame, columns=columns, show="headings", selectmode="extended",
            style="Queue.Treeview",
        )
        self._apply_tree_headings()
        self._reset_batch_tree_columns()
        self.batch_tree.grid(row=2, column=1, sticky="nsew", padx=0, pady=0)
        self._configure_batch_queue_style(self._theme_palette())
        # Visible scrollbars keep long titles, paths and large queues reachable.
        self.batch_tree_vscroll = ttk.Scrollbar(tree_frame, orient="vertical", command=self.batch_tree.yview)
        self.batch_tree_hscroll = ttk.Scrollbar(tree_frame, orient="horizontal", command=self.batch_tree.xview)
        self.batch_tree.configure(yscrollcommand=self.batch_tree_vscroll.set, xscrollcommand=self.batch_tree_hscroll.set)
        self.batch_tree_vscroll.grid(row=2, column=2, sticky="ns")
        self.batch_tree_hscroll.grid(row=3, column=1, sticky="ew")
        self.batch_tree.bind("<MouseWheel>", self._on_batch_tree_mousewheel, add="+")
        self.batch_tree.bind("<Shift-MouseWheel>", self._on_batch_tree_shift_mousewheel, add="+")
        self.batch_tree.bind("<Button-4>", lambda e: (self.batch_tree.yview_scroll(-3, "units"), "break")[1], add="+")
        self.batch_tree.bind("<Button-5>", lambda e: (self.batch_tree.yview_scroll(3, "units"), "break")[1], add="+")
        self.batch_tree.bind("<Button-3>", self._on_batch_queue_right_click)
        self.batch_tree.bind("<<TreeviewSelect>>", lambda e: (self._refresh_batch_preview(), self._refresh_batch_queue_counter()))
        self._enable_batch_tree_column_reorder()

        # Queue stays on the left.  The inspector occupies the top-right rail;
        # the process console is built beneath it by _build_log_frame().
        self.batch_split_pane.add(tree_frame, minsize=620, stretch="always")

        preview_box = ctk.CTkFrame(
            self.inspector_slot, width=520, fg_color="#171612", corner_radius=0,
            border_width=1, border_color="#6f5b2e",
        )
        self.batch_preview_box = preview_box
        preview_box.grid(row=0, column=0, padx=0, pady=0, sticky="nsew")
        preview_box.grid_columnconfigure(0, weight=1)
        preview_box.grid_rowconfigure(0, weight=1)

        inspector = ctk.CTkScrollableFrame(preview_box, fg_color="#171612", corner_radius=0, border_width=0)
        self.batch_inspector_body = inspector
        inspector.grid(row=0, column=0, sticky="nsew")

        inspector_header = ctk.CTkFrame(
            inspector, fg_color="#11100d", corner_radius=0, height=44, border_width=0,
        )
        self.batch_inspector_header = inspector_header
        inspector_header.pack(fill="x", padx=0, pady=0)
        inspector_header.pack_propagate(False)
        self._install_onyx_gold_header_background(inspector_header)
        self.batch_inspector_heading = ctk.CTkLabel(
            inspector_header, text="COVER & TITLE", anchor="w", text_color="#d7b86a",
            font=(self.input_font_family, 10, "bold"),
        )
        self.batch_inspector_heading.pack(fill="x", padx=14, pady=4)
        self._build_batch_item_metadata_editor(inspector)

        # Larger 3:4 cover card; hover still opens the existing 50%-scale popup.
        self.batch_preview_label = ctk.CTkLabel(
            inspector, text=self.tr("cover_select_hint"), text_color="#a89e86",
            width=340, height=450, wraplength=320, anchor="center", compound="center",
            fg_color="#0d0d0c", border_width=1, border_color="#4c422c", corner_radius=0,
        )
        self.batch_preview_label.pack(padx=16, pady=(14, 10), anchor="n")
        self.batch_preview_label.bind("<Button-3>", self._on_batch_preview_right_click)
        self._bind_cover_hover(self.batch_preview_label, "batch_preview_path")

        edit_frame = ctk.CTkFrame(inspector, fg_color="transparent", corner_radius=0)
        self.batch_edit_frame = edit_frame
        edit_frame.pack(fill="x", padx=12, pady=(0, 10))

        self.batch_en_label = self._reg(
            ctk.CTkLabel(
                edit_frame, text="", anchor="w", text_color="#9a9a9a",
                font=(self.input_font_family, 10),
            ),
            "lbl_en_title",
        )
        self.batch_en_label.pack(fill="x", pady=(0, 2))
        self.batch_edit_en_entry = ctk.CTkEntry(
            edit_frame, font=self.input_font, height=30, corner_radius=0,
            fg_color="#0a0a0a", border_color="#2a2a2a", border_width=1,
        )
        self.batch_edit_en_entry.pack(fill="x", pady=(0, 7))

        self.batch_jp_label = self._reg(
            ctk.CTkLabel(
                edit_frame, text="", anchor="w", text_color="#9a9a9a",
                font=(self.input_font_family, 10),
            ),
            "lbl_jp_title",
        )
        self.batch_jp_label.pack(fill="x", pady=(0, 2))
        self.batch_edit_jp_entry = ctk.CTkEntry(
            edit_frame, font=self.input_font, height=30, corner_radius=0,
            fg_color="#0a0a0a", border_color="#2a2a2a", border_width=1,
        )
        self.batch_edit_jp_entry.pack(fill="x", pady=(0, 8))

        for widget in (self.batch_edit_en_entry, self.batch_edit_jp_entry):
            self._bind_context_menu(widget)
            widget.bind("<KeyRelease>", self._on_batch_title_edited)
            widget.bind("<FocusOut>", self._on_batch_title_edited)
            widget.configure(state="normal")

        title_actions = ctk.CTkFrame(edit_frame, fg_color="transparent", corner_radius=0)
        self.batch_title_action_row = title_actions
        title_actions.pack(fill="x", pady=(0, 4))
        for col in range(3):
            title_actions.grid_columnconfigure(col, weight=1, uniform="insp_action")

        self.batch_translate_btn = ctk.CTkButton(
            title_actions, text="Translate", height=24, width=1,
            font=(self.input_font_family, 9),
            command=lambda: self._translate_batch_title(),
        )
        self.batch_translate_btn.grid(row=0, column=0, padx=(0, 2), sticky="ew")

        self.batch_cover_title_btn = ctk.CTkButton(
            title_actions, text="Fetch", height=24, width=1,
            font=(self.input_font_family, 9),
            command=lambda: (
                self._fetch_titles_from_selected_source(
                    self.batch_queue_items.get(self.batch_tree.selection()[0], {}).get("path", "")
                    if self.batch_tree.selection() and self.batch_queue_items.get(self.batch_tree.selection()[0])
                    else "",
                    self.batch_edit_en_entry, self.batch_edit_jp_entry,
                    self.metadata_source_var.get(),
                )
                if self.batch_tree.selection()
                else messagebox.showwarning("No Selection", "Select a batch item first.", parent=self)
            ),
        )
        self.batch_cover_title_btn.grid(row=0, column=1, padx=2, sticky="ew")

        self.batch_fetch_metadata_btn = ctk.CTkButton(
            title_actions, text="E/Ex", height=24, width=1,
            font=(self.input_font_family, 9),
            command=lambda: self._search_ehentai_titles_from_japanese(
                self.batch_edit_jp_entry, self.batch_edit_en_entry,
            ),
        )
        self.batch_fetch_metadata_btn.grid(row=0, column=2, padx=(2, 0), sticky="ew")

        self.batch_metadata_source_combo = ctk.CTkComboBox(
            edit_frame, values=METADATA_SOURCES, variable=self.metadata_source_var,
            font=self.small_input_font, state="readonly", height=26,
            fg_color="#1c1c1c", border_color="#2a2a2a",
            button_color="#1c1c1c", button_hover_color="#242424",
        )
        self.batch_metadata_source_combo.pack(fill="x")

        self.after(60, self._reflow_batch_toolbar)
        self.after(80, self._reflow_batch_action_buttons)
        if self._dnd_available:
            try:
                self.batch_tree.drop_target_register(DND_FILES)
                self.batch_tree.dnd_bind("<<Drop>>", self._on_dnd_drop)
            except Exception as exc:
                self._dnd_available = False
                self._dnd_error = f"Could not register queue as a drop target: {exc}"
        if self._dnd_available:
            self.batch_queue_scroll_hint.configure(
                text="Drop folders or archives onto the queue · Drag headings to reorder or resize")
        else:
            self.batch_queue_scroll_hint.configure(
                text="Drag & drop unavailable; use Add Folder / Add Archives. See the console for details.")

    def _commit_batch_title_edit(self, event=None):
        """Persist Eng/Jap entry text to the row those entries currently belong to.

        Always targets ``_batch_edit_item_id`` (the row loaded into the editors),
        never the live tree selection.  That prevents the classic FocusOut race
        where clicking another folder first changes the selection and then
        writes the previous folder's titles into the newly selected row.
        """
        if getattr(self, "_batch_title_load_suppress", False):
            return
        try:
            row_id = getattr(self, "_batch_edit_item_id", None)
            if not row_id:
                selected = self.batch_tree.selection()
                if not selected:
                    return
                row_id = selected[0]
            item = self.batch_queue_items.get(row_id)
            if not isinstance(item, dict):
                return
            en_text = self._get_text_widget_value(self.batch_edit_en_entry)
            jp_text = self._get_text_widget_value(self.batch_edit_jp_entry)
            item["title_en"] = en_text
            item["title_jp"] = jp_text
            self.batch_queue_items[row_id] = item
            if self.batch_tree.exists(row_id):
                vals = list(self.batch_tree.item(row_id, "values"))
                while len(vals) < 5:
                    vals.append("")
                vals[0] = self._compose_title_cell(en_text, jp_text)
                vals[1] = jp_text
                self.batch_tree.item(row_id, values=vals)
            self._save_persistent_queue()
        except Exception:
            pass

    def _populate_batch_title_widgets(self, item, item_id=None):
        if not hasattr(self, "batch_edit_en_entry") or not hasattr(self, "batch_edit_jp_entry"):
            return
        if not isinstance(item, dict):
            return
        self._batch_title_load_suppress = True
        try:
            if item_id is not None:
                self._batch_edit_item_id = item_id
            for widget, value in (
                (self.batch_edit_en_entry, item.get("title_en", "")),
                (self.batch_edit_jp_entry, item.get("title_jp", "")),
            ):
                try:
                    if self._get_text_widget_value(widget) != str(value or "").strip():
                        self._set_text_widget_value(widget, value)
                except Exception:
                    pass
        finally:
            self._batch_title_load_suppress = False

    def _search_gallery_matches_by_text(self, query_text, max_pages=4):
        """Search E-Hentai/ExHentai by text and return the best direct gallery match."""
        query = str(query_text or "").strip()
        if not query:
            return {}

        # Keep all E/Ex HTTP behavior in the backend.  The previous GUI copy of
        # this routine referenced session methods that the GUI does not own.
        backend = EHentaiBackend(
            self._get_cookies(),
            log_fn=self.log,
            use_ex=self.use_ex_var.get(),
            cookie_file=str(self._resolve_cookie_file() or "cookies.txt"),
        )
        return backend._search_gallery_matches_by_text(query, max_pages=max_pages)

        # Legacy implementation retained below for source compatibility; the
        # backend return above is authoritative.
        try:
            self.ensure_tos_accepted()
        except Exception:
            pass

        bases = ["https://exhentai.org", "https://e-hentai.org"] if self.use_ex_var.get() else ["https://e-hentai.org"]
        seen = set()
        results = []

        for base in bases:
            for page_idx in range(max_pages):
                page = page_idx + 1
                url = f"{base}/?f_search={quote(query)}"
                if page > 1:
                    url = f"{url}&page={page - 1}"
                try:
                    resp = self.session.get(
                        url,
                        headers={
                            "Referer": f"{base}/",
                            "Accept": "text/html,application/xhtml+xml,application/xml;q=0.9,*/*;q=0.8",
                            "User-Agent": USER_AGENT,
                        },
                        timeout=30,
                        allow_redirects=True,
                    )
                    resp.raise_for_status()
                except Exception as exc:
                    self.log(f"[E/Ex text search] {base} page {page} failed: {exc}")
                    continue

                soup = BeautifulSoup(resp.text, "html.parser")
                for a in soup.select("a[href*='/g/']"):
                    href = (a.get("href") or "").strip()
                    if not href:
                        continue
                    match = re.search(r"/g/(\d+)/([^/?#]+)", href)
                    if not match:
                        continue
                    gallery_url = urljoin(resp.url, href.split("#", 1)[0])
                    if gallery_url in seen:
                        continue
                    seen.add(gallery_url)

                    title = ""
                    glink = a.find_parent(["div", "td", "tr", "li"])
                    if glink is not None:
                        for candidate in [glink.select_one("div.glink"), glink.select_one(".glink"), glink.select_one(".glname")]:
                            if candidate is not None:
                                title = candidate.get_text(" ", strip=True)
                                if title:
                                    break
                    if not title:
                        title = a.get_text(" ", strip=True)
                    title = re.sub(r"\s+", " ", str(title or "")).strip(" -")
                    if title and title.lower() not in {"next", "prev", "search", "show more"}:
                        results.append({"title": title, "url": gallery_url})

                low = " ".join(s for s in soup.stripped_strings if s).lower()
                if re.search(r"no results|no hits|nothing found", low, flags=re.I):
                    break
                if len(results) >= 12:
                    break
            if len(results) >= 12:
                break

        if not results:
            return {}

        best = results[0]
        try:
            metadata = self.fetch_gallery_title_metadata(best["url"])
            english = metadata.get("english") or [best["title"]]
            japanese = metadata.get("japanese") or [best["title"]]
            return {
                "title_en": english[0],
                "title_jp": japanese[0] if japanese else best["title"],
                "url": best["url"],
            }
        except Exception:
            return {"title_en": best["title"], "title_jp": best["title"], "url": best["url"]}

    def _search_ehentai_titles_from_japanese(self, jp_widget, en_widget):
        if jp_widget is None:
            return
        title_text = self._get_text_widget_value(jp_widget)
        if not title_text:
            messagebox.showinfo("E/Ex search", "Add a Japanese title first, then search E/Ex.", parent=self)
            return

        search_button = None
        if jp_widget is getattr(self, "batch_edit_jp_entry", None):
            search_button = getattr(self, "batch_fetch_metadata_btn", None)
        if search_button is not None:
            search_button.configure(state="disabled", text="Searching E/Ex…")

        def finish(result=None, error=None):
            if search_button is not None:
                search_button.configure(state="normal", text="Search E/Ex by Japanese title")
            if error is not None:
                self.log(f"[E/Ex] title search failed: {error}")
                messagebox.showerror("E/Ex search", f"Search failed:\n\n{error}", parent=self)
                return
            if not isinstance(result, dict) or not result:
                messagebox.showinfo("E/Ex search", f"No E/Ex match found for: {title_text}", parent=self)
                return
            self._set_entry_text(en_widget, result.get("title_en") or title_text)
            self._set_entry_text(jp_widget, result.get("title_jp") or title_text)
            if jp_widget is getattr(self, "batch_edit_jp_entry", None):
                self._commit_batch_title_edit()

        def worker():
            try:
                result = self._search_gallery_matches_by_text(title_text)
                self.after(0, lambda: finish(result=result))
            except Exception as exc:
                self.after(0, lambda exc=exc: finish(error=exc))

        threading.Thread(target=worker, daemon=True).start()

    def search_titles_from_cover_image(self, folder_path, title_en_entry=None, title_jp_entry=None):
        """Trigger cover image search and populate English and Japanese title widgets."""
        self._fetch_titles_from_selected_source(
            folder_path,
            title_en_entry,
            title_jp_entry,
            METADATA_SOURCES[0],
        )

    def _fetch_titles_from_selected_source(
        self,
        folder_or_image,
        title_en_entry=None,
        title_jp_entry=None,
        source=None,
    ):
        source = source if source in METADATA_SOURCES else METADATA_SOURCES[0]
        supplied_path = str(folder_or_image or "").strip()
        cover_path = supplied_path if os.path.isfile(supplied_path) else get_first_image_path(supplied_path)
        if not cover_path or not os.path.isfile(cover_path):
            messagebox.showwarning("No Cover Image", "No valid cover image found in the selected folder.", parent=self)
            return
        if source == METADATA_SOURCES[0]:
            self._open_cover_title_search_dialog(cover_path, title_en_entry, title_jp_entry)
            return
        if source == OCR_ALL_SOURCES_LABEL:
            self._fetch_titles_by_cover_ocr(cover_path, title_en_entry, title_jp_entry)
            return
        if source == GOOGLE_OCR_TITLE_LABEL:
            self._fetch_titles_by_google_ocr(cover_path, title_en_entry, title_jp_entry)
            return

        current_en = self._get_text_widget_value(title_en_entry)
        current_jp = self._get_text_widget_value(title_jp_entry)
        if os.path.isdir(supplied_path):
            folder_name = os.path.basename(os.path.normpath(supplied_path))
        else:
            folder_name = os.path.basename(os.path.dirname(os.path.abspath(supplied_path)))
        query_text = current_en or current_jp or folder_name
        if not query_text:
            messagebox.showinfo(
                f"{source} Search",
                f"Enter a title or choose a named gallery folder before searching {source}.",
                parent=self,
            )
            return
        backend = AlternateTitleMetadataBackend(source, query_text, log_fn=self.log)
        self._open_metadata_search_dialog(
            backend,
            cover_path,
            title_en_entry,
            title_jp_entry,
            source,
        )

    def _open_cover_title_search_dialog(self, cover_path, title_en_entry=None, title_jp_entry=None):
        """Open the non-blocking HappyPanda-style cover lookup for one image."""
        if not cover_path or not os.path.isfile(cover_path):
            messagebox.showwarning("No Cover Image", "No valid cover image was selected.", parent=self)
            return

        cookies = self._get_cookies()
        backend = EHentaiBackend(
            cookies,
            log_fn=self.log,
            use_ex=self.use_ex_var.get(),
            cookie_file=str(self._resolve_cookie_file() or "cookies.txt"),
        )

        self._open_metadata_search_dialog(
            backend,
            cover_path,
            title_en_entry,
            title_jp_entry,
            "E-Hentai / ExHentai",
        )

    def _fetch_titles_by_cover_ocr(self, cover_path, title_en_entry=None, title_jp_entry=None):
        """OCR the cover, then text-search E/Ex, nhentai and HentaiEra at once.

        The OCR pass runs first in a worker thread so a missing Tesseract
        install shows the usual installer prompt instead of a dialog error.
        Successful OCR is cached, so the dialog's search reuses it instantly.
        """
        if not cover_path or not os.path.isfile(cover_path):
            messagebox.showwarning("No Cover Image", "No valid cover image was selected.", parent=self)
            return
        self.log(f"[OCR Search] Reading cover text, then searching all sources: {cover_path}")

        def show_error(exc):
            message = str(exc)
            missing_ocr = "Tesseract is not installed" in message or "OCR is not available" in message
            if missing_ocr and not self._ocr_install_in_progress:
                self._ocr_install_prompted = True
                answer = messagebox.askyesno(
                    "Install OCR Support",
                    "Tesseract is required for cover-title OCR.\n\nInstall it now using the built-in installer?",
                    parent=self,
                )
                if answer:
                    self._install_tesseract_ocr()
                return
            messagebox.showwarning("Cover OCR Search", message, parent=self)

        def open_dialog():
            cookies = self._get_cookies()
            ehentai_backend = EHentaiBackend(
                cookies,
                log_fn=self.log,
                use_ex=self.use_ex_var.get(),
                cookie_file=str(self._resolve_cookie_file() or "cookies.txt"),
            )
            backend = OcrCoverTitleSearchBackend(
                ehentai_backend,
                ocr_fn=self._extract_cover_title_candidates,
                log_fn=self.log,
            )
            self._open_metadata_search_dialog(
                backend,
                cover_path,
                title_en_entry,
                title_jp_entry,
                OCR_ALL_SOURCES_LABEL,
            )

        def worker():
            try:
                jp_words, en_words = self._extract_cover_title_candidates(cover_path)
            except Exception as exc:
                self.after(0, lambda exc=exc: show_error(exc))
                return
            if not jp_words and not en_words:
                self.after(
                    0,
                    lambda: messagebox.showinfo(
                        "Cover OCR Search",
                        "No readable title text was found in that cover image.",
                        parent=self,
                    ),
                )
                return
            self.after(0, open_dialog)

        threading.Thread(target=worker, daemon=True).start()

    @staticmethod
    def _compose_ocr_google_query(jp_words, en_words, full_text=""):
        compact = re.sub(r"\s+", " ", str(full_text or "")).strip()
        if 3 <= len(compact) <= 160:
            return compact
        jp_title = max((str(word).strip() for word in jp_words or []), key=len, default="")
        en_title = max((str(word).strip() for word in en_words or []), key=len, default="")
        return re.sub(r"\s+", " ", " ".join(part for part in (jp_title, en_title) if part)).strip()

    def _fetch_titles_by_google_ocr(self, cover_path, title_en_entry=None, title_jp_entry=None):
        """OCR the cover with Windows OCR (Tesseract fallback), then Google-search the title."""
        if not cover_path or not os.path.isfile(cover_path):
            messagebox.showwarning("No Cover Image", "No valid cover image was selected.", parent=self)
            return
        self.log(f"[OCR Search] Reading cover title for Google search: {cover_path}")

        def show_error(exc):
            message = str(exc)
            missing_ocr = "Tesseract is not installed" in message or "OCR is not available" in message
            if missing_ocr and not self._ocr_install_in_progress:
                self._ocr_install_prompted = True
                answer = messagebox.askyesno(
                    "Install OCR Support",
                    "No Windows OCR text was found, and Tesseract is required as fallback.\n\nInstall Tesseract now?",
                    parent=self,
                )
                if answer:
                    self._install_tesseract_ocr()
                return
            messagebox.showwarning("Google Title Search", message, parent=self)

        def finish(jp_words, en_words, query, engine):
            jp_title = max((str(word).strip() for word in jp_words or []), key=len, default="")
            en_title = max((str(word).strip() for word in en_words or []), key=len, default="")
            if jp_title and title_jp_entry is not None:
                self._set_text_widget_value(title_jp_entry, jp_title)
            if en_title and title_en_entry is not None:
                self._set_text_widget_value(title_en_entry, en_title)
            if (
                title_en_entry is getattr(self, "batch_edit_en_entry", None)
                or title_jp_entry is getattr(self, "batch_edit_jp_entry", None)
            ):
                self._commit_batch_title_edit()
            edited = self._prompt_text_dialog(
                "Google Title Search",
                f"Title from {engine} OCR. Edit if needed, then OK to search Google.",
                query,
            )
            if edited is None:
                return
            edited = re.sub(r"\s+", " ", str(edited)).strip()
            if not edited:
                return
            url = "https://www.google.com/search?hl=en&q=" + quote(edited)
            self.log(f"[OCR Search] Google title search ({engine}): {edited}")
            self._browser_open_url("image", url, "Google Title Search")

        def worker():
            try:
                jp_words, en_words = self._extract_cover_title_candidates(cover_path)
            except Exception as exc:
                self.after(0, lambda exc=exc: show_error(exc))
                return
            cached = self._get_cached_cover_metadata(cover_path) or {}
            full_text = str(cached.get("full_text") or "")
            engine = str(cached.get("engine") or "ocr")
            query = self._compose_ocr_google_query(jp_words, en_words, full_text)
            if not query:
                self.after(
                    0,
                    lambda: messagebox.showinfo(
                        "Google Title Search",
                        "No readable title text was found in that cover image.",
                        parent=self,
                    ),
                )
                return
            self.after(0, lambda: finish(jp_words, en_words, query, engine))

        threading.Thread(target=worker, daemon=True).start()

    def _open_metadata_search_dialog(
        self,
        backend,
        cover_path,
        title_en_entry=None,
        title_jp_entry=None,
        source_label="Gallery Source",
    ):

        def apply_titles_callback(title_en, title_jp):
            if title_en_entry is not None:
                self._set_text_widget_value(title_en_entry, title_en or "")
            if title_jp_entry is not None:
                self._set_text_widget_value(title_jp_entry, title_jp or "")
            if (
                title_en_entry is getattr(self, "batch_edit_en_entry", None)
                or title_jp_entry is getattr(self, "batch_edit_jp_entry", None)
            ):
                self._commit_batch_title_edit()
            if title_en_entry is not None or title_jp_entry is not None:
                heading = "Applied Titles"
            else:
                heading = "Gallery Titles"
            messagebox.showinfo("Titles Updated", f"{heading}:\nEnglish: {title_en}\nJapanese: {title_jp}", parent=self)

        CoverImageTitleSearchDialog(
            parent=self,
            backend=backend,
            image_path=cover_path,
            on_select_callback=apply_titles_callback,
            source_label=source_label,
        )

    def _on_batch_tree_mousewheel(self, event):
        try:
            delta = int(getattr(event, "delta", 0))
            if not delta:
                return "break"
            steps = -max(-8, min(8, int(delta / 120)))
            self.batch_tree.yview_scroll(steps * 3, "units")
        except Exception:
            pass
        return "break"

    def _on_batch_tree_shift_mousewheel(self, event):
        try:
            delta = int(getattr(event, "delta", 0))
            if not delta:
                return "break"
            steps = -max(-8, min(8, int(delta / 120)))
            self.batch_tree.xview_scroll(steps * 3, "units")
        except Exception:
            pass
        return "break"

    def _refresh_batch_queue_counter(self):
        if not hasattr(self, "batch_tree") or not hasattr(self, "batch_queue_counter"):
            return
        try:
            items = self.batch_tree.get_children()
            total = len(items)
            active = 0
            done = 0
            paused = 0
            issues = 0
            for item_id in items:
                values = self.batch_tree.item(item_id, "values")
                status = self._status_key_from_display(values[3] if len(values) > 3 else "")
                if status in {"status_published", "status_draft_saved"}:
                    done += 1
                elif status == "status_paused":
                    paused += 1
                elif status in {"status_error", "status_no_images"}:
                    issues += 1
                elif status in {"status_creating", "status_uploading", "status_publishing"}:
                    active += 1
            self.batch_queue_counter.configure(
                text=f"{total} galleries  ·  {len(self.batch_tree.selection())} selected  ·  {active} active  ·  {paused} paused  ·  {issues} issues  ·  {done} done"
            )
        except Exception:
            pass

    def _batch_tree_display_column_from_id(self, col_id):
        try:
            idx = int(str(col_id).lstrip("#")) - 1
        except (TypeError, ValueError):
            return None
        cols = self.batch_tree.cget("displaycolumns")
        if cols == "#all" or tuple(cols) == ("#all",):
            cols = self.batch_tree.cget("columns")
        cols = tuple(cols)
        return cols[idx] if 0 <= idx < len(cols) else None

    def _enable_batch_tree_column_reorder(self):
        self._batch_tree_drag_col = None
        self._batch_tree_drag_active = False
        self._batch_tree_drop_marker = tk.Frame(self.batch_tree, width=3, bg=self._theme_palette()["primary"])
        self.batch_tree.bind("<ButtonPress-1>", self._on_batch_tree_heading_press, add="+")
        self.batch_tree.bind("<B1-Motion>", self._on_batch_tree_heading_motion, add="+")
        self.batch_tree.bind("<ButtonRelease-1>", self._on_batch_tree_heading_release, add="+")
        self.batch_tree.bind("<Escape>", self._cancel_batch_tree_heading_drag, add="+")
        self.batch_tree.bind("<Double-Button-1>", self._autofit_batch_tree_column, add="+")

    def _on_batch_tree_heading_press(self, event):
        self._cancel_batch_tree_heading_drag()
        # Let Tk own separator resizing and normal row selection.
        if self.batch_tree.identify_region(event.x, event.y) != "heading":
            return
        self._batch_tree_drag_col = self._batch_tree_display_column_from_id(self.batch_tree.identify_column(event.x))
        self._batch_tree_drag_origin = (event.x, event.y)
        self.batch_tree.focus_set()
        return "break"

    def _on_batch_tree_heading_release(self, event):
        active = getattr(self, "_batch_tree_drag_active", False)
        source = getattr(self, "_batch_tree_drag_col", None)
        target = self._batch_tree_drop_target(event.x) if active and 0 <= event.y <= self.batch_tree.winfo_height() else None
        if source and target:
            target_name, after, _marker_x = target
            cols = list(self._batch_tree_visible_columns())
            if source in cols and target_name in cols and source != target_name:
                cols.remove(source)
                cols.insert(cols.index(target_name) + int(after), source)
                self.batch_tree["displaycolumns"] = tuple(cols)
        self._cancel_batch_tree_heading_drag()
        if active:
            return "break"

    def _build_single_tab(self):
        tab = self.single_tab
        self.single_tab_root = tab
        tab.bind("<Configure>", self._queue_box_style_refresh, add="+")

        tab.grid_columnconfigure(
            1,
            weight=1,
        )

        self._reg(
            ctk.CTkLabel(
                tab,
                text="",
            ),
            "single_jp_title",
        ).grid(
            row=0,
            column=0,
            padx=5,
            pady=5,
            sticky="w",
        )

        self.single_jtitle_entry = ctk.CTkEntry(
            tab,
            width=720,
            font=self.input_font,
        )

        self.single_jtitle_entry.grid(
            row=0,
            column=1,
            padx=5,
            pady=5,
            sticky="ew",
        )

        self._bind_context_menu(
            self.single_jtitle_entry
        )

        self.single_translate_btn = ctk.CTkButton(
            tab,
            text="Translate JPN → ENG",
            width=180,
            height=28,
            command=lambda: self._translate_single_title(),
        )
        self.single_translate_btn.grid(
            row=0,
            column=2,
            padx=(0, 8),
            pady=5,
            sticky="w",
        )

        self._reg(
            ctk.CTkLabel(
                tab,
                text="",
            ),
            "single_en_title",
        ).grid(
            row=1,
            column=0,
            padx=5,
            pady=5,
            sticky="w",
        )

        self.single_etitle_entry = ctk.CTkEntry(
            tab,
            width=720,
            font=self.input_font,
        )

        self.single_etitle_entry.grid(
            row=1,
            column=1,
            padx=5,
            pady=5,
            sticky="ew",
        )

        self._bind_context_menu(
            self.single_etitle_entry
        )

        single_metadata_frame = ctk.CTkFrame(tab, fg_color="transparent")
        single_metadata_frame.grid(row=1, column=2, padx=(0, 8), pady=5, sticky="w")
        self.single_metadata_source_combo = ctk.CTkComboBox(
            single_metadata_frame,
            values=METADATA_SOURCES,
            variable=self.metadata_source_var,
            width=230,
            font=self.small_input_font,
            state="readonly",
        )
        self.single_metadata_source_combo.pack(side="left", padx=(0, 6))
        self.single_cover_title_btn = ctk.CTkButton(
            single_metadata_frame,
            text="Fetch Titles",
            width=110,
            height=28,
            command=lambda: self._fetch_titles_from_selected_source(
                self.single_folder_entry.get().strip(),
                self.single_etitle_entry,
                self.single_jtitle_entry,
                self.metadata_source_var.get(),
            ),
        )
        self.single_cover_title_btn.pack(side="left")

        self._reg(
            ctk.CTkLabel(
                tab,
                text="",
            ),
            "single_category",
        ).grid(
            row=2,
            column=0,
            padx=5,
            pady=5,
            sticky="w",
        )

        self.single_cat_combo = ctk.CTkComboBox(
            tab,
            values=CATEGORIES,
        )

        self.single_cat_combo.grid(
            row=2,
            column=1,
            padx=5,
            pady=5,
            sticky="w",
        )

        self._reg(
            ctk.CTkLabel(
                tab,
                text="",
            ),
            "single_language",
        ).grid(
            row=3,
            column=0,
            padx=5,
            pady=5,
            sticky="w",
        )

        self.single_lang_combo = ctk.CTkComboBox(
            tab,
            values=["Japanese", "No Text", "English"],
            width=220,
        )

        self.single_lang_combo.set(
            "Japanese"
        )

        self.single_lang_combo.grid(
            row=3,
            column=1,
            padx=5,
            pady=5,
            sticky="w",
        )

        self._reg(
            ctk.CTkLabel(
                tab,
                text="",
            ),
            "single_gallery_folder",
        ).grid(
            row=4,
            column=0,
            padx=5,
            pady=5,
            sticky="w",
        )

        self.single_folder_combo = ctk.CTkComboBox(
            tab,
            values=["Unsorted"],
            width=220,
        )

        self._bind_context_menu(
            self.single_folder_combo,
        )

        self.single_folder_combo.set(
            "Unsorted"
        )

        self.single_folder_combo.grid(
            row=4,
            column=1,
            padx=5,
            pady=5,
            sticky="w",
        )

        self._reg(
            ctk.CTkLabel(
                tab,
                text="",
            ),
            "single_sort_order",
        ).grid(
            row=5,
            column=0,
            padx=5,
            pady=5,
            sticky="w",
        )

        self.single_sort_combo = ctk.CTkComboBox(
            tab,
            values=self._sort_values(),
            command=lambda _: self._refresh_single_preview(),
        )
        self.single_sort_combo.set(self.tr("sort_natural"))

        self.single_sort_combo.grid(
            row=5,
            column=1,
            padx=5,
            pady=5,
            sticky="w",
        )

        self._reg(
            ctk.CTkLabel(
                tab,
                text="",
            ),
            "single_image_folder",
        ).grid(
            row=6,
            column=0,
            padx=5,
            pady=5,
            sticky="w",
        )

        folder_frame = ctk.CTkFrame(
            tab,
            fg_color="transparent",
        )

        folder_frame.grid(
            row=6,
            column=1,
            padx=5,
            pady=5,
            sticky="ew",
        )

        folder_frame.grid_columnconfigure(
            0,
            weight=1,
        )

        self.single_folder_entry = ctk.CTkEntry(
            folder_frame,
            font=self.input_font,
        )

        self.single_folder_entry.grid(
            row=0,
            column=0,
            sticky="ew",
            padx=(0, 5),
        )

        self._bind_context_menu(
            self.single_folder_entry
        )

        self._reg(
            ctk.CTkButton(
                folder_frame,
                text="",
                width=80,
                command=self._browse_single_folder,
            ),
            "btn_browse",
        ).grid(
            row=0,
            column=1
        )

        ctk.CTkButton(
            folder_frame,
            text="Rename",
            width=82,
            command=lambda: self._rename_folder_path_widget(self.single_folder_entry),
        ).grid(
            row=0,
            column=2,
            padx=(4, 0),
        )

        opts_frame = ctk.CTkFrame(
            tab,
            fg_color="transparent",
        )

        opts_frame.grid(
            row=7,
            column=1,
            padx=5,
            pady=5,
            sticky="w",
        )

        self.single_publish_var = ctk.BooleanVar(
            value=True
        )

        self._reg(
            ctk.CTkCheckBox(
                opts_frame,
                text="",
                variable=self.single_publish_var,
            ),
            "chk_autopublish",
        ).pack(
            side="left",
            padx=(0, 15),
        )

        self.single_unlisted_var = ctk.BooleanVar(
            value=False
        )

        self._reg(
            ctk.CTkCheckBox(
                opts_frame,
                text="",
                variable=self.single_unlisted_var,
            ),
            "chk_unlisted_gallery",
        ).pack(
            side="left"
        )

        classification = ctk.CTkFrame(tab, fg_color="transparent")
        classification.grid(row=7, column=2, sticky="w", padx=8, pady=5)
        ctk.CTkLabel(classification, text="Language type", anchor="w",
                     font=self.small_input_font).pack(fill="x")
        self.single_language_type_combo = ctk.CTkComboBox(
            classification, values=["Official / Textless", "Translated", "Rewrite"],
            width=240, height=30, state="readonly", font=self.input_font,
            command=lambda _value: self._save_config())
        self.single_language_type_combo.pack(fill="x", pady=(0, 7))
        self.single_language_type_combo.set("Official / Textless")
        self.single_ai_var = tk.BooleanVar(value=False)
        self.single_ai_checkbox = ctk.CTkCheckBox(
            classification, text="Primarily AI-generated artwork/images",
            variable=self.single_ai_var, font=self.small_input_font,
            command=self._save_config)
        self.single_ai_checkbox.pack(anchor="w")

        self.single_preview_frame = ctk.CTkFrame(
            tab,
            height=260,
        )

        self.single_preview_frame.grid(
            row=8,
            column=1,
            padx=5,
            pady=10,
            sticky="w",
        )

        self.single_preview_label = ctk.CTkLabel(
            self.single_preview_frame,
            text=self.tr("single_no_folder"),
            text_color="gray",
            width=220,
            height=220,
            wraplength=220,
            anchor="center",
        )

        self.single_preview_label.pack(
            padx=10,
            pady=10,
        )
        self.single_preview_label.bind("<Button-3>", self._on_single_preview_right_click)
        self._bind_cover_hover(self.single_preview_label, "single_preview_path")

        self.single_fetch_metadata_btn = ctk.CTkButton(
            self.single_preview_frame,
            text="Search E/Ex by Japanese title",
            width=220,
            height=28,
            command=lambda: self._search_ehentai_titles_from_japanese(
                self.single_jtitle_entry,
                self.single_etitle_entry,
            ),
        )
        self.single_fetch_metadata_btn.pack(padx=10, pady=(0, 10))

        self.single_start_btn = self._reg(
            ctk.CTkButton(
                tab,
                text="",
                command=self._start_single_upload,
                fg_color="#f0f0f0",
                hover_color="#d8d8d8",
                text_color="#0a0a0a",
                height=35,
            ),
            "btn_create_upload",
        )

        self.single_start_btn.grid(
            row=9,
            column=1,
            padx=5,
            pady=10,
            sticky="w",
        )

        self._queue_box_style_refresh()

    def _build_log_frame(self):
        log_frame = ctk.CTkFrame(
            self.log_slot, fg_color="#0c0c0b", corner_radius=0,
            border_width=1, border_color="#6f5b2e", width=520,
        )
        self._log_frame = log_frame
        log_frame.grid(row=0, column=0, padx=0, pady=0, sticky="nsew")
        log_frame.grid_columnconfigure(0, weight=1)
        log_frame.grid_rowconfigure(1, weight=1)

        header = ctk.CTkFrame(log_frame, fg_color="#11100d", corner_radius=0, height=44)
        self._log_header_frame = header
        header.grid(row=0, column=0, sticky="ew")
        header.grid_propagate(False)
        header.grid_columnconfigure(0, weight=1)
        self._install_onyx_gold_header_background(header)
        self._log_header_label = self._reg(
            ctk.CTkLabel(
                header, text="", cursor="hand2", anchor="w",
                font=(self.input_font_family, 9, "bold"), text_color="#d7b86a",
            ),
            "log_title",
        )
        self._log_header_label.grid(row=0, column=0, padx=14, pady=4, sticky="w")
        self._log_header_label.bind("<Button-1>", lambda e: self._toggle_log_panel())
        self._log_debug_label = ctk.CTkLabel(
            header, text="Debug off", font=(self.input_font_family, 9), text_color="#88764b",
        )
        self._log_debug_label.grid(row=0, column=1, padx=14, pady=4, sticky="e")

        self.log_textbox = ctk.CTkTextbox(
            log_frame, font=("Consolas", 10), wrap="word",
            fg_color="#080807", border_width=1, border_color="#4d4229",
            corner_radius=0, text_color="#cdbf9a",
        )
        self.log_textbox.grid(row=1, column=0, padx=10, pady=(8, 10), sticky="nsew")
        self._bind_context_menu(self.log_textbox)

    def _status_key_from_display(self, value):
        text = str(value or "").strip()
        icon_lookup = {
            "!": "status_queued",
            "||": "status_paused",
            "..": "status_creating",
            "^^": "status_uploading",
            "!!": "status_publishing",
            "OK": "status_published",
            "DR": "status_draft_saved",
            "X": "status_error",
        }
        if text in icon_lookup:
            return icon_lookup[text]
        for key in (
            "status_queued",
            "status_paused",
            "status_no_images",
            "status_creating",
            "status_uploading",
            "status_publishing",
            "status_published",
            "status_draft_saved",
            "status_error",
        ):
            entry = TRANSLATIONS.get(key, {})
            if text and any(text == str(v).strip() for v in entry.values()):
                return key
        low = text.lower()
        if "published" in low or "公開済み" in text or "已发布" in text:
            return "status_published"
        if "draft" in low or "ドラフト" in text or "草稿" in text:
            return "status_draft_saved"
        if "upload" in low or "アップロード" in text or "上传" in text:
            return "status_uploading"
        if "publish" in low or "公開中" in text or "发布" in text:
            return "status_publishing"
        if "pause" in low or "paused" in low or "一時停止" in text:
            return "status_paused"
        if "no image" in low or "画像が見つかりません" in text:
            return "status_no_images"
        if "error" in low or "エラー" in text or "错误" in text:
            return "status_error"
        return "status_queued"

    def _queue_status_display(self, status_key):
        key = status_key if status_key in TRANSLATIONS else "status_queued"
        return self.tr(key)

    def _folder_mtime_ns(self, path):
        try:
            return int(os.stat(path).st_mtime_ns)
        except Exception:
            return 0

    def _persistent_queue_records(self):
        records = []
        with self._queue_state_lock:
            for item_id in self.batch_tree.get_children():
                item = self.batch_queue_items.get(item_id)
                if not item:
                    continue
                values = self.batch_tree.item(item_id, "values")
                status_display = values[3] if len(values) > 3 else self._queue_status_display("status_queued")
                status_key = self._status_key_from_display(status_display)
                # A process cannot safely be resumed mid-request after the GUI closes.
                # Requeue transient work, but preserve completed drafts/published rows.
                if status_key in {"status_creating", "status_uploading", "status_publishing"}:
                    status_key = "status_queued"
                image_count = 0
                if len(values) > 2:
                    try:
                        image_count = int(values[2])
                    except Exception:
                        image_count = 0
                folder_path = str(item.get("path", ""))
                records.append({
                    "path": folder_path,
                    "title_en": str(item.get("title_en", "")),
                    "title_jp": str(item.get("title_jp", "")),
                    **self._batch_item_metadata(item),
                    "upload_resume": dict(item.get("upload_resume") or {}),
                    "status": status_key,
                    "image_count": image_count,
                    "mtime_ns": self._folder_mtime_ns(folder_path),
                })
        return records

    def _save_persistent_queue(self, force=False):
        now = time.monotonic()
        if not force and now - self._last_queue_save_ts < 0.25:
            return
        self._last_queue_save_ts = now
        try:
            payload = {
                "version": 1,
                "saved_at": time.time(),
                "items": self._persistent_queue_records(),
            }
            tmp = QUEUE_STATE_FILE.with_suffix(QUEUE_STATE_FILE.suffix + ".tmp")
            with self._queue_state_lock:
                with open(tmp, "w", encoding="utf-8") as fh:
                    json.dump(payload, fh, ensure_ascii=False, indent=2)
                os.replace(tmp, QUEUE_STATE_FILE)
        except Exception as exc:
            self.log(f"[Queue] Failed to save persistent queue: {exc}")

    def _load_persistent_queue(self):
        if not QUEUE_STATE_FILE.exists():
            return
        try:
            with open(QUEUE_STATE_FILE, "r", encoding="utf-8") as fh:
                payload = json.load(fh)
            items = payload.get("items", []) if isinstance(payload, dict) else []
            if not isinstance(items, list):
                return

            existing_paths = {d.get("path") for d in self.batch_queue_items.values() if isinstance(d, dict)}

            restored = 0
            for record in items:
                if not isinstance(record, dict):
                    continue
                folder_path = os.path.abspath(str(record.get("path", "")).strip())
                if not folder_path:
                    continue
                if folder_path in existing_paths:
                    continue

                title_en = str(record.get("title_en") or os.path.basename(folder_path))
                title_jp = str(record.get("title_jp") or "")
                status_key = str(record.get("status") or "status_queued")
                if status_key not in TRANSLATIONS:
                    status_key = "status_queued"
                if status_key in {"status_creating", "status_uploading", "status_publishing"}:
                    status_key = "status_queued"

                img_count = 0
                source_exists = os.path.isdir(folder_path) or (
                    os.path.isfile(folder_path) and folder_path.lower().endswith(ARCHIVE_EXTENSIONS)
                )
                if source_exists:
                    # The queue file is a UI/state cache, not an authority for
                    # filesystem contents. Folder timestamps can be preserved by
                    # OCR/rename/copy workflows, so always rebuild this cheap
                    # display count when restoring a queue.
                    img_count = count_images_in_folder(folder_path)
                if not source_exists:
                    status_key = "status_error"
                elif img_count == 0 and status_key not in {"status_published", "status_draft_saved"}:
                    status_key = "status_no_images"

                item_id = self.batch_tree.insert(
                    "",
                    "end",
                    values=(
                        self._compose_title_cell(title_en, title_jp),
                        title_jp,
                        img_count,
                        self._queue_status_display(status_key),
                        folder_path,
                    ),
                    tags=(
                        "queue_even" if len(self.batch_tree.get_children()) % 2 == 0 else "queue_odd",
                        status_key,
                    ),
                )
                self.batch_queue_items[item_id] = {
                    "path": folder_path,
                    "title_en": title_en,
                    "title_jp": title_jp,
                    **self._batch_item_metadata(record),
                    "upload_resume": dict(record.get("upload_resume") or {}),
                }
                existing_paths.add(folder_path)
                restored += 1

            if restored:
                self.log(f"[Queue] Restored {restored} queued folder(s) from disk.")
                self._refresh_batch_preview()
                self._refresh_batch_queue_counter()
        except Exception as exc:
            self.log(f"[Queue] Failed to restore persistent queue: {exc}")

    def _load_config(self):
        if HARDCODED_MEMBER_ID:
            self.member_id_entry.insert(
                0,
                HARDCODED_MEMBER_ID,
            )

        if HARDCODED_PASS_HASH:
            self.pass_hash_entry.insert(
                0,
                HARDCODED_PASS_HASH,
            )

        if HARDCODED_IGNEOUS:
            self.igneous_entry.insert(
                0,
                HARDCODED_IGNEOUS,
            )

        if not CONFIG_FILE.exists():
            return

        try:
            with open(
                CONFIG_FILE,
                "r",
                encoding="utf-8",
            ) as f:
                data = json.load(f)

            cached_schema = data.get("creation_options")
            if isinstance(cached_schema, dict) and cached_schema:
                self._creation_schema = cached_schema
                self._populate_gui_from_schema(cached_schema)
            language_type = data.get("single_language_type", "Official / Textless")
            if language_type in {"Official / Textless", "Translated", "Rewrite"}:
                self.single_language_type_combo.set(language_type)
            self.single_ai_var.set(data.get("single_ai_generated", False) is True)
            saved_translation = data.get("translation_settings")
            if isinstance(saved_translation, dict):
                for key in self.translation_settings:
                    if key in saved_translation:
                        self.translation_settings[key] = str(saved_translation.get(key) or "")

            # Language / debug / speed settings are restored first so tr()
            # and the spinbox vars reflect the saved state before the rest.
            if "language" in data and data["language"] in [c for c, _ in LANGUAGES]:
                self.lang_code = data["language"]

            if "theme" in data:
                saved_theme = str(data.get("theme") or "dark").lower()
                # 2q gives every theme its own visual identity, so preserve a
                # valid saved choice across build upgrades instead of resetting it.
                if saved_theme in {"dark", "ehentai", "winter"}:
                    self._ui_theme = saved_theme
                else:
                    self._ui_theme = "dark"

            if "box_style" in data:
                saved_style = str(data.get("box_style") or "balanced").lower()
                if saved_style in BOX_STYLE_PRESETS:
                    self._box_style = saved_style
                    try:
                        self._box_style_var.set(saved_style)
                    except Exception:
                        pass

            if "debug_enabled" in data:
                try:
                    self.debug_enabled.set(bool(data["debug_enabled"]))
                except Exception:
                    pass

            if "upload_batch_size" in data:
                try:
                    self.batch_size_var.set(max(1, min(UPLOAD_MAX_REQUEST_FILES, int(data["upload_batch_size"]))))
                except Exception:
                    pass

            if "upload_workers" in data:
                try:
                    self.workers_var.set(max(1, min(UPLOAD_MAX_WORKERS, int(data["upload_workers"]))))
                except Exception:
                    pass

            if "upload_delay" in data:
                try:
                    self.delay_var.set(float(data["upload_delay"]))
                except Exception:
                    pass

            if "open_automation_result_in_app" in data:
                try:
                    self.open_automation_result_in_app_var.set(bool(data["open_automation_result_in_app"]))
                except Exception:
                    pass

            if data.get("member_id"):
                self.member_id_entry.delete(
                    0,
                    "end",
                )

                self.member_id_entry.insert(
                    0,
                    data["member_id"],
                )

            if data.get("pass_hash"):
                self.pass_hash_entry.delete(
                    0,
                    "end",
                )

                self.pass_hash_entry.insert(
                    0,
                    data["pass_hash"],
                )

            if data.get("igneous"):
                self.igneous_entry.delete(
                    0,
                    "end",
                )

                self.igneous_entry.insert(
                    0,
                    data["igneous"],
                )

            if "cookie_file" in data and data["cookie_file"]:
                self.cookie_file_entry.delete(0, "end")
                self.cookie_file_entry.insert(0, data["cookie_file"])
                try:
                    cookie_path = Path(data["cookie_file"]).expanduser()
                    if cookie_path.exists():
                        self._populate_credentials_from_cookie_file(cookie_path)
                except Exception:
                    pass

            if "use_ex" in data:
                self.use_ex_var.set(
                    data["use_ex"]
                )

            saved_source = str(data.get("metadata_source") or "")
            if saved_source in METADATA_SOURCES:
                self.metadata_source_var.set(saved_source)

            if (
                "batch_category" in data
                and data["batch_category"] in CATEGORIES
            ):
                self.batch_cat_combo.set(
                    data["batch_category"]
                )

            if "batch_language" in data:
                self.batch_lang_combo.set(
                    data["batch_language"]
                )

            if "batch_folder" in data:
                self.batch_folder_combo.set(
                    data["batch_folder"]
                )

            if "batch_sort" in data:
                sort_key = self._sort_display_to_key(data["batch_sort"])
                self.batch_sort_combo.set(
                    self.tr(SORT_I18N.get(sort_key, "sort_natural"))
                )

            if "batch_publish" in data:
                self.batch_publish_var.set(
                    data["batch_publish"]
                )

            if "batch_unlisted" in data:
                self.batch_unlisted_var.set(
                    data["batch_unlisted"]
                )

            layout_state = data.get("layout", {})
            self.after(160, lambda s=layout_state: self._apply_layout_state(s))
            self.after(200, self._queue_box_style_refresh)
            if self._get_cookies() or self._resolve_cookie_file():
                self.after(1200, self._sync_server_form)

            self.log(
                "Loaded configuration."
            )

        except Exception as e:
            self.log(
                f"Failed loading saved configuration: {e}"
            )

    def _save_config(self):
        # Spinboxes also allow typed input: normalize before saving.
        try:
            workers = max(1, min(UPLOAD_MAX_WORKERS, int(self.workers_var.get())))
        except (TypeError, ValueError, tk.TclError):
            workers = UPLOAD_MAX_WORKERS
        self.workers_var.set(workers)
        data = {
            "member_id": self.member_id_entry.get().strip(),
            "pass_hash": self.pass_hash_entry.get().strip(),
            "igneous": self.igneous_entry.get().strip(),
            "cookie_file": self.cookie_file_entry.get().strip(),
            "use_ex": self.use_ex_var.get(),
            "language": self.lang_code,
            "debug_enabled": self.debug_enabled.get(),
            "theme": self._ui_theme,
            "ui_build_id": UI_BUILD_ID,
            "box_style": self._box_style,
            "upload_batch_size": self.batch_size_var.get(),
            "upload_workers": workers,
            "upload_delay": self.delay_var.get(),
            "open_automation_result_in_app": self.open_automation_result_in_app_var.get(),
            "metadata_source": self.metadata_source_var.get(),
            "batch_category": self.batch_cat_combo.get(),
            "batch_language": self.batch_lang_combo.get().strip(),
            "batch_folder": self.batch_folder_combo.get().strip(),
            # Store the stable internal sort key so it survives language changes.
            "batch_sort": self._sort_display_to_key(self.batch_sort_combo.get()),
            "batch_publish": self.batch_publish_var.get(),
            "batch_unlisted": self.batch_unlisted_var.get(),
            "translation_settings": dict(self.translation_settings),
            "single_language_type": self.single_language_type_combo.get(),
            "single_ai_generated": bool(self.single_ai_var.get()),
            "creation_options": {
                key: {"name": value.get("name"), "options": value.get("options", [])}
                for key, value in getattr(self, "_creation_schema", {}).items()
                if key in {"category", "lang", "folder"} and isinstance(value, dict)
            },
            "layout": self._get_layout_state(),
        }

        try:
            with open(
                CONFIG_FILE,
                "w",
                encoding="utf-8",
            ) as f:
                json.dump(
                    data,
                    f,
                    indent=4,
                )

            cookie_path = APP_DIR / "cookies.txt"
            if not cookie_path.exists() and self._get_cookies():
                cookies = self._get_cookies()
                with open(cookie_path, "w", encoding="utf-8", newline="") as fh:
                    for key, value in sorted(cookies.items()):
                        domain = ".e-hentai.org"
                        if key == "igneous":
                            domain = ".exhentai.org" if self.use_ex_var.get() else ".e-hentai.org"
                        fh.write(
                            f"{domain}\tTRUE\t/\tFALSE\t0\t{key}\t{value}\n"
                        )
            elif cookie_path.exists():
                self.log(
                    "[Debug] Preserved the existing cookies.txt; not overwriting with manual GUI values."
                )

        except Exception as e:
            self.log(
                f"Failed to save configuration: {e}"
            )

    def _on_closing(self):
        try:
            timer = getattr(self, "_cache_save_timer", None)
            if timer is not None:
                timer.cancel()
            self._save_startup_cache()
        except Exception:
            pass
        for proc in getattr(self, "_qt_browser_processes", {}).values():
            try:
                if proc is not None and proc.poll() is None:
                    proc.terminate()
            except Exception:
                pass
        self._close_image_search_browsers(show_message=False)
        self._save_persistent_queue(force=True)
        self._save_config()
        self.destroy()

    def _bind_cover_hover(self, label, path_attribute):
        """Show the label's current cover at 50% scale while it is hovered."""
        label.bind(
            "<Enter>",
            lambda event, attr=path_attribute: self._schedule_cover_hover(event, attr),
            add="+",
        )
        label.bind("<Leave>", self._hide_cover_hover, add="+")

    def _schedule_cover_hover(self, event, path_attribute):
        self._hide_cover_hover()
        image_path = getattr(self, path_attribute, None)
        if not image_path or not os.path.isfile(image_path):
            return

        # A short delay keeps the popup from flashing while the pointer merely
        # crosses the cover on its way to the title controls.
        pointer_x = int(getattr(event, "x_root", self.winfo_pointerx()))
        pointer_y = int(getattr(event, "y_root", self.winfo_pointery()))
        self._cover_hover_after_id = self.after(
            140,
            lambda: self._show_cover_hover(image_path, pointer_x, pointer_y),
        )

    def _show_cover_hover(self, image_path, pointer_x, pointer_y):
        self._cover_hover_after_id = None
        if not image_path or not os.path.isfile(image_path):
            return

        try:
            with Image.open(image_path) as source:
                image = ImageOps.exif_transpose(source).convert("RGBA")
                half_width = max(1, round(image.width * 0.5))
                half_height = max(1, round(image.height * 0.5))

                # Preserve the requested 50% scale unless it would extend past
                # the desktop; oversized scans are reduced just enough to fit.
                max_width = max(200, int(self.winfo_screenwidth() * 0.50))
                max_height = max(200, int(self.winfo_screenheight() * 0.50))
                scale = min(1.0, max_width / half_width, max_height / half_height)
                popup_size = (
                    max(1, round(half_width * scale)),
                    max(1, round(half_height * scale)),
                )
                if image.size != popup_size:
                    image = image.resize(popup_size, LANCZOS_FILTER)
                else:
                    image = image.copy()

            popup = tk.Toplevel(self)
            popup.overrideredirect(True)
            popup.attributes("-topmost", True)
            popup.configure(bg="#c6a65a")

            photo = ImageTk.PhotoImage(image)
            tk.Label(
                popup,
                image=photo,
                bg="#0d0d0c",
                bd=2,
                relief="solid",
                highlightthickness=0,
            ).pack()

            popup.update_idletasks()
            popup_width = int(popup.winfo_reqwidth())
            popup_height = int(popup.winfo_reqheight())
            screen_width = int(self.winfo_screenwidth())
            screen_height = int(self.winfo_screenheight())
            popup_x = min(pointer_x + 18, max(0, screen_width - popup_width - 8))
            popup_y = min(pointer_y + 18, max(0, screen_height - popup_height - 48))
            popup.geometry(f"+{popup_x}+{popup_y}")

            self._cover_hover_window = popup
            self._cover_hover_image = photo
        except Exception as exc:
            self._cover_hover_window = None
            self._cover_hover_image = None
            self.log(f"[Cover hover] Could not display {image_path}: {exc}")

    def _hide_cover_hover(self, event=None):
        if self._cover_hover_after_id is not None:
            try:
                self.after_cancel(self._cover_hover_after_id)
            except Exception:
                pass
            self._cover_hover_after_id = None

        popup = self._cover_hover_window
        self._cover_hover_window = None
        self._cover_hover_image = None
        if popup is not None:
            try:
                popup.destroy()
            except Exception:
                pass

    def _render_thumbnail(self, image_path, target_label, max_size=(210, 280)):
        valid = image_path if image_path and os.path.exists(image_path) else None
        if target_label is getattr(self, 'batch_preview_label', None):
            self.batch_preview_path = valid
        elif target_label is getattr(self, 'single_preview_label', None):
            self.single_preview_path = valid
        self.current_preview_path = valid
        if not valid:
            self._last_preview_render.pop(id(target_label), None)
            target_label.configure(image=None, text=self.tr('cover_no_preview'))
            return
        stat = os.stat(valid)
        key = (valid, int(max_size[0]), int(max_size[1]), stat.st_mtime_ns, stat.st_size)
        if self._last_preview_render.get(id(target_label)) == key:
            return
        self._last_preview_render[id(target_label)] = key
        cached = self._thumbnail_cache.get(key)
        if cached is not None:
            target_label.configure(image=cached, text='')
            self.current_preview_image = cached
            return
        if not hasattr(self, '_thumbnail_results'):
            self._thumbnail_results = queue.Queue()
            self._thumbnail_workers_pending = 0
        self._thumbnail_workers_pending += 1
        if getattr(self, '_thumbnail_poll_after', None) is None:
            self._thumbnail_poll_after = self.after(30, self._poll_thumbnail_results)
        results = self._thumbnail_results
        def load():
            try:
                with Image.open(valid) as original:
                    decoded = ImageOps.exif_transpose(original).convert('RGBA')
                    decoded.thumbnail(max_size, LANCZOS_FILTER)
                    decoded = decoded.copy()
                results.put((target_label, key, decoded, None))
            except Exception as exc:
                results.put((target_label, key, None, str(exc)))
        threading.Thread(target=load, daemon=True).start()

    def _poll_thumbnail_results(self):
        self._thumbnail_poll_after = None
        while True:
            try:
                label, key, decoded, error = self._thumbnail_results.get_nowait()
            except queue.Empty:
                break
            self._thumbnail_workers_pending -= 1
            if self._last_preview_render.get(id(label)) != key:
                continue
            try:
                if not label.winfo_exists():
                    continue
                if error:
                    self._last_preview_render.pop(id(label), None)
                    label.configure(image=None, text='Error loading image: ' + error)
                    continue
                image = ctk.CTkImage(light_image=decoded, dark_image=decoded, size=decoded.size)
                _bounded_cache_set(self._thumbnail_cache, key, image, MAX_THUMBNAIL_CACHE_ENTRIES)
                label.configure(image=image, text='')
                self.current_preview_image = image
            except tk.TclError:
                pass
        if self._thumbnail_workers_pending:
            self._thumbnail_poll_after = self.after(30, self._poll_thumbnail_results)

    # ------------------------------------------------------------------
    # Desktop title translation / Japanese romanization
    # ------------------------------------------------------------------
    _nllb_tokenizer = None
    _nllb_model = None
    _nllb_model_name = None
    _nllb_lock = threading.Lock()

    def _set_entry_text(self, entry, text):
        self._set_text_widget_value(entry, text or "")
        try:
            if entry is self.single_etitle_entry:
                self.single_etitle_entry.event_generate("<KeyRelease>")
            elif entry is self.batch_edit_en_entry:
                self._on_batch_title_edited()
        except Exception:
            pass

    def _set_text_widget_value(self, widget, text):
        if widget is None:
            return
        value = str(text or "")
        previous_state = None
        try:
            previous_state = widget.cget("state")
        except Exception:
            pass
        if previous_state in {"disabled", "readonly"}:
            try:
                widget.configure(state="normal")
            except Exception:
                pass
        try:
            cls = widget.__class__.__name__
            if cls in {"Text", "CTkTextbox"}:
                widget.delete("1.0", "end")
                widget.insert("1.0", value)
            else:
                # Entry fields are intentionally single-line.  Metadata and
                # provider responses occasionally contain embedded newlines.
                value = re.sub(r"[\r\n]+", " ", value)
                widget.delete(0, "end")
                widget.insert(0, value)
        except Exception:
            return
        finally:
            if previous_state in {"disabled", "readonly"}:
                try:
                    widget.configure(state=previous_state)
                except Exception:
                    try:
                        widget.configure(state="disabled")
                    except Exception:
                        pass

    def _get_text_widget_value(self, widget):
        if widget is None:
            return ""
        try:
            cls = widget.__class__.__name__
            if cls in {"Text", "CTkTextbox"}:
                return widget.get("1.0", "end-1c").strip()
        except Exception:
            pass
        try:
            return str(widget.get()).strip()
        except Exception:
            return ""

    def _set_text_widget_state(self, widget, enabled):
        if widget is None:
            return
        state = "normal" if enabled else "disabled"
        try:
            if widget.cget("state") != state:
                widget.configure(state=state)
        except Exception:
            pass

    def _nllb_load(self):
        model_name = self.translation_settings.get("nllb_model") or "facebook/nllb-200-distilled-600M"
        with self._nllb_lock:
            if self.__class__._nllb_model is not None and self.__class__._nllb_model_name == model_name:
                return self.__class__._nllb_tokenizer, self.__class__._nllb_model

            try:
                import torch
                from transformers import AutoModelForSeq2SeqLM, AutoTokenizer
            except ImportError as exc:
                raise RuntimeError(
                    "NLLB requires transformers and torch. Install with: "
                    "python -m pip install transformers torch sentencepiece accelerate"
                ) from exc

            device_pref = (self.translation_settings.get("nllb_device") or "auto").lower()
            if device_pref == "cpu":
                device = "cpu"
            elif device_pref == "cuda":
                if not torch.cuda.is_available():
                    raise RuntimeError("NLLB is configured for CUDA, but PyTorch cannot see an NVIDIA GPU.")
                device = "cuda"
            else:
                device = "cuda" if torch.cuda.is_available() else "cpu"

            self.log(f"[Translator] Loading NLLB model: {model_name} on {device}...")
            tokenizer = AutoTokenizer.from_pretrained(model_name, src_lang="jpn_Jpan")
            model_kwargs = {"low_cpu_mem_usage": True}
            if device == "cuda":
                model_kwargs["torch_dtype"] = torch.float16
            model = AutoModelForSeq2SeqLM.from_pretrained(model_name, **model_kwargs)
            model.to(device)
            model.eval()

            self.__class__._nllb_tokenizer = tokenizer
            self.__class__._nllb_model = model
            self.__class__._nllb_model_name = model_name
            self.log(f"[Translator] NLLB ready: {model_name} ({device}).")
            return tokenizer, model

    def _translate_nllb(self, text):
        import torch
        tokenizer, model = self._nllb_load()
        inputs = tokenizer(text, return_tensors="pt", truncation=True, max_length=256)
        inputs = {k: v.to(model.device) for k, v in inputs.items()}
        forced_bos_token_id = tokenizer.convert_tokens_to_ids("eng_Latn")
        with torch.inference_mode():
            generated = model.generate(
                **inputs,
                forced_bos_token_id=forced_bos_token_id,
                max_new_tokens=160,
                num_beams=4,
                no_repeat_ngram_size=3,
            )
        return tokenizer.batch_decode(generated, skip_special_tokens=True)[0].strip()

    _opus_tokenizer = None
    _opus_model = None
    _opus_model_name = None
    _opus_lock = threading.Lock()

    def _opus_load(self):
        model_name = self.translation_settings.get("opus_model") or "Helsinki-NLP/opus-mt-ja-en"
        with self._opus_lock:
            if self.__class__._opus_model is not None and self.__class__._opus_model_name == model_name:
                return self.__class__._opus_tokenizer, self.__class__._opus_model
            try:
                import torch
                from transformers import AutoModelForSeq2SeqLM, AutoTokenizer
            except ImportError as exc:
                raise RuntimeError("OPUS-MT requires torch, transformers, and sentencepiece. Install NLLB components first.") from exc
            device_pref = (self.translation_settings.get("opus_device") or "auto").lower()
            if device_pref == "cpu":
                device = "cpu"
            elif device_pref == "cuda":
                if not torch.cuda.is_available():
                    raise RuntimeError("OPUS-MT is configured for CUDA, but PyTorch cannot see an NVIDIA GPU.")
                device = "cuda"
            else:
                device = "cuda" if torch.cuda.is_available() else "cpu"
            self.log(f"[Translator] Loading OPUS-MT model: {model_name} on {device}...")
            tokenizer = AutoTokenizer.from_pretrained(model_name)
            model_kwargs = {}
            if device == "cuda":
                model_kwargs["torch_dtype"] = torch.float16
            tokenizer = tokenizer
            model = AutoModelForSeq2SeqLM.from_pretrained(model_name, **model_kwargs)
            model.to(device)
            model.eval()
            self.__class__._opus_tokenizer = tokenizer
            self.__class__._opus_model = model
            self.__class__._opus_model_name = model_name
            self.log(f"[Translator] OPUS-MT ready: {model_name} ({device}).")
            return tokenizer, model

    def _translate_opus_mt(self, text):
        import torch
        tokenizer, model = self._opus_load()
        inputs = tokenizer(text, return_tensors="pt", truncation=True, max_length=256)
        inputs = {k: v.to(model.device) for k, v in inputs.items()}
        with torch.inference_mode():
            generated = model.generate(**inputs, max_new_tokens=160, num_beams=5, no_repeat_ngram_size=3, renormalize_logits=True)
        return tokenizer.batch_decode(generated, skip_special_tokens=True)[0].strip()

    _m2m100_tokenizer = None
    _m2m100_model = None
    _m2m100_model_name = None
    _m2m100_lock = threading.Lock()

    def _m2m100_load(self):
        model_name = "facebook/m2m100_418M"
        with self._m2m100_lock:
            if self.__class__._m2m100_model is not None and self.__class__._m2m100_model_name == model_name:
                return self.__class__._m2m100_tokenizer, self.__class__._m2m100_model
            try:
                import torch
                from transformers import AutoModelForSeq2SeqLM, AutoTokenizer
            except ImportError as exc:
                raise RuntimeError("M2M100 requires torch and transformers. Install with: python -m pip install torch transformers sentencepiece") from exc
            device = "cuda" if torch.cuda.is_available() else "cpu"
            self.log(f"[Translator] Loading M2M100 model: {model_name} on {device}...")
            tokenizer = AutoTokenizer.from_pretrained(model_name)
            model = AutoModelForSeq2SeqLM.from_pretrained(model_name)
            model.to(device)
            model.eval()
            self.__class__._m2m100_tokenizer = tokenizer
            self.__class__._m2m100_model = model
            self.__class__._m2m100_model_name = model_name
            self.log(f"[Translator] M2M100 ready: {model_name} ({device}).")
            return tokenizer, model

    def _translate_m2m100(self, text):
        import torch
        tokenizer, model = self._m2m100_load()
        tokenizer.src_lang = "ja"
        inputs = tokenizer(text, return_tensors="pt", truncation=True, max_length=256)
        inputs = {k: v.to(model.device) for k, v in inputs.items()}
        with torch.inference_mode():
            generated = model.generate(**inputs, forced_bos_token_id=tokenizer.lang_code_to_id["en"], max_new_tokens=160, num_beams=4)
        return tokenizer.batch_decode(generated, skip_special_tokens=True)[0].strip()

    def _translate_google_web(self, text):
        params = {
            "client": "gtx",
            "sl": "ja",
            "tl": "en",
            "dt": "t",
            "q": text,
        }
        r = requests.get("https://translate.googleapis.com/translate_a/single", params=params, timeout=30)
        r.raise_for_status()
        payload = r.json()
        if not isinstance(payload, list) or not payload or not isinstance(payload[0], list):
            raise RuntimeError("Google Translate returned an unexpected payload")
        translated_parts = [str(seg[0]) for seg in payload[0] if isinstance(seg, list) and seg and seg[0]]
        out = "".join(translated_parts).strip()
        if not out:
            raise RuntimeError("Google Translate returned no translated text")
        return out

    def _translate_lingva(self, text):
        configured = (self.translation_settings.get("lingva_mirror") or "").strip().rstrip("/")
        mirrors = [
            configured,
            "https://lingva.ml",
            "https://translate.plausibility.cloud",
        ]
        last_error = None
        for base in [m for m in mirrors if m]:
            try:
                endpoint = f"{base}/api/v1/ja/en/{quote(text)}"
                r = requests.get(endpoint, timeout=30, headers={"Accept": "application/json", "User-Agent": USER_AGENT})
                r.raise_for_status()
                data = r.json()
                out = str(data.get("translation") or "").strip()
                if out:
                    return out
                last_error = RuntimeError(f"{base} returned empty translation")
            except Exception as exc:
                last_error = exc
                self.log(f"[Translator] Lingva mirror failed ({base}): {exc}")
        raise RuntimeError(f"Lingva is unavailable. Last error: {last_error}")

    def _translate_with_translators_engine(self, engine, text):
        try:
            import translators as ts
        except ImportError as exc:
            raise RuntimeError(
                "The 'translators' package is required for this provider. Install with: python -m pip install translators"
            ) from exc

        try:
            out = ts.translate_text(
                text,
                translator=engine,
                from_language="ja",
                to_language="en",
                timeout=25,
            )
        except Exception as exc:
            raise RuntimeError(f"{engine} translator failed: {exc}") from exc

        result = str(out or "").strip()
        if not result:
            raise RuntimeError(f"{engine} translator returned an empty result")
        return result

    def _translation_worker(self, key, text):
        cached = self._get_cached_translation(key, text)
        if cached is not None:
            return cached

        if key == "google_web":
            out = self._translate_google_web(text)
            self._set_cached_translation(key, text, out)
            return out

        if key == "bing_web":
            out = self._translate_with_translators_engine("bing", text)
            self._set_cached_translation(key, text, out)
            return out

        if key == "deepl_web":
            out = self._translate_with_translators_engine("deepl", text)
            self._set_cached_translation(key, text, out)
            return out

        if key == "youdao_web":
            out = self._translate_with_translators_engine("youdao", text)
            self._set_cached_translation(key, text, out)
            return out

        if key == "sogou_web":
            out = self._translate_with_translators_engine("sogou", text)
            self._set_cached_translation(key, text, out)
            return out

        if key == "alibaba_web":
            out = self._translate_with_translators_engine("alibaba", text)
            self._set_cached_translation(key, text, out)
            return out

        if key == "lingva":
            out = self._translate_lingva(text)
            self._set_cached_translation(key, text, out)
            return out

        if key == "pykakasi_eng":
            out = self._romaji_worker("auto_accurate", text)
            self._set_cached_translation(key, text, out)
            return out

        if key == "mymemory":
            params = {"q": text, "langpair": "ja|en", "mt": "1"}
            email = (self.translation_settings.get("mymemory_email") or "").strip()
            if email:
                params["de"] = email
            if len(text.encode("utf-8")) > 500:
                raise RuntimeError("MyMemory accepts a maximum of 500 UTF-8 bytes per request; use NLLB or LibreTranslate for longer titles.")
            r = requests.get("https://api.mymemory.translated.net/get", params=params, timeout=30)
            r.raise_for_status()
            data = r.json()
            response_data = data.get("responseData") or {}
            out = response_data.get("translatedText")
            if not out:
                raise RuntimeError(f"MyMemory returned no translation: {data}")
            translated = html.unescape(str(out)).strip()
            self._set_cached_translation(key, text, translated)
            return translated

        raise RuntimeError(f"Unknown translator: {key}")

    def _normalize_romanized_title(self, text):
        cleaned = (text or "").strip()
        if not cleaned:
            return ""

        cleaned = cleaned.replace("。", ". ")
        cleaned = cleaned.replace("、", ", ")
        cleaned = cleaned.replace("・", " ")
        cleaned = cleaned.replace("—", " - ")
        cleaned = re.sub(r"\s*([,.;:!?])\s*", r"\1 ", cleaned)
        cleaned = re.sub(r"\s+", " ", cleaned)
        cleaned = cleaned.strip()

        pieces = re.split(r"\s+", cleaned)
        normalized = []
        for idx, piece in enumerate(pieces):
            if not piece:
                continue
            if piece in {".", ",", ";", ":", "!", "?"}:
                normalized.append(piece)
                continue
            if idx == 0:
                normalized.append(piece[:1].upper() + piece[1:])
            else:
                lowered = piece.lower()
                if lowered in {"a", "an", "and", "as", "at", "but", "by", "for", "in", "of", "on", "or", "the", "to", "with", "via"}:
                    normalized.append(lowered)
                else:
                    normalized.append(piece[:1].upper() + piece[1:])

        final = " ".join(normalized)
        final = re.sub(r"\s+([,.!?;:])", r"\1", final)
        final = re.sub(r"\s+([\)])", r"\1", final)
        final = re.sub(r"([\(])\s+", r"\1", final)
        final = re.sub(r"\s{2,}", " ", final).strip()
        return final

    def _kana_to_hepburn(self, kana_text):
        try:
            from pykakasi import kakasi
        except ImportError as exc:
            raise RuntimeError("Install pykakasi from Translation Settings to convert Japanese readings.") from exc
        conv = self._romaji_engine("pykakasi", kakasi)
        return "".join(item["hepburn"] for item in conv.convert(kana_text)).strip()

    def _romaji_worker(self, key, text):
        text = (text or "").strip()
        if not text:
            return ""
        lock = self.__dict__.setdefault("_romaji_lock", threading.RLock())
        with lock:
            cache_key = self._romaji_cache_namespace(key)
            cached = self._get_cached_translation(cache_key, text)
            if cached:
                return cached
            result = self._romaji_worker_uncached(key, text)
            # Auto may temporarily fall back to a smaller engine. Do not persist
            # that fallback as the best answer after a dictionary is installed.
            if key != "auto_accurate":
                self._set_cached_translation(cache_key, text, result)
            return result

    def _romaji_worker_uncached(self, key, text):
        if key == "auto_accurate":
            errors = []
            for provider in ("sudachi", "mecab_unidic", "cutlet", "pykakasi"):
                try:
                    out = self._romaji_worker(provider, text)
                    if out:
                        self._romaji_last_auto_provider = provider
                        return out
                except Exception as exc:
                    errors.append(f"{provider}: {exc}")
            raise RuntimeError("Romaji engines unavailable: " + " | ".join(errors))

        if key == "mecab_unidic":
            try:
                from fugashi import GenericTagger
            except ImportError as exc:
                raise RuntimeError("Install MeCab + UniDic-lite in Translation Settings.") from exc
            preference = self.translation_settings.get("mecab_dictionary", "auto")
            modules = ("unidic", "unidic_lite") if preference == "auto" else (preference,)
            dicdir = None
            for module in modules:
                try:
                    candidate = importlib.import_module(module).DICDIR
                    if os.path.isfile(os.path.join(candidate, "sys.dic")):
                        dicdir = candidate
                        break
                except ImportError:
                    continue
            if not dicdir:
                raise RuntimeError("No usable UniDic dictionary found. Install UniDic-lite in Settings, or select an installed dictionary.")
            def make_tagger():
                mecabrc = os.path.join(dicdir, "mecabrc")
                return GenericTagger(f'-r "{mecabrc}" -d "{dicdir}"')
            try:
                tagger = self._romaji_engine(("mecab", dicdir), make_tagger)
                tokens = []
                for word in tagger(text):
                    feat = word.feature
                    # GenericTagger returns tuples, not named features. UniDic's
                    # pronunciation is field 9 in both lite and full dictionaries.
                    reading = getattr(feat, "pron", None)
                    if not reading and len(feat) > 9:
                        reading = feat[9]
                    pos = getattr(feat, "pos1", None) or (feat[0] if feat else "")
                    tokens.append((word.surface, reading, pos))
                return self._romanize_tokens(tokens)
            except Exception as exc:
                raise RuntimeError(f"MeCab / UniDic failed: {exc}") from exc

        if key == "sudachi":
            try:
                from sudachipy import Dictionary, SplitMode
            except ImportError as exc:
                raise RuntimeError("Install SudachiPy and a dictionary in Translation Settings.") from exc
            edition = self.translation_settings.get("sudachi_dictionary", "core")
            mode_name = self.translation_settings.get("sudachi_split_mode", "B")
            if edition not in {"small", "core", "full"}:
                edition = "core"
            if mode_name not in {"A", "B", "C"}:
                mode_name = "B"
            def make_tokenizer():
                dictionary = Dictionary(dict=edition)
                mode = getattr(SplitMode, mode_name)
                factory = getattr(dictionary, "tokenizer", None) or dictionary.create
                return dictionary, factory(mode)
            try:
                dictionary, tokenizer = self._romaji_engine(("sudachi", edition, mode_name), make_tokenizer)
                return self._romanize_tokens((word.surface(), word.reading_form(), word.part_of_speech()[0])
                                            for word in tokenizer.tokenize(text))
            except Exception as exc:
                raise RuntimeError(f"Sudachi {edition} ({mode_name}) failed: {exc}. Check the selected dictionary in Settings.") from exc

        if key in {"pykakasi", "pykakasi_passport", "pykakasi_kunrei"}:
            try:
                from pykakasi import kakasi
            except ImportError as exc:
                raise RuntimeError("Install pykakasi in Translation Settings.") from exc
            conv = self._romaji_engine("pykakasi", kakasi)
            style = {"pykakasi": "hepburn", "pykakasi_passport": "passport", "pykakasi_kunrei": "kunrei"}[key]
            converted = conv.convert(text)
            if any(style not in item for item in converted):
                raise RuntimeError(f"This pykakasi version does not provide {style}; update pykakasi in Settings.")
            return self._normalize_romanized_title(" ".join(item[style] for item in converted))

        if key == "cutlet":
            try:
                import cutlet
                import unidic_lite
            except ImportError as exc:
                raise RuntimeError("Install Cutlet in Translation Settings.") from exc
            def make_cutlet():
                mecabrc = os.path.join(unidic_lite.DICDIR, "mecabrc")
                return cutlet.Cutlet("hepburn", mecab_args=f'-r "{mecabrc}" -d "{unidic_lite.DICDIR}"')
            try:
                katsu = self._romaji_engine("cutlet", make_cutlet)
                return self._normalize_romanized_title(katsu.romaji(text).strip())
            except Exception as exc:
                raise RuntimeError(f"Cutlet / UniDic-lite failed: {exc}") from exc
        raise RuntimeError(f"Unknown romaji engine: {key}")

    def _pick_from_candidates(self, title, candidates):
        if not candidates:
            return None
        if len(candidates) == 1:
            return candidates[0]

        dialog = ctk.CTkToplevel(self)
        dialog.title(title)
        dialog.geometry("680x420")
        dialog.transient(self)
        dialog.grab_set()

        ctk.CTkLabel(dialog, text=f"{title} — choose the best match:", font=("Arial", 13, "bold")).pack(anchor="w", padx=14, pady=(12, 8))

        box = tk.Listbox(dialog, width=90, height=min(12, max(6, len(candidates))), font=("Arial", 11), exportselection=False)
        box.pack(fill="both", expand=True, padx=14, pady=(0, 10))

        for item in candidates:
            box.insert("end", item)
        box.selection_set(0)

        result = {"value": candidates[0]}

        def accept():
            idx = box.curselection()
            if idx:
                result["value"] = candidates[idx[0]]
            dialog.destroy()

        buttons = ctk.CTkFrame(dialog, fg_color="transparent")
        buttons.pack(fill="x", padx=14, pady=(0, 12))
        ctk.CTkButton(buttons, text="Use Selected", command=accept, width=140).pack(side="right")
        dialog.bind("<Return>", lambda _e: accept())
        dialog.wait_window(dialog)
        return result["value"]

    def _gemini_api_key(self):
        settings = getattr(self, "translation_settings", {}) or {}
        for value in (
            os.environ.get("GEMINI_API_KEY"),
            os.environ.get("GOOGLE_API_KEY"),
            os.environ.get("GOOGLE_AI_API_KEY"),
            settings.get("gemini_api_key"),
        ):
            key = str(value or "").strip()
            if key:
                return key
        return ""

    def _ocr_cover_with_better_engine(self, image_path):
        """Gemini (free-tier) + PaddleOCR, then Windows OCR; Tesseract is last."""
        jp_words = []
        en_words = []
        used = []
        preferred_full = ""

        def absorb(full_text, engine):
            nonlocal preferred_full
            full_text = _tighten_cjk_ocr_text(full_text)
            if not str(full_text or "").strip():
                return
            used.append(engine)
            if engine == "gemini" or not preferred_full:
                preferred_full = full_text
            jp, en = _split_ocr_text_candidates(full_text)
            for word in jp:
                if word not in jp_words:
                    jp_words.append(word)
            for word in en:
                if word not in en_words:
                    en_words.append(word)
            self.log(f"[OCR] {engine} title: {full_text[:180]}")

        gemini_key = self._gemini_api_key()
        if gemini_key:
            try:
                absorb(_ocr_image_gemini(image_path, gemini_key, log_fn=self.log), "gemini")
            except Exception as exc:
                self.log(f"[OCR] Gemini unavailable: {exc}")
        else:
            self.log("[OCR] Gemini skipped (no API key). Set it in Settings > Cover OCR.")

        try:
            absorb(_ocr_image_paddle(image_path, log_fn=self.log), "paddleocr")
        except Exception as exc:
            self.log(f"[OCR] PaddleOCR unavailable: {exc}")

        try:
            absorb(_ocr_image_windows(image_path, langs=("ja", "en"), log_fn=self.log), "windows")
        except Exception as exc:
            self.log(f"[OCR] Windows OCR unavailable: {exc}")

        if not jp_words and not en_words:
            return None
        engine_name = "gemini" if "gemini" in used else ("paddleocr" if "paddleocr" in used else "windows")
        self._set_cached_cover_metadata(
            image_path,
            {
                "japanese": jp_words,
                "english": en_words,
                "engine": engine_name,
                "full_text": preferred_full,
                "ocr_set": "v3-gemini-paddle-windows",
            },
        )
        return jp_words, en_words

    def _extract_cover_title_candidates(self, image_path):
        cached = self._get_cached_cover_metadata(image_path)
        if cached and cached.get("ocr_set") == "v3-gemini-paddle-windows":
            return cached.get("japanese", []), cached.get("english", [])

        better = self._ocr_cover_with_better_engine(image_path)
        if better is not None:
            return better

        try:
            import pytesseract
            from pytesseract import Output
        except ImportError as exc:
            raise RuntimeError(
                "OCR is not available. Install Tesseract OCR and then run: python -m pip install pytesseract"
            ) from exc

        tess = shutil.which("tesseract")
        if tess:
            pytesseract.pytesseract.tesseract_cmd = tess
        elif os.name == "nt":
            alt = os.environ.get("TESSERACT_CMD") or os.environ.get("TESSERACT_PATH")
            if not alt:
                alt_candidates = [
                    r"C:\Program Files\Tesseract-OCR\tesseract.exe",
                    r"C:\Program Files (x86)\Tesseract-OCR\tesseract.exe",
                ]
                alt = next((p for p in alt_candidates if os.path.exists(p)), "")
            if alt and os.path.exists(alt):
                os.environ["PATH"] = os.path.dirname(alt) + os.pathsep + os.environ.get("PATH", "")
                pytesseract.pytesseract.tesseract_cmd = alt
            else:
                raise RuntimeError(
                    "Tesseract is not installed or not on PATH. Install Tesseract OCR from the app settings (winget) or from https://github.com/UB-Mannheim/tesseract/wiki, then restart the app."
                )
        else:
            raise RuntimeError(
                "Tesseract is not installed or not on PATH. Install Tesseract OCR with your package manager, then restart the app."
            )

        with Image.open(image_path) as raw:
            img = ImageOps.exif_transpose(raw).convert("RGB")
            gray = ImageOps.grayscale(img)
            enlarged = gray.resize((gray.width * 2, gray.height * 2), LANCZOS_FILTER)

        try:
            text = pytesseract.image_to_string(enlarged, config="--psm 6 -c preserve_interword_spaces=1", lang="jpn+eng")
            data = pytesseract.image_to_data(enlarged, config="--psm 6", lang="jpn+eng", output_type=Output.DICT)
        except Exception as exc:
            raise RuntimeError(f"OCR failed while reading the cover: {exc}") from exc

        candidates = {"japanese": [], "english": []}
        seen = set()

        for item_text, conf in zip(data.get("text", []), data.get("conf", [])):
            value = (item_text or "").strip()
            if not value:
                continue
            try:
                confidence = float(conf)
            except (TypeError, ValueError):
                confidence = 0.0
            if confidence < 20:
                continue
            cleaned = re.sub(r"\s+", " ", value)
            if not cleaned or cleaned in seen:
                continue
            seen.add(cleaned)

            if re.search(r"[\u3040-\u30ff\u3400-\u4dbf\u4e00-\u9fff]", cleaned):
                candidates["japanese"].append(cleaned)
            elif re.search(r"[A-Za-z]", cleaned):
                candidates["english"].append(cleaned)

        if not candidates["english"] and text:
            lines = [line.strip() for line in text.splitlines() if line.strip()]
            for line in lines:
                if not re.search(r"[\u3040-\u30ff\u3400-\u4dbf\u4e00-\u9fff]", line) and re.search(r"[A-Za-z]", line):
                    if line not in seen:
                        candidates["english"].append(line)
                        seen.add(line)

        if not candidates["japanese"] and text:
            lines = [line.strip() for line in text.splitlines() if line.strip()]
            for line in lines:
                if re.search(r"[\u3040-\u30ff\u3400-\u4dbf\u4e00-\u9fff]", line):
                    if line not in seen:
                        candidates["japanese"].append(line)
                        seen.add(line)

        candidates["engine"] = "tesseract"
        candidates["full_text"] = str(text or "")
        self._set_cached_cover_metadata(image_path, candidates)
        return candidates["japanese"], candidates["english"]

    def _search_cover_image_for_matching_gallery(self, image_path, en_entry=None, jp_entry=None, silent=False, open_search=True):
        if not image_path or not os.path.exists(image_path):
            if not silent:
                messagebox.showwarning("E-Hentai / ExHentai Match", "Select a cover image before searching for matching galleries.")
            return None

        cookies = self._get_cookies()
        try:
            backend = EHentaiBackend(
                cookies,
                log_fn=self.log,
                use_ex=self.use_ex_var.get(),
                cookie_file=str(self._resolve_cookie_file() or "cookies.txt"),
            )
            matches = backend.search_gallery_matches_by_image(image_path)
            if not matches:
                if not silent:
                    messagebox.showinfo("E-Hentai / ExHentai Match", "No galleries with that cover image were found on the site.")
                return None

            candidates = []
            for match in matches:
                try:
                    meta = backend.fetch_gallery_title_metadata(match["url"])
                    english = meta.get("english") or [match["title"]]
                    japanese = meta.get("japanese") or []
                except Exception:
                    english = [match["title"]]
                    japanese = []

                en_value = english[0].strip() if english else ""
                jp_value = japanese[0].strip() if japanese else ""
                label = f"{en_value or match['title']}"
                if jp_value:
                    label = f"{label} | {jp_value}"
                sim = float(match.get("similarity") or 0.0)
                if sim < MIN_COVER_SIMILARITY:
                    continue
                if sim > 0:
                    label = f"[{sim:.1f}%] {label}"
                candidates.append({"label": label, "english": en_value, "japanese": jp_value, "url": match["url"], "similarity": sim})

            deduped = []
            seen = set()
            for entry in candidates:
                key = (entry["url"], entry["english"], entry["japanese"])
                if key in seen:
                    continue
                seen.add(key)
                deduped.append(entry)

            deduped.sort(key=lambda item: float(item.get("similarity") or 0.0), reverse=True)

            if len(deduped) == 1 or silent:
                chosen = deduped[0]
            else:
                selected = self._pick_from_candidates("Matching Gallery Titles", [item["label"] for item in deduped])
                chosen = next((item for item in deduped if item["label"] == selected), deduped[0])

            if chosen.get("japanese") and jp_entry is not None:
                self._set_text_widget_value(jp_entry, chosen["japanese"])
                if hasattr(jp_entry, "event_generate"):
                    try:
                        jp_entry.event_generate("<KeyRelease>")
                    except Exception:
                        pass

            if chosen.get("english") and en_entry is not None:
                self._set_text_widget_value(en_entry, chosen["english"])
                if hasattr(en_entry, "event_generate"):
                    try:
                        en_entry.event_generate("<KeyRelease>")
                    except Exception:
                        pass

            if (
                en_entry is getattr(self, "batch_edit_en_entry", None)
                or jp_entry is getattr(self, "batch_edit_jp_entry", None)
            ):
                self._sync_selected_batch_item_titles(
                    new_en=self._get_text_widget_value(getattr(self, "batch_edit_en_entry", None)),
                    new_jp=self._get_text_widget_value(getattr(self, "batch_edit_jp_entry", None)),
                )

            search_query = (chosen.get("english") or chosen.get("japanese") or chosen.get("label") or "").strip()
            if search_query and open_search:
                self._browser_open_url("ehentai", self._build_ehentai_search_url(search_query), "E-Hentai / ExHentai Search")

            self.log(f"[Site Match] Filled metadata from matching gallery: {chosen.get('url')} (similarity={chosen.get('similarity', 0):.1f}%)")
            return chosen
        except Exception as exc:
            self.log(f"[Site Match] Failed: {exc}")
            if not silent:
                messagebox.showwarning("E-Hentai / ExHentai Match", f"Gallery search failed:\n\n{exc}", parent=self)
            return None

    def _fetch_cover_title_metadata(self, image_path, en_entry=None, jp_entry=None):
        if not image_path or not os.path.exists(image_path):
            messagebox.showwarning("Cover Metadata", "Select a cover image before fetching title metadata.")
            return

        try:
            jp_candidates, en_candidates = self._extract_cover_title_candidates(image_path)
        except Exception as exc:
            message = str(exc)
            if ("Tesseract is not installed" in message or "OCR is not available" in message) and not self._ocr_install_in_progress:
                self._ocr_install_prompted = True
                self._ocr_install_in_progress = True
                answer = messagebox.askyesno(
                    "Install OCR Support",
                    "Tesseract is required for cover-title OCR.\n\nInstall it now using the built-in installer?",
                    parent=self,
                )
                if answer:
                    self._install_tesseract_ocr()
                else:
                    self._ocr_install_in_progress = False
            else:
                if not self._ocr_install_in_progress:
                    self._ocr_install_prompted = True
                messagebox.showwarning("Cover Metadata", message, parent=self)
            return

        if not jp_candidates and not en_candidates:
            messagebox.showinfo("Cover Metadata", "No readable title text was found in that image.")
            return

        if jp_candidates:
            jp_candidates = list(dict.fromkeys(jp_candidates))
            selected_jp = jp_candidates[0] if len(jp_candidates) == 1 else self._pick_from_candidates("Japanese Title", jp_candidates)
            if selected_jp and jp_entry is not None:
                self._set_text_widget_value(jp_entry, selected_jp)
                if jp_entry is getattr(self, "batch_edit_jp_entry", None):
                    current_en = self._get_text_widget_value(self.batch_edit_en_entry)
                    self._sync_selected_batch_item_titles(new_en=current_en, new_jp=selected_jp)
                if hasattr(jp_entry, "event_generate"):
                    try:
                        jp_entry.event_generate("<KeyRelease>")
                    except Exception:
                        pass
        if en_candidates:
            en_candidates = list(dict.fromkeys(en_candidates))
            selected_en = en_candidates[0] if len(en_candidates) == 1 else self._pick_from_candidates("English Title", en_candidates)
            if selected_en and en_entry is not None:
                self._set_text_widget_value(en_entry, selected_en)
                if en_entry is getattr(self, "batch_edit_en_entry", None):
                    current_jp = self._get_text_widget_value(self.batch_edit_jp_entry)
                    self._sync_selected_batch_item_titles(new_en=selected_en, new_jp=current_jp)
                if hasattr(en_entry, "event_generate"):
                    try:
                        en_entry.event_generate("<KeyRelease>")
                    except Exception:
                        pass

        if en_entry is not None and jp_entry is not None and (jp_candidates or en_candidates):
            self.log(f"[Cover Metadata] OCR match extracted from {image_path}")

    def _start_cover_ocr_lookup(self, image_path, en_entry=None, jp_entry=None):
        """Run slow OCR outside Tk's event loop, then show choices on the UI."""
        if not image_path or not os.path.isfile(image_path):
            messagebox.showwarning("Cover Metadata", "Select a cover image before running OCR.", parent=self)
            return
        self.log(f"[Cover Metadata] Reading cover text in the background: {image_path}")

        def show_error(exc):
            message = str(exc)
            missing_ocr = "Tesseract is not installed" in message or "OCR is not available" in message
            if missing_ocr and not self._ocr_install_in_progress:
                install = messagebox.askyesno(
                    "Install OCR Support",
                    "Tesseract is required for cover-title OCR.\n\nInstall it now using the built-in installer?",
                    parent=self,
                )
                if install:
                    self._install_tesseract_ocr()
                return
            messagebox.showwarning("Cover Metadata", message, parent=self)

        def worker():
            try:
                self._extract_cover_title_candidates(image_path)
            except Exception as exc:
                self.after(0, lambda exc=exc: show_error(exc))
                return
            self.after(0, lambda: self._fetch_cover_title_metadata(image_path, en_entry, jp_entry))

        threading.Thread(target=worker, daemon=True).start()

    def _install_tesseract_ocr(self, status_callback=None):
        if self._ocr_install_in_progress:
            return

        self._ocr_install_in_progress = True

        def worker():
            try:
                if os.name == "nt":
                    available = shutil.which("tesseract")
                    if available:
                        if status_callback:
                            self.after(0, lambda: status_callback("Tesseract is already installed and on PATH."))
                        self._ocr_install_in_progress = False
                        return
                    cmd = ["winget", "install", "--id", "TesseractOCR.Tesseract", "--source", "winget", "-e"]
                    proc = subprocess.run(cmd, capture_output=True, text=True, timeout=600)
                    if proc.returncode != 0:
                        raise RuntimeError((proc.stderr or proc.stdout or "winget install failed").strip()[:1200])
                    common = [
                        r"C:\Program Files\Tesseract-OCR\tesseract.exe",
                        r"C:\Program Files (x86)\Tesseract-OCR\tesseract.exe",
                    ]
                    installed = next((p for p in common if os.path.exists(p)), None)
                    if installed:
                        os.environ["PATH"] = os.path.dirname(installed) + os.pathsep + os.environ.get("PATH", "")
                    if status_callback:
                        self.after(0, lambda: status_callback("Tesseract installed with winget. Restart the app if PATH still needs to refresh."))
                    self._ocr_install_in_progress = False
                    return

                if status_callback:
                    self.after(0, lambda: status_callback("On Linux/macOS, install Tesseract via your package manager and ensure it is on PATH."))
                self._ocr_install_in_progress = False
            except Exception as exc:
                self._ocr_install_in_progress = False
                if status_callback:
                    self.after(0, lambda: status_callback(f"Tesseract install failed: {exc}"))
        threading.Thread(target=worker, daemon=True).start()

    def _load_startup_cache(self):
        try:
            if not self._cache_path.exists():
                return
            with open(self._cache_path, "r", encoding="utf-8") as fh:
                payload = json.load(fh)
            if isinstance(payload, dict):
                translations = payload.get("translations", {})
                cover_metadata = payload.get("cover_metadata", {})
                with self._cache_lock:
                    if isinstance(translations, dict):
                        self._title_cache["translations"] = dict(
                            list(translations.items())[-MAX_TRANSLATION_CACHE_ENTRIES:]
                        )
                    if isinstance(cover_metadata, dict):
                        self._title_cache["cover_metadata"] = dict(
                            list(cover_metadata.items())[-MAX_COVER_CACHE_ENTRIES:]
                        )
        except Exception as exc:
            self.log(f"[Startup Cache] Failed to load cache: {exc}")

    def _save_startup_cache(self):
        try:
            with self._cache_lock:
                self._cache_save_timer = None
                payload = {
                    "translations": dict(self._title_cache.get("translations", {})),
                    "cover_metadata": dict(self._title_cache.get("cover_metadata", {})),
                }
                tmp = self._cache_path.with_suffix(self._cache_path.suffix + ".tmp")
                with open(tmp, "w", encoding="utf-8") as fh:
                    json.dump(payload, fh, ensure_ascii=False, indent=2)
                os.replace(tmp, self._cache_path)
        except Exception as exc:
            self.log(f"[Startup Cache] Failed to write cache: {exc}")

    def _schedule_startup_cache_save(self):
        """Coalesce rapid translation/OCR cache updates into one disk write."""
        with self._cache_lock:
            previous = self._cache_save_timer
            if previous is not None:
                previous.cancel()
            timer = threading.Timer(0.75, self._save_startup_cache)
            timer.daemon = True
            self._cache_save_timer = timer
            timer.start()

    def _translation_cache_key(self, key, text):
        payload = f"{key}:{(text or '').strip()}".encode("utf-8")
        return hashlib.sha256(payload).hexdigest()

    def _get_cached_translation(self, key, text):
        stable_key = self._translation_cache_key(key, text)
        with self._cache_lock:
            value = self._title_cache.get("translations", {}).get(stable_key)
        if isinstance(value, str) and value.strip():
            return value.strip()
        return None

    def _set_cached_translation(self, key, text, value):
        if not value or not str(value).strip():
            return
        stable_key = self._translation_cache_key(key, text)
        with self._cache_lock:
            cache = self._title_cache.setdefault("translations", {})
            _bounded_cache_set(cache, stable_key, str(value).strip(), MAX_TRANSLATION_CACHE_ENTRIES)
        self._schedule_startup_cache_save()

    def _cover_cache_key(self, image_path):
        try:
            stat = os.stat(image_path)
            digest = hashlib.sha256()
            digest.update(str(stat.st_mtime_ns).encode("utf-8"))
            digest.update(str(stat.st_size).encode("utf-8"))
            digest.update(os.path.abspath(image_path).encode("utf-8"))
            return digest.hexdigest()
        except Exception:
            return hashlib.sha256(str(os.path.abspath(image_path or "")).encode("utf-8")).hexdigest()

    def _get_cached_cover_metadata(self, image_path):
        key = self._cover_cache_key(image_path)
        with self._cache_lock:
            value = self._title_cache.get("cover_metadata", {}).get(key)
        if isinstance(value, dict):
            return value
        return None

    def _set_cached_cover_metadata(self, image_path, candidates):
        if not candidates or not isinstance(candidates, dict):
            return
        key = self._cover_cache_key(image_path)
        with self._cache_lock:
            cache = self._title_cache.setdefault("cover_metadata", {})
            _bounded_cache_set(
                cache,
                key,
                {
                    "japanese": list(candidates.get("japanese", []))[:25],
                    "english": list(candidates.get("english", []))[:25],
                    "engine": str(candidates.get("engine") or ""),
                    "full_text": str(candidates.get("full_text") or "")[:4000],
                    "ocr_set": str(candidates.get("ocr_set") or ""),
                },
                MAX_COVER_CACHE_ENTRIES,
            )
        self._schedule_startup_cache_save()

    def _run_pip_install(self, packages, status_callback=None, post_install=None):
        if getattr(sys, "frozen", False):
            self._translator_status(status_callback, "Package installation is unavailable in the packaged app; use the Python script for setup.")
            return
        if getattr(self, "_translator_install_busy", False):
            self._translator_status(status_callback, "An installation is already running. Please wait.")
            return
        self._translator_install_busy = True
        self._translator_status(status_callback, "Installing / updating components…")
        def worker():
            try:
                self.log(f"[Translator Setup] Installing: {' '.join(packages)}")
                cmd = [sys.executable, "-m", "pip", "install", "--upgrade", *packages]
                proc = subprocess.run(cmd, capture_output=True, text=True, timeout=1800,
                                      creationflags=getattr(subprocess, "CREATE_NO_WINDOW", 0))
                if proc.returncode != 0:
                    raise RuntimeError((proc.stderr or proc.stdout or "pip install failed").strip()[-1600:])
                importlib.invalidate_caches()
                lock = self.__dict__.setdefault("_romaji_lock", threading.RLock())
                with lock:
                    self.__dict__.pop("_romaji_engines", None)
                if post_install:
                    post_install()
                self.log("[Translator Setup] Installation complete.")
                self._translator_status(status_callback, "Installed. Test engines below; restart the app if a loaded package was updated.")
            except Exception as exc:
                message = f"Installation failed: {exc}"
                self.log(f"[Translator Setup] {message}")
                self._translator_status(status_callback, message)
            finally:
                self._translator_install_busy = False
        threading.Thread(target=worker, daemon=True).start()

    def _install_mecab_unidic(self, status_callback=None):
        self._run_pip_install(["fugashi", "unidic-lite", "pykakasi"], status_callback)

    def _start_libretranslate_local(self, status_callback=None):
        if getattr(sys, "frozen", False):
            self._translator_status(status_callback, "Start LibreTranslate separately and connect to its URL.")
            return
        def worker():
            try:
                base = (self.translation_settings.get("libretranslate_url") or "http://127.0.0.1:5000").strip().rstrip("/")
                from urllib.parse import urlparse
                parsed = urlparse(base)
                host = parsed.hostname or "127.0.0.1"
                port = parsed.port or 5000
                check = requests.get(f"{base}/languages", timeout=3)
                if check.ok:
                    if status_callback:
                        self.after(0, lambda: status_callback(f"LibreTranslate is already running at {base}"))
                    return
            except Exception:
                host, port, base = "127.0.0.1", 5000, "http://127.0.0.1:5000"

            try:
                flags = 0
                if os.name == "nt":
                    flags = getattr(subprocess, "CREATE_NO_WINDOW", 0)
                log_path = (APP_DIR / "libretranslate_startup.log")
                log_handle = open(log_path, "a", encoding="utf-8", errors="replace")
                log_handle.write("\n===== LibreTranslate start =====\n")
                log_handle.flush()
                proc = subprocess.Popen(
                    [sys.executable, "-m", "libretranslate", "--host", host, "--port", str(port), "--load-only", "ja,en"],
                    stdout=log_handle,
                    stderr=subprocess.STDOUT,
                    creationflags=flags,
                )
                self._libretranslate_process = proc
                self._libretranslate_log_handle = log_handle
                self.log(f"[Translator Setup] Started LibreTranslate process PID={proc.pid} at {base}; startup log: {log_path}")
                for _ in range(30):
                    time.sleep(1)
                    try:
                        r = requests.get(f"{base}/languages", timeout=2)
                        if r.ok:
                            if status_callback:
                                self.after(0, lambda: status_callback(f"LibreTranslate is ready at {base}"))
                            return
                    except Exception:
                        pass
                if status_callback:
                    self.after(0, lambda: status_callback(f"LibreTranslate process started, but it is not responding yet. Check the console/logs."))
            except Exception as exc:
                self.log(f"[Translator Setup] Could not start LibreTranslate: {exc}")
                if status_callback:
                    self.after(0, lambda: status_callback(f"Could not start LibreTranslate: {exc}"))
        threading.Thread(target=worker, daemon=True).start()

    def _open_ocr_settings(self, parent=None):
        parent = parent or self
        dialog = ctk.CTkToplevel(parent)
        dialog.title("Cover OCR")
        dialog.geometry("720x420")
        dialog.minsize(640, 380)
        dialog.transient(parent)

        ctk.CTkLabel(dialog, text="Gemini OCR (free tier)", font=("Arial", 13, "bold")).pack(anchor="w", padx=16, pady=(16, 6))
        ctk.CTkLabel(
            dialog,
            text="Google Cloud Vision OCR is not free (billing required). This app uses Gemini Flash from Google AI Studio instead. Create a key at https://aistudio.google.com/apikey — or set GEMINI_API_KEY.",
            text_color="gray",
            wraplength=680,
            justify="left",
        ).pack(anchor="w", padx=16, pady=(0, 8))
        key_entry = ctk.CTkEntry(dialog, font=self.input_font, show="*")
        key_entry.pack(fill="x", padx=16)
        key_entry.insert(0, self.translation_settings.get("gemini_api_key", ""))
        self._bind_context_menu(key_entry)

        ctk.CTkLabel(dialog, text="PaddleOCR", font=("Arial", 13, "bold")).pack(anchor="w", padx=16, pady=(16, 6))
        paddle_state = "RapidOCR / Paddle PP-OCR is installed." if _module_available("rapidocr_onnxruntime") or _module_available("paddleocr") else "Not installed."
        ctk.CTkLabel(
            dialog,
            text=paddle_state + " Full PaddlePaddle often has no Python 3.14 wheel; RapidOCR runs the same Paddle detection/recognition models via ONNX.",
            text_color="gray",
            wraplength=680,
            justify="left",
        ).pack(anchor="w", padx=16, pady=(0, 8))

        status = ctk.CTkLabel(dialog, text="", text_color="gray", wraplength=680, justify="left")
        status.pack(anchor="w", padx=16, pady=(4, 8))
        buttons = ctk.CTkFrame(dialog, fg_color="transparent")
        buttons.pack(fill="x", padx=16, pady=(8, 14))
        ctk.CTkButton(
            buttons,
            text="Install PaddleOCR (RapidOCR)",
            width=210,
            command=lambda: self._run_pip_install(["rapidocr-onnxruntime"], status.configure),
        ).pack(side="left")

        def save():
            self.translation_settings["gemini_api_key"] = key_entry.get().strip()
            self._save_config()
            status.configure(text="Saved.")

        ctk.CTkButton(buttons, text="Save", width=90, command=save).pack(side="right")

    def _open_translation_settings(self, parent=None):
        parent = parent or self
        d = ctk.CTkToplevel(parent)
        d.title("Translation Settings")
        d.geometry("880x760")
        d.minsize(700, 580)
        d.transient(parent)
        d.grid_columnconfigure(0, weight=1)
        d.grid_rowconfigure(1, weight=1)
        ctk.CTkLabel(d, text="Translation & Japanese readings", font=(self.input_font_family, 23, "bold")).grid(
            row=0, column=0, sticky="w", padx=24, pady=(22, 10))
        body = ctk.CTkScrollableFrame(d, corner_radius=12)
        body.grid(row=1, column=0, sticky="nsew", padx=20, pady=8)
        body.grid_columnconfigure(0, weight=1)
        fields = {}
        def field(row, title, setting, default, values=None):
            ctk.CTkLabel(body, text=title, anchor="w", font=(self.input_font_family, 13, "bold")).grid(
                row=row, column=0, sticky="ew", padx=14, pady=(14, 4))
            widget = ctk.CTkOptionMenu(body, values=values, height=34) if values else ctk.CTkEntry(body, height=36, font=self.input_font)
            widget.grid(row=row+1, column=0, sticky="ew", padx=14, pady=(0, 4))
            value = self.translation_settings.get(setting, default)
            if values:
                widget.set(value if value in values else default)
            else:
                widget.insert(0, value)
                self._bind_context_menu(widget)
            fields[setting] = widget
        field(0, "Lingva mirror URL", "lingva_mirror", "https://lingva.ml")
        field(2, "MyMemory contact email (optional)", "mymemory_email", "")
        field(4, "Sudachi dictionary", "sudachi_dictionary", "core", ["small", "core", "full"])
        field(6, "Sudachi word spacing: A = short · B = balanced · C = compounds", "sudachi_split_mode", "B", ["A", "B", "C"])
        field(8, "MeCab dictionary: auto prefers installed full UniDic, then lite", "mecab_dictionary", "auto", ["auto", "unidic_lite", "unidic"])
        ctk.CTkLabel(body, text="Local components", font=(self.input_font_family, 17, "bold"), anchor="w").grid(
            row=10, column=0, sticky="ew", padx=14, pady=(22, 8))
        setup = ctk.CTkFrame(body, fg_color="transparent")
        setup.grid(row=11, column=0, sticky="ew", padx=10, pady=(0, 10))
        setup.grid_columnconfigure((0, 1), weight=1, uniform="install")
        status = ctk.CTkLabel(d, text="Choose a dictionary, install its components, then test a Japanese phrase.",
                              anchor="w", justify="left", wraplength=790)
        status.grid(row=2, column=0, sticky="ew", padx=24, pady=10)
        installers = [
            ("Install / update Sudachi", lambda: self._run_pip_install(
                ["sudachipy", "sudachidict_" + fields["sudachi_dictionary"].get(), "pykakasi"], status.configure)),
            ("Install / update MeCab + lite", lambda: self._install_mecab_unidic(status.configure)),
            ("Install / update pykakasi", lambda: self._run_pip_install(["pykakasi"], status.configure)),
            ("Install / update Cutlet", lambda: self._run_pip_install(["cutlet", "unidic-lite"], status.configure)),
            ("Install online providers", lambda: self._run_pip_install(["translators"], status.configure)),
            ("Install cover OCR", lambda: self._install_tesseract_ocr(status.configure)),
        ]
        for index, (label, command) in enumerate(installers):
            ctk.CTkButton(setup, text=label, command=command, height=36).grid(
                row=index//2, column=index%2, sticky="ew", padx=5, pady=5)
        ctk.CTkLabel(body, text="Core balances dictionary coverage and size. Full has broader vocabulary and a larger download. "
                    "MeCab's full UniDic option uses a dictionary already installed on this computer; the installer above includes UniDic-lite.",
                    wraplength=730, justify="left", anchor="w", text_color=("#526075", "#AAB8CB")).grid(
                        row=12, column=0, sticky="ew", padx=14, pady=8)
        test_entry = ctk.CTkEntry(body, height=36, font=self.input_font)
        test_entry.grid(row=13, column=0, sticky="ew", padx=14, pady=(12, 6))
        test_entry.insert(0, "私は東京へ行く。")
        self._bind_context_menu(test_entry)
        report = ctk.CTkTextbox(body, height=130, font=self.input_font, wrap="word")
        report.grid(row=15, column=0, sticky="ew", padx=14, pady=(6, 14))
        report.configure(state="disabled")

        def save():
            mirror = fields["lingva_mirror"].get().strip()
            if mirror and not mirror.startswith(("https://", "http://")):
                status.configure(text="The Lingva mirror must start with https:// or http://.")
                return False
            for setting, widget in fields.items():
                self.translation_settings[setting] = widget.get().strip()
            self.translation_settings["lingva_mirror"] = mirror or "https://lingva.ml"
            self._save_config()
            status.configure(text="Settings saved.")
            return True

        def test_engines():
            if not save():
                return
            sample = test_entry.get().strip()
            if not sample:
                status.configure(text="Enter Japanese text to test.")
                return
            test_button.configure(state="disabled")
            self._set_text_widget_value(report, "Testing local engines…")
            def worker():
                results = []
                for name, key in (("Sudachi", "sudachi"), ("MeCab / UniDic", "mecab_unidic"), ("pykakasi", "pykakasi")):
                    try:
                        # A health check must initialize engines, not return an old cache hit.
                        lock = self.__dict__.setdefault("_romaji_lock", threading.RLock())
                        with lock:
                            value = self._romaji_worker_uncached(key, sample)
                        results.append(f"{name}: {value}")
                    except Exception as exc:
                        results.append(f"{name}: {exc}")
                def finish():
                    if d.winfo_exists():
                        self._set_text_widget_value(report, "\n\n".join(results))
                        test_button.configure(state="normal")
                        status.configure(text="Local engine check complete.")
                try:
                    self.after(0, finish)
                except (tk.TclError, RuntimeError):
                    pass
            threading.Thread(target=worker, daemon=True).start()
        test_button = ctk.CTkButton(body, text="Test local engines", command=test_engines, height=36)
        test_button.grid(row=14, column=0, sticky="w", padx=14, pady=6)
        footer = ctk.CTkFrame(d, fg_color="transparent")
        footer.grid(row=3, column=0, sticky="ew", padx=24, pady=(0, 20))
        ctk.CTkButton(footer, text="Save settings", command=save, height=36).pack(side="right")
        ctk.CTkButton(footer, text="Close", command=d.destroy, height=36, fg_color="transparent", border_width=1).pack(side="right", padx=8)

    def _open_title_translator(self, source_text, target_entry):
        text = (source_text or "").strip()
        if not text:
            messagebox.showinfo("Japanese Title", "Enter a Japanese title first.")
            return
        dialog = ctk.CTkToplevel(self)
        dialog.title("Free Translator Desktop")
        dialog.geometry("1060x810")
        dialog.minsize(720, 600)
        dialog.transient(self)
        dialog.grid_columnconfigure(0, weight=1)
        dialog.grid_rowconfigure(2, weight=1)
        heading = ctk.CTkFrame(dialog, fg_color="transparent")
        heading.grid(row=0, column=0, sticky="ew", padx=24, pady=(20, 10))
        ctk.CTkLabel(heading, text="Free Translator", font=(self.input_font_family, 26, "bold")).pack(side="left")
        ctk.CTkButton(heading, text="Settings & engines", width=155, height=34,
                      command=lambda: self._open_translation_settings(dialog)).pack(side="right")
        source_card = ctk.CTkFrame(dialog, corner_radius=12)
        source_card.grid(row=1, column=0, sticky="ew", padx=20, pady=(0, 10))
        ctk.CTkLabel(source_card, text="SOURCE JAPANESE", font=(self.input_font_family, 12, "bold"), anchor="w").pack(fill="x", padx=16, pady=(12, 4))
        source_box = ctk.CTkTextbox(source_card, height=75, font=self.input_font, wrap="word")
        source_box.pack(fill="x", padx=12, pady=(0, 12))
        self._set_text_widget_value(source_box, text)
        source_box.configure(state="disabled")
        self._bind_context_menu(source_box)
        tabs = ctk.CTkTabview(dialog, corner_radius=12)
        tabs.grid(row=2, column=0, sticky="nsew", padx=20, pady=(0, 8))
        tab_english = tabs.add("English translation")
        tab_romaji = tabs.add("Japanese readings")
        footer = ctk.CTkLabel(dialog, text="Edit a result before using it. Online translation sends the source text to the selected provider.",
                              text_color=("#526075", "#AAB8CB"), anchor="w", wraplength=980, justify="left")
        footer.grid(row=3, column=0, sticky="ew", padx=24, pady=(6, 18))

        def add_card(parent, label, key, romanize=False):
            card = ctk.CTkFrame(parent, corner_radius=10, border_width=1, border_color=("#CFD8E5", "#344359"))
            card.pack(fill="x", padx=6, pady=6)
            card.grid_columnconfigure(0, weight=1)
            title = ctk.CTkFrame(card, fg_color="transparent")
            title.grid(row=0, column=0, columnspan=2, sticky="ew", padx=14, pady=(12, 6))
            ctk.CTkLabel(title, text=label, font=(self.input_font_family, 14, "bold"), anchor="w").pack(side="left")
            status = ctk.CTkLabel(title, text="Local engine" if romanize else "Online provider", anchor="e",
                                  text_color=("#526075", "#AAB8CB"))
            status.pack(side="right")
            result = ctk.CTkTextbox(card, height=70, font=self.input_font, wrap="word")
            result.grid(row=1, column=0, sticky="nsew", padx=(12, 8), pady=(0, 12))
            self._bind_context_menu(result)
            actions = ctk.CTkFrame(card, fg_color="transparent")
            actions.grid(row=1, column=1, sticky="ne", padx=(0, 12), pady=(0, 12))
            state = {"generation": 0, "has_result": False}

            def use_result():
                if not state["has_result"]:
                    return
                value = self._get_text_widget_value(result)
                if value:
                    try:
                        exists = bool(target_entry.winfo_exists())
                    except Exception:
                        exists = False
                    if not exists:
                        status.configure(text="The target title field has closed.")
                        return
                    self._set_entry_text(target_entry, value)
                    status.configure(text="Applied to English title")

            def copy_result():
                if state["has_result"]:
                    value = self._get_text_widget_value(result)
                    self.clipboard_clear()
                    self.clipboard_append(value)
                    status.configure(text="Copied")

            def run():
                state["generation"] += 1
                generation = state["generation"]
                state["has_result"] = False
                for button in (run_button, use_button, copy_button):
                    button.configure(state="disabled")
                status.configure(text="Reading Japanese…" if romanize else "Translating…")
                self._set_text_widget_value(result, "")
                def worker():
                    try:
                        value = self._romaji_worker(key, text) if romanize else self._translation_worker(key, text)
                        error = None
                    except Exception as exc:
                        value, error = "", str(exc)
                    auto_provider = getattr(self, "_romaji_last_auto_provider", "") if key == "auto_accurate" else ""
                    def finish():
                        if not dialog.winfo_exists() or generation != state["generation"]:
                            return
                        run_button.configure(state="normal")
                        if error:
                            self._set_text_widget_value(result, error)
                            status.configure(text="Unavailable · see details")
                            self.log(f"[Translator] {label} failed: {error}")
                            return
                        state["has_result"] = bool(value)
                        self._set_text_widget_value(result, value)
                        status.configure(text=f"Ready · {auto_provider}" if auto_provider else "Ready · editable")
                        for button in (use_button, copy_button):
                            button.configure(state="normal" if value else "disabled")
                    try:
                        self.after(0, finish)
                    except (tk.TclError, RuntimeError):
                        pass
                threading.Thread(target=worker, daemon=True).start()
            run_button = ctk.CTkButton(actions, text="Romanize" if romanize else "Translate", command=run, width=112, height=30)
            run_button.pack(pady=(0, 5))
            secondary = ctk.CTkFrame(actions, fg_color="transparent")
            secondary.pack()
            use_button = ctk.CTkButton(secondary, text="Use", command=use_result, width=54, height=28, state="disabled")
            use_button.pack(side="left", padx=(0, 4))
            copy_button = ctk.CTkButton(secondary, text="Copy", command=copy_result, width=54, height=28, state="disabled")
            copy_button.pack(side="left")
            cache_key = self._romaji_cache_namespace(key) if romanize else key
            cached = self._get_cached_translation(cache_key, text)
            if cached:
                state["has_result"] = True
                self._set_text_widget_value(result, cached)
                status.configure(text="Saved result · editable")
                use_button.configure(state="normal")
                copy_button.configure(state="normal")
            return run

        first_translation = None
        first_romaji = None
        for page, providers, romanize in ((tab_english, TITLE_TRANSLATORS, False),
                                         (tab_romaji, sorted(ROMAJI_PROVIDERS, key=lambda item: item[1] != "auto_accurate"), True)):
            page.grid_columnconfigure(0, weight=1)
            page.grid_rowconfigure(1, weight=1)
            hint = "Compare providers, then use the best English title." if not romanize else "Auto tries Sudachi, MeCab, Cutlet, then pykakasi. Proper names may still need correction."
            ctk.CTkLabel(page, text=hint, anchor="w", justify="left", wraplength=900).grid(row=0, column=0, sticky="ew", padx=10, pady=8)
            cards = ctk.CTkScrollableFrame(page, fg_color="transparent")
            cards.grid(row=1, column=0, sticky="nsew")
            for index, (label, key) in enumerate(providers):
                run = add_card(cards, label, key, romanize)
                if index == 0:
                    if romanize:
                        first_romaji = run
                    else:
                        first_translation = run
        # Start the same default English provider as before plus the improved
        # local automatic engine after layout, without a recursive canvas resize.
        if first_translation:
            dialog.after(100, first_translation)
        if first_romaji:
            dialog.after(150, first_romaji)

    def _translate_batch_title(self):
        selected = self.batch_tree.selection()
        if not selected:
            messagebox.showinfo("Japanese Title", "Select a gallery first.")
            return
        text = self._get_text_widget_value(self.batch_edit_jp_entry)
        self._open_title_translator(text, self.batch_edit_en_entry)

    def _translate_single_title(self):
        self._open_title_translator(
            self.single_jtitle_entry.get().strip(),
            self.single_etitle_entry,
        )

    # ------------------------------------------------------------------
    # Right-click reverse image search menu
    # ------------------------------------------------------------------
    def _open_reverse_image_search_page(self, provider, image_path):
        pages = {
            "bing_visual": "https://www.bing.com/images/",
            "yandex_images": "https://yandex.com/images/",
            "saucenao": "https://saucenao.com/",
            "ascii2d": "https://ascii2d.net/",
            "tineye": "https://tineye.com/",
            "surugaya": "https://www.suruga-ya.jp/",
        }
        url = pages.get(provider)
        if url:
            result_url = self._try_browser_upload(provider, image_path)
            if result_url:
                if self.open_automation_result_in_app_var.get():
                    self._browser_open_url("image", result_url, provider.replace("_", " ").title())
                return
            tab_key = "image"
            label = provider.replace("_", " ").title()
            if self._browser_open_url(tab_key, url, label):
                self._copy_path_to_clipboard(image_path)
                messagebox.showinfo(
                    "Reverse Image Search",
                    "The image-search page is open in the app browser sidebar.\n\n"
                    "Use the site's Upload/Browse control and choose the copied file path if needed.\n\n"
                    f"File:\n{image_path}",
                )
                return
            self._copy_path_to_clipboard(image_path)
            messagebox.showinfo(
                "Reverse Image Search",
                "The image-search page is open.\n\n"
                "Use the site's Upload/Browse control and choose the copied file path if needed.\n\n"
                f"File:\n{image_path}",
            )

    def _copy_path_to_clipboard(self, path):
        try:
            self.clipboard_clear()
            self.clipboard_append(str(path))
            self.update()
        except Exception as exc:
            self.log(f"[Image Search] Clipboard copy failed: {exc}")

    def _try_browser_upload(self, provider, image_path):
        if not image_path or not os.path.isfile(image_path):
            return ""

        lens_manual_prefix = "__LENS_MANUAL__::"

        try:
            from selenium import webdriver
            from selenium.webdriver.chrome.options import Options
        except Exception as exc:
            self.log(f"[Image Search] Selenium not available for {provider}: {exc}")
            return ""

        try:
            provider_urls = {
                "google_lens": "https://lens.google.com/upload",
                "bing_visual": "https://www.bing.com/visualsearch",
                "yandex_images": "https://yandex.com/images/search",
                "saucenao": "https://saucenao.com/",
                "ascii2d": "https://ascii2d.net/search/file",
                "tineye": "https://tineye.com/",
            }
            url = provider_urls.get(provider)
            if not url:
                return ""

            options = Options()
            options.add_argument("--new-window")
            options.add_argument("--disable-notifications")
            options.add_argument("--disable-blink-features=AutomationControlled")
            profile_dir = tempfile.mkdtemp(prefix="eh_imgsearch_chrome_")
            options.add_argument(f"--user-data-dir={profile_dir}")
            options.add_experimental_option("excludeSwitches", ["enable-automation"])
            options.add_experimental_option("useAutomationExtension", False)
            options.add_experimental_option("detach", True)

            driver = webdriver.Chrome(options=options)
            driver.get(url)
            start_url = driver.current_url
            selectors = [
                "input[name='encoded_image']",
                "input[type='file'][name='encoded_image']",
                "input[type='file']",
                "input[type=file]",
                "input[name='file']",
                "input[name='image']",
                "input[id*='file']",
                "input[id*='image']",
                "input[accept*='image']",
            ]

            upload_ok = False
            for selector in selectors:
                try:
                    elem = driver.find_element("css selector", selector)
                    if elem.is_displayed() or elem.get_attribute("type") == "file":
                        elem.send_keys(image_path)
                        upload_ok = True
                        break
                except Exception:
                    continue

            if not upload_ok and provider == "google_lens":
                shadow_script = """
                    const roots = [document];
                    while (roots.length) {
                        const root = roots.shift();
                        const direct = root.querySelector("input[name='encoded_image'],input[type='file'],input[accept*='image']");
                        if (direct) return direct;
                        const nodes = root.querySelectorAll("*");
                        for (const node of nodes) {
                            if (node.shadowRoot) roots.push(node.shadowRoot);
                        }
                    }
                    return null;
                """
                for _ in range(12):
                    try:
                        elem = driver.execute_script(shadow_script)
                        if elem is not None:
                            elem.send_keys(image_path)
                            upload_ok = True
                            break
                    except Exception:
                        pass
                    time.sleep(0.4)

            if not upload_ok:
                driver.execute_script("window.focus();")
                self.log(f"[Image Search] Browser automation opened {provider}, but no upload field was found.")
                if provider == "google_lens":
                    if not hasattr(self, "_selenium_image_drivers"):
                        self._selenium_image_drivers = []
                    self._selenium_image_drivers.append(driver)

                    if not hasattr(self, "_selenium_image_profiles"):
                        self._selenium_image_profiles = []
                    self._selenium_image_profiles.append(profile_dir)

                    return lens_manual_prefix + (driver.current_url or start_url or "https://lens.google.com/")
                return ""

            # Some providers require a submit click after selecting a file.
            submit_selectors = [
                "button[type='submit']",
                "input[type='submit']",
                "button[id*='search']",
                "button[class*='search']",
                "button[id*='upload']",
                "button[class*='upload']",
            ]
            for selector in submit_selectors:
                try:
                    btn = driver.find_element("css selector", selector)
                    if btn.is_displayed() and btn.is_enabled():
                        btn.click()
                        break
                except Exception:
                    continue

            # Wait for URL transition or result markers.
            result_url = ""
            for _ in range(24):
                time.sleep(0.5)
                current = driver.current_url or ""
                page = (driver.page_source or "")[-12000:].lower()
                if current and current != start_url:
                    result_url = current
                    break
                if any(marker in page for marker in (
                    "result", "similar", "matches", "best guess", "visually similar", "sauce", "ascii2d", "tineye"
                )):
                    result_url = current or start_url
                    break

            if not result_url:
                result_url = driver.current_url or start_url

            if not hasattr(self, "_selenium_image_drivers"):
                self._selenium_image_drivers = []
            self._selenium_image_drivers.append(driver)

            if not hasattr(self, "_selenium_image_profiles"):
                self._selenium_image_profiles = []
            self._selenium_image_profiles.append(profile_dir)

            self.log(f"[Image Search] Browser automation upload succeeded for {provider}: {result_url}")
            return result_url
        except Exception as exc:
            try:
                if "profile_dir" in locals() and profile_dir and os.path.isdir(profile_dir):
                    shutil.rmtree(profile_dir, ignore_errors=True)
            except Exception:
                pass
            self.log(f"[Image Search] Browser automation failed for {provider}: {exc}")
            return ""

    def _open_surugaya_metadata_search(self, image_path=None, title_text="", artist_text="", japanese_title_text=""):
        def build_keyword_tokens(value):
            text = str(value or "").strip()
            if not text:
                return []
            tokens = re.split(r"[\s/|、。！？!?.，（）\[\]【】()]+", text)
            cleaned = []
            for token in tokens:
                token = token.strip(" _-\t\r\n")
                if token:
                    cleaned.append(token)
            return cleaned

        ordered_values = []
        for value in (artist_text, japanese_title_text):
            ordered_values.extend(build_keyword_tokens(value))

        if not ordered_values and image_path and os.path.isfile(image_path):
            try:
                file_name = os.path.splitext(os.path.basename(image_path))[0]
                ordered_values.append(file_name)
            except Exception:
                pass

        if not ordered_values:
            messagebox.showwarning(
                "Suruga-ya",
                "No title or artist metadata is available for a Suruga-ya search.",
            )
            return

        seen = set()
        ordered_unique_values = []
        for token in ordered_values:
            key = token.casefold()
            if key in seen:
                continue
            seen.add(key)
            ordered_unique_values.append(token)

        query = " ".join(ordered_unique_values)
        query = re.sub(r"\s+", " ", query).strip()
        encoded = quote(query)
        url = f"https://www.suruga-ya.jp/search?search_word={encoded}"
        if self._browser_open_url("metadata", url, "Suruga-ya Search"):
            messagebox.showinfo(
                "Suruga-ya Search",
                "Suruga-ya search results have been opened in the app browser sidebar.\n\n"
                f"Query:\n{query}",
            )
        else:
            messagebox.showinfo(
                "Suruga-ya Search",
                "Suruga-ya search results have been opened in the browser.\n\n"
                f"Query:\n{query}",
            )

    def _search_google_lens_file(self, image_path):
        if not image_path or not os.path.isfile(image_path):
            messagebox.showwarning("Google Lens", "No cover image is available for searching.")
            return

        lens_result = self._try_browser_upload("google_lens", image_path)
        lens_manual_prefix = "__LENS_MANUAL__::"

        if lens_result.startswith(lens_manual_prefix):
            lens_url = lens_result[len(lens_manual_prefix):] or "https://lens.google.com/"
            self._copy_path_to_clipboard(image_path)
            self.log("[Image Search] Google Lens opened, but auto-upload field was not detected. Manual upload is required in the opened browser window.")
            messagebox.showinfo(
                "Google Lens",
                "Google Lens is open in Chrome, but the upload field could not be auto-detected this time.\n\n"
                "Use the opened Chrome window to upload manually (or drag the image onto Lens).\n"
                "The file path has been copied to your clipboard.\n\n"
                f"Lens URL:\n{lens_url}\n\n"
                f"File:\n{image_path}",
            )
            return

        if lens_result:
            if self.open_automation_result_in_app_var.get():
                self._browser_open_url("image", lens_result, "Google Lens Results")
            return

        if self._browser_open_url("image", "https://lens.google.com/", "Google Lens"):
            self._copy_path_to_clipboard(image_path)
            messagebox.showinfo(
                "Google Lens",
                "Google Lens has been opened in the app browser sidebar.\n\n"
                "Use the Upload image button and select the copied file path, or drag the image into the page.\n\n"
                f"File:\n{image_path}",
            )
            return

        self._copy_path_to_clipboard(image_path)
        messagebox.showinfo(
            "Google Lens",
            "Google Lens has been opened.\n\n"
            "Use the Upload image button and select the copied file path, or drag the image into the page.\n\n"
            f"File:\n{image_path}",
        )

    def _open_manual_ocr_selector(self, image_path, en_entry=None, jp_entry=None):
        if not image_path or not os.path.isfile(str(image_path)):
            messagebox.showwarning(
                "Manual OCR",
                "Select a cover image before opening Manual OCR.",
                parent=self,
            )
            return
        try:
            dialog = ManualOCRSelectorDialog(
                self,
                image_path=str(image_path),
                en_entry=en_entry,
                jp_entry=jp_entry,
            )
            dialog.focus_force()
        except Exception as exc:
            self.log(f"[Manual OCR] Could not open selector: {exc}")
            messagebox.showerror("Manual OCR", f"Could not open Manual OCR:\n\n{exc}", parent=self)

    def _show_image_search_menu(self, event, image_path, context=None):
        if context == "batch":
            en_entry = getattr(self, "batch_edit_en_entry", None)
            jp_entry = getattr(self, "batch_edit_jp_entry", None)
        elif context == "single":
            en_entry = getattr(self, "single_etitle_entry", None)
            jp_entry = getattr(self, "single_jtitle_entry", None)
        else:
            en_entry = None
            jp_entry = None

        menu = tk.Menu(self, tearoff=0)
        menu.add_command(
            label="Google Lens — search this cover",
            command=lambda: self._search_google_lens_file(image_path),
        )
        menu.add_command(
            label="Google — search OCR title",
            command=lambda: self._fetch_titles_by_google_ocr(image_path, en_entry, jp_entry),
        )
        menu.add_command(
            label="Manual OCR — draw marquee on cover…",
            command=lambda: self._open_manual_ocr_selector(image_path, en_entry, jp_entry),
        )
        menu.add_separator()
        menu.add_command(
            label="Bing Visual Search",
            command=lambda: self._open_reverse_image_search_page("bing_visual", image_path),
        )
        menu.add_command(
            label="Yandex Images",
            command=lambda: self._open_reverse_image_search_page("yandex_images", image_path),
        )
        menu.add_command(
            label="SauceNAO (SearchNAO)",
            command=lambda: self._open_reverse_image_search_page("saucenao", image_path),
        )
        menu.add_command(
            label="ascii2d",
            command=lambda: self._open_reverse_image_search_page("ascii2d", image_path),
        )
        menu.add_command(
            label="TinEye",
            command=lambda: self._open_reverse_image_search_page("tineye", image_path),
        )
        menu.add_command(
            label="Suruga-ya (metadata search)",
            command=lambda: self._open_surugaya_metadata_search(
                image_path,
                self._get_text_widget_value(en_entry),
                "",
                self._get_text_widget_value(jp_entry),
            ),
        )
        menu.add_separator()
        title_source_menu = tk.Menu(menu, tearoff=0)
        for source_name in METADATA_SOURCES:
            title_source_menu.add_command(
                label=source_name,
                command=lambda selected_source=source_name: self._fetch_titles_from_selected_source(
                    image_path,
                    en_entry,
                    jp_entry,
                    selected_source,
                ),
            )
        menu.add_cascade(label="Fetch titles from…", menu=title_source_menu)
        menu.add_command(
            label="Extract title text from this cover with OCR",
            command=lambda: self._start_cover_ocr_lookup(
                image_path,
                en_entry,
                jp_entry,
            ),
        )
        try:
            menu.tk_popup(event.x_root, event.y_root)
        finally:
            menu.grab_release()

    def _on_batch_queue_right_click(self, event):
        item_id = self.batch_tree.identify_row(event.y)
        if not item_id:
            return
        self.batch_tree.selection_set(item_id)
        item = self.batch_queue_items.get(item_id)
        if not item:
            return

        menu = tk.Menu(self, tearoff=0)
        menu.add_command(
            label="Rename selected folder",
            command=lambda: self._rename_selected_batch_folder(item_id),
        )
        menu.add_command(
            label="Open folder in Explorer",
            command=lambda: self._open_folder_in_explorer(item["path"]),
        )
        try:
            status = self.batch_tree.item(item_id, "values")[3]
            if self._status_key_from_display(status) == "status_draft_saved":
                menu.add_command(label="View Draft Preview", command=self._show_selected_draft_preview)
        except Exception:
            pass
        try:
            menu.tk_popup(event.x_root, event.y_root)
        finally:
            menu.grab_release()

    def _rename_selected_batch_folder_from_button(self):
        selected = self.batch_tree.selection()
        if not selected:
            messagebox.showinfo("Rename Folder", "Select a queued gallery folder first.", parent=self)
            return
        self._rename_selected_batch_folder(selected[0])

    def _open_folder_in_explorer(self, folder_path):
        path = os.path.abspath(str(folder_path or "").strip())
        if not path or not os.path.isdir(path):
            messagebox.showwarning("Open Folder", "The selected folder no longer exists.", parent=self)
            return
        try:
            if os.name == "nt":
                os.startfile(path)
            elif sys.platform == "darwin":
                subprocess.Popen(["open", path])
            else:
                subprocess.Popen(["xdg-open", path])
        except Exception as exc:
            messagebox.showerror("Open Folder", f"Could not open the folder:\n\n{exc}", parent=self)

    def _rename_selected_batch_folder(self, item_id):
        item = self.batch_queue_items.get(item_id)
        if not item:
            return

        source_dir = os.path.normpath(str(item.get("path", "")).strip())
        if not source_dir or not os.path.isdir(source_dir):
            messagebox.showwarning("Rename Folder", "The selected queued folder no longer exists.", parent=self)
            return

        parent_dir = os.path.dirname(source_dir) or os.getcwd()
        current_name = os.path.basename(source_dir)
        new_name = self._prompt_text_dialog(
            "Rename Folder",
            f"New name for: {current_name}",
            initial_value=current_name,
        )
        if new_name is None:
            return

        cleaned = str(new_name).strip()
        if not cleaned or cleaned in {".", ".."}:
            messagebox.showwarning("Rename Folder", "Please enter a valid folder name.", parent=self)
            return

        target_dir = os.path.join(parent_dir, cleaned)
        if os.path.exists(target_dir):
            messagebox.showwarning("Rename Folder", f"A folder named '{cleaned}' already exists.", parent=self)
            return

        try:
            os.rename(source_dir, target_dir)
            item["path"] = target_dir
            values = list(self.batch_tree.item(item_id, "values"))
            values[4] = target_dir
            self.batch_tree.item(item_id, values=values)
            self._save_persistent_queue()
            self.log(f"[Queue] Renamed queued folder: {source_dir} -> {target_dir}")
        except Exception as exc:
            messagebox.showerror("Rename Folder", f"Rename failed:\n\n{exc}", parent=self)

    def _on_batch_preview_right_click(self, event):
        path = self.batch_preview_path
        if not path:
            selected = self.batch_tree.selection()
            if selected:
                item = self.batch_queue_items.get(selected[0])
                if item:
                    path = get_first_image_path(
                        item["path"],
                        self._sort_display_to_key(self.batch_sort_combo.get()),
                    )
        self._show_image_search_menu(event, path, context="batch")

    def _on_single_preview_right_click(self, event):
        path = self.single_preview_path
        if not path:
            folder = self.single_folder_entry.get().strip()
            if folder and os.path.isdir(folder):
                path = get_first_image_path(
                    folder,
                    self._sort_display_to_key(self.single_sort_combo.get()),
                )
        self._show_image_search_menu(event, path, context="single")

    def _refresh_batch_preview(self):
        previous = getattr(self, "_batch_preview_after_id", None)
        if previous is not None:
            try:
                self.after_cancel(previous)
            except Exception:
                pass
        self._batch_preview_after_id = self.after(75, self._refresh_batch_preview_now)

    def _refresh_batch_preview_now(self):
        self._batch_preview_after_id = None

        selected = self.batch_tree.selection()

        if not selected:
            # Commit whatever was still in the editors to the previous row.
            self._commit_batch_title_edit()
            self._batch_edit_item_id = None
            self._last_batch_preview_key = None
            self.batch_preview_path = None
            self._batch_title_load_suppress = True
            try:
                self._set_text_widget_state(self.batch_edit_en_entry, False)
                self._set_text_widget_state(self.batch_edit_jp_entry, False)
                self._set_text_widget_value(self.batch_edit_en_entry, "")
                self._set_text_widget_value(self.batch_edit_jp_entry, "")
            finally:
                self._batch_title_load_suppress = False

            self.batch_preview_label.configure(
                image=None,
                text=self.tr("cover_select_hint"),
            )

            if hasattr(self, "batch_preview_draft_btn"):
                self.batch_preview_draft_btn.configure(state="disabled")

            return

        item_id = selected[0]
        previous_id = getattr(self, "_batch_edit_item_id", None)
        # Save the previously edited row BEFORE loading the new selection's
        # titles into the shared entry widgets.
        if previous_id and previous_id != item_id:
            self._commit_batch_title_edit()

        item_data = self.batch_queue_items.get(
            item_id
        )

        if item_data:
            self._set_text_widget_state(self.batch_edit_en_entry, True)
            self._set_text_widget_state(self.batch_edit_jp_entry, True)
            self._populate_batch_title_widgets(item_data, item_id=item_id)

            cover_path = get_first_image_path(
                item_data["path"],
                self._sort_display_to_key(self.batch_sort_combo.get()),
            )
            preview_key = (item_id, cover_path, self._sort_display_to_key(self.batch_sort_combo.get()))
            current_img = self.batch_preview_label.cget("image") if hasattr(self.batch_preview_label, "cget") else None
            if preview_key == self._last_batch_preview_key and current_img is not None:
                return
            self._last_batch_preview_key = preview_key

            self._render_thumbnail(
                cover_path,
                self.batch_preview_label,
                max_size=(320, 420),
            )

        if hasattr(self, "batch_preview_draft_btn"):
            status = self.batch_tree.item(item_id, "values")[3]
            self.batch_preview_draft_btn.configure(
                state="normal" if self._status_key_from_display(status) == "status_draft_saved" else "disabled"
            )

    def _sync_selected_batch_item_titles(self, new_en="", new_jp=""):
        item_id = getattr(self, "_batch_edit_item_id", None)
        if not item_id:
            selected = self.batch_tree.selection()
            if not selected:
                return
            item_id = selected[0]
        if item_id not in self.batch_queue_items:
            return

        self.batch_queue_items[item_id]["title_en"] = new_en
        self.batch_queue_items[item_id]["title_jp"] = new_jp

        if self.batch_tree.exists(item_id):
            vals = list(self.batch_tree.item(item_id, "values"))
            if len(vals) >= 2:
                vals[0] = self._compose_title_cell(new_en, new_jp)
                vals[1] = new_jp
                if len(vals) >= 4:
                    image_count = count_images_in_folder(
                        self.batch_queue_items[item_id].get("path", "")
                    )
                    vals[2] = image_count
                    if image_count > 0 and self._status_key_from_display(vals[3]) == "status_no_images":
                        vals[3] = self._queue_status_display("status_queued")
                self.batch_tree.item(item_id, values=vals)

        self._save_persistent_queue()

    def _on_batch_title_edited(self, event=None):
        if getattr(self, "_batch_title_load_suppress", False):
            return
        # Always write back to the row the editors are bound to, not the
        # current tree selection (selection can change before FocusOut).
        item_id = getattr(self, "_batch_edit_item_id", None)
        if not item_id or item_id not in self.batch_queue_items:
            selected = self.batch_tree.selection()
            if not selected:
                return
            item_id = selected[0]
            if item_id not in self.batch_queue_items:
                return

        new_en = self._get_text_widget_value(self.batch_edit_en_entry)
        new_jp = self._get_text_widget_value(self.batch_edit_jp_entry)

        self.batch_queue_items[item_id]["title_en"] = new_en
        self.batch_queue_items[item_id]["title_jp"] = new_jp

        if self.batch_tree.exists(item_id):
            vals = list(self.batch_tree.item(item_id, "values"))
            while len(vals) < 5:
                vals.append("")
            vals[0] = self._compose_title_cell(new_en, new_jp)
            vals[1] = new_jp
            if len(vals) >= 4:
                image_count = count_images_in_folder(
                    self.batch_queue_items[item_id].get("path", "")
                )
                vals[2] = image_count
                if image_count > 0 and self._status_key_from_display(vals[3]) == "status_no_images":
                    vals[3] = self._queue_status_display("status_queued")
            self.batch_tree.item(item_id, values=vals)
        self._save_persistent_queue()

    def _refresh_single_preview(self):
        folder = self.single_folder_entry.get().strip()
        max_size = getattr(self, '_single_thumbnail_size', None)
        if max_size is None:
            size = int(BOX_STYLE_PRESETS.get(self._box_style, BOX_STYLE_PRESETS['balanced'])['single_preview_size'])
            max_size = (size, size)
        cover = None
        if folder and os.path.isdir(folder):
            cover = get_first_image_path(folder, self._sort_display_to_key(self.single_sort_combo.get()))
        self._render_thumbnail(cover, self.single_preview_label, max_size=max_size)

    def _add_folder_to_queue(self, folder_path):
        folder_path = os.path.abspath(
            folder_path
        )

        is_archive = os.path.isfile(folder_path) and folder_path.lower().endswith(ARCHIVE_EXTENSIONS)
        if not os.path.isdir(folder_path) and not is_archive:
            return

        for data in self.batch_queue_items.values():
            if data["path"] == folder_path:
                return

        name = os.path.basename(folder_path)
        if is_archive:
            name = os.path.splitext(name)[0]

        img_count, archive_errors = get_sorted_image_files_with_debug(
            folder_path,
            "natural",
        )
        img_count = len(img_count) if isinstance(img_count, list) else img_count

        status = (
            self._queue_status_display("status_queued")
            if img_count > 0
            else self._queue_status_display("status_no_images")
        )

        if img_count == 0 and archive_errors:
            self.log(f"[Archive scan] {name}: {'; '.join(archive_errors)}")

        item_id = self.batch_tree.insert(
            "",
            "end",
            values=(
                self._compose_title_cell(name, ""),
                "",
                img_count,
                status,
                folder_path,
            ),
            tags=(
                "queue_even" if len(self.batch_tree.get_children()) % 2 == 0 else "queue_odd",
                self._status_key_from_display(status),
            ),
        )

        self.batch_queue_items[item_id] = {
            "path": folder_path,
            "title_en": name,
            "title_jp": "",
            **self._batch_metadata_defaults(),
            "upload_resume": {},
        }
        self._refresh_batch_queue_counter()
        self._save_persistent_queue()

    def _on_dnd_drop(self, event):
        # Tcl already removes list quoting; stripping characters here would
        # corrupt legitimate Windows names containing apostrophes or braces.
        for path in self.tk.splitlist(event.data):
            if os.path.isdir(path):
                self._add_folder_to_queue(path)
            elif os.path.isfile(path):
                if path.lower().endswith(ARCHIVE_EXTENSIONS):
                    self._add_folder_to_queue(path)
                else:
                    self._add_folder_to_queue(os.path.dirname(path))
        return "copy"

    def _add_batch_folders(self):
        d = filedialog.askdirectory(
            title="Select Folder to Add to Queue"
        )

        if d:
            self._add_folder_to_queue(d)

    def _add_batch_archives(self):
        archives = filedialog.askopenfilenames(
            title="Select ZIP/RAR archives to add to the queue",
            filetypes=[
                ("Comic and image archives", "*.zip *.rar *.cbz *.cbr *.7z"),
                ("ZIP archives", "*.zip *.cbz"),
                ("RAR archives", "*.rar *.cbr"),
                ("7-Zip archives", "*.7z"),
                ("All files", "*.*"),
            ],
        )
        for archive_path in archives:
            if str(archive_path).lower().endswith(ARCHIVE_EXTENSIONS):
                self._add_folder_to_queue(archive_path)

    def _add_batch_root_dir(self):
        root_dir = filedialog.askdirectory(
            title=(
                "Select Root Directory "
                "Containing Subfolders"
            )
        )

        if root_dir:
            subfolders = sorted(
                [
                    os.path.join(root_dir, f)
                    for f in os.listdir(root_dir)
                    if os.path.isdir(
                        os.path.join(
                            root_dir,
                            f,
                        )
                    )
                ],
                key=natural_sort_key,
            )

            for f in subfolders:
                self._add_folder_to_queue(f)

    def _remove_selected_batch(self):
        for item in self.batch_tree.selection():
            self.batch_tree.delete(item)
            self.batch_queue_items.pop(
                item,
                None,
            )

        self._refresh_batch_preview()
        self._refresh_batch_queue_counter()
        self._save_persistent_queue()

    def _clear_batch_queue(self):
        for item in self.batch_tree.get_children():
            self.batch_tree.delete(item)

        self.batch_queue_items.clear()

        self._refresh_batch_preview()
        self._refresh_batch_queue_counter()
        self._save_persistent_queue()

    def _update_row_status(
        self,
        item_id,
        new_status,
    ):
        if not item_id:
            return

        status_text = str(new_status)[:80]
        previous = self._row_status_cache.get(item_id)
        if previous == status_text:
            return
        self._row_status_cache[item_id] = status_text

        def update():
            if self.batch_tree.exists(item_id):
                vals = list(
                    self.batch_tree.item(
                        item_id,
                        "values",
                    )
                )

                vals[3] = status_text

                self.batch_tree.item(
                    item_id,
                    values=vals,
                    tags=(
                        "queue_even" if self.batch_tree.index(item_id) % 2 == 0 else "queue_odd",
                        self._status_key_from_display(status_text),
                    ),
                )
                self._refresh_batch_queue_counter()
                self._save_persistent_queue()

        self.after(
            0,
            update,
        )

    def _ensure_pause_state(self, item_id):
        self.batch_pause_flags.setdefault(item_id, False)
        self.batch_pause_events.setdefault(item_id, threading.Event())
        self.batch_pause_events[item_id].set()
        return self.batch_pause_events[item_id]

    def _wait_if_paused(self, item_id):
        while True:
            paused = self.batch_pause_flags.get(item_id, False)
            all_paused = not self.batch_pause_all_event.is_set()
            if not paused and not all_paused:
                return
            self._update_row_status(item_id, self._queue_status_display("status_paused"))
            time.sleep(0.25)

    def _pause_selected_batch(self):
        for item in self.batch_tree.selection():
            values = self.batch_tree.item(item, "values")
            status_key = self._status_key_from_display(values[3] if len(values) > 3 else "")
            if status_key in {"status_published", "status_draft_saved"}:
                continue
            self.batch_pause_flags[item] = True
            self.batch_pause_events.setdefault(item, threading.Event())
            self.batch_pause_events[item].clear()
            self._update_row_status(item, self._queue_status_display("status_paused"))

    def _resume_selected_batch(self):
        resumed = False
        for item in self.batch_tree.selection():
            values = self.batch_tree.item(item, "values")
            status_key = self._status_key_from_display(values[3] if len(values) > 3 else "")
            if status_key in {"status_published", "status_draft_saved"}:
                continue
            self.batch_pause_flags[item] = False
            self.batch_pause_events.setdefault(item, threading.Event())
            self.batch_pause_events[item].set()
            item_values = self.batch_tree.item(item, "values")
            if item_values and self._status_key_from_display(item_values[3]) == "status_paused":
                self._update_row_status(item, self._queue_status_display("status_queued"))
            resumed = True
        if resumed and not self.is_processing:
            self.after(75, self._start_batch_upload)

    def _pause_all_batch(self):
        self.batch_pause_all_event.clear()
        for item in self.batch_tree.get_children():
            values = self.batch_tree.item(item, "values")
            status_key = self._status_key_from_display(values[3] if len(values) > 3 else "")
            if status_key in {"status_published", "status_draft_saved"}:
                continue
            self.batch_pause_flags[item] = True
            self.batch_pause_events.setdefault(item, threading.Event())
            self.batch_pause_events[item].clear()
            self._update_row_status(item, self._queue_status_display("status_paused"))

    def _resume_all_batch(self):
        self._resume_batch_queue()

    def _resume_batch_queue(self):
        """Wake live paused workers or restart all unfinished/error rows if idle."""
        self.batch_pause_all_event.set()
        resumable = {
            "status_paused", "status_error", "status_creating",
            "status_uploading", "status_publishing", "status_queued",
        }
        resumed = 0
        for item in self.batch_tree.get_children():
            values = self.batch_tree.item(item, "values")
            status_key = self._status_key_from_display(values[3] if len(values) > 3 else "")
            if status_key not in resumable:
                continue
            self.batch_pause_flags[item] = False
            event = self.batch_pause_events.setdefault(item, threading.Event())
            event.set()
            if status_key in {
                "status_paused", "status_error", "status_creating",
                "status_uploading", "status_publishing",
            }:
                self._update_row_status(item, self._queue_status_display("status_queued"))
            resumed += 1

        self._save_persistent_queue(force=True)
        if not resumed:
            messagebox.showinfo("Resume Queue", "There are no unfinished uploads to resume.")
            return
        if self.is_processing:
            self.log(f"[Queue] Resumed {resumed} paused/incomplete queue item(s).")
        else:
            self.log(f"[Queue] Restarting {resumed} unfinished/error queue item(s).")
            self.after(75, self._start_batch_upload)

    def _show_selected_draft_preview(self):
        selected = self.batch_tree.selection()
        if not selected:
            return
        item_id = selected[0]
        item_data = self.batch_queue_items.get(item_id)
        if not item_data:
            return
        folder = item_data["path"]
        status = self.batch_tree.item(item_id, "values")[3]
        if self._status_key_from_display(status) != "status_draft_saved":
            messagebox.showinfo(
                "Draft Preview",
                "Only galleries with a saved draft can be previewed here.",
            )
            return
        self._open_gallery_image_preview(item_id, folder, item_data["title_en"])

    def _open_gallery_image_preview(self, item_id, folder_path, title):
        """Open a fast, all-images draft reordering workspace.

        Design goals:
          * Show the entire gallery in one vertically scrollable workspace.
          * Keep each image card alive while reordering so drag/drop is immediate.
          * Use a real per-card Page dropdown, matching the draft-reorder UI pattern.
          * Load thumbnails asynchronously without rebuilding the grid.
          * Apply Changes renames files to a stable ``pg_XX_`` sequence and deletes
            only items explicitly marked for deletion.
        """
        if not os.path.isdir(folder_path):
            messagebox.showwarning(
                "Preview unavailable",
                "The source folder is no longer available.",
            )
            return

        preview_window = ctk.CTkToplevel(self)
        preview_window.title(f"Draft Images - {title}")
        preview_window.geometry("1740x980")
        preview_window.minsize(1500, 760)

        sort_key = self._sort_display_to_key(self.tr("sort_natural"))
        original_paths = get_sorted_image_files(folder_path, sort_key)
        state = {
            "items": [],
            "original_paths": list(original_paths),
            "deleted": set(),
            "drag_item": None,
            "drop_index": None,
            "dragging": False,
            "dirty": False,
            "close_prompt": False,
            "executor": ThreadPoolExecutor(max_workers=8, thread_name_prefix="preview-thumb"),
        }

        for path in original_paths:
            state["items"].append({
                "path": path,
                "tile": None,
                "page_combo": None,
                "filename_label": None,
                "preview_label": None,
                "x_button": None,
            })

        CARD_W = 214
        CARD_H = 360
        GAP_X = 5
        GAP_Y = 7
        COLUMNS = 8
        IMAGE_W = 198
        IMAGE_H = 272

        toolbar = ctk.CTkFrame(preview_window)
        toolbar.pack(fill="x", padx=10, pady=(10, 6))

        ctk.CTkLabel(
            toolbar,
            text="All Pages",
            font=("Arial", 16, "bold"),
        ).pack(side="left", padx=(6, 10))

        info_label = ctk.CTkLabel(
            toolbar,
            text="",
            font=("Arial", 13, "bold"),
        )
        info_label.pack(side="left", padx=(0, 18))

        ctk.CTkLabel(
            toolbar,
            text="Automatic Resorting:",
            font=("Arial", 13, "bold"),
        ).pack(side="left", padx=(0, 6))

        sort_combo = ttk.Combobox(
            toolbar,
            values=[
                "Select a sorting method...",
                "Remove Exact Duplicates",
                "Natural Sort",
                "Lexical Sort",
            ],
            state="readonly",
            width=25,
        )
        sort_combo.current(0)
        sort_combo.pack(side="left", padx=(0, 6))

        status_label = ctk.CTkLabel(
            toolbar,
            text="",
            font=("Arial", 12),
            text_color=self._theme_palette()["muted"],
        )
        status_label.pack(side="left", padx=(8, 0))

        scroll_wrap = ctk.CTkFrame(preview_window, fg_color="transparent")
        scroll_wrap.pack(fill="both", expand=True, padx=10, pady=(0, 8))
        scroll_wrap.grid_rowconfigure(0, weight=1)
        scroll_wrap.grid_columnconfigure(0, weight=1)

        canvas = tk.Canvas(
            scroll_wrap,
            highlightthickness=0,
            borderwidth=0,
            background=self._theme_palette()["canvas"],
            xscrollincrement=1,
            yscrollincrement=1,
        )
        canvas.grid(row=0, column=0, sticky="nsew")

        vbar = ctk.CTkScrollbar(scroll_wrap, orientation="vertical", command=canvas.yview)
        vbar.grid(row=0, column=1, sticky="ns")
        canvas.configure(yscrollcommand=vbar.set)

        gallery_frame = ctk.CTkFrame(canvas, fg_color="transparent")
        gallery_window_id = canvas.create_window((0, 0), window=gallery_frame, anchor="nw")

        def update_scroll_region(_event=None):
            try:
                canvas.configure(scrollregion=canvas.bbox("all"))
            except Exception:
                pass

        gallery_frame.bind("<Configure>", update_scroll_region)

        bottom = ctk.CTkFrame(preview_window, fg_color="transparent")
        bottom.pack(fill="x", padx=10, pady=(0, 10))

        revert_btn = ctk.CTkButton(
            bottom,
            text="Revert Changes",
            width=125,
            command=lambda: revert_changes(),
        )
        revert_btn.pack(side="left", padx=4)

        apply_btn = ctk.CTkButton(
            bottom,
            text="Apply Changes",
            width=125,
            command=lambda: apply_changes(),
        )
        apply_btn.pack(side="left", padx=4)

        publish_btn = ctk.CTkButton(
            bottom,
            text="Publish Gallery",
            width=135,
            command=lambda: publish_draft(),
        )
        publish_btn.pack(side="left", padx=4)

        ctk.CTkLabel(
            bottom,
            text="Drag a card with the left mouse button. Choose a Page from its dropdown to move it instantly.",
            font=("Arial", 12),
            text_color=self._theme_palette()["muted"],
            anchor="w",
        ).pack(side="left", padx=12)

        def active_items():
            return [item for item in state["items"] if item["path"] not in state["deleted"]]

        def mark_dirty():
            state["dirty"] = True
            info_label.configure(text=f"{len(active_items())} images")
            apply_btn.configure(state="normal")

        def update_status(text):
            try:
                status_label.configure(text=text)
            except Exception:
                pass

        def thumb_cache_key(path):
            try:
                st = os.stat(path)
                return (path, int(st.st_mtime_ns), int(st.st_size), IMAGE_W, IMAGE_H)
            except OSError:
                return (path, 0, 0, IMAGE_W, IMAGE_H)

        def install_pil_thumbnail(item, pil_img):
            if not pil_img or item["path"] in state["deleted"]:
                return
            key = thumb_cache_key(item["path"])
            _bounded_cache_set(
                self._preview_pil_cache,
                key,
                pil_img,
                MAX_PREVIEW_CACHE_ENTRIES,
            )
            try:
                ctk_img = ctk.CTkImage(light_image=pil_img, dark_image=pil_img, size=pil_img.size)
                item["preview_image"] = ctk_img
                if item.get("preview_label") is not None:
                    item["preview_label"].configure(image=ctk_img, text="")
            except Exception:
                pass

        def preload_one(item):
            path = item["path"]
            key = thumb_cache_key(path)
            cached = self._preview_pil_cache.get(key)
            if cached is not None:
                self.after(0, lambda it=item, im=cached: install_pil_thumbnail(it, im))
                return
            try:
                with Image.open(path) as raw:
                    img = ImageOps.exif_transpose(raw).convert("RGBA")
                    img.thumbnail((IMAGE_W, IMAGE_H), LANCZOS_FILTER)
                    img = img.copy()
                self.after(0, lambda it=item, im=img: install_pil_thumbnail(it, im))
            except Exception as exc:
                self.after(0, lambda it=item, e=exc: it["preview_label"].configure(text=f"Load error\n{e}"))

        def clear_drop_highlight():
            target = state.get("drop_index")
            if target is None:
                return
            active = active_items()
            if 0 <= target < len(active):
                tile = active[target]["tile"]
                if tile is not None:
                    try:
                        tile.configure(border_width=1, border_color=self._theme_palette()["border"])
                    except Exception:
                        pass
            state["drop_index"] = None

        def set_drop_highlight(index):
            if index == state.get("drop_index"):
                return
            clear_drop_highlight()
            active = active_items()
            if 0 <= index < len(active):
                tile = active[index]["tile"]
                if tile is not None:
                    try:
                        tile.configure(border_width=3, border_color=self._theme_palette()["accent"])
                    except Exception:
                        pass
                state["drop_index"] = index

        def layout_cards():
            active = active_items()
            for index, item in enumerate(active):
                row = index // COLUMNS
                col = index % COLUMNS
                tile = item["tile"]
                if tile is None:
                    continue
                tile.grid(
                    row=row,
                    column=col,
                    padx=GAP_X,
                    pady=GAP_Y,
                    sticky="n",
                )
                combo = item["page_combo"]
                if combo is not None:
                    combo.configure(values=[str(i) for i in range(1, len(active) + 1)])
                    combo.set(str(index + 1))
            rows = (len(active) + COLUMNS - 1) // COLUMNS
            gallery_frame.grid_rowconfigure(rows, minsize=4)
            info_label.configure(text=f"{len(active)} images • 8 columns • all pages visible")
            canvas.configure(scrollregion=canvas.bbox("all"))

        def update_item_page(item):
            active = active_items()
            if item not in active:
                return
            combo = item["page_combo"]
            try:
                destination = int(combo.get())
            except (TypeError, ValueError):
                return
            destination = max(1, min(destination, len(active)))
            current = active.index(item)
            target = destination - 1
            if current == target:
                return
            active.pop(current)
            active.insert(target, item)
            # Reconstruct the master list while retaining pending-deleted items at
            # the end; their eventual deletion means they do not affect the order.
            deleted = [x for x in state["items"] if x["path"] in state["deleted"]]
            state["items"] = active + deleted
            clear_drop_highlight()
            mark_dirty()
            layout_cards()
            update_status(f"Moved to Page {destination}")

        def move_item_to_index(item, destination):
            active = active_items()
            if item not in active:
                return
            current = active.index(item)
            destination = max(0, min(destination, len(active) - 1))
            if current == destination:
                return
            active.pop(current)
            active.insert(destination, item)
            deleted = [x for x in state["items"] if x["path"] in state["deleted"]]
            state["items"] = active + deleted
            clear_drop_highlight()
            mark_dirty()
            layout_cards()
            update_status(f"Moved to Page {destination + 1}")

        def event_to_target_index(event):
            try:
                local_x = canvas.canvasx(event.x_root - canvas.winfo_rootx())
                local_y = canvas.canvasy(event.y_root - canvas.winfo_rooty())
            except Exception:
                return None
            pitch_x = CARD_W + GAP_X * 2
            pitch_y = CARD_H + GAP_Y * 2
            col = int(local_x // pitch_x)
            row = int(local_y // pitch_y)
            if col < 0 or col >= COLUMNS or row < 0:
                return None
            idx = row * COLUMNS + col
            active = active_items()
            if idx >= len(active):
                return len(active) - 1 if active else None
            return idx

        def begin_drag(item, event):
            state["drag_item"] = item
            state["dragging"] = True
            try:
                item["tile"].configure(border_width=3, border_color=self._theme_palette()["accent2"])
            except Exception:
                pass
            canvas.configure(cursor="fleur")
            update_status("Dragging…")
            return "break"

        def drag_motion(item, event):
            if not state.get("dragging") or state.get("drag_item") is not item:
                return "break"
            try:
                top = canvas.winfo_rooty()
                bottom_edge = top + canvas.winfo_height()
                if event.y_root < top + 70:
                    canvas.yview_scroll(-3, "units")
                elif event.y_root > bottom_edge - 70:
                    canvas.yview_scroll(3, "units")
            except Exception:
                pass
            target = event_to_target_index(event)
            if target is not None:
                set_drop_highlight(target)
            return "break"

        def end_drag(item, event):
            if not state.get("dragging") or state.get("drag_item") is not item:
                return "break"
            target = state.get("drop_index")
            clear_drop_highlight()
            state["dragging"] = False
            state["drag_item"] = None
            canvas.configure(cursor="arrow")
            if target is not None:
                move_item_to_index(item, target)
            else:
                layout_cards()
            try:
                for other in active_items():
                    other["tile"].configure(border_width=1, border_color=self._theme_palette()["border"])
            except Exception:
                pass
            update_status("Ready")
            return "break"

        def mark_delete(item):
            if item["path"] in state["deleted"]:
                return
            state["deleted"].add(item["path"])
            try:
                item["tile"].grid_remove()
            except Exception:
                pass
            mark_dirty()
            layout_cards()
            update_status(f"Marked for deletion: {os.path.basename(item['path'])}")

        def restore_deleted():
            if not state["deleted"]:
                return
            state["deleted"].clear()
            mark_dirty()
            layout_cards()
            update_status("Pending deletions restored")

        def apply_changes():
            active = active_items()
            if not active and not state["deleted"]:
                return
            confirm = messagebox.askyesno(
                "Apply Changes",
                "Apply the current page order and pending deletions to the local image folder?\n\n"
                "Files will be renamed using a pg_XX_ prefix so Natural Sort follows the displayed order.",
                parent=preview_window,
            )
            if not confirm:
                return

            preview_window.configure(cursor="watch")
            apply_btn.configure(state="disabled")
            status_label.configure(text="Applying changes…")

            def worker():
                error = None
                try:
                    # Delete only items explicitly marked by the user.
                    for path in list(state["deleted"]):
                        if os.path.exists(path):
                            os.remove(path)

                    # Two-phase rename avoids collisions when files already have
                    # page prefixes such as pg_01_, pg_02_, etc.
                    rename_map = []
                    for index, item in enumerate(active, start=1):
                        old_path = item["path"]
                        if not os.path.exists(old_path):
                            continue
                        base = os.path.basename(old_path)
                        base = re.sub(r"^pg_\d+_", "", base, flags=re.I)
                        new_name = f"pg_{index:02d}_{base}"
                        rename_map.append((old_path, os.path.join(folder_path, new_name)))

                    temp_pairs = []
                    nonce = f".__reorder_{time.time_ns()}__"
                    for idx, (old_path, new_path) in enumerate(rename_map):
                        temp_path = os.path.join(folder_path, f"{nonce}{idx:04d}{Path(old_path).suffix}")
                        os.replace(old_path, temp_path)
                        temp_pairs.append((temp_path, new_path))

                    for temp_path, new_path in temp_pairs:
                        os.replace(temp_path, new_path)
                except Exception as exc:
                    error = str(exc)

                def finish():
                    preview_window.configure(cursor="")
                    if error:
                        apply_btn.configure(state="normal")
                        status_label.configure(text="Apply failed")
                        messagebox.showerror("Apply Changes", error, parent=preview_window)
                        return
                    state["dirty"] = False
                    state["deleted"].clear()
                    # Refresh paths to the names now on disk while retaining card
                    # objects so the UI remains visually stable.
                    new_paths = get_sorted_image_files(folder_path, "natural")
                    by_name = {os.path.basename(x["path"]): x for x in state["items"]}
                    new_items = []
                    for path in new_paths:
                        old_name_match = None
                        for item in state["items"]:
                            old_base = os.path.basename(item["path"])
                            stripped = re.sub(r"^pg_\d+_", "", old_base, flags=re.I)
                            if re.sub(r"^pg_\d+_", "", os.path.basename(path), flags=re.I) == stripped:
                                old_name_match = item
                                break
                        if old_name_match:
                            old_name_match["path"] = path
                            new_items.append(old_name_match)
                    if len(new_items) == len(new_paths):
                        state["items"] = new_items
                    else:
                        # Safe fallback if a filename collision made matching
                        # ambiguous: rebuild cards from the resulting directory.
                        for item in state["items"]:
                            try:
                                item["tile"].destroy()
                            except Exception:
                                pass
                        state["items"] = []
                        for path in new_paths:
                            state["items"].append({
                                "path": path,
                                "tile": None,
                                "page_combo": None,
                                "filename_label": None,
                                "preview_label": None,
                                "x_button": None,
                            })
                        build_cards()
                    layout_cards()
                    apply_btn.configure(state="disabled")
                    status_label.configure(text="Changes applied")

                self.after(0, finish)

            threading.Thread(target=worker, daemon=True).start()

        def revert_changes():
            if not state["dirty"] and not state["deleted"]:
                return
            confirm = messagebox.askyesno(
                "Revert Changes",
                "Revert all page moves and pending deletions in this preview?\n\n"
                "Any changes already applied to disk cannot be reverted by this button.",
                parent=preview_window,
            )
            if not confirm:
                return
            # Restore the original in-memory order. Pending deletions were never
            # written to disk until Apply Changes.
            originals = []
            by_path = {item["path"]: item for item in state["items"]}
            for path in state["original_paths"]:
                if path in by_path:
                    originals.append(by_path[path])
            state["items"] = originals + [x for x in state["items"] if x not in originals]
            state["deleted"].clear()
            state["dirty"] = False
            clear_drop_highlight()
            layout_cards()
            apply_btn.configure(state="disabled")
            update_status("Changes reverted")

        def publish_draft():
            # Keep the existing uploader flow intact. The preview window cannot
            # safely publish a draft without a fresh authenticated gallery token,
            # so provide the same useful behavior as the old preview: direct the
            # caller back to the application's normal publish workflow.
            messagebox.showinfo(
                "Publish Gallery",
                "Apply your local page changes first, then publish the gallery through the uploader's normal draft workflow.",
                parent=preview_window,
            )

        def auto_sort_changed(_event=None):
            method = sort_combo.get()
            if method == "Select a sorting method...":
                return
            if method == "Natural Sort":
                active = active_items()
                active.sort(key=lambda item: natural_sort_key(os.path.basename(item["path"])))
                deleted = [x for x in state["items"] if x["path"] in state["deleted"]]
                state["items"] = active + deleted
                mark_dirty()
                layout_cards()
                update_status("Natural sort applied")
            elif method == "Lexical Sort":
                active = active_items()
                active.sort(key=lambda item: os.path.basename(item["path"]).lower())
                deleted = [x for x in state["items"] if x["path"] in state["deleted"]]
                state["items"] = active + deleted
                mark_dirty()
                layout_cards()
                update_status("Lexical sort applied")
            elif method == "Remove Exact Duplicates":
                def dedupe_worker():
                    import hashlib
                    hashes = {}
                    duplicates = []
                    for item in active_items():
                        path = item["path"]
                        try:
                            digest = hashlib.sha256()
                            with open(path, "rb") as fh:
                                for chunk in iter(lambda: fh.read(1024 * 1024), b""):
                                    digest.update(chunk)
                            key = digest.hexdigest()
                            if key in hashes:
                                duplicates.append(path)
                            else:
                                hashes[key] = path
                        except Exception:
                            continue

                    def finish_dedupe():
                        for path in duplicates:
                            state["deleted"].add(path)
                        if duplicates:
                            mark_dirty()
                            layout_cards()
                            update_status(f"Marked {len(duplicates)} exact duplicates for deletion")
                        else:
                            update_status("No exact duplicates found")

                    self.after(0, finish_dedupe)

                update_status("Scanning for exact duplicates…")
                threading.Thread(target=dedupe_worker, daemon=True).start()

        def build_cards():
            # Create five-column card widgets once. Reordering moves these same
            # widgets; it never destroys/recreates the grid during drag/drop.
            for child in gallery_frame.winfo_children():
                child.destroy()
            for item in state["items"]:
                tile = ctk.CTkFrame(
                    gallery_frame,
                    width=CARD_W,
                    height=CARD_H,
                    corner_radius=0,
                    border_width=1,
                    border_color=self._theme_palette()["border"],
                )
                tile.grid_propagate(False)
                item["tile"] = tile

                head = ctk.CTkFrame(tile, fg_color="transparent", height=38)
                head.pack(fill="x", padx=6, pady=(6, 0))
                head.pack_propagate(False)

                ctk.CTkLabel(
                    head,
                    text="Page",
                    font=("Arial", 13, "bold"),
                ).pack(side="left", padx=(2, 5))

                combo = ttk.Combobox(
                    head,
                    values=[str(i) for i in range(1, max(1, len(active_items())) + 1)],
                    state="readonly",
                    width=5,
                    justify="center",
                )
                combo.pack(side="left")
                item["page_combo"] = combo
                combo.bind("<<ComboboxSelected>>", lambda _e, it=item: update_item_page(it))

                def delete_command(it=item):
                    mark_delete(it)

                xbtn = ctk.CTkButton(
                    head,
                    text="X",
                    width=30,
                    height=28,
                    fg_color="#c62828",
                    hover_color="#e53935",
                    font=("Arial", 14, "bold"),
                    command=delete_command,
                )
                xbtn.pack(side="right")
                item["x_button"] = xbtn

                filename = os.path.basename(item["path"])
                name_label = ctk.CTkLabel(
                    tile,
                    text=filename,
                    font=("Arial", 13, "bold"),
                    width=200,
                    height=42,
                    wraplength=198,
                    justify="center",
                    anchor="center",
                )
                name_label.pack(padx=5, pady=(2, 4))
                item["filename_label"] = name_label

                preview_label = ctk.CTkLabel(
                    tile,
                    text="Loading…",
                    width=IMAGE_W,
                    height=IMAGE_H,
                    anchor="center",
                )
                preview_label.pack(padx=7, pady=(0, 6), fill="both", expand=False)
                item["preview_label"] = preview_label
                item["preview_image"] = None
                cached = self._preview_pil_cache.get(thumb_cache_key(item["path"]))
                if cached is not None:
                    install_pil_thumbnail(item, cached)
                else:
                    preview_label.configure(text="Loading…")

                # Right-click reverse image search on the actual cover.
                preview_label.bind(
                    "<Button-3>",
                    lambda e, p=item["path"]: self._show_image_search_menu(e, p),
                )

                # Drag handlers are bound to both the image and the tile, while
                # the explicit dropdown/X/button retain their normal controls.
                for widget in (tile, name_label, preview_label):
                    widget.bind("<ButtonPress-1>", lambda e, it=item: begin_drag(it, e), add="+")
                    widget.bind("<B1-Motion>", lambda e, it=item: drag_motion(it, e), add="+")
                    widget.bind("<ButtonRelease-1>", lambda e, it=item: end_drag(it, e), add="+")

            layout_cards()

        def mousewheel(event):
            try:
                if event.delta:
                    units = -8 if event.delta > 0 else 8
                    if abs(event.delta) >= 240:
                        units = -12 if event.delta > 0 else 12
                    canvas.yview_scroll(units, "units")
                elif event.num == 4:
                    canvas.yview_scroll(-8, "units")
                elif event.num == 5:
                    canvas.yview_scroll(8, "units")
            except Exception:
                pass
            return "break"

        for widget in (canvas, gallery_frame, preview_window):
            widget.bind("<MouseWheel>", mousewheel, add="+")
            widget.bind("<Button-4>", mousewheel, add="+")
            widget.bind("<Button-5>", mousewheel, add="+")

        def go_top(_event=None):
            canvas.yview_moveto(0.0)
            return "break"
        def go_bottom(_event=None):
            canvas.yview_moveto(1.0)
            return "break"
        def page_up(_event=None):
            canvas.yview_scroll(-1, "pages")
            return "break"
        def page_down(_event=None):
            canvas.yview_scroll(1, "pages")
            return "break"

        for seq, handler in (("<Home>", go_top), ("<End>", go_bottom), ("<Prior>", page_up), ("<Next>", page_down)):
            preview_window.bind_all(seq, handler, add="+")

        sort_combo.bind("<<ComboboxSelected>>", auto_sort_changed)

        def on_close():
            if state["dirty"] or state["deleted"]:
                answer = messagebox.askyesnocancel(
                    "Close Preview",
                    "There are unapplied changes.\n\nYes = Apply Changes\nNo = Discard in preview\nCancel = Keep window open",
                    parent=preview_window,
                )
                if answer is None:
                    return
                if answer:
                    apply_changes()
                    # apply_changes runs asynchronously; don't destroy the window
                    # until the worker has finished.
                    return
            try:
                state["executor"].shutdown(wait=False, cancel_futures=True)
            except Exception:
                pass
            for seq in ("<Home>", "<End>", "<Prior>", "<Next>"):
                try:
                    preview_window.unbind_all(seq)
                except Exception:
                    pass
            preview_window.destroy()

        preview_window.protocol("WM_DELETE_WINDOW", on_close)

        build_cards()
        for item in active_items():
            state["executor"].submit(preload_one, item)
        update_status("Loading thumbnails…")
        apply_btn.configure(state="disabled")
        preview_window.after(40, lambda: canvas.configure(scrollregion=canvas.bbox("all")))
        preview_window.grab_set()

    def _browse_single_folder(self):
        d = filedialog.askdirectory(
            title="Select Folder Containing Images"
        )

        if d:
            self.single_folder_entry.delete(
                0,
                "end",
            )

            self.single_folder_entry.insert(
                0,
                d,
            )

            self._refresh_single_preview()

    def log(self, msg):
        text = str(msg)
        # Feature 3: suppress [Debug]-prefixed lines when the toggle is off.
        if text.startswith("[Debug]"):
            try:
                enabled = self.debug_enabled.get()
            except Exception:
                enabled = True
            if not enabled:
                return
        self.log_queue.put(text)

    def _poll_log_queue(self):
        try:
            while True:
                msg = self.log_queue.get_nowait()

                self.log_textbox.insert(
                    "end",
                    msg + "\n",
                )

                self.log_textbox.see("end")

        except queue.Empty:
            pass

        self.after(
            100,
            self._poll_log_queue,
        )

    def _get_cookies(self):
        member_id = (
            self.member_id_entry.get().strip()
            or HARDCODED_MEMBER_ID
        )

        pass_hash = (
            self.pass_hash_entry.get().strip()
            or HARDCODED_PASS_HASH
        )

        igneous = (
            self.igneous_entry.get().strip()
            or HARDCODED_IGNEOUS
        )

        sk = HARDCODED_SK

        cookies = {}

        if member_id:
            cookies["ipb_member_id"] = member_id

        if pass_hash:
            cookies["ipb_pass_hash"] = pass_hash

        if igneous:
            cookies["igneous"] = igneous

        if sk:
            cookies["sk"] = sk

        return cookies

    def _set_processing_state(self, active):
        self.is_processing = active

        state = (
            "disabled"
            if active
            else "normal"
        )

        self.batch_start_btn.configure(
            state=state
        )

        self.single_start_btn.configure(
            state=state
        )
        self._load_batch_item_metadata()
        self.single_language_type_combo.configure(state="disabled" if active else "readonly")
        self.single_ai_checkbox.configure(state="disabled" if active else "normal")

    def _populate_gui_from_schema(self, schema):
        """Refresh available options only; Sync never changes a user's choice."""
        def apply_schema():
            self._creation_schema = schema
            for key, suffix in (("category", "cat"), ("lang", "lang"), ("folder", "folder")):
                values = [str(label) for label, _ in schema.get(key, {}).get("options", []) if label]
                if not values:
                    continue
                for prefix in ("batch", "single"):
                    widget = getattr(self, f"{prefix}_{suffix}_combo", None)
                    if widget is not None:
                        current = widget.get()
                        widget.configure(values=values)
                        widget.set(current)
                field = {"category": "category", "lang": "language", "folder": "gallery_folder"}[key]
                widget = getattr(self, "batch_item_metadata_combos", {}).get(field)
                if widget is not None:
                    current = widget.get()
                    widget.configure(values=values)
                    widget.set(current)
            self._load_batch_item_metadata()
            self._save_config()
        self.after(0, apply_schema)

    def _validate_session(self):
        if self.is_processing:
            messagebox.showwarning(
                self.tr("msg_busy"),
                self.tr("msg_busy_validate"),
            )
            return

        cookies = self._get_cookies()
        use_ex = bool(self.use_ex_var.get())
        cookie_file = str(self._resolve_cookie_file() or "cookies.txt")
        self._save_config()

        def worker():
            try:
                self.log("Validating current E-Hentai session...")

                backend = EHentaiBackend(
                    cookies,
                    log_fn=self.log,
                    use_ex=use_ex,
                    cookie_file=cookie_file,
                )

                backend.ensure_tos_accepted()
                saved_path = backend.save_session_to_cookie_file()

                if saved_path:
                    self.log(f"Session validation passed. Cookie state saved to {saved_path}.")
                    self.after(0, lambda: messagebox.showinfo(
                        "Session valid",
                        f"Current E-Hentai session is valid and saved to:\n{saved_path}",
                        parent=self,
                    ))
                else:
                    self.log("Session validation passed, but cookie export could not be written.")
                    self.after(0, lambda: messagebox.showinfo(
                        "Session valid",
                        "Current E-Hentai session is valid.",
                        parent=self,
                    ))

            except Exception as exc:
                self.log(f"Session validation failed: {exc}")
                self.after(0, lambda exc=exc: messagebox.showerror(
                    "Session validation failed",
                    str(exc),
                    parent=self,
                ))

        threading.Thread(
            target=worker,
            daemon=True,
        ).start()

    def _sync_server_form(self):
        if getattr(self, '_form_sync_in_progress', False):
            return
        self._form_sync_in_progress = True
        cookies = self._get_cookies()
        use_ex = bool(self.use_ex_var.get())
        cookie_file = str(self._resolve_cookie_file() or 'cookies.txt')
        if hasattr(self, 'batch_item_metadata_hint'):
            self.batch_item_metadata_hint.configure(text='Loading all language and gallery-folder choices from the server…')
        def finish(error=None):
            self._form_sync_in_progress = False
            if error:
                self.log('Server form sync failed: ' + error)
                if hasattr(self, 'batch_item_metadata_hint'):
                    self.batch_item_metadata_hint.configure(
                        text='Refresh failed. Saved choices were kept. Check the session and see the console for details.')
            else:
                self._load_batch_item_metadata()
        def worker():
            try:
                self.log('Fetching live gallery categories, languages and gallery folders…')
                backend = EHentaiBackend(cookies, log_fn=self.log, use_ex=use_ex,
                                         cookie_file=cookie_file, save_cookie_file=False)
                schema = backend.get_creation_schema(refresh=True)
                self._populate_gui_from_schema(schema)
                counts = {key: len(schema.get(key, {}).get('options', [])) for key in ('category', 'lang', 'folder')}
                self.log(f"Server choices loaded: {counts['category']} categories, {counts['lang']} languages, {counts['folder']} gallery folders. Each gallery keeps its own selections.")
                self.after(0, finish)
            except Exception as exc:
                self.after(0, lambda error=str(exc): finish(error))
        threading.Thread(target=worker, daemon=True).start()

    def _start_single_upload(self):
        if self.is_processing:
            messagebox.showwarning(
                self.tr("msg_busy"),
                self.tr("msg_busy_running"),
            )
            return

        cookies = self._get_cookies()

        folder = (
            self.single_folder_entry
            .get()
            .strip()
        )

        if not folder or not os.path.isdir(folder):
            messagebox.showerror(
                self.tr("msg_error"),
                self.tr("msg_folder_missing"),
            )
            return

        self._save_config()

        data = {
            "use_ex": bool(self.use_ex_var.get()),
            "cookie_file": str(self._resolve_cookie_file() or "cookies.txt"),
            "batch_size": max(1, min(UPLOAD_MAX_REQUEST_FILES, int(self.batch_size_var.get()))),
            "delay": max(0.0, min(5.0, float(self.delay_var.get()))),
            "title_jp": (
                self.single_jtitle_entry
                .get()
                .strip()
            ),
            "title_en": (
                self.single_etitle_entry
                .get()
                .strip()
                or os.path.basename(folder)
            ),
            "category": (
                self.single_cat_combo.get()
            ),
            "language": (
                self.single_lang_combo
                .get()
                .strip()
            ),
            "gallery_folder": (
                self.single_folder_combo
                .get()
                .strip()
            ),
            "sort_mode": (
                self._sort_display_to_key(self.single_sort_combo.get())
            ),
            "local_folder": folder,
            "language_type": self.single_language_type_combo.get(),
            "ai_generated": bool(self.single_ai_var.get()),
            "publish": (
                self.single_publish_var.get()
            ),
            "unlisted": (
                self.single_unlisted_var.get()
            ),
        }

        self._set_processing_state(True)

        threading.Thread(
            target=self._single_worker,
            args=(cookies, data),
            daemon=True,
        ).start()

    def _single_worker(self, cookies, data):
        try:
            backend = EHentaiBackend(
                cookies,
                log_fn=self.log,
                use_ex=data["use_ex"],
                cookie_file=data["cookie_file"],
            )

            backend.ensure_tos_accepted()

            images = get_sorted_image_files(
                data["local_folder"],
                data["sort_mode"],
            )

            if not images:
                self.log(
                    "No valid images found to upload."
                )
                return

            batch_size = data["batch_size"]
            delay = data["delay"]
            total_images = len(images)

            self.log(
                f"Uploading {total_images} images "
                f"(batch size {batch_size}, max per gallery {MAX_GALLERY_IMAGES})..."
            )

            uploaded_total = 0
            gallery_count = (total_images + MAX_GALLERY_IMAGES - 1) // MAX_GALLERY_IMAGES

            for gallery_index in range(gallery_count):
                chunk_start = gallery_index * MAX_GALLERY_IMAGES
                chunk_end = min(chunk_start + MAX_GALLERY_IMAGES, total_images)
                chunk = images[chunk_start:chunk_end]

                effective_title_en = (
                    data["title_en"] if gallery_index == 0 else f"{data['title_en']} (Part {gallery_index + 1})"
                )
                effective_title_jp = (
                    data["title_jp"] if gallery_index == 0 else (
                        f"{data['title_jp']} (Part {gallery_index + 1})" if data["title_jp"] else ""
                    )
                )

                gid, token = backend.create_gallery(
                    title_en=effective_title_en,
                    title_jp=effective_title_jp,
                    category=data["category"],
                    language=data["language"],
                    folder=data["gallery_folder"],
                    unlisted=data["unlisted"],
                    language_type=data.get("language_type", "Official / Textless"),
                    ai_generated=data.get("ai_generated", False),
                )

                self.log(
                    f"[Gallery {gallery_index + 1}/{gallery_count}] "
                    f"Created draft upload ID: {gid} for {len(chunk)} images"
                )

                for offset in range(0, len(chunk), batch_size):
                    start_index = offset + 1
                    upload_chunk = chunk[offset:offset + batch_size]
                    self.log(
                        f"[{uploaded_total + len(upload_chunk)}/{total_images}] "
                        f"Uploading {len(upload_chunk)} files to GID {gid}..."
                    )

                    backend.upload_files(
                        gid,
                        upload_chunk,
                        start_index,
                    )

                    uploaded_total += len(upload_chunk)

                    if delay > 0 and offset + batch_size < len(chunk):
                        time.sleep(delay)

                if data["publish"]:
                    self.log(
                        f"Publishing gallery {gallery_index + 1}/{gallery_count}..."
                    )

                    publish_result = backend.publish_gallery(
                        gid,
                        token,
                        expected_files=len(chunk),
                    )

                    self.log(
                        "Successfully published and verified gallery: "
                        f"{publish_result.get('gallery_url') or publish_result.get('gid') or gid}"
                    )
                else:
                    self.log(
                        f"Upload Complete! "
                        f"Draft saved at upload ID: {gid}"
                    )

        except Exception as e:
            self.log(
                f"ERROR processing single gallery: {e}"
            )

        finally:
            self.after(
                0,
                lambda: self._set_processing_state(
                    False
                ),
            )

    def _start_batch_upload(self):
        if self.is_processing:
            messagebox.showwarning(
                self.tr("msg_busy"),
                self.tr("msg_busy_running"),
            )
            return

        cookies = self._get_cookies()

        items = self.batch_tree.get_children()
        self.batch_pause_all_event.set()
        for item_id in items:
            self.batch_pause_flags.setdefault(item_id, False)
            self.batch_pause_events.setdefault(item_id, threading.Event())
            self.batch_pause_events[item_id].set()

        if not items:
            messagebox.showinfo(
                self.tr("msg_empty_queue"),
                self.tr("msg_empty_queue_body"),
            )
            return

        batch_tasks = []
        for item_id in items:
            item_data = self.batch_queue_items.get(
                item_id
            )

            if not item_data:
                continue

            vals = self.batch_tree.item(
                item_id,
                "values",
            )

            status_display = vals[3] if len(vals) > 3 else self._queue_status_display("status_queued")
            status_key = self._status_key_from_display(status_display)
            status_text = self.tr(status_key)

            if status_key in {"status_published", "status_draft_saved"}:
                continue
            if status_key in {"status_creating", "status_uploading", "status_publishing"}:
                self.log(f"[Batch] Skipping live in-progress row {item_id}: {status_text}")
                continue

            # Recount at the last responsible moment.  The queue's displayed
            # count may predate an OCR-driven rename/copy operation, and must
            # never decide whether real files are uploaded.
            img_count = count_images_in_folder(item_data["path"])
            if len(vals) >= 4:
                vals = list(vals)
                vals[2] = img_count
                if img_count > 0 and status_key == "status_no_images":
                    status_key = "status_queued"
                    vals[3] = self._queue_status_display(status_key)
                elif img_count == 0 and status_key not in {"status_published", "status_draft_saved"}:
                    status_key = "status_no_images"
                    vals[3] = self._queue_status_display(status_key)
                self.batch_tree.item(item_id, values=vals)

            if img_count > 0:
                batch_tasks.append(
                    (
                        item_id,
                        item_data["path"],
                        item_data["title_en"],
                        item_data["title_jp"],
                        self._batch_item_metadata(item_data),
                    )
                )

        if not batch_tasks:
            messagebox.showinfo(
                self.tr("msg_no_images"),
                self.tr("msg_no_images_body"),
            )
            return

        settings = {
            "use_ex": bool(self.use_ex_var.get()),
            "cookie_file": str(self._resolve_cookie_file() or "cookies.txt"),
            "workers": max(1, min(UPLOAD_MAX_WORKERS, int(self.workers_var.get()))),
            "batch_size": max(1, min(UPLOAD_MAX_REQUEST_FILES, int(self.batch_size_var.get()))),
            "delay": max(0.0, min(5.0, float(self.delay_var.get()))),
            "category": (
                self.batch_cat_combo.get()
            ),
            "language": (
                self.batch_lang_combo.get()
                .strip()
            ),
            "folder": (
                self.batch_folder_combo.get()
                .strip()
            ),
            "sort_mode": (
                self._sort_display_to_key(self.batch_sort_combo.get())
            ),
            "publish": (
                self.batch_publish_var.get()
            ),
            "unlisted": (
                self.batch_unlisted_var.get()
            ),
        }

        self._save_config()
        self._set_processing_state(True)

        threading.Thread(
            target=self._batch_worker,
            args=(
                cookies,
                batch_tasks,
                settings,
            ),
            daemon=True,
        ).start()

    def _process_one_gallery(
        self,
        item_id,
        path,
        title_en,
        title_jp,
        settings,
        cookies,
        batch_size,
        delay,
    ):
        """Run a single gallery end-to-end inside a worker thread.

        Each worker uses its OWN EHentaiBackend (own requests.Session) cloned
        from the same cookies and does NOT write cookies.txt. ToS acceptance
        is performed once in the main thread before the pool starts.
        Within a single gallery, image chunks are uploaded SEQUENTIALLY to
        avoid same-draft races.
        """
        try:
            backend = EHentaiBackend(
                cookies,
                log_fn=self.log,
                use_ex=settings["use_ex"],
                cookie_file=settings["cookie_file"],
                save_cookie_file=False,
            )

            self._ensure_pause_state(item_id)
            self._wait_if_paused(item_id)

            images = get_sorted_image_files(
                path,
                settings["sort_mode"],
            )
            if not images:
                self._update_row_status(
                    item_id,
                    self._queue_status_display("status_no_images"),
                )
                return

            total_images = len(images)
            gallery_count = (total_images + MAX_GALLERY_IMAGES - 1) // MAX_GALLERY_IMAGES

            item_data = self.batch_queue_items.get(item_id, {})
            saved_resume = item_data.get("upload_resume") or {}
            try:
                uploaded_total = max(0, int(saved_resume.get("uploaded_total", 0)))
            except Exception:
                uploaded_total = 0
            try:
                start_gallery_index = (
                    max(0, min(gallery_count - 1, int(saved_resume.get("gallery_index", 0))))
                    if saved_resume.get("gid") else 0
                )
            except Exception:
                start_gallery_index = 0
            for gallery_index in range(start_gallery_index, gallery_count):
                self._ensure_pause_state(item_id)
                self._wait_if_paused(item_id)

                chunk_start = gallery_index * MAX_GALLERY_IMAGES
                chunk_end = min(chunk_start + MAX_GALLERY_IMAGES, total_images)
                chunk = images[chunk_start:chunk_end]
                gallery_title_en = title_en if gallery_index == 0 else f"{title_en} (Part {gallery_index + 1})"
                gallery_title_jp = title_jp if gallery_index == 0 else (
                    f"{title_jp} (Part {gallery_index + 1})" if title_jp else ""
                )

                resume_this_part = (
                    saved_resume
                    and int(saved_resume.get("gallery_index", -1)) == gallery_index
                    and saved_resume.get("gid")
                )
                if resume_this_part:
                    gid = str(saved_resume["gid"])
                    token = saved_resume.get("token")
                    uploaded_in_part = max(
                        0,
                        min(len(chunk), int(saved_resume.get("uploaded_in_part", 0))),
                    )
                    uploaded_total = max(
                        uploaded_total,
                        chunk_start + uploaded_in_part,
                    )
                    self.log(
                        f"[Resume] Continuing existing draft {gid} at image "
                        f"{uploaded_in_part + 1}/{len(chunk)} for '{title_en}'."
                    )
                else:
                    self._update_row_status(
                        item_id,
                        self._queue_status_display("status_creating"),
                    )
                    gid, token = backend.create_gallery(
                        title_en=gallery_title_en,
                        title_jp=gallery_title_jp,
                        category=settings["category"],
                        language=settings["language"],
                        folder=settings["folder"],
                        unlisted=settings["unlisted"],
                        language_type=settings.get("language_type", "Official / Textless"),
                        ai_generated=settings.get("ai_generated", False),
                    )
                    uploaded_in_part = 0
                    saved_resume = {
                        "gid": str(gid),
                        "token": token,
                        "gallery_index": gallery_index,
                        "uploaded_in_part": 0,
                        "uploaded_total": chunk_start,
                    }
                    item_data["upload_resume"] = saved_resume

                self._update_row_status(
                    item_id,
                    f"{self._queue_status_display('status_uploading')} {uploaded_total}/{total_images}",
                )

                for offset in range(uploaded_in_part, len(chunk), batch_size):
                    chunk_number = offset // batch_size + 1
                    start_index = offset + 1
                    upload_chunk = chunk[offset:offset + batch_size]
                    self._wait_if_paused(item_id)
                    self.log(
                        f"[Debug] Uploading chunk {chunk_number} for gallery {gallery_index + 1}: "
                        f"files {start_index}-{start_index + len(upload_chunk) - 1} "
                        f"({len(upload_chunk)} files) to ulgid={gid}"
                    )
                    backend.upload_files(gid, upload_chunk, start_index)
                    uploaded_total += len(upload_chunk)
                    uploaded_in_part += len(upload_chunk)
                    saved_resume.update({
                        "gid": str(gid),
                        "token": token,
                        "gallery_index": gallery_index,
                        "uploaded_in_part": uploaded_in_part,
                        "uploaded_total": uploaded_total,
                    })
                    item_data["upload_resume"] = saved_resume
                    self._update_row_status(
                        item_id,
                        f"{self._queue_status_display('status_uploading')} {uploaded_total}/{total_images}",
                    )
                    if delay > 0 and offset + batch_size < len(chunk):
                        time.sleep(delay)

                if settings["publish"]:
                    self._update_row_status(
                        item_id,
                        self._queue_status_display("status_publishing"),
                    )

                    publish_result = backend.publish_gallery(
                        gid,
                        token,
                        expected_files=len(chunk),
                    )

                    self._update_row_status(
                        item_id,
                        self._queue_status_display("status_published"),
                    )

                    self.log(
                        "Successfully published and verified gallery: "
                        f"{publish_result.get('gallery_url') or publish_result.get('gid') or gid}"
                    )
                else:
                    self._update_row_status(
                        item_id,
                        self._queue_status_display("status_draft_saved"),
                    )

                    self.log(
                        f"Draft saved at upload ID: {gid}"
                    )

                # This part is complete. A later part receives its own draft
                # state; when all parts finish, no resumable draft remains.
                item_data["upload_resume"] = {}
                saved_resume = {}

        except Exception as err:
            self.log(
                f"ERROR on '{title_en}': {err}"
            )

            try:
                self.log(f"[Traceback]\n{traceback.format_exc()}")
            except Exception:
                pass

            self._update_row_status(
                item_id,
                f"{self._queue_status_display('status_error')} {str(err)[:72]}",
            )

    def _batch_worker(
        self,
        cookies,
        batch_tasks,
        settings,
    ):
        try:
            # ToS acceptance runs ONCE in the main thread before the pool; the
            # per-worker backends reuse this authenticated session's cookies.
            backend = EHentaiBackend(
                cookies,
                log_fn=self.log,
                use_ex=settings["use_ex"],
                cookie_file=settings["cookie_file"],
            )

            backend.ensure_tos_accepted()

            total = len(batch_tasks)

            workers = max(1, min(UPLOAD_MAX_WORKERS, int(settings["workers"])))
            batch_size = max(1, min(UPLOAD_MAX_REQUEST_FILES, int(settings["batch_size"])))
            delay = settings["delay"]

            self.log(
                f"--- Starting Batch Process "
                f"for {total} Galleries ---"
            )
            self.log(
                f"[Debug] Legacy multipart requests: workers={workers}, "
                f"batch_size={batch_size}, delay={delay}"
            )

            with ThreadPoolExecutor(max_workers=workers) as executor:
                futures = []
                for idx, (
                    item_id,
                    path,
                    title_en,
                    title_jp,
                    item_metadata,
                ) in enumerate(
                    batch_tasks,
                    1,
                ):
                    self.log(
                        f"\n[{idx}/{total}] "
                        f"Processing: {title_en}"
                    )
                    futures.append(
                        executor.submit(
                            self._process_one_gallery,
                            item_id,
                            path,
                            title_en,
                            title_jp,
                            {**settings, "category": item_metadata["category"],
                             "language": item_metadata["language"],
                             "folder": item_metadata["gallery_folder"],
                             "language_type": item_metadata.get("language_type", "Official / Textless"),
                             "ai_generated": item_metadata.get("ai_generated", False)},
                            cookies,
                            batch_size,
                            delay,
                        )
                    )

                for fut in futures:
                    try:
                        fut.result()
                    except Exception as exc:
                        self.log(f"[Debug] Worker raised: {exc}")

            self.log(
                "\n--- All Batch Tasks Complete ---"
            )

        except Exception as e:
            self.log(
                f"Fatal Batch Error: {e}"
            )

        finally:
            self.after(
                0,
                lambda: self._set_processing_state(
                    False
                ),
            )

    def _flush_split_geometry(self):
        self._split_frame_after = None
        width = getattr(self, '_pending_right_width', None)
        top = getattr(self, '_pending_right_top', None)
        self._pending_right_width = self._pending_right_top = None
        if width is not None and width != getattr(self, '_applied_right_width', None):
            self._applied_right_width = width
            self.right_pane_frame.configure(width=width)
            self.app_body.grid_columnconfigure(2, minsize=width)
        if top is not None and top != getattr(self, '_applied_right_top', None):
            self._applied_right_top = top
            self._right_top_target = top
            self.right_pane_frame.grid_rowconfigure(0, weight=0, minsize=top)
            self.right_pane_frame.grid_rowconfigure(2, weight=1, minsize=150)

    def _finish_split_drag(self, grip):
        pending = getattr(self, '_split_frame_after', None)
        if pending is not None:
            self.after_cancel(pending)
        self._flush_split_geometry()
        try:
            grip.grab_release()
        except tk.TclError:
            pass
        self._save_config()

    def _batch_metadata_defaults(self):
        return {"category": self.batch_cat_combo.get().strip(),
                "language": self.batch_lang_combo.get().strip(),
                "gallery_folder": self.batch_folder_combo.get().strip(),
                "language_type": "Official / Textless", "ai_generated": False}


    def _batch_item_metadata(self, item):
        defaults = self._batch_metadata_defaults()
        metadata = {key: str(item.get(key) or value) for key, value in defaults.items()
                    if key != "ai_generated"}
        # Keep JSON booleans as booleans; bool("False") would incorrectly mark a gallery as AI.
        metadata["ai_generated"] = item.get("ai_generated", False) is True
        return metadata


    def _build_batch_item_metadata_editor(self, parent):
        """Per-row editor: toolbar values are defaults for newly queued sources."""
        frame = ctk.CTkFrame(parent, fg_color="transparent")
        frame.pack(fill="x", pady=(0, 10))
        frame.grid_columnconfigure(1, weight=1)
        ctk.CTkLabel(frame, text="THIS GALLERY · saved separately", anchor="w",
                     font=(self.input_font_family, 11, "bold"), text_color="#d7b86a").grid(
                         row=0, column=0, columnspan=2, sticky="ew", pady=(4, 6))
        self.batch_item_metadata_combos = {}
        for row, (field, label, default_widget) in enumerate((
            ("category", "Category", self.batch_cat_combo),
            ("language", "Language", self.batch_lang_combo),
            ("gallery_folder", "Gallery folder", self.batch_folder_combo),
        ), 1):
            ctk.CTkLabel(frame, text=label, anchor="w",
                         font=(self.input_font_family, 11)).grid(row=row, column=0, padx=(0, 8), sticky="w")
            combo = ctk.CTkComboBox(frame, values=list(default_widget.cget("values")),
                                   height=30, state="disabled",
                                   command=lambda value, key=field: self._set_batch_item_metadata(key, value))
            combo.grid(row=row, column=1, sticky="ew", pady=3)
            combo.set("")
            self.batch_item_metadata_combos[field] = combo
        ctk.CTkLabel(frame, text="Language type", anchor="w",
                     font=(self.input_font_family, 11)).grid(row=4, column=0, padx=(0, 8), sticky="w")
        language_type_combo = ctk.CTkComboBox(
            frame, values=["Official / Textless", "Translated", "Rewrite"],
            height=30, state="disabled",
            command=lambda value: self._set_batch_item_metadata("language_type", value))
        language_type_combo.grid(row=4, column=1, sticky="ew", pady=3)
        language_type_combo.set("")
        self.batch_item_metadata_combos["language_type"] = language_type_combo
        self.batch_item_ai_var = tk.BooleanVar(value=False)
        self.batch_item_ai_checkbox = ctk.CTkCheckBox(
            frame, text="Primarily AI-generated artwork/images",
            variable=self.batch_item_ai_var, state="disabled",
            font=(self.input_font_family, 11),
            command=lambda: self._set_batch_item_metadata("ai_generated", bool(self.batch_item_ai_var.get())))
        self.batch_item_ai_checkbox.grid(row=5, column=0, columnspan=2, sticky="w", pady=(7, 3))
        self.batch_item_metadata_hint = ctk.CTkLabel(
            frame, text="Select one row to edit. Toolbar choices apply to new additions.",
            wraplength=340, justify="left", anchor="w", font=(self.input_font_family, 10),
            text_color="#aaa69c")
        self.batch_item_metadata_hint.grid(row=6, column=0, columnspan=2, sticky="ew", pady=(5, 0))
        ctk.CTkButton(frame, text="Refresh server choices", height=28,
                      command=self._sync_server_form).grid(row=7, column=0, columnspan=2, sticky="ew", pady=(6, 0))
        self.batch_tree.bind("<<TreeviewSelect>>", self._load_batch_item_metadata, add="+")


    def _load_batch_item_metadata(self, event=None):
        widgets = getattr(self, "batch_item_metadata_combos", {})
        if not widgets:
            return
        selected = self.batch_tree.selection()
        item_id = selected[0] if len(selected) == 1 else None
        item = self.batch_queue_items.get(item_id)
        self._batch_metadata_item_id = item_id
        metadata = self._batch_item_metadata(item) if item else {}
        self.batch_item_ai_var.set(metadata.get("ai_generated", False))
        self.batch_item_ai_checkbox.configure(state="normal" if item and not self.is_processing else "disabled")
        unavailable = []
        for field, widget in widgets.items():
            value = metadata.get(field, "")
            widget.set(value)
            widget.configure(state="readonly" if item and not self.is_processing else "disabled")
            if value and value not in widget.cget("values"):
                unavailable.append(field.replace("_", " "))
        if unavailable:
            hint = "Saved choice is absent from the server list: " + ", ".join(unavailable) + ". Choose a current value before upload."
        elif item:
            hint = "Changes save to this gallery only. Sync refreshes choices without replacing them."
        else:
            hint = "Select one row to edit. Toolbar choices apply to new additions."
        if not getattr(self, "_creation_schema", None):
            hint += " Refresh server choices to load all languages and your gallery folders."
        self.batch_item_metadata_hint.configure(text=hint)


    def _set_batch_item_metadata(self, field, value):
        if self.is_processing or field not in {"category", "language", "gallery_folder", "language_type", "ai_generated"}:
            return
        item_id = getattr(self, "_batch_metadata_item_id", None)
        # A delayed dropdown event must never write into the newly selected row.
        if self.batch_tree.selection() != (item_id,):
            self._load_batch_item_metadata()
            return
        item = self.batch_queue_items.get(item_id)
        if item is None:
            return
        if field == "language_type" and value not in {"Official / Textless", "Translated", "Rewrite"}:
            return
        item[field] = (value is True) if field == "ai_generated" else str(value).strip()
        self._save_persistent_queue(force=True)
        if hasattr(self, "_refresh_batch_metadata_columns"):
            self._refresh_batch_metadata_columns(item_id)
        self._load_batch_item_metadata()

    def _batch_tree_visible_columns(self):
        cols = self.batch_tree.cget("displaycolumns")
        if cols == "#all" or tuple(cols) == ("#all",):
            cols = self.batch_tree.cget("columns")
        return tuple(cols)


    def _batch_tree_drop_target(self, x):
        if not 0 <= x <= self.batch_tree.winfo_width():
            return None
        cols = self._batch_tree_visible_columns()
        total_width = sum(int(self.batch_tree.column(c, "width")) for c in cols)
        left = -round(float(self.batch_tree.xview()[0]) * total_width)
        for col in cols:
            width = int(self.batch_tree.column(col, "width"))
            if left <= x <= left + width:
                after = x >= left + width / 2
                return col, after, left + width if after else left
            left += width
        return (cols[-1], True, left) if cols else None


    def _on_batch_tree_heading_motion(self, event):
        source = getattr(self, "_batch_tree_drag_col", None)
        if not source:
            return
        origin_x, origin_y = self._batch_tree_drag_origin
        if not self._batch_tree_drag_active and max(abs(event.x-origin_x), abs(event.y-origin_y)) < 7:
            return
        self._batch_tree_drag_active = True
        self.batch_tree.configure(cursor="fleur")
        if event.x < 24:
            self.batch_tree.xview_scroll(-1, "units")
        elif event.x > self.batch_tree.winfo_width() - 24:
            self.batch_tree.xview_scroll(1, "units")
        target = self._batch_tree_drop_target(event.x)
        if target and 0 <= event.y <= self.batch_tree.winfo_height():
            target_name, after, marker_x = target
            self._batch_tree_drop_marker.place(x=max(0, marker_x - 1), y=0, width=3, relheight=1)
            self._batch_tree_drop_marker.lift()
            source_label = self.batch_tree.heading(source, "text")
            target_label = self.batch_tree.heading(target_name, "text")
            self.batch_queue_scroll_hint.configure(text=f"Move {source_label} {'after' if after else 'before'} {target_label} · Esc cancels")
        else:
            self._batch_tree_drop_marker.place_forget()
            self.batch_queue_scroll_hint.configure(text="Release outside the table to cancel · Esc cancels")
        return "break"


    def _cancel_batch_tree_heading_drag(self, event=None):
        self._batch_tree_drag_col = None
        self._batch_tree_drag_active = False
        self.batch_tree.configure(cursor="")
        marker = getattr(self, "_batch_tree_drop_marker", None)
        if marker is not None:
            marker.place_forget()
        self.batch_queue_scroll_hint.configure(text="Drag a heading to reorder · Drag its edge to resize · Double-click its edge to fit")
        if event is not None:
            return "break"


    def _reset_batch_tree_columns(self):
        self.batch_tree["displaycolumns"] = ("status", "title_en", "title_jp", "image_count", "path")
        for name, width, minimum, anchor, stretch in (
            ("status", 140, 100, "w", False),
            ("title_en", 360, 220, "w", True),
            ("title_jp", 290, 180, "w", True),
            ("image_count", 86, 70, "center", False),
            ("path", 320, 180, "w", True),
        ):
            self.batch_tree.column(name, width=width, minwidth=minimum, anchor=anchor, stretch=stretch)
            self.batch_tree.heading(name, anchor=anchor)


    def _autofit_batch_tree_column(self, event):
        if self.batch_tree.identify_region(event.x, event.y) != "separator":
            return
        self._cancel_batch_tree_heading_drag()
        name = self._batch_tree_display_column_from_id(self.batch_tree.identify_column(event.x))
        if not name:
            return
        font = tkfont.Font(root=self, family=self.input_font_family, size=11)
        width = font.measure(self.batch_tree.heading(name, "text")) + 40
        # Bound the measurement work for huge queues; do not change row data.
        for row_id in self.batch_tree.get_children()[:300]:
            width = max(width, font.measure(str(self.batch_tree.set(row_id, name))) + 32)
        minimum = int(self.batch_tree.column(name, "minwidth"))
        self.batch_tree.column(name, width=max(minimum, min(width, 720)))
        return "break"

    def _romaji_engine(self, name, factory):
        # Callers hold the instance RLock: tokenizer instances are reused but
        # never entered concurrently by the popup's worker threads.
        engines = self.__dict__.setdefault("_romaji_engines", {})
        if name not in engines:
            engines[name] = factory()
        return engines[name]


    def _romaji_cache_namespace(self, key):
        settings = self.translation_settings
        return (f"romaji:v3:{key}:{settings.get('sudachi_dictionary', 'core')}:"
                f"{settings.get('sudachi_split_mode', 'B')}:{settings.get('mecab_dictionary', 'auto')}:")


    def _romanize_tokens(self, tokens):
        pieces = []
        for surface, reading, pos in tokens:
            if not surface.strip():
                continue
            # Preserve Latin words, numbers, and punctuation exactly; dictionary
            # readings can otherwise turn an English title into Japanese sounds.
            if not re.search(r"[\u3040-\u30ff\u3400-\u9fff]", surface):
                value = surface
            elif pos == "助詞" and surface in {"は", "へ", "を"}:
                value = {"は": "wa", "へ": "e", "を": "o"}[surface]
            else:
                value = self._kana_to_hepburn(reading if reading and reading != "*" else surface)
            if value:
                pieces.append(value)
        value = " ".join(pieces)
        value = re.sub(r"\s+([、。,.!?;:！？」』）\]})])", r"\1", value)
        value = re.sub(r"([「『（\[({])\s+", r"\1", value)
        return self._normalize_romanized_title(value)


    def _translator_status(self, callback, message):
        if callback is None:
            return
        def deliver():
            try:
                callback(text=message)
            except TypeError:
                callback(message)
            except (tk.TclError, RuntimeError):
                pass  # The settings window may have closed during installation.
        try:
            self.after(0, deliver)
        except (tk.TclError, RuntimeError):
            pass

    def _windows_set_titlebar_color(self, color_mode):
        # CTk's default implementation withdraws the entire window and recursively
        # calls update(). Setting the DWM attribute needs neither operation.
        if sys.platform != 'win32':
            return
        try:
            import ctypes
            hwnd = ctypes.windll.user32.GetParent(self.winfo_id())
            value = ctypes.c_int(1 if str(color_mode).lower() == 'dark' else 0)
            for attribute in (20, 19):
                if ctypes.windll.dwmapi.DwmSetWindowAttribute(hwnd, attribute, ctypes.byref(value), ctypes.sizeof(value)) == 0:
                    break
        except Exception:
            pass





class ManualLookupCancelled(Exception):
    """A superseded/closed manual lookup, not a user-facing search failure."""


class ManualLookupAccessError(RuntimeError):
    """Authentication, challenge or rate-limit response: stop, never bypass."""


class EHManualTitleLookup:
    """Read-only, hash-first gallery identification for the marquee dialog.

    Reference: https://ehwiki.org/wiki/Gallery_Searching and /wiki/API.
    The hash is of the ORIGINAL FILE BYTES, not the displayed image or crop.
    Text candidates are not filtered by the app's cover-similarity threshold.
    No image upload, uploader ToS call, publishing or cookie-file write occurs.
    Each worker owns its session; the new workflow shares conservative limits.
    """

    MAX_RESULTS = 12
    SEARCH_INTERVAL = 3.2
    API_INTERVAL = 5.0
    _request_lock = threading.Lock()
    _last_request = {"search": 0.0, "api": 0.0}
    _cooldown_until = 0.0

    def __init__(self, cookies=None, cookie_file="cookies.txt", use_ex=False,
                 log_fn=None, session=None):
        self.use_ex = bool(use_ex)
        self.base = "https://exhentai.org" if self.use_ex else "https://e-hentai.org"
        self.api_url = ("https://exhentai.org/api.php" if self.use_ex
                        else "https://api.e-hentai.org/api.php")
        if session is not None:  # Dependency injection for offline tests.
            self.session = session
        else:
            backend = EHentaiBackend(
                cookies=cookies, cookie_file=cookie_file, use_ex=self.use_ex,
                log_fn=log_fn or (lambda _message: None), save_cookie_file=False,
            )
            self.session = backend.session
            # A 429/challenge must not trigger the legacy adapter's quick retries.
            for scheme in ("https://", "http://"):
                self.session.mount(scheme, HTTPAdapter(max_retries=0))

    def close(self):
        self.session.close()

    @staticmethod
    def _check_cancel(cancel):
        if cancel is not None and cancel.is_set():
            raise ManualLookupCancelled()

    @classmethod
    def _wait_turn(cls, kind, cancel=None):
        interval = cls.SEARCH_INTERVAL if kind == "search" else cls.API_INTERVAL
        while not cls._request_lock.acquire(timeout=0.1):
            cls._check_cancel(cancel)
        try:
            cls._check_cancel(cancel)
            now = time.monotonic()
            if now < cls._cooldown_until:
                raise ManualLookupAccessError(
                    "E/Ex asked this lookup to slow down. Wait at least "
                    f"{int(cls._cooldown_until - now) + 1} seconds before retrying. "
                    "Raw OCR is still available."
                )
            remaining = interval - (now - cls._last_request[kind])
            while remaining > 0:
                if cancel is not None:
                    if cancel.wait(min(remaining, 0.1)):
                        raise ManualLookupCancelled()
                else:
                    time.sleep(min(remaining, 0.1))
                remaining = interval - (time.monotonic() - cls._last_request[kind])
            cls._check_cancel(cancel)
            cls._last_request[kind] = time.monotonic()
        finally:
            cls._request_lock.release()

    @classmethod
    def _check_response(cls, response):
        code = response.status_code
        if code == 429:
            try:
                delay = max(60, min(3600, int(response.headers.get("Retry-After", "60"))))
            except (TypeError, ValueError):
                delay = 60
            with cls._request_lock:
                cls._cooldown_until = max(cls._cooldown_until, time.monotonic() + delay)
            raise ManualLookupAccessError(
                "E/Ex rate-limited the lookup. Wait before retrying; raw OCR was kept."
            )
        if code in (401, 403):
            raise ManualLookupAccessError(
                "E/Ex denied access. Check your session/cookies and the Use ExHentai "
                "setting, then reopen Manual OCR. No titles were changed."
            )
        response.raise_for_status()
        content_type = response.headers.get("Content-Type", "").lower()
        if content_type.startswith("image/"):
            raise ManualLookupAccessError(
                "E/Ex returned an access-denied image rather than search results. "
                "Check your ExHentai access and cookies, or use E-Hentai."
            )
        # JSON is handled by the metadata parser, not the HTML access-gate test.
        # Otherwise a legitimate title containing "too many requests" could be
        # mistaken for a rate-limit message.
        if "application/json" in content_type:
            return BeautifulSoup("", "html.parser")
        # Do not scan gallery titles for these words: only recognize page-level gates.
        soup = BeautifulSoup(response.text, "html.parser")
        title = soup.title.get_text(" ", strip=True).lower() if soup.title else ""
        is_gallery = bool(soup.select_one("#gn, #gj, .itg"))
        plain = soup.get_text(" ", strip=True).lower()
        if ("just a moment" in title or "attention required" in title
                or soup.select_one("#challenge-form, #cf-challenge-running") is not None
                or response.headers.get("cf-mitigated", "").lower() == "challenge"):
            raise ManualLookupAccessError(
                "A browser challenge blocked the lookup. Open E/Ex normally and "
                "resolve it there; this tool does not bypass challenges. Raw OCR is kept."
            )
        if not is_gallery and any(phrase in plain for phrase in (
                "temporarily banned", "excessive pageloads", "too many requests",
                "you are opening pages too fast")):
            with cls._request_lock:
                cls._cooldown_until = max(cls._cooldown_until, time.monotonic() + 60)
            raise ManualLookupAccessError(
                "E/Ex returned a rate-limit or temporary-ban notice. Stop and wait "
                "as directed by the site; raw OCR is still available."
            )
        if not is_gallery and ("act=login" in response.url.lower()
                               or "login.php" in response.url.lower()
                               or soup.select_one("input[type='password']") is not None):
            raise ManualLookupAccessError(
                "E/Ex returned a login page. Refresh your cookies and reopen Manual OCR."
            )
        return soup

    @staticmethod
    def title_query(text):
        # Quote the user-selected text as one TITLE phrase, never as a tag expression.
        fragment = re.sub(r"\s+", " ", str(text or "")).strip()
        fragment = re.sub(r'["*%]', " ", fragment)
        fragment = re.sub(r"\s+", " ", fragment).strip()
        if len(fragment) < 2 or not any(ch.isalnum() for ch in fragment):
            raise ValueError("Use at least two readable characters from the title, not only punctuation.")
        query = 'title:"' + fragment + '"'
        if len(query) > 200:
            raise ValueError("Use a shorter title fragment (at most 192 characters).")
        return query

    @staticmethod
    def hash_file(path, cancel=None):
        digest = hashlib.sha1()
        with open(path, "rb") as source:
            while True:
                EHManualTitleLookup._check_cancel(cancel)
                block = source.read(1024 * 1024)
                if not block:
                    break
                digest.update(block)
        return digest.hexdigest()

    @staticmethod
    def _gallery_link(url, base):
        from urllib.parse import urlsplit
        absolute = urljoin(base, str(url or ""))
        parts = urlsplit(absolute)
        if parts.scheme != "https" or parts.hostname not in {"e-hentai.org", "exhentai.org"}:
            return None
        match = re.fullmatch(r"/g/(\d+)/([a-zA-Z0-9]+)/?", parts.path)
        if not match:
            return None
        gid, token = int(match.group(1)), match.group(2)
        return {"gid": gid, "token": token,
                "url": f"https://{parts.hostname}/g/{gid}/{token}/"}

    @classmethod
    def parse_search_rows(cls, soup, base):
        # The metadata API supplies the canonical title and thumbnail, so we need
        # only direct gallery IDs here. Merge the image/title anchors for a row.
        rows = {}
        for anchor in soup.select("a[href]"):
            row = cls._gallery_link(anchor.get("href"), base)
            if row is None:
                continue
            key = (row["gid"], row["token"])
            row = rows.setdefault(key, dict(row, display_title=""))
            label = anchor.select_one(".glink")
            text = (label or anchor).get_text(" ", strip=True)
            if text and len(text) > len(row["display_title"]):
                row["display_title"] = html.unescape(text)
        # Some exact searches may redirect to a single gallery.
        direct = cls._gallery_link(base, base)
        if direct and soup.select_one("#gn") is not None:
            key = (direct["gid"], direct["token"])
            rows.setdefault(key, dict(direct, display_title=soup.select_one("#gn").get_text(" ", strip=True)))
        return list(rows.values())

    @staticmethod
    def _canonical_title(value):
        return re.sub(r"\s+", " ", html.unescape(str(value or ""))).strip()

    def enrich_metadata(self, rows, cancel=None):
        if not rows:
            return [], ""
        selected = [dict(row) for row in rows[:self.MAX_RESULTS]]
        self._wait_turn("api", cancel)
        response = self.session.post(
            self.api_url,
            json={"method": "gdata", "gidlist": [[r["gid"], r["token"]] for r in selected], "namespace": 1},
            headers={"Accept": "application/json", "Referer": self.base + "/"},
            timeout=(10, 25),
        )
        self._check_cancel(cancel)
        self._check_response(response)
        try:
            payload = response.json()
        except ValueError as exc:
            raise RuntimeError("The metadata API did not return JSON. Raw OCR is still available.") from exc
        if not isinstance(payload, dict) or not isinstance(payload.get("gmetadata"), list):
            raise RuntimeError("The metadata API did not return gallery metadata. Raw OCR is still available.")
        by_id = {}
        for metadata in payload["gmetadata"]:
            if isinstance(metadata, dict):
                try:
                    by_id[int(metadata["gid"])] = metadata
                except (KeyError, ValueError, TypeError):
                    continue
        missing = 0
        for row in selected:
            metadata = by_id.get(row["gid"], {})
            if not metadata or metadata.get("error") or (
                    metadata.get("token") and metadata["token"] != row["token"]):
                row.update(title_en="", title_jp="", thumb="", metadata_ok=False,
                           metadata_error="Gallery metadata unavailable for this result.")
                missing += 1
                continue
            row.update(
                title_en=self._canonical_title(metadata.get("title")),
                title_jp=self._canonical_title(metadata.get("title_jpn")),
                thumb=str(metadata.get("thumb") or ""),
                category=str(metadata.get("category") or ""),
                filecount=str(metadata.get("filecount") or ""),
                metadata_ok=True,
            )
            # Missing Japanese metadata stays missing. Never invent a translation
            # or copy the English/display/OCR title into the Japanese field.
        notice = f"Metadata unavailable for {missing} result(s); those cannot be applied." if missing else ""
        return selected, notice

    def lookup(self, image_path=None, text=None, cancel=None):
        self._check_cancel(cancel)
        if text is None:
            method = "hash"
            query = self.hash_file(image_path, cancel)
            params = {"f_shash": query, "fs_similar": "0", "fs_covers": "0"}
        else:
            method = "text"
            query = self.title_query(text)
            params = {"f_search": query}
        self._wait_turn("search", cancel)
        response = self.session.get(
            self.base + "/", params=params,
            headers={"Referer": self.base + "/"}, timeout=(10, 25),
        )
        self._check_cancel(cancel)
        soup = self._check_response(response)
        rows = self.parse_search_rows(soup, response.url)
        if not rows:
            plain = soup.get_text(" ", strip=True).lower()
            empty_markers = ("no hits found", "no results found", "no unfiltered results",
                             "no galleries found", "nothing found", "no hits", "no results")
            if not any(marker in plain for marker in empty_markers):
                raise RuntimeError(
                    "The site returned a page this lookup could not recognize, not a verified "
                    "'no matches' response. Check E/Ex in your browser; raw OCR was kept."
                )
        matches, notice = self.enrich_metadata(rows, cancel)
        for row in matches:
            row["match_kind"] = method
        if len(rows) > self.MAX_RESULTS:
            notice = f"Showing the first {self.MAX_RESULTS} results. Use a more distinctive phrase to narrow the list. " + notice
        return {"matches": matches, "method": method, "query": query,
                "search_url": response.url, "notice": notice}

    @staticmethod
    def thumbnail_allowed(url):
        from urllib.parse import urlsplit
        parts = urlsplit(str(url or ""))
        host = (parts.hostname or "").lower()
        return parts.scheme == "https" and any(
            host == domain or host.endswith("." + domain)
            for domain in ("ehgt.org", "hath.network", "e-hentai.org", "exhentai.org")
        )

    def thumbnail(self, row, cancel=None):
        url = row.get("thumb") or ""
        if not self.thumbnail_allowed(url):
            return None
        self._check_cancel(cancel)
        response = self.session.get(url, headers={"Referer": row["url"]},
                                    timeout=(8, 12), stream=True, allow_redirects=False)
        try:
            response.raise_for_status()
            if response.status_code != 200:
                return None
            if not response.headers.get("Content-Type", "").lower().startswith("image/"):
                return None
            data = bytearray()
            for block in response.iter_content(32768):
                self._check_cancel(cancel)
                data.extend(block)
                if len(data) > 5 * 1024 * 1024:
                    return None
            with Image.open(io.BytesIO(data)) as raw:
                if raw.width * raw.height > 30_000_000:
                    return None
                image = ImageOps.exif_transpose(raw).convert("RGB")
                image.thumbnail((160, 180), LANCZOS_FILTER)
                return image.copy()
        finally:
            response.close()


class ManualOCRTitleTarget:
    """Bind a popup to its ORIGINAL gallery, even when the user selects another row."""

    def __init__(self, app, en_entry, jp_entry):
        self.app = app
        self.entries = {"title_en": en_entry, "title_jp": jp_entry}
        self.is_batch = any(
            widget is not None and widget is getattr(app, attr, None)
            for widget, attr in ((en_entry, "batch_edit_en_entry"), (jp_entry, "batch_edit_jp_entry"))
        )
        self.item_id = None
        self.source_path = None
        self.single_folder = None
        self.label = "Current title fields"
        if self.is_batch:
            commit = getattr(app, "_commit_batch_title_edit", None)
            if callable(commit):
                commit()
            self.item_id = getattr(app, "_batch_edit_item_id", None)
            if not self.item_id:
                selected = app.batch_tree.selection()
                self.item_id = selected[0] if selected else None
            item = app.batch_queue_items.get(self.item_id)
            if item is not None:
                self.source_path = str(item.get("path") or "")
                self.label = os.path.basename(os.path.normpath(self.source_path)) or self.source_path
        elif any(widget is not None and widget is getattr(app, attr, None)
                 for widget, attr in ((en_entry, "single_etitle_entry"), (jp_entry, "single_jtitle_entry"))):
            self.single_folder = app._get_text_widget_value(getattr(app, "single_folder_entry", None))
            self.label = os.path.basename(os.path.normpath(self.single_folder)) or "Single Gallery"

    def current(self):
        if self.is_batch:
            item = self.app.batch_queue_items.get(self.item_id)
            if item is None or str(item.get("path") or "") != self.source_path:
                raise ValueError("The original queue item was removed or replaced. Reopen Manual OCR for the desired gallery.")
            values = {key: str(item.get(key) or "") for key in self.entries}
            if getattr(self.app, "_batch_edit_item_id", None) == self.item_id:
                for key, widget in self.entries.items():
                    if widget is not None:
                        values[key] = self.app._get_text_widget_value(widget)
            return values
        if self.single_folder is not None and self.app._get_text_widget_value(
                getattr(self.app, "single_folder_entry", None)) != self.single_folder:
            raise ValueError("The Single Gallery folder changed. Reopen Manual OCR for the new folder.")
        return {key: self.app._get_text_widget_value(widget) if widget is not None else ""
                for key, widget in self.entries.items()}

    def apply(self, updates):
        if not updates:
            return
        current = self.current()
        for key, value in updates.items():
            if key not in self.entries or self.entries[key] is None:
                raise ValueError("That title field is not available here.")
            if not str(value).strip():
                raise ValueError("No title was supplied for that field; its existing value was kept.")
            if not self.entries[key].winfo_exists():
                raise ValueError("The title editor was closed. Reopen Manual OCR.")
        current.update(updates)
        if self.is_batch:
            self.app.batch_queue_items[self.item_id].update(current)
            if self.app.batch_tree.exists(self.item_id):
                values = list(self.app.batch_tree.item(self.item_id, "values"))
                while len(values) < 5:
                    values.append("")
                values[0] = self.app._compose_title_cell(current["title_en"], current["title_jp"])
                values[1] = current["title_jp"]
                self.app.batch_tree.item(self.item_id, values=values)
            if getattr(self.app, "_batch_edit_item_id", None) == self.item_id:
                previous = getattr(self.app, "_batch_title_load_suppress", False)
                self.app._batch_title_load_suppress = True
                try:
                    for key, value in updates.items():
                        self.app._set_text_widget_value(self.entries[key], value)
                finally:
                    self.app._batch_title_load_suppress = previous
            self.app._save_persistent_queue()
        else:
            for key, value in updates.items():
                self.app._set_text_widget_value(self.entries[key], value)


class ManualOCRSelectorDialog(ctk.CTkToplevel):
    """Manual Google-Lens-like marquee OCR picker for a cover image.

    The user draws the recognition rectangle; OCR segmentation boxes are not
    used to determine what gets recognized.
    """

    BG = "#0a0a0a"
    PANEL = "#161616"
    SOFT = "#1c1c1c"
    BORDER = "#2a2a2a"
    BORDER_STRONG = "#3d3d3d"
    TEXT = "#f0f0f0"
    MUTED = "#9a9a9a"

    def __init__(self, parent, image_path, en_entry=None, jp_entry=None):
        super().__init__(parent)
        self.parent_app = parent
        self.image_path = os.path.abspath(str(image_path))
        self.en_entry = en_entry
        self.jp_entry = jp_entry
        self.zoom = 1.0
        self._fit_pending = None
        self._photo = None
        self._image_item = None
        self._destroyed = False
        self._drag_start_canvas = None
        self._drag_item = None
        self.marquee_source_box = None
        self._ocr_job_serial = 0
        self._append_next_result = False
        self._last_ocr_candidates = []
        self._title_target = ManualOCRTitleTarget(parent, en_entry, jp_entry)
        self._events = queue.Queue()
        self._events_after = None
        self._lookup_pool = ThreadPoolExecutor(max_workers=1, thread_name_prefix="manual-gallery")
        self._lookup_future = None
        self._lookup_cancel = threading.Event()
        self._lookup_serial = 0
        self._lookup_kind = None
        self._lookup_busy = False
        self._pending_lookup_text = None
        self._lookup_result = None
        self._lookup_picker = None
        # Read Tk variables ONLY here, on the main thread. Worker sessions use a snapshot.
        self._lookup_options = {
            "cookies": dict(parent._get_cookies()),
            "cookie_file": str(parent._resolve_cookie_file() or "cookies.txt"),
            "use_ex": bool(parent.use_ex_var.get()),
        }

        with Image.open(self.image_path) as raw:
            self.source_image = ImageOps.exif_transpose(raw).convert("RGB")

        self.title("Manual OCR + E/Ex Title Lookup")
        self.geometry("1120x780")
        self.minsize(820, 600)
        self.configure(fg_color=self.BG)
        self.transient(parent)
        self.protocol("WM_DELETE_WINDOW", self._close)

        self.grid_rowconfigure(1, weight=1)
        self.grid_columnconfigure(0, weight=1)

        top = ctk.CTkFrame(self, fg_color="#111111", corner_radius=0, height=46)
        top.grid(row=0, column=0, sticky="ew")
        top.grid_propagate(False)
        ctk.CTkLabel(
            top,
            text="MANUAL OCR  ·  drag a rectangle over the exact text you want",
            text_color=self.TEXT,
            font=("Segoe UI", 12, "bold"),
        ).pack(side="left", padx=14, pady=10)

        self.engine_label = ctk.CTkLabel(
            top,
            text="Ready for marquee",
            text_color=self.MUTED,
            font=("Segoe UI", 10),
        )
        self.engine_label.pack(side="right", padx=14)

        body = ctk.CTkFrame(self, fg_color=self.BG, corner_radius=0)
        body.grid(row=1, column=0, sticky="nsew")
        body.grid_rowconfigure(0, weight=1)
        body.grid_columnconfigure(0, weight=1)

        canvas_wrap = ctk.CTkFrame(body, fg_color="#050505", corner_radius=0)
        canvas_wrap.grid(row=0, column=0, sticky="nsew")
        canvas_wrap.grid_rowconfigure(0, weight=1)
        canvas_wrap.grid_columnconfigure(0, weight=1)

        self.canvas = tk.Canvas(
            canvas_wrap,
            bg="#050505",
            highlightthickness=0,
            bd=0,
            cursor="crosshair",
        )
        self.canvas.grid(row=0, column=0, sticky="nsew")
        xbar = ttk.Scrollbar(canvas_wrap, orient="horizontal", command=self.canvas.xview)
        ybar = ttk.Scrollbar(canvas_wrap, orient="vertical", command=self.canvas.yview)
        xbar.grid(row=1, column=0, sticky="ew")
        ybar.grid(row=0, column=1, sticky="ns")
        self.canvas.configure(xscrollcommand=xbar.set, yscrollcommand=ybar.set)
        self.canvas.bind("<Configure>", self._schedule_initial_fit, add="+")
        self.canvas.bind("<MouseWheel>", self._on_mousewheel)
        self.canvas.bind("<Button-4>", lambda _e: self._change_zoom(1.15))
        self.canvas.bind("<Button-5>", lambda _e: self._change_zoom(1 / 1.15))
        self.canvas.bind("<ButtonPress-1>", self._marquee_press)
        self.canvas.bind("<B1-Motion>", self._marquee_drag)
        self.canvas.bind("<ButtonRelease-1>", self._marquee_release)

        sidebar = ctk.CTkFrame(body, fg_color=self.PANEL, corner_radius=0, width=370)
        sidebar.grid(row=0, column=1, sticky="nsew")
        sidebar.grid_propagate(False)
        sidebar.grid_rowconfigure(0, weight=1)
        sidebar.grid_columnconfigure(0, weight=1)
        panel = ctk.CTkScrollableFrame(sidebar, fg_color=self.PANEL, corner_radius=0, width=342)
        panel.grid(row=0, column=0, sticky="nsew")
        apply_footer = ctk.CTkFrame(sidebar, fg_color=self.PANEL, corner_radius=0)
        apply_footer.grid(row=1, column=0, sticky="ew")

        ctk.CTkLabel(
            panel,
            text="MARQUEE OCR",
            anchor="w",
            text_color=self.MUTED,
            font=("Segoe UI", 10, "bold"),
        ).pack(fill="x", padx=14, pady=(14, 5))

        self.hover_label = ctk.CTkLabel(
            panel,
            text=(
                "Drag around a word, line, symbols, or several characters. "
                "OCR runs on exactly that crop. Shift+drag appends another crop."
            ),
            anchor="nw",
            justify="left",
            wraplength=290,
            height=66,
            text_color=self.MUTED,
            font=("Segoe UI", 10),
        )
        self.hover_label.pack(fill="x", padx=14, pady=(0, 8))

        zoom_row = ctk.CTkFrame(panel, fg_color="transparent")
        zoom_row.pack(fill="x", padx=14, pady=(0, 10))
        ctk.CTkButton(zoom_row, text="−", width=34, height=28, command=lambda: self._change_zoom(1 / 1.2)).pack(side="left")
        ctk.CTkButton(zoom_row, text="+", width=34, height=28, command=lambda: self._change_zoom(1.2)).pack(side="left", padx=(5, 0))
        ctk.CTkButton(zoom_row, text="Fit", width=54, height=28, command=self._fit_image).pack(side="left", padx=(5, 0))
        ctk.CTkButton(zoom_row, text="100%", width=62, height=28, command=self._actual_size).pack(side="left", padx=(5, 0))

        ctk.CTkLabel(
            panel,
            text="Recognized text",
            anchor="w",
            text_color=self.MUTED,
            font=("Segoe UI", 10),
        ).pack(fill="x", padx=14, pady=(2, 3))
        self.selection_box = ctk.CTkTextbox(
            panel,
            height=100,
            corner_radius=0,
            fg_color=self.BG,
            border_width=1,
            border_color=self.BORDER,
            text_color=self.TEXT,
            wrap="word",
            font=("Segoe UI", 11),
        )
        self.selection_box.pack(fill="x", padx=14, pady=(0, 8))

        select_row = ctk.CTkFrame(panel, fg_color="transparent")
        select_row.pack(fill="x", padx=14, pady=(0, 12))
        ctk.CTkButton(select_row, text="Clear", height=28, command=self._clear_selection).pack(side="left", fill="x", expand=True, padx=(0, 3))
        ctk.CTkButton(select_row, text="Re-run OCR", height=28, command=self._rerun_marquee_ocr).pack(side="left", fill="x", expand=True, padx=3)
        ctk.CTkButton(select_row, text="Whole image", height=28, command=self._ocr_whole_image).pack(side="left", fill="x", expand=True, padx=(3, 0))

        self._build_lookup_controls(panel)
        self.selection_box.bind("<KeyRelease>", self._ocr_text_edited, add="+")

        ctk.CTkLabel(
            panel,
            text="Raw OCR language / destination",
            anchor="w",
            text_color=self.MUTED,
            font=("Segoe UI", 10),
        ).pack(fill="x", padx=14, pady=(0, 4))
        self.target_var = tk.StringVar(value="japanese" if jp_entry is not None else "english")
        target_row = ctk.CTkFrame(panel, fg_color="transparent")
        target_row.pack(fill="x", padx=14, pady=(0, 10))
        self.english_radio = ctk.CTkRadioButton(
            target_row,
            text="English Title",
            variable=self.target_var,
            value="english",
            text_color=self.TEXT,
            fg_color=self.TEXT,
            hover_color="#d0d0d0",
            command=self._rerun_marquee_ocr,
        )
        self.english_radio.pack(anchor="w", pady=2)
        self.japanese_radio = ctk.CTkRadioButton(
            target_row,
            text="Japanese Title",
            variable=self.target_var,
            value="japanese",
            text_color=self.TEXT,
            fg_color=self.TEXT,
            hover_color="#d0d0d0",
            command=self._rerun_marquee_ocr,
        )
        self.japanese_radio.pack(anchor="w", pady=2)
        if en_entry is None:
            self.english_radio.configure(state="disabled")
        if jp_entry is None:
            self.japanese_radio.configure(state="disabled")

        ctk.CTkButton(
            apply_footer,
            text="Replace title with recognized text",
            height=34,
            fg_color="#f0f0f0",
            hover_color="#d8d8d8",
            text_color="#0a0a0a",
            command=lambda: self._apply_selection(append=False),
        ).pack(fill="x", padx=14, pady=(2, 5))
        ctk.CTkButton(
            apply_footer,
            text="Append recognized text to title",
            height=32,
            fg_color=self.SOFT,
            hover_color="#242424",
            text_color=self.TEXT,
            border_width=1,
            border_color=self.BORDER_STRONG,
            command=lambda: self._apply_selection(append=True),
        ).pack(fill="x", padx=14, pady=(0, 5))
        ctk.CTkButton(
            apply_footer,
            text="Close",
            height=30,
            fg_color="transparent",
            hover_color="#242424",
            border_width=1,
            border_color=self.BORDER,
            command=self._close,
        ).pack(fill="x", padx=14, pady=(0, 12))

        self._initial_fit_after = self.after(80, self._fit_image)
        self._events_after = self.after(60, self._poll_events)
        self._initial_lookup_after = self.after(160, lambda: self._start_lookup("hash"))

    def _close(self):
        if self._destroyed:
            return
        self._destroyed = True
        self._ocr_job_serial += 1
        self._lookup_serial += 1
        self._lookup_cancel.set()
        self._lookup_pool.shutdown(wait=False, cancel_futures=True)
        for timer in (self._events_after, self._fit_pending,
                      self._initial_fit_after, self._initial_lookup_after):
            if timer is not None:
                try:
                    self.after_cancel(timer)
                except tk.TclError:
                    pass
        if self._lookup_picker is not None and self._lookup_picker.winfo_exists():
            self._lookup_picker._close()
        self.destroy()

    def _schedule_initial_fit(self, _event=None):
        if self._fit_pending is not None:
            try:
                self.after_cancel(self._fit_pending)
            except Exception:
                pass
        self._fit_pending = self.after(120, self._fit_once)

    def _fit_once(self):
        self._fit_pending = None
        if not getattr(self, "_did_initial_fit", False):
            self._did_initial_fit = True
            self._fit_image()

    def _fit_image(self):
        try:
            self.update_idletasks()
            cw = max(100, self.canvas.winfo_width() - 18)
            ch = max(100, self.canvas.winfo_height() - 18)
            iw, ih = self.source_image.size
            self.zoom = max(0.05, min(cw / iw, ch / ih))
            self._render_canvas()
        except Exception:
            pass

    def _actual_size(self):
        self.zoom = 1.0
        self._render_canvas()

    def _change_zoom(self, factor):
        self.zoom = max(0.05, min(8.0, self.zoom * float(factor)))
        self._render_canvas()

    def _on_mousewheel(self, event):
        if event.state & 0x0004:  # Ctrl+wheel zooms; normal wheel scrolls vertically.
            self._change_zoom(1.15 if event.delta > 0 else 1 / 1.15)
            return "break"
        self.canvas.yview_scroll(-1 if event.delta > 0 else 1, "units")
        return "break"

    def _render_canvas(self):
        if self._destroyed:
            return
        iw, ih = self.source_image.size
        dw = max(1, int(iw * self.zoom))
        dh = max(1, int(ih * self.zoom))
        rendered = self.source_image.resize((dw, dh), LANCZOS_FILTER) if (dw, dh) != (iw, ih) else self.source_image
        self._photo = ImageTk.PhotoImage(rendered)
        self.canvas.delete("all")
        self._image_item = self.canvas.create_image(0, 0, image=self._photo, anchor="nw")
        self.canvas.configure(scrollregion=(0, 0, dw, dh))
        self.canvas.tag_lower(self._image_item)
        self._draw_saved_marquee()

    def _canvas_point(self, event):
        x = float(self.canvas.canvasx(event.x))
        y = float(self.canvas.canvasy(event.y))
        iw, ih = self.source_image.size
        return (
            max(0.0, min(x, iw * self.zoom)),
            max(0.0, min(y, ih * self.zoom)),
        )

    def _marquee_press(self, event):
        self._ocr_job_serial += 1
        self._cancel_text_lookup()
        self._drag_start_canvas = self._canvas_point(event)
        self._append_next_result = bool(event.state & 0x0001)  # Shift
        try:
            self.canvas.delete("manual_marquee")
            self.canvas.delete("saved_marquee")
        except Exception:
            pass
        self._drag_item = None
        x, y = self._drag_start_canvas
        self._drag_item = self.canvas.create_rectangle(
            x, y, x, y,
            outline="#f0f0f0",
            width=2,
            dash=(6, 3),
            tags=("manual_marquee",),
        )
        self.engine_label.configure(text="Drawing marquee…")
        return "break"

    def _marquee_drag(self, event):
        if self._drag_start_canvas is None or self._drag_item is None:
            return
        x0, y0 = self._drag_start_canvas
        x1, y1 = self._canvas_point(event)
        self.canvas.coords(self._drag_item, x0, y0, x1, y1)
        return "break"

    def _marquee_release(self, event):
        if self._drag_start_canvas is None:
            return "break"
        x0, y0 = self._drag_start_canvas
        x1, y1 = self._canvas_point(event)
        self._drag_start_canvas = None
        left, right = sorted((x0, x1))
        top, bottom = sorted((y0, y1))
        if (right - left) < 6 or (bottom - top) < 6:
            self.engine_label.configure(text="Marquee too small — drag a rectangle")
            return "break"

        iw, ih = self.source_image.size
        box = (
            max(0, min(iw - 1, int(left / self.zoom))),
            max(0, min(ih - 1, int(top / self.zoom))),
            max(1, min(iw, int(round(right / self.zoom)))),
            max(1, min(ih, int(round(bottom / self.zoom)))),
        )
        if box[2] <= box[0] or box[3] <= box[1]:
            self.engine_label.configure(text="Invalid marquee — try again")
            return "break"
        self.marquee_source_box = box
        self._draw_saved_marquee()
        self._start_marquee_ocr(append=self._append_next_result)
        return "break"

    def _draw_saved_marquee(self):
        try:
            self.canvas.delete("manual_marquee")
            self.canvas.delete("saved_marquee")
        except Exception:
            pass
        if not self.marquee_source_box:
            return
        x0, y0, x1, y1 = self.marquee_source_box
        self._drag_item = self.canvas.create_rectangle(
            x0 * self.zoom, y0 * self.zoom, x1 * self.zoom, y1 * self.zoom,
            outline="#f0f0f0", width=3, dash=(7, 3),
            tags=("saved_marquee",),
        )

    def _start_marquee_ocr(self, append=False):
        if not self.marquee_source_box or self._destroyed:
            return
        self._cancel_text_lookup()
        box = tuple(self.marquee_source_box)
        target = self.target_var.get()
        crop = self.source_image.crop(box).copy()
        self._ocr_job_serial += 1
        serial = self._ocr_job_serial
        self.engine_label.configure(text=f"OCRing {crop.width}x{crop.height} crop...")
        self.hover_label.configure(text="Recognizing your crop. A gallery lookup can then provide clean titles.")
        events = self._events

        def worker():
            try:
                result = _manual_ocr_crop_text(crop, target=target,
                                               log_fn=lambda msg: events.put(("log", str(msg))))
                events.put(("ocr", serial, result, append, None))
            except Exception as exc:
                events.put(("ocr", serial, None, append, exc))
            finally:
                crop.close()
        threading.Thread(target=worker, daemon=True).start()

    def _finish_marquee_error(self, serial, exc):
        if serial != self._ocr_job_serial or self._destroyed:
            return
        self.engine_label.configure(text="No text recognized")
        self.hover_label.configure(text=str(exc))

    def _finish_marquee_ocr(self, serial, result, append=False):
        if serial != self._ocr_job_serial or self._destroyed:
            return
        text, engine, variant, alternatives = result
        self._last_ocr_candidates = list(alternatives or [])
        existing = self.selection_box.get("1.0", "end-1c").strip()
        if append and existing:
            target = self.target_var.get()
            joiner = " "
            if target == "japanese" and re.search(r"[\u3040-\u30ff\u3400-\u9fff]$", existing):
                joiner = ""
            text = existing + joiner + text
        self.selection_box.delete("1.0", "end")
        self.selection_box.insert("1.0", text)
        self.engine_label.configure(text=f"{engine} · {variant}")
        self.hover_label.configure(
            text=(
                "Marquee OCR complete. Edit the recognized text if needed, or drag a new rectangle. "
                "Shift+drag appends another area."
            )
        )

        if self.lookup_auto_var.get() and text.strip():
            self._start_lookup("text", text, automatic=True)

    def _rerun_marquee_ocr(self):
        if self.marquee_source_box:
            self._start_marquee_ocr(append=False)

    def _ocr_whole_image(self):
        iw, ih = self.source_image.size
        self.marquee_source_box = (0, 0, iw, ih)
        self._draw_saved_marquee()
        self._start_marquee_ocr(append=False)

    def _clear_selection(self):
        self._cancel_text_lookup()
        self._ocr_job_serial += 1
        self.marquee_source_box = None
        self._drag_start_canvas = None
        if self._drag_item is not None:
            try:
                self.canvas.delete(self._drag_item)
            except Exception:
                pass
        self._drag_item = None
        try:
            self.canvas.delete("manual_marquee")
            self.canvas.delete("saved_marquee")
        except Exception:
            pass
        self.selection_box.delete("1.0", "end")
        self.engine_label.configure(text="Ready for marquee")
        self.hover_label.configure(
            text="Drag around the exact word(s), characters, or symbols you want OCR to read."
        )

    def _apply_selection(self, append=False):
        text = self.selection_box.get("1.0", "end-1c").strip()
        if not text:
            messagebox.showinfo("Manual OCR", "Draw a marquee and OCR some text first.", parent=self)
            return
        target = self.target_var.get()
        key = "title_en" if target == "english" else "title_jp"
        if target == "japanese":
            text = _tighten_cjk_ocr_text(text)
        try:
            if append:
                current = self._title_target.current()[key].strip()
                if current:
                    joiner = "" if target == "japanese" and re.search(r"[\u3040-\u30ff\u3400-\u9fff]$", current) else " "
                    text = current + joiner + text
            self._title_target.apply({key: text})
        except Exception as exc:
            messagebox.showwarning("Manual OCR", str(exc), parent=self)
            return
        self.parent_app.log(f"[Manual OCR] Applied raw crop text to {target} title for {self._title_target.label}")
        self.engine_label.configure(text=f"Applied to {target.title()} Title")

    def _build_lookup_controls(self, panel):
        section = ctk.CTkFrame(panel, fg_color=self.BG, corner_radius=0,
                               border_width=1, border_color=self.BORDER)
        section.pack(fill="x", padx=14, pady=(0, 10))
        ctk.CTkLabel(section, text="E/Ex gallery title lookup", anchor="w",
                     text_color=self.TEXT, font=("Segoe UI", 11, "bold")).pack(
                         fill="x", padx=10, pady=(8, 2))
        self.lookup_auto_var = tk.BooleanVar(value=True)
        ctk.CTkCheckBox(section, text="Search after marquee OCR", variable=self.lookup_auto_var,
                        command=self._auto_lookup_changed, height=24,
                        checkbox_width=16, checkbox_height=16).pack(
                            fill="x", padx=10, pady=(2, 5))
        row = ctk.CTkFrame(section, fg_color="transparent")
        row.pack(fill="x", padx=10, pady=(0, 5))
        ctk.CTkButton(row, text="Check cover hash", width=140, height=28,
                       command=lambda: self._start_lookup("hash")).pack(
                           side="left", fill="x", expand=True, padx=(0, 4))
        ctk.CTkButton(row, text="Search OCR text", width=140, height=28,
                       command=self._search_edited_ocr).pack(side="left", fill="x", expand=True)
        self.lookup_review_btn = ctk.CTkButton(section, text="Review gallery matches", height=28,
                                              state="disabled", command=self._review_lookup)
        self.lookup_review_btn.pack(fill="x", padx=10, pady=(0, 5))
        self.lookup_status = ctk.CTkLabel(
            section, text="Checking the original cover's SHA-1 first. No image is uploaded.",
            anchor="w", justify="left", wraplength=280, font=("Segoe UI", 10), text_color=self.MUTED,
        )
        self.lookup_status.pack(fill="x", padx=10, pady=(0, 8))

    def _auto_lookup_changed(self):
        if not self.lookup_auto_var.get():
            self._pending_lookup_text = None
            if getattr(self, "_lookup_kind", None) == "text":
                self._cancel_text_lookup()

    def _cancel_text_lookup(self):
        if getattr(self, "_lookup_kind", None) == "text" and self._lookup_busy:
            self._lookup_cancel.set()
            if self._lookup_future is not None:
                self._lookup_future.cancel()
            self._lookup_serial += 1
            self._lookup_busy = False
        self._pending_lookup_text = None

    def _ocr_text_edited(self, _event=None):
        if getattr(self, "_lookup_kind", None) == "text":
            self._cancel_text_lookup()
            self._lookup_result = None
            self.lookup_review_btn.configure(state="disabled", text="Review gallery matches")
            self.lookup_status.configure(text="Text edited. Click Search OCR text to look up this phrase.")

    def _search_edited_ocr(self):
        self._start_lookup("text", self.selection_box.get("1.0", "end-1c"))

    def _start_lookup(self, kind, text=None, automatic=False):
        if self._destroyed:
            return
        if kind == "text":
            text = str(text or "").strip()
            try:
                EHManualTitleLookup.title_query(text)
            except ValueError as exc:
                self.lookup_status.configure(text=str(exc))
                return
            # If the first hash lookup is still working, keep the promised order.
            if self._lookup_busy and self._lookup_kind == "hash":
                self._pending_lookup_text = (text, automatic)
                self.lookup_status.configure(text="Waiting for the cover-hash result, then using OCR text if needed.")
                return
        else:
            self._pending_lookup_text = None
        self._lookup_cancel.set()
        if self._lookup_future is not None:
            self._lookup_future.cancel()
        self._lookup_serial += 1
        serial = self._lookup_serial
        self._lookup_cancel = cancel = threading.Event()
        self._lookup_kind = kind
        self._lookup_busy = True
        self._lookup_result = None
        self.lookup_review_btn.configure(state="disabled", text="Review gallery matches")
        self.lookup_status.configure(text=(
            "Checking the original cover's exact SHA-1..."
            if kind == "hash" else "Searching E/Ex titles for: " + text[:120]
        ))
        options = dict(self._lookup_options)
        events = self._events
        image_path = self.image_path

        def worker():
            client = None
            try:
                EHManualTitleLookup._check_cancel(cancel)
                client = EHManualTitleLookup(**options)
                result = client.lookup(image_path=image_path, text=text if kind == "text" else None,
                                       cancel=cancel)
                if not cancel.is_set():
                    events.put(("lookup", serial, result, None))
            except ManualLookupCancelled:
                pass
            except Exception as exc:
                if not cancel.is_set():
                    events.put(("lookup", serial, None, exc))
            finally:
                if client is not None:
                    client.close()
        self._lookup_future = self._lookup_pool.submit(worker)

    def _poll_events(self):
        self._events_after = None
        if self._destroyed:
            return
        try:
            while True:
                event = self._events.get_nowait()
                if event[0] == "lookup":
                    self._finish_lookup(*event[1:])
                elif event[0] == "ocr":
                    serial, result, append, error = event[1:]
                    if error is not None:
                        self._finish_marquee_error(serial, error)
                    else:
                        self._finish_marquee_ocr(serial, result, append)
                elif event[0] == "log":
                    self.parent_app.log(event[1])
        except queue.Empty:
            pass
        if not self._destroyed:
            self._events_after = self.after(60, self._poll_events)

    def _finish_lookup(self, serial, result, error):
        if self._destroyed or serial != self._lookup_serial:
            return
        kind = self._lookup_kind
        self._lookup_busy = False
        pending = self._pending_lookup_text
        self._pending_lookup_text = None
        if error is not None:
            self.lookup_status.configure(text="Lookup failed: " + str(error))
            self.parent_app.log(f"[Manual lookup] {error}")
            return
        self._lookup_result = result
        count = len(result["matches"])
        if count:
            self.lookup_review_btn.configure(state="normal", text=f"Review {count} gallery match(es)")
            self.lookup_status.configure(text=(
                f"{count} {'exact-file match(es)' if kind == 'hash' else 'title candidate(s)'}. "
                "Choose a gallery and Use English / Japanese / Both."
            ))
            self._review_lookup()
        else:
            self.lookup_status.configure(text=(
                "No exact-file match. Draw a marquee around a distinctive title fragment; "
                "OCR text will be used for the next search."
                if kind == "hash" else
                "No matching titles. Raw OCR was kept. Correct the text or try a shorter, distinctive phrase."
            ))
        if kind == "hash" and pending and (not count or not pending[1]):
            text, automatic = pending
            self._start_lookup("text", text, automatic=automatic)

    def _review_lookup(self):
        if not self._lookup_result or not self._lookup_result.get("matches"):
            return
        old = self._lookup_picker
        if old is not None and old.winfo_exists():
            old._close()
        self._lookup_picker = ManualGalleryTitlePicker(self, self._lookup_result)
        self._lookup_picker.lift()



class ManualGalleryTitlePicker(ctk.CTkToplevel):
    """Review canonical gallery titles before choosing which fields to replace."""

    def __init__(self, owner, result):
        super().__init__(owner)
        self.owner = owner
        self.result = result
        self.target = owner._title_target
        self.rows = {str(index): row for index, row in enumerate(result["matches"])}
        self._closed = False
        self._thumb_serial = 0
        self._thumb_cancel = threading.Event()
        self._thumb_events = queue.Queue()
        self._thumb_pool = ThreadPoolExecutor(max_workers=1, thread_name_prefix="gallery-thumb")
        self._thumb_future = None
        self._thumb_photo = None
        self._thumb_cache = {}
        self.title("E/Ex Gallery Matches - choose titles")
        self.geometry("940x640")
        self.minsize(760, 570)
        self.configure(fg_color=owner.BG)
        self.transient(owner)
        self.protocol("WM_DELETE_WINDOW", self._close)
        self.grid_columnconfigure(0, weight=1)
        self.grid_rowconfigure(2, weight=1)

        kind = ("Exact file-hash matches (the image may appear anywhere in a gallery)"
                if result["method"] == "hash" else "Title-text candidates - verify the work and edition")
        if result["method"] == "text":
            kind += "\n" + result.get("query", "")
        ctk.CTkLabel(self, text=kind, anchor="w", justify="left", wraplength=700,
                     font=("Segoe UI", 13, "bold"), text_color=owner.TEXT).grid(row=0, column=0, padx=14, pady=(12, 3), sticky="ew")
        ctk.CTkLabel(self, text="Destination: " + self.target.label, anchor="w",
                     text_color=owner.MUTED, wraplength=700).grid(
                         row=1, column=0, padx=14, pady=(0, 6), sticky="ew")

        table = ctk.CTkFrame(self, fg_color=owner.PANEL, corner_radius=0)
        table.grid(row=2, column=0, padx=14, pady=4, sticky="nsew")
        table.grid_rowconfigure(0, weight=1)
        table.grid_columnconfigure(0, weight=1)
        self.tree = ttk.Treeview(table, columns=("en", "jp", "category"),
                                 show="headings", selectmode="browse", height=6)
        for key, title, width in (("en", "English / Romaji title", 345),
                                  ("jp", "Japanese title", 345), ("category", "Category", 105)):
            self.tree.heading(key, text=title)
            self.tree.column(key, width=width, minwidth=80)
        self.tree.grid(row=0, column=0, sticky="nsew")
        vsb = ttk.Scrollbar(table, orient="vertical", command=self.tree.yview)
        hsb = ttk.Scrollbar(table, orient="horizontal", command=self.tree.xview)
        vsb.grid(row=0, column=1, sticky="ns")
        hsb.grid(row=1, column=0, sticky="ew")
        self.tree.configure(yscrollcommand=vsb.set, xscrollcommand=hsb.set)
        for key, row in self.rows.items():
            self.tree.insert("", "end", iid=key, values=(
                row.get("title_en") or row.get("display_title") or "[metadata unavailable]",
                row.get("title_jp") or "[not supplied]", row.get("category", "")))
        self.tree.bind("<<TreeviewSelect>>", self._selected)

        detail = ctk.CTkFrame(self, fg_color=owner.PANEL, corner_radius=0)
        detail.grid(row=3, column=0, padx=14, pady=(6, 4), sticky="ew")
        detail.grid_columnconfigure(1, weight=1)
        self.thumb_label = ctk.CTkLabel(detail, text="Select a result", width=166, height=186,
                                       fg_color=owner.BG, corner_radius=0)
        self.thumb_label.grid(row=0, column=0, rowspan=4, padx=10, pady=10)
        ctk.CTkLabel(detail, text="English / Romaji (metadata, not translation)", anchor="w",
                     text_color=owner.MUTED).grid(row=0, column=1, padx=(0, 10), sticky="ew")
        self.en_box = ctk.CTkTextbox(detail, height=54, wrap="word", fg_color=owner.BG)
        self.en_box.grid(row=1, column=1, padx=(0, 10), sticky="ew")
        ctk.CTkLabel(detail, text="Japanese", anchor="w", text_color=owner.MUTED).grid(
            row=2, column=1, padx=(0, 10), sticky="ew")
        self.jp_box = ctk.CTkTextbox(detail, height=54, wrap="word", fg_color=owner.BG)
        self.jp_box.grid(row=3, column=1, padx=(0, 10), pady=(0, 10), sticky="ew")
        self.status = ctk.CTkLabel(self, text=result.get("notice") or "Select a gallery; nothing is applied automatically.",
                                  anchor="w", justify="left", wraplength=730, text_color=owner.MUTED)
        self.status.grid(row=4, column=0, padx=14, pady=(2, 4), sticky="ew")

        # A separate fixed footer keeps title-choice actions visible on short windows.
        footer = ctk.CTkFrame(self, fg_color="transparent")
        footer.grid(row=5, column=0, padx=14, pady=(4, 14), sticky="ew")
        footer.grid_columnconfigure(0, weight=1)
        left = ctk.CTkFrame(footer, fg_color="transparent")
        left.grid(row=0, column=0, sticky="w")
        ctk.CTkButton(left, text="Open gallery", width=105, height=32,
                       command=self._open_gallery).pack(side="left", padx=(0, 6))
        ctk.CTkButton(left, text="Back to OCR", width=105, height=32,
                       command=self._close).pack(side="left")
        right = ctk.CTkFrame(footer, fg_color="transparent")
        right.grid(row=0, column=1, sticky="e")
        self.apply_buttons = {}
        for mode, text in (("english", "Use English"), ("japanese", "Use Japanese"), ("both", "Use Both")):
            button = ctk.CTkButton(right, text=text, width=112, height=32, state="disabled",
                                   command=lambda mode=mode: self._apply(mode))
            button.pack(side="left", padx=(6, 0))
            self.apply_buttons[mode] = button
        self._thumb_after = self.after(60, self._poll_thumbnail)
        if self.rows:
            self.tree.selection_set(next(iter(self.rows)))

    def _row(self):
        selection = self.tree.selection()
        return self.rows.get(selection[0]) if selection else None

    def _selected(self, _event=None):
        row = self._row()
        if row is None:
            return
        for box, text in ((self.en_box, row.get("title_en")), (self.jp_box, row.get("title_jp"))):
            box.configure(state="normal")
            box.delete("1.0", "end")
            box.insert("1.0", text or "[Not supplied by the gallery; your existing field will be kept]")
            box.configure(state="disabled")
        available = {key: bool(row.get(key)) and self.target.entries[key] is not None
                     and row.get("metadata_ok", False) for key in ("title_en", "title_jp")}
        self.apply_buttons["english"].configure(state="normal" if available["title_en"] else "disabled")
        self.apply_buttons["japanese"].configure(state="normal" if available["title_jp"] else "disabled")
        self.apply_buttons["both"].configure(state="normal" if any(available.values()) else "disabled")
        note = row.get("metadata_error") or (
            "Choose a title button below. Missing fields are never cleared or translated.")
        self.status.configure(text=note)
        self._thumb_cancel.set()
        if self._thumb_future is not None:
            self._thumb_future.cancel()
        self._thumb_serial += 1
        serial = self._thumb_serial
        self._thumb_cancel = cancel = threading.Event()
        self.thumb_label.configure(image=None, text="Loading cover..." if row.get("thumb") else "No cover available")
        self._thumb_photo = None
        if not row.get("thumb"):
            return
        if row["thumb"] in self._thumb_cache:
            self._show_thumbnail(self._thumb_cache[row["thumb"]])
            return
        options = dict(self.owner._lookup_options)
        events = self._thumb_events

        def worker():
            client = None
            try:
                client = EHManualTitleLookup(**options)
                image = client.thumbnail(row, cancel)
                if not cancel.is_set():
                    events.put((serial, row["thumb"], image))
            except Exception:
                if not cancel.is_set():
                    events.put((serial, row["thumb"], None))
            finally:
                if client is not None:
                    client.close()
        self._thumb_future = self._thumb_pool.submit(worker)

    def _poll_thumbnail(self):
        self._thumb_after = None
        if self._closed:
            return
        try:
            while True:
                serial, url, image = self._thumb_events.get_nowait()
                if image is not None:
                    self._thumb_cache[url] = image
                if serial == self._thumb_serial:
                    self._show_thumbnail(image)
        except queue.Empty:
            pass
        self._thumb_after = self.after(60, self._poll_thumbnail)

    def _show_thumbnail(self, image):
        if image is None:
            self.thumb_label.configure(image=None, text="Cover unavailable\nTitles are still usable")
            self._thumb_photo = None
        else:
            self._thumb_photo = ctk.CTkImage(light_image=image, dark_image=image, size=image.size)
            self.thumb_label.configure(text="", image=self._thumb_photo)

    def _apply(self, mode):
        row = self._row()
        if not row or not row.get("metadata_ok"):
            return
        wanted = ("title_en", "title_jp") if mode == "both" else ("title_en" if mode == "english" else "title_jp",)
        updates = {key: row[key] for key in wanted if row.get(key) and self.target.entries[key] is not None}
        if not updates:
            return
        try:
            self.target.apply(updates)
        except Exception as exc:
            messagebox.showwarning("Apply gallery titles", str(exc), parent=self)
            return
        fields = " + ".join("English" if key == "title_en" else "Japanese" for key in updates)
        text = f"Applied {fields} to {self.target.label}."
        if len(updates) < len(wanted):
            text += " Missing/unavailable fields were left unchanged."
        self.status.configure(text=text)
        self.owner.lookup_status.configure(text=text)
        self.owner.parent_app.log(f"[Manual lookup] Applied {fields} metadata from {row['url']}")

    def _open_gallery(self):
        row = self._row()
        if row:
            self.owner.parent_app._browser_open_url("ehentai", row["url"], "Gallery result")

    def _close(self):
        if self._closed:
            return
        self._closed = True
        self._thumb_cancel.set()
        self._thumb_pool.shutdown(wait=False, cancel_futures=True)
        if self._thumb_after is not None:
            try:
                self.after_cancel(self._thumb_after)
            except tk.TclError:
                pass
        self.destroy()



class CoverImageTitleSearchDialog(ctk.CTkToplevel):
    """Search one metadata source and choose a visually ranked gallery."""

    def __init__(self, parent, backend, image_path, on_select_callback, source_label="E-Hentai / ExHentai"):
        super().__init__(parent)
        self.backend = backend
        self.image_path = image_path
        self.on_select_callback = on_select_callback
        self.source_label = source_label
        self.selected_metadata = None

        self.title(f"{source_label} — Cover Title Search")
        self.geometry("750x450")
        self.transient(parent)
        self.grab_set()

        lbl = ctk.CTkLabel(
            self,
            text=f"Searching {source_label} and comparing candidate covers…",
            font=("Helvetica", 12, "bold"),
        )
        lbl.pack(padx=10, pady=(10, 5))

        self.progress = ctk.CTkProgressBar(self)
        self.progress.pack(fill="x", padx=15, pady=5)
        self.progress.configure(mode="indeterminate")
        self.progress.start()

        frame = ctk.CTkFrame(self)
        frame.pack(fill="both", expand=True, padx=10, pady=5)

        cols = ("similarity", "title", "url")
        self.tree = ttk.Treeview(frame, columns=cols, show="headings", selectmode="browse")
        self.tree.heading("similarity", text="Match %")
        self.tree.heading("title", text="Gallery Title")
        self.tree.heading("url", text="Gallery URL")

        self.tree.column("similarity", width=80, anchor="center")
        self.tree.column("title", width=420)
        self.tree.column("url", width=200)

        vsb = ttk.Scrollbar(frame, orient="vertical", command=self.tree.yview)
        self.tree.configure(yscrollcommand=vsb.set)
        self.tree.pack(side="left", fill="both", expand=True)
        vsb.pack(side="right", fill="y")

        btn_frame = ctk.CTkFrame(self)
        btn_frame.pack(fill="x", padx=10, pady=10)

        self.btn_apply = ctk.CTkButton(btn_frame, text="Apply Selected Title Metadata", state="disabled", command=self._on_apply)
        self.btn_apply.pack(side="right", padx=5)

        btn_cancel = ctk.CTkButton(btn_frame, text="Cancel", command=self.destroy)
        btn_cancel.pack(side="right", padx=5)

        self.tree.bind("<<TreeviewSelect>>", self._on_tree_select)

        threading.Thread(target=self._run_search, daemon=True).start()

    def _run_search(self):
        try:
            if not hasattr(self.backend, "search_gallery_matches_by_image") or not hasattr(self.backend, "fetch_gallery_title_metadata"):
                raise TypeError(
                    "Cover-title search backend is missing the required gallery lookups. "
                    "Use a backend instance, not the main app window."
                )
            matches = self.backend.search_gallery_matches_by_image(self.image_path)
            self.after(0, lambda: self._populate_matches(matches))
        except Exception as exc:
            self.after(0, lambda exc=exc: messagebox.showerror("Search Error", f"{self.source_label} search failed: {exc}", parent=self))
            self.after(0, self.destroy)

    def _populate_matches(self, matches):
        self.progress.stop()
        self.progress.pack_forget()

        for item in matches:
            sim = f"{item.get('similarity', 0)}%"
            title = item.get("title", "")
            url = item.get("url", "")
            self.tree.insert("", "end", values=(sim, title, url))

        if not matches:
            messagebox.showinfo(
                "No Matches",
                f"No near-identical covers (>= {MIN_COVER_SIMILARITY:.0f}% match) were found on {self.source_label}.\n\n"
                "Unrelated title-text hits below that threshold are intentionally hidden.",
                parent=self,
            )

    def _on_tree_select(self, event):
        selected = self.tree.selection()
        self.btn_apply.configure(state="normal" if selected else "disabled")

    def _on_apply(self):
        selected = self.tree.selection()
        if not selected:
            return

        values = self.tree.item(selected[0], "values")
        gallery_url = values[2]

        self.btn_apply.configure(state="disabled", text="Fetching Titles...")

        def fetch_task():
            try:
                metadata = self.backend.fetch_gallery_title_metadata(gallery_url)
                english = metadata.get("english", [])
                japanese = metadata.get("japanese", [])

                title_en = english[0] if english else values[1]
                title_jp = japanese[0] if japanese else ""

                self.after(0, lambda: self._finish_apply(title_en, title_jp))
            except Exception as exc:
                self.after(0, lambda exc=exc: messagebox.showerror("Fetch Error", f"Failed to fetch gallery metadata: {exc}", parent=self))
                self.after(0, lambda: self.btn_apply.configure(state="normal", text="Apply Selected Title Metadata"))

        threading.Thread(target=fetch_task, daemon=True).start()

    def _finish_apply(self, title_en, title_jp):
        if self.on_select_callback:
            self.on_select_callback(title_en, title_jp)
        self.destroy()


if __name__ == "__main__":
    app = EHentaiUploaderApp()
    app.mainloop()
