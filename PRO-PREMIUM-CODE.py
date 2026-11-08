import asyncio
import os
import re
import sqlite3
import random
import logging
import time
import json
import aiohttp
import hmac
import hashlib
import base64
import csv
import sys
import getpass
import secrets
import shutil
import signal
from collections import deque
from html import escape as html_escape
import urllib.parse
from datetime import datetime, timedelta
from typing import Optional, List, Tuple, Dict, Any

from aiogram import Bot, Dispatcher, F, BaseMiddleware
from aiogram.client.default import DefaultBotProperties
from aiogram.filters import Command, CommandStart, StateFilter
from aiogram.fsm.context import FSMContext
from aiogram.fsm.state import StatesGroup, State
from aiogram.types import (
    ReplyKeyboardMarkup, KeyboardButton, ReplyKeyboardRemove,
    InlineKeyboardMarkup, InlineKeyboardButton, CallbackQuery, Message, Dice, BufferedInputFile, FSInputFile
)


# ==============================================================================
# 0. SECURITY BOOTSTRAP  (secrets, password lock, encryption helpers - stdlib only)
# ==============================================================================
os.umask(0o077)                                   # every new file is private (owner only)
BASE_DIR = os.path.dirname(os.path.abspath(__file__))
VAULT_FILE = os.path.join(BASE_DIR, "bot_secrets.vault")
DATA_KEY_FILE = os.path.join(BASE_DIR, ".bot_data_key")
DB_FILE = "Cuibcc.db"

def _load_dotenv(path: str) -> None:
    """Tiny .env reader: KEY=VALUE lines (the file must stay private, never share it)."""
    try:
        with open(path, "r", encoding="utf-8") as fh:
            for line in fh:
                line = line.strip()
                if not line or line.startswith("#") or "=" not in line:
                    continue
                k, v = line.split("=", 1)
                os.environ.setdefault(k.strip(), v.strip().strip('"').strip("'"))
    except OSError:
        pass

_load_dotenv(os.path.join(BASE_DIR, ".env"))

# ---- authenticated encryption built only from hmac/sha256/scrypt (encrypt-then-MAC) ----
def _stream(key: bytes, nonce: bytes, n: int) -> bytes:
    out, i = bytearray(), 0
    while len(out) < n:
        out += hmac.new(key, nonce + i.to_bytes(8, "big"), hashlib.sha256).digest()
        i += 1
    return bytes(out[:n])

def seal(enc_key: bytes, mac_key: bytes, data: bytes) -> bytes:
    nonce = os.urandom(16)
    ct = bytes(a ^ b for a, b in zip(data, _stream(enc_key, nonce, len(data))))
    tag = hmac.new(mac_key, nonce + ct, hashlib.sha256).digest()
    return nonce + tag + ct

def unseal(enc_key: bytes, mac_key: bytes, blob: bytes) -> bytes:
    if len(blob) < 48:
        raise ValueError("corrupt")
    nonce, tag, ct = blob[:16], blob[16:48], blob[48:]
    if not hmac.compare_digest(tag, hmac.new(mac_key, nonce + ct, hashlib.sha256).digest()):
        raise ValueError("bad key or tampered data")
    return bytes(a ^ b for a, b in zip(ct, _stream(enc_key, nonce, len(ct))))

def _split_key(material: bytes) -> Tuple[bytes, bytes]:
    d = hashlib.sha512(material).digest()
    return d[:32], d[32:]

def hash_password(pw: str) -> str:
    salt = os.urandom(16)
    dk = hashlib.scrypt(pw.encode(), salt=salt, n=2 ** 14, r=8, p=1, dklen=32)
    return "scrypt$" + base64.b64encode(salt).decode() + "$" + base64.b64encode(dk).decode()

def verify_password(pw: str, stored: str) -> bool:
    try:
        _, s, h = stored.split("$")
        dk = hashlib.scrypt((pw or "").encode(), salt=base64.b64decode(s), n=2 ** 14, r=8, p=1, dklen=32)
        return hmac.compare_digest(dk, base64.b64decode(h))
    except Exception:
        return False

def password_is_strong(pw: str, min_len: int = 10) -> bool:
    return len(pw) >= min_len and bool(re.search(r"[A-Za-z]", pw)) and bool(re.search(r"\d", pw))

def vault_write(path: str, secrets_dict: dict, password: str) -> None:
    salt = os.urandom(16)
    key = hashlib.scrypt(password.encode(), salt=salt, n=2 ** 14, r=8, p=1, dklen=64)
    blob = seal(key[:32], key[32:], json.dumps(secrets_dict).encode())
    with open(path, "wb") as fh:
        fh.write(b"BV1" + salt + blob)
    try: os.chmod(path, 0o600)
    except OSError: pass

def vault_read(path: str, password: str) -> dict:
    raw = open(path, "rb").read()
    if raw[:3] != b"BV1":
        raise ValueError("not a vault")
    salt, blob = raw[3:19], raw[19:]
    key = hashlib.scrypt(password.encode(), salt=salt, n=2 ** 14, r=8, p=1, dklen=64)
    return json.loads(unseal(key[:32], key[32:], blob).decode())

def _run_setup() -> None:
    """python <this file> --setup  ->  stores the bot token in an encrypted, password-locked vault
    (optional - you can also simply use the BOT_TOKEN environment variable)."""
    print("=== BOT SECURITY SETUP ===")
    token = getpass.getpass("1) Paste the BOT TOKEN (hidden): ").strip()
    if not re.match(r"^\d{6,}:[A-Za-z0-9_-]{30,}$", token):
        sys.exit("That does not look like a Telegram bot token.")
    while True:
        p1 = getpass.getpass("2) Choose the BOT START PASSWORD (min 8 chars - asked every time the bot starts): ")
        p2 = getpass.getpass("   Repeat it: ")
        if p1 == p2 and len(p1) >= 8:
            break
        print("   Passwords differ or too short, try again.")
    vault_write(VAULT_FILE, {"BOT_TOKEN": token}, p1)
    print("\nDONE. Token is now locked inside bot_secrets.vault.")
    print("Delete BOT_TOKEN from any .env file / environment, then start the bot normally.")
    print("Hosting without a terminal? Set the env var BOT_VAULT_PASSWORD to the START password.")

if "--setup" in sys.argv:
    _run_setup()
    sys.exit(0)

_TOKEN_SRC = ["unknown"]

def _load_bot_token() -> str:
    tok = (os.getenv("BOT_TOKEN") or "").strip()
    if tok:
        _TOKEN_SRC[0] = "environment / .env"
        return tok                                   # 1) environment / private .env file
    if os.path.exists(VAULT_FILE):                   # 2) password-locked vault
        for attempt in range(3):
            pw = os.getenv("BOT_VAULT_PASSWORD") or (getpass.getpass("🔐 Bot start password: ") if sys.stdin.isatty() else "")
            if not pw:
                sys.exit("Bot is locked. Start it from a terminal, or set BOT_VAULT_PASSWORD.")
            try:
                _TOKEN_SRC[0] = "password-locked vault"
                return vault_read(VAULT_FILE, pw)["BOT_TOKEN"]
            except Exception:
                time.sleep(2)
                if os.getenv("BOT_VAULT_PASSWORD"):
                    break
                print("❌ Wrong password.")
        sys.exit("Wrong password - bot stays locked.")
    sys.exit("No bot token found.\nRun:  python " + os.path.basename(__file__) + " --setup   (recommended)\n"
             "or set the BOT_TOKEN environment variable / .env file.")

# ---- encryption at rest for API keys saved in the database ----
def _data_key() -> Tuple[bytes, bytes]:
    env = os.getenv("BOT_DATA_KEY", "").strip()
    if env:
        return _split_key(env.encode())
    if not os.path.exists(DATA_KEY_FILE):
        with open(DATA_KEY_FILE, "w") as fh:
            fh.write(secrets.token_hex(32))
        try: os.chmod(DATA_KEY_FILE, 0o600)
        except OSError: pass
    return _split_key(open(DATA_KEY_FILE).read().strip().encode())

_DATA_KEYS: Optional[Tuple[bytes, bytes]] = None
def secret_enc(plain: str) -> str:
    global _DATA_KEYS
    _DATA_KEYS = _DATA_KEYS or _data_key()
    return "enc1:" + base64.b64encode(seal(_DATA_KEYS[0], _DATA_KEYS[1], plain.encode())).decode()

def secret_dec(value: str) -> str:
    global _DATA_KEYS
    _DATA_KEYS = _DATA_KEYS or _data_key()
    return unseal(_DATA_KEYS[0], _DATA_KEYS[1], base64.b64decode(value[5:])).decode()

SENSITIVE_SETTINGS = {"sgvip_token", "binance_api", "binance_secret", "reseller_api_key", "reseller_master_key", "fam_live_key"}
_bad_secrets: set = set()     # secret setting keys that could not be decrypted (data key changed)

# ==============================================================================
# 1. BOT CONFIGURATION & CONSTANTS
# ==============================================================================
# The token is NEVER written in this file. It comes from the locked vault (python file.py --setup),
# the BOT_TOKEN environment variable, or a private .env file.
BOT_TOKEN = "9081658964:AAEQibLFFKEv5QHdbdbgwW9UxRI6gSiJpOs"
BOT_USERNAME = "@KARAN_MENU_STORE_BOT"
ADMIN_ID = 8680144387
ADMIN_CONTACT = "@karan_shukla_36"

# --- Force-join channel: users must join this channel before the bot works ---
# NOTE: the bot must be an ADMIN of this channel, otherwise Telegram cannot check membership.
REQUIRED_CHANNEL = "@yt_honter17"
REQUIRED_CHANNEL_URL = "https://t.me/yt_honter17"

# --- SGVIP Payment Gateway (new) ---
SGVIP_API_TOKEN = os.getenv("SGVIP_API_TOKEN", "PAYMENT_GATEWAY_API_TOKEN")
 # Replace with your actual API token
SGVIP_CREATE_ORDER_URL = "https://sgvip.site/api/create-order"
SGVIP_CHECK_STATUS_URL = "https://sgvip.site/api/check-order-status"
SGVIP_ORDER_TIMEOUT_MINUTES = 10
# After payment the gateway redirects the user here (your bot link)
SGVIP_REDIRECT_URL = f"https://t.me/{BOT_USERNAME.lstrip('@')}"

# --- Reseller API (2-Tier Stock Fulfillment: Live Fallback) ---
# These are the DEFAULT values. They can be overridden live from the
# Admin Panel -> "Reseller API Settings" (stored in the `settings` table).
RESELLER_API_URL = "https://bantibhaiya.to/api/reseller_v1.php"
# change only reseller API key
RESELLER_API_KEY = os.getenv("RESELLER_API_KEY", "YOUR_RESELLER_API_KEY")
# Don't make any other changes anywhere else.
RESELLER_MASTER_KEY = "a7f3e8b2c9d1f4a6b8c2d5e9f1a3b6c8"
RESELLER_USER_AGENT = ("Mozilla/5.0 (Windows NT 10.0; Win64; x64) "
                       "AppleWebKit/537.36 (KHTML, like Gecko) "
                       "Chrome/120.0.0.0 Safari/537.36")
RESELLER_API_TIMEOUT = 25  # seconds

USDT_TO_INR = 90.0
VIP_DISCOUNT_PERCENTAGE = 10.0
VIP_PRICE_INR = 1000.0

WELCOME_STICKER_ID = "CAACAgIAAxkBAAEU-WZmH_..."  # Replace with your sticker ID

FIXED_CATEGORIES = [
    "ANDROID NON ROOT PANEL",
    "ANDROID ROOT PANEL",
    "PC PANEL"
]

# ==============================================================================
# YOUR PREMIUM EMOJIS – all required emoji IDs (updated with new premium ones)
# ==============================================================================
DEFAULT_EMOJIS = {
    'product_store': '5312361253610475399',
    'profile': '5258011929993026890',
    'add_balance': '5985630530111020079',
    'history': '6032594876506312598',
    'support': '5967280668885913944',
    'store_title': '5994502837327892086',
    'back': '5877536313623711363',
    'upi': '5807750375033278838',
    'reseller': '5886505193180239900',
    'tutorial': '6005986106703613755',
    'telegram': '5875465628285931233',
    'whatsapp': '5954224165874569584',
    'welcome': '5994502837327892086',
    'vip': '5886505193180239900',
    'category_android_non_root': '6161172706856282588',
    'category_android_root': '6161449831031118974',
    'category_pc': '5350554349074391003',
    'grid_id': '5474625972751837256',
    'name': '5215399540814781035',
    'account_level': '6129584162992034014',
    'regular_user': '5904630315946611415',
    'wallet': '6210859306602995217',
    'current_balance': '5316711376876485361',
    'global_stats': '6161437856662298090',
    'total_orders': '6160968017304888311',
    'total_spent': '5197503331215361533',
    'joined_grid': '5433614043006903194',
    'info_icon': '6037421444789440735',
    'check_icon': '6161241250239356403',
    'checkbox_icon': '6161437856662298090',
    'shield_icon': '6086672466132865380',
    'money_icon': '5890848474563352982',
    'redeem_icon': '5377624166436445368',
    'wallet_left': '6210859306602995217',
    'wallet_right': '5305699699204837855',
    'point_down': '6161302621027049305',
    # --- new features: paste your premium emoji ID here, or set it from Admin -> Edit All Emojis ---
    # Default premium IDs so nothing is ever blank. Admin -> Edit All Emojis overrides these any time.
    'referral': '5377624166436445368',
    'spin': '5890848474563352982',
    'files': '6161302621027049305',
    'binance': '5305699699204837855',
    # profile: "Total Referrals" line
    'total_referrals': '5904630315946611415',
    # admin panel header
    'admin_title': '6086672466132865380',
    # YouTube / video button. No premium ID yet -> normal emoji is shown until you set one
    # from Admin -> Edit All Emojis -> video
    'video': '',
    # profile dashboard decoration (normal emoji until you set a premium ID)
    'arrow': '',
    'wave': '',
    'hosting': '5312361253610475399',
}

# Normal emoji shown until a premium ID is set for the slot
# Normal (plain) emoji for EVERY slot - used when an emoji has no premium ID or when
# the admin chooses "Normal Emoji" mode.
NORMAL_EMOJI = {
    'product_store': '🛒', 'profile': '👤', 'add_balance': '💳', 'history': '🧾', 'support': '🎫',
    'store_title': '✨', 'back': '⬅️', 'upi': '📲', 'reseller': '👑', 'tutorial': '📢',
    'telegram': '✈️', 'whatsapp': '📱', 'welcome': '✨', 'vip': '💎',
    'category_android_non_root': '🤖', 'category_android_root': '🔓', 'category_pc': '💻',
    'grid_id': '🆔', 'name': '🧑', 'account_level': '🏅', 'regular_user': '🙂', 'wallet': '👛',
    'current_balance': '💰', 'global_stats': '📊', 'total_orders': '📦', 'total_spent': '💸',
    'joined_grid': '📅', 'info_icon': 'ℹ️', 'check_icon': '✅', 'checkbox_icon': '☑️',
    'shield_icon': '🔐', 'money_icon': '💵', 'redeem_icon': '🎟', 'wallet_left': '👛',
    'wallet_right': '👛', 'point_down': '👇', 'referral': '🎁', 'spin': '🎲', 'files': '📥',
    'binance': '🪙', 'total_referrals': '👥', 'admin_title': '⚙️', 'video': '▶️',
    'arrow': '❯', 'wave': '〰️', 'hosting': '🤖',
}
NORMAL_MARK = "\u2062"     # invisible marker: "this text must keep NORMAL emoji"
PREMIUM_MARK = "\u2063"    # invisible marker: "this text must use PREMIUM emoji"
_TG_EMOJI_RE = re.compile(r"<tg-emoji[^>]*>(.*?)</tg-emoji>", re.S)

EMOJI_FALLBACK = {'referral': '🎁', 'spin': '🎲', 'files': '📥', 'binance': '🪙', 'total_referrals': '👥', 'admin_title': '⚙️', 'video': '▶️'}

logging.basicConfig(
    level=logging.INFO,
    format='%(asctime)s - %(name)s - %(levelname)s - %(message)s',
    handlers=[
        logging.FileHandler("bot_activity.log"),
        logging.StreamHandler()
    ]
)
logger = logging.getLogger(__name__)

class _RedactFilter(logging.Filter):
    _pat = re.compile(r"\d{6,}:[A-Za-z0-9_-]{30,}")
    def filter(self, record: logging.LogRecord) -> bool:
        try:
            record.msg = self._pat.sub("[TOKEN-REDACTED]", record.getMessage())
            record.args = ()
        except Exception:
            pass
        return True
for _h in logging.getLogger().handlers:
    _h.addFilter(_RedactFilter())

# separate private log for security events (logins, blocked admin attempts, imports)
sec_logger = logging.getLogger("security")
_sec_h = logging.FileHandler(os.path.join(BASE_DIR, "security.log"))
_sec_h.setFormatter(logging.Formatter("%(asctime)s %(message)s"))
sec_logger.addHandler(_sec_h)
sec_logger.setLevel(logging.INFO)

def sec_log(event: str, uid: int = 0, detail: str = "") -> None:
    sec_logger.info(f"{event} uid={uid} {detail[:200]}")

bot = Bot(token=BOT_TOKEN, default=DefaultBotProperties(parse_mode="HTML"))
dp = Dispatcher()

def fmt_curr(amount: float) -> str:
    return f"₹{amount:,.2f}"

def safe_float(val, default=0.0):
    """Safely convert a value to float, return default if fails."""
    if val is None or val == "":
        return default
    try:
        return float(val)
    except (ValueError, TypeError):
        return default

# ==============================================================================
# 2. DATABASE FUNCTIONS
# ==============================================================================
def db_query(query: str, params: tuple = (), fetchone: bool = False, fetchall: bool = False, commit: bool = True) -> Any:
    conn = sqlite3.connect(DB_FILE)
    c = conn.cursor()
    try:
        c.execute(query, params)
        if fetchone:
            res = c.fetchone()
        elif fetchall:
            res = c.fetchall()
        else:
            res = None
        if commit: conn.commit()
        return res
    except Exception as e:
        logger.error(f"DB Error: {e} | Query: {query} | Params: {params}")
        if commit: conn.rollback()
        return None
    finally:
        conn.close()

def get_setting(key: str, default: str = "") -> str:
    val = db_query("SELECT value FROM settings WHERE key=?", (key,), fetchone=True)
    if not (val and val[0]):
        return default
    v = val[0]
    if isinstance(v, str) and v.startswith("enc1:"):          # API keys are stored encrypted
        try:
            return secret_dec(v)
        except Exception:
            logger.error(f"Cannot decrypt setting '{key}' (data key changed?) - please enter it again in the admin panel.")
            _bad_secrets.add(key)
            return default
    return v

def set_setting(key: str, value: str) -> None:
    if key in SENSITIVE_SETTINGS and value and not str(value).startswith("enc1:"):
        value = secret_enc(str(value))
    db_query("INSERT OR REPLACE INTO settings (key, value) VALUES (?, ?)", (key, value))

def encrypt_sensitive_settings() -> None:
    """One-time upgrade: encrypt API keys that were saved as plain text."""
    for k in SENSITIVE_SETTINGS:
        r = db_query("SELECT value FROM settings WHERE key=?", (k,), fetchone=True)
        if r and r[0] and not str(r[0]).startswith("enc1:"):
            set_setting(k, str(r[0]))

def log_activity(user_id: int, action: str, details: str = "") -> None:
    try:
        timestamp = datetime.now().strftime("%Y-%m-%d %H:%M:%S")
        db_query(
            "INSERT INTO activity_logs (user_id, action, details, timestamp) VALUES (?, ?, ?, ?)",
            (user_id, action, details, timestamp)
        )
    except Exception as e:
        logger.error(f"Failed to log activity: {e}")

def get_emoji_mode() -> str:
    """Global emoji mode chosen by admin: 'premium' (default) or 'normal'."""
    return "normal" if get_setting("emoji_mode", "premium") == "normal" else "premium"

def get_emoji(slot: str, default_id: str = None, normal: bool = False) -> str:
    fb = EMOJI_FALLBACK.get(slot) or NORMAL_EMOJI.get(slot, "✨")
    if normal:
        return fb
    stored = get_setting(f"emoji_{slot}", "")
    emoji_id = stored if stored and stored.isdigit() else (default_id or DEFAULT_EMOJIS.get(slot, ""))
    if emoji_id:
        return f'<tg-emoji emoji-id="{emoji_id}">{fb}</tg-emoji>'
    return fb

def get_emoji_icon(slot: str, default_id: str = None) -> str:
    stored = get_setting(f"emoji_{slot}", "")
    emoji_id = stored if stored and stored.isdigit() else (default_id or DEFAULT_EMOJIS.get(slot, ""))
    return emoji_id


# ==============================================================================
# 2B. AUTO PREMIUM EMOJI ENGINE
#     Every normal emoji in ANY message / caption / button is automatically
#     converted to a premium (custom) emoji. Which premium emoji is used for
#     which normal emoji is decided by _EMOJI_SLOT_MAP below; the premium IDs
#     themselves come from DEFAULT_EMOJIS / Admin -> Edit All Emojis.
# ==============================================================================
_EMOJI_SLOT_MAP = {
    '✅': 'check_icon', '☑': 'check_icon', '✔': 'check_icon', '🟢': 'check_icon',
    '❌': 'info_icon', '⚠': 'info_icon', '🚫': 'info_icon', '🔴': 'info_icon',
    '🚨': 'info_icon', '⏳': 'info_icon', '🔄': 'info_icon', 'ℹ': 'info_icon', '🗑': 'info_icon',
    '🎉': 'redeem_icon', '🎟': 'redeem_icon', '🎁': 'referral',
    '💰': 'money_icon', '💵': 'money_icon', '💲': 'money_icon', '💸': 'money_icon',
    '💳': 'add_balance', '➕': 'add_balance',
    '🧾': 'history', '📦': 'history', '📭': 'history', '📋': 'history',
    '🔑': 'shield_icon', '🛡': 'shield_icon', '🔒': 'shield_icon', '🔌': 'shield_icon',
    '📅': 'joined_grid', '🗓': 'joined_grid',
    '👤': 'name', '👥': 'total_referrals',
    '👑': 'reseller', '⚡': 'reseller',
    '🌟': 'vip', '💎': 'vip', '🏆': 'vip',
    '🎲': 'spin', '📥': 'files', '📤': 'files', '🪙': 'binance',
    '🎫': 'support', '📝': 'support', '✏': 'support', '📞': 'support',
    '🔗': 'telegram', '📊': 'global_stats',
    '🎨': 'store_title', '🖼': 'store_title', '📢': 'tutorial', '📹': 'tutorial',
    '🖌': 'store_title',
    '✨': 'store_title', '🛒': 'product_store', '🏷': 'history', '🔖': 'history',
    '👇': 'point_down', '⏭': 'point_down', '📱': 'whatsapp', '🌐': 'telegram', '✈': 'telegram',
    '💬': 'support', '🗨': 'support', '💻': 'category_pc', '🚀': 'reseller',
    '⏱': 'info_icon', '📛': 'info_icon', '➖': 'info_icon', '👁': 'info_icon', '🧭': 'info_icon',
    '📌': 'info_icon', '😅': 'info_icon', '☢': 'info_icon',
    '🔐': 'shield_icon', '🔰': 'shield_icon', '⚙': 'shield_icon', '📡': 'shield_icon', '📁': 'files',
    '🆔': 'grid_id', '➡': 'point_down', '👉': 'point_down', '⬇': 'point_down',
    '❤': 'vip', '🔥': 'vip', '⭐': 'vip', '🎮': 'spin', '🎰': 'spin', '🎯': 'spin',
    '🔔': 'info_icon', '📣': 'tutorial', '🎬': 'tutorial', '🏠': 'back', '⬅': 'back', '🔙': 'back',
    '🤝': 'reseller', '🧑': 'name', '🙋': 'name',
    '▶': 'video', '❯': 'arrow', '〰': 'wave', '🤖': 'hosting', '🖥': 'hosting',
}
_DEFAULT_SLOT = 'store_title'      # any emoji that is not listed above still becomes premium with this slot

def _slot_for(ch: str) -> str:
    return _EMOJI_SLOT_MAP.get(ch, _DEFAULT_SLOT)
_ANY_EMOJI = "[\U0001F300-\U0001FAFF\u2600-\u27BF\u2B50\u2B55\u2B05-\u2B07\u2934\u2935\u2B1B\u2B1C]"
_EMOJI_RE = re.compile(
    "(" + "|".join(sorted((re.escape(k) for k in _EMOJI_SLOT_MAP), key=len, reverse=True)) + "|" + _ANY_EMOJI + ")\ufe0f?"
)
_TAG_SPLIT_RE = re.compile(r"(<tg-emoji.*?</tg-emoji>|<[^>]+>)", re.S)
_icon_cache: Dict[str, Tuple[float, str]] = {}

def _cached_icon(slot: str, force: bool = False) -> str:
    if not force and get_emoji_mode() == "normal":   # admin chose Normal Emoji mode
        return ""
    now = time.time()
    hit = _icon_cache.get(slot)
    if hit and now - hit[0] < 30:
        return hit[1]
    icon = get_emoji_icon(slot) or ""
    _icon_cache[slot] = (now, icon)
    return icon

def premiumize_text(text: str) -> str:
    """Turn every plain emoji in an HTML message into a premium <tg-emoji>."""
    if not text or not isinstance(text, str):
        return text
    force_premium = False
    if text.startswith(NORMAL_MARK):                 # this UI text is set to Normal Emoji
        return text[1:]
    if text.startswith(PREMIUM_MARK):                # this UI text is set to Premium Emoji
        text = text[1:]
        force_premium = True
    elif get_emoji_mode() == "normal":               # global Normal Emoji mode
        return _TG_EMOJI_RE.sub(r"\1", text)
    parts = _TAG_SPLIT_RE.split(text)          # odd indexes = tags (left untouched)
    def _sub(m):
        ch = m.group(1)
        icon = _cached_icon(_slot_for(ch), force_premium)
        return f'<tg-emoji emoji-id="{icon}">{ch}</tg-emoji>' if icon else m.group(0)
    for i in range(0, len(parts), 2):
        parts[i] = _EMOJI_RE.sub(_sub, parts[i])
    return "".join(parts)

_BUTTON_RULES = [
    (r"back", "back"),
    (r"gateway_inr|upi", "upi"),
    (r"crypto|binance", "binance"),
    (r"spin", "spin"), (r"referral|share", "referral"), (r"dlfile|download|files?\b", "files"),
    (r"reseller", "reseller"), (r"vip", "vip"),
    (r"ticket|support|reply|contact", "support"),
    (r"emoji|ui_|text", "store_title"),
    (r"pay_|deposit|balance|fund|keypad|kp_|price", "add_balance"),
    (r"shop|panel|product|prod_|view_p_|_p_|cat_|package", "product_store"),
    (r"order|history|audit|list", "history"),
    (r"stat", "global_stats"),
    (r"user|ban|warn", "name"),
    (r"key|api|token|master|agent|endpoint|gateway", "shield_icon"),
    (r"tutorial|video|broadcast", "tutorial"),
    (r"confirm|yes|verify|upgrade|buy|purchase|grant|make", "check_icon"),
    (r"cancel|close|delete|del|remove|revoke|toggle|status|reset|minus|min", "info_icon"),
]
_TRAIL_EMOJI_RE = re.compile("(" + "|".join(sorted((re.escape(k) for k in _EMOJI_SLOT_MAP), key=len, reverse=True)) + "|" + _ANY_EMOJI + ")\ufe0f?\\s*$")

def _button_slot(b, text: str) -> Optional[str]:
    if re.match(r"kp_\d+$", b.callback_data or ""):         # keypad digits stay plain
        return None
    t = text.lstrip()
    m = _EMOJI_RE.match(t)
    if m:                                                   # 1) leading emoji
        return _slot_for(m.group(1))
    m = _TRAIL_EMOJI_RE.search(t)
    if m:                                                   # 2) trailing emoji
        return _slot_for(m.group(1))
    probe = f"{(b.callback_data or '')} {t}".lower()        # 3) keyword rules
    for pattern, slot in _BUTTON_RULES:
        if re.search(pattern, probe):
            return slot
    return "info_icon"                                      # 4) default

def _strip_button_emoji(text: str) -> str:
    t = text.strip()
    m = _EMOJI_RE.match(t)
    if m:
        t = t[m.end():].strip()
    else:
        m = _TRAIL_EMOJI_RE.search(t)
        if m:
            t = t[:m.start()].strip()
    return t

def premiumize_markup(markup):
    """Every inline button gets a premium icon (its own emoji if it has one)."""
    if isinstance(markup, ReplyKeyboardMarkup):
        try:
            krows = []
            for row in markup.keyboard:
                new_row = []
                for b in row:
                    try:
                        if not getattr(b, "icon_custom_emoji_id", None) and b.text:
                            slot = _button_slot(b, b.text)
                            icon = _cached_icon(slot) if slot else ""
                            if icon:
                                b = b.model_copy(update={"text": _strip_button_emoji(b.text) or b.text,
                                                         "icon_custom_emoji_id": icon})
                    except Exception:
                        pass
                    new_row.append(b)
                krows.append(new_row)
            return markup.model_copy(update={"keyboard": krows})
        except Exception:
            return markup
    if not isinstance(markup, InlineKeyboardMarkup):
        return markup
    rows = []
    for row in markup.inline_keyboard:
        new_row = []
        for b in row:
            try:
                if not b.icon_custom_emoji_id and b.text:
                    slot = _button_slot(b, b.text)
                    icon = _cached_icon(slot) if slot else ""
                    if icon:
                        rest = _strip_button_emoji(b.text)
                        b = b.model_copy(update={"text": rest or b.text, "icon_custom_emoji_id": icon})
            except Exception:
                pass
            new_row.append(b)
        rows.append(new_row)
    return InlineKeyboardMarkup(inline_keyboard=rows)

def _normalize_markup(markup):
    """Normal Emoji mode: replace premium button icons with plain emoji in the button text."""
    if get_emoji_mode() != "normal":
        return markup
    idmap = {}
    for s in DEFAULT_EMOJIS:
        i = get_emoji_icon(s)
        if i:
            idmap.setdefault(i, EMOJI_FALLBACK.get(s) or NORMAL_EMOJI.get(s, "✨"))
    def fix(b):
        icon = getattr(b, "icon_custom_emoji_id", None)
        if icon:
            return b.model_copy(update={"icon_custom_emoji_id": None, "text": f"{idmap.get(icon, '✨')} {b.text}"})
        return b
    try:
        if isinstance(markup, InlineKeyboardMarkup):
            return InlineKeyboardMarkup(inline_keyboard=[[fix(b) for b in r] for r in markup.inline_keyboard])
        if isinstance(markup, ReplyKeyboardMarkup):
            return markup.model_copy(update={"keyboard": [[fix(b) for b in r] for r in markup.keyboard]})
    except Exception:
        pass
    return markup

async def premium_emoji_request_middleware(make_request, bot_, method):
    """Runs on every Telegram API call the bot makes."""
    try:
        fields = getattr(type(method), "model_fields", {})
        pm = getattr(method, "parse_mode", None)
        html_ok = "parse_mode" in fields and (pm is None or not isinstance(pm, str) or pm.upper() == "HTML")
        if html_ok:
            for fld in ("text", "caption"):
                val = getattr(method, fld, None)
                if isinstance(val, str) and val:
                    setattr(method, fld, premiumize_text(val))
        rm = getattr(method, "reply_markup", None)
        if rm is not None:
            setattr(method, "reply_markup", _normalize_markup(premiumize_markup(rm)))
    except Exception as e:
        logger.warning(f"Premium emoji middleware skipped: {e}")
    return await make_request(bot_, method)

try:
    bot.session.middleware(premium_emoji_request_middleware)
except Exception as _e:
    logger.warning(f"Could not enable auto premium emoji: {_e}")

# ==============================================================================
# 3. STRING RESOURCES – using placeholders for premium emojis
# ==============================================================================
UI_STYLE_NAMES = {
    "1": "💎 Style 1 — Premium Box",
    "2": "✨ Style 2 — Clean Shop",
    "3": "🌙 Style 3 — Dark Neon",
    "4": "🌸 Style 4 — Pastel Elegant",
    "5": "⚡ Style 5 — Minimal Pro",
    "6": "🔥 Style 6 — Bold Banner",
}

# Two complete looks. Switch from Admin -> "UI Style". Placeholders like {profile} / {vip} are the
# premium emoji slots (DEFAULT_EMOJIS); {v_...} are live values filled in by the bot.
UI_THEMES = {
    # ------------------------------------------------------------------ STYLE 1 : PREMIUM BOX
    "1": {
        "start_menu": (
            "{store_title}<b>𝐒𝐆 𝐏𝐀𝐍𝐄𝐋 𝐒𝐓𝐎𝐑𝐄</b>{store_title}\n"
            "━━━━━━━━━━━━━━━━━━\n"
            "{product_store} 𝐏𝐫𝐨𝐝𝐮𝐜𝐭 𝐒𝐭𝐨𝐫𝐞  : 𝗮𝗹𝗹 𝗸𝗲𝘆𝘀 𝗣𝘂𝗿𝗰𝗵𝗮𝘀𝗲  &amp; 𝗶𝗻𝘀𝘁𝗮𝗻𝘁𝗹𝘆 𝗱𝗲𝗹𝗶𝘃𝗲𝗿𝘆\n"
            "{profile} 𝗠𝘆 𝗽𝗿𝗼𝗳𝗶𝗹𝗲 : 𝗰𝗵𝗲𝗰𝗸 𝘆𝗼𝘂𝗿 𝗮𝗰𝗰𝗼𝘂𝗻𝘁 𝗶𝗻𝗳𝗼𝗿𝗺𝗮𝘁𝗶𝗼𝗻\n"
            "{add_balance} 𝗔𝗱𝗱 𝗯𝗮𝗹𝗮𝗻𝗰𝗲 : 𝗱𝗲𝗽𝗼𝘀𝗶𝘁𝗲 𝗯𝗮𝗹𝗮𝗻𝗰𝗲 &amp; 𝘀𝗲𝗰𝘂𝗿𝗲 𝘀𝗲𝗿𝘃𝗶𝗰𝗲\n"
            "{history} 𝗔𝗹𝗹 𝗵𝗶𝘀𝘁𝗼𝗿𝘆 : 𝗰𝗵𝗲𝗰𝗸 𝗮𝗹𝗹 𝗽𝘂𝗿𝗰𝗵𝗮𝘀𝗲 𝗵𝗶𝘀𝘁𝗼𝗿𝘆\n"
            "{tutorial} 𝗧𝘂𝘁𝗼𝗿𝗶𝗮𝗹 : 𝘃𝗶𝗲𝘄 𝘁𝘂𝘁𝗼𝗿𝗶𝗮𝗹 &amp; 𝘄𝗼𝗿𝗸 𝘁𝗵𝗶𝘀 𝗯𝗼𝘁\n"
            "{support} 𝗦𝘂𝗽𝗽𝗼𝗿𝘁 : 𝗯𝗼𝘁 𝗽𝗿𝗼𝗯𝗹𝗲𝗺 𝘀𝗼𝗹𝘃𝗲𝗱 𝗳𝗼𝗿 𝘀𝘂𝗽𝗽𝗼𝗿𝘁 𝗮𝗱𝗺𝗶𝗻\n"
            "{referral} <b>𝗥𝗲𝗳𝗲𝗿𝗿𝗮𝗹</b> : 𝗶𝗻𝘃𝗶𝘁𝗲 𝗳𝗿𝗶𝗲𝗻𝗱𝘀 &amp; 𝗲𝗮𝗿𝗻 𝗿𝗲𝘄𝗮𝗿𝗱𝘀\n"
            "{spin} <b>𝗟𝘂𝗱𝗼 𝗦𝗽𝗶𝗻</b> : 𝗽𝗹𝗮𝘆 𝗴𝗮𝗺𝗲 𝗮𝗻𝗱 𝘄𝗶𝗻 𝗯𝗮𝗹𝗮𝗻𝗰𝗲\n"
            "{files} <b>𝗗𝗼𝘄𝗻𝗹𝗼𝗮𝗱 𝗙𝗶𝗹𝗲</b> : 𝗱𝗼𝘄𝗻𝗹𝗼𝗮𝗱 𝗹𝗮𝘁𝗲𝘀𝘁 𝗮𝗽𝗸 𝗳𝗼𝗿 𝘀𝗮𝗳𝗲𝘁𝘆\n"
            "━━━━━━━━━━━━━━━━━━"
        ),
        "profile": (
            "<blockquote>{reseller} <b>YOUR PROFILE DASHBOARD</b></blockquote>\n"
            "{arrow}  {wave}{wave}{wave}{wave}{wave}{wave}{wave}{wave}\n\n"
            "<blockquote>{grid_id} <b>Account ID:</b> {v_id}</blockquote>\n"
            "<blockquote>{account_level} <b>Account Tier:</b> {v_tier}</blockquote>\n"
            "<blockquote>{current_balance} <b>Current Funds:</b> {current_balance}{v_balance}</blockquote>\n"
            "<blockquote>{total_referrals} <b>Active Referrals:</b> {v_refs} users</blockquote>\n\n"
            "<i>Select a history filter below to view records.</i>"
        ),
        "add_balance_menu": (
            "{add_balance} <b>ADD BALANCE</b> {info_icon}\n\n"
            "{info_icon} Select your preferred payment method. {check_icon}\n\n"
            "┣ {upi} UPI — Fast Indian payments {checkbox_icon}\n"
            "{binance_line}"
            "{shield_icon} Payments are verified securely. {check_icon}"
        ),
        "vip_menu": (
            "{vip} <b><u>VIP MEMBERSHIP CLUB</u></b> {vip}\n\n"
            "Unlock premium benefits and permanent discounts!\n\n"
            "{vip} <b>VIP Benefits:</b>\n"
            "• Flat {v_discount}% off on ALL products\n"
            "• Priority Support\n"
            "• Exclusive VIP-only giveaways\n\n"
            "{add_balance} <b>VIP Price:</b> {v_price} (Lifetime)\n"
            "{name} <b>Your Status:</b> {vip_status}"
        ),
        "tutorial": (
            "{tutorial} <b><u>— TUTORIALS &amp; GUIDE —</u></b> {tutorial}\n\n"
            "1️⃣ Add funds via <b>Add Balance</b>\n"
            "2️⃣ Navigate to <b>Product Store</b>\n"
            "3️⃣ Choose your desired Panel and Package validity.\n"
            "4️⃣ The Key and Installation APK link will be instantly provided."
        ),
        "support": (
            "{telegram}{whatsapp} <b><u>— PREMIUM SUPPORT CENTER —</u></b>\n\n"
            "Contact us via Telegram or WhatsApp for instant help, or open a support ticket for admin assistance."
        ),
        "upi_menu": (
            "{upi} <b><u>— UPI DEPOSIT —</u></b> {upi}\n\n"
            "{money_icon} Select amount to deposit:\n"
            "{shield_icon} Instant auto-verification {check_icon}"
        ),
        "shop_menu": (
            "{product_store} <b><u>SELECT PRODUCT PANEL</u></b> {product_store}\n"
            "━━━━━━━━━━━━━━━━━━\n\n"
            "{point_down} <b>Choose a panel to view its packages:</b>"
        ),
        "orders": (
            "{history} <b><u>— YOUR RECENT ORDERS (LAST 10) —</u></b> {history}\n\n"
            "{v_orders_list}"
        ),
        "orders_empty": (
            "{history} <b>No purchases yet.</b>\n"
            "{info_icon} Your vault is empty."
        ),
        "deposit_history": (
            "{current_balance} <b><u>— DEPOSIT HISTORY (LAST 10) —</u></b> {current_balance}\n\n"
            "{v_deposit_list}"
        ),
        "deposit_empty": (
            "{current_balance} <b>No deposits yet.</b>\n"
            "{info_icon} Add balance and it will show up here."
        ),
        "hosting_menu": (
            "{hosting} <b><u>— PRIME HOSTING —</u></b> {hosting}\n\n"
            "Apna Telegram bot (.py) upload karo aur 24/7 chalao!\n\n"
            "{files} <b>Slots:</b> {v_slots}\n"
            "{vip} <b>Plan:</b> {v_plan}\n\n"
            "{point_down} Neeche se option chuno:"
        ),
        "hosting_upload": (
            "{files} <b><u>— UPLOAD BOT —</u></b> {files}\n\n"
            "Apni <b>.py</b> file bhejo (max {v_max} MB).\n"
            "{hosting} <b>Slots:</b> {v_slots}\n\n"
            "{shield_icon} Bot ka token file me daal dena.\n"
            "<i>Cancel ke liye /cancel</i>"
        ),
        "hosting_mybots": (
            "{hosting} <b><u>— MY HOSTED BOTS ({v_count}) —</u></b>\n"
            "━━━━━━━━━━━━━━━━━━\n"
            "🟢 Running  |  🔴 Stopped"
        ),
        "hosting_empty": (
            "{history} <b>Abhi koi bot hosted nahi hai.</b>\n\n"
            "{files} Pehla bot upload karo!"
        ),
        "hosting_panel": (
            "{hosting} <b><u>— BOT CONTROL PANEL —</u></b>\n"
            "━━━━━━━━━━━━━━━━━━\n"
            "{files} Name: <code>{v_name}</code>\n"
            "{grid_id} Bot ID: <code>{v_id}</code>\n"
            "{v_owner_line}"
            "{global_stats} Status: {v_status}\n"
            "━━━━━━━━━━━━━━━━━━"
        ),
        "hosting_profile": (
            "{profile} <b><u>— HOSTING PROFILE —</u></b>\n\n"
            "{grid_id} <b>ID:</b> <code>{v_uid}</code>\n"
            "{vip} <b>Plan:</b> {v_plan}\n"
            "{joined_grid} <b>Premium till:</b> {v_until}\n"
            "{files} <b>Slots:</b> {v_slots}\n"
            "{hosting} <b>Running bots:</b> {v_running}"
        ),
        "hosting_status": (
            "{global_stats} <b><u>— SERVER STATUS —</u></b>\n\n"
            "⚡ <b>CPU:</b> {v_cpu}\n"
            "💾 <b>RAM:</b> {v_ram}\n"
            "💽 <b>Disk:</b> {v_disk}\n"
            "{hosting} <b>Active bots:</b> {v_bots}"
        ),
        "hosting_help": (
            "{support} <b><u>— HOSTING HELP —</u></b>\n\n"
            "1️⃣ <b>Upload Bot</b> dabao aur apni .py file bhejo (max {v_max} MB)\n"
            "2️⃣ <b>My Hosted Bots</b> me bot kholo aur <b>Start</b> dabao\n"
            "3️⃣ Library chahiye to <b>Pip Install</b> use karo\n"
            "4️⃣ <b>Live Logs</b> me error dekho\n\n"
            "{vip} Premium: auto-restart, zyada slots, full logs"
        ),
        "reseller_menu": (
            "{reseller} <b><u>— BECOME A RESELLER —</u></b> {reseller}\n\n"
            "Upgrade your account to access wholesale <b>Reseller Prices</b>!\n\n"
            "{history} <b>Requirements to Upgrade:</b>\n"
            "1️⃣ Must have a minimum balance of <b>{v_min_balance}</b>.\n"
            "2️⃣ A one-time setup fee of <b>{v_setup_fee}</b> will be deducted.\n\n"
            "{wallet} <b>Your Current Balance:</b> {v_balance}"
        ),
        "reseller_active": (
            "{shield_icon} <b><u>— RESELLER DASHBOARD —</u></b> {shield_icon}\n\n"
            "{check_icon} <b>Status:</b> Active\n"
            "{joined_grid} <b>Since:</b> {v_since}\n"
            "{money_icon} <b>Total Saved:</b> {v_saved}\n\n"
            "{redeem_icon} You are enjoying exclusive wholesale prices on all products!"
        ),
        "referral": (
            "{referral} <b><u>— REFERRAL PROGRAM —</u></b> {referral}\n\n"
            "Invite friends and earn <b>{v_pct}%</b> of <b>every deposit</b> they make!\n\n"
            "{telegram} <b>Your link:</b>\n<code>{v_link}</code>\n\n"
            "{total_referrals} <b>Friends invited:</b> {v_count}\n"
            "{money_icon} <b>Total earned:</b> {v_earned}"
        ),
        "spin": (
            "{spin} <b><u>— LUDO SPIN —</u></b> {spin}\n\n"
            "Roll the dice once every 24 hours and win free balance!\n"
            "{vip} <b>Top prize:</b> {v_top}\n\n"
            "{v_status}"
        ),
        "files": (
            "{files} <b><u>— DOWNLOAD FILES —</u></b> {files}\n\n"
            "{point_down} Tap a file to receive it:"
        ),
        "join_channel": (
            "{shield_icon} <b><u>— JOIN OUR CHANNEL —</u></b> {shield_icon}\n\n"
            "{telegram} To use this bot you must join our channel first.\n\n"
            "{point_down} Tap <b>Join Channel</b>, then press <b>I Joined</b>."
        ),
    },
    # ------------------------------------------------------------------ STYLE 2 : CLEAN SHOP
    "2": {
        "start_menu": (
            "{store_title} <b>WELCOME TO THE SHOP</b>\n\n"
            "{product_store} <b>PRODUCT Store</b> : all keys purchase &amp; instantly delivery\n"
            "{profile} <b>My profile</b> : check your account information\n"
            "{add_balance} <b>Add balance</b> : deposite balance &amp; secure service\n"
            "{history} <b>All history</b> : check all purchase history\n"
            "{referral} <b>Referral</b> : invite friends &amp; earn rewards\n"
            "{tutorial} <b>Tutorial</b> : view tutorial &amp; work this bot\n"
            "{support} <b>Support</b> : bot problem solved for support admin\n"
            "{spin} <b>Ludo Spin</b> : play game and win balance\n"
            "{files} <b>Download File</b> : download latest apk for safety."
        ),
        "profile": (
            "{profile} <b>MY PROFILE</b>\n\n"
            "{grid_id} ID: <code>{v_id}</code>\n"
            "{account_level} Tier: <b>{v_tier}</b>\n"
            "{current_balance} Funds: <b>{v_balance}</b>\n"
            "{total_referrals} Referrals: <b>{v_refs}</b>\n\n"
            "<i>Select a history filter below.</i>"
        ),
        "add_balance_menu": (
            "{add_balance} <b>Add Balance</b>\n\n"
            "Choose a payment method:\n"
            "{upi} UPI\n"
            "{binance_line}"
            "{shield_icon} Secure &amp; instant verification"
        ),
        "vip_menu": (
            "{vip} <b>VIP CLUB</b>\n\n"
            "{check_icon} {v_discount}% off on all products\n"
            "{check_icon} Priority support\n"
            "{check_icon} VIP-only giveaways\n\n"
            "{add_balance} Price: <b>{v_price}</b> (Lifetime)\n"
            "{name} Status: {vip_status}"
        ),
        "tutorial": (
            "{tutorial} <b>HOW TO USE</b>\n\n"
            "1. Add balance\n"
            "2. Open Product Store\n"
            "3. Pick panel &amp; validity\n"
            "4. Get your key + APK link instantly"
        ),
        "support": (
            "{telegram}{whatsapp} <b>SUPPORT</b>\n\n"
            "Talk to us on Telegram / WhatsApp or open a ticket."
        ),
        "upi_menu": (
            "{upi} <b>UPI Deposit</b>\n\n"
            "{point_down} Select amount:"
        ),
        "shop_menu": (
            "{product_store} <b>PRODUCT STORE</b>\n\n"
            "{point_down} Choose a panel:"
        ),
        "orders": (
            "{history} <b>Recent Orders</b>\n\n"
            "{v_orders_list}"
        ),
        "orders_empty": (
            "{history} No orders yet."
        ),
        "deposit_history": (
            "{current_balance} <b>Deposit History</b>\n\n"
            "{v_deposit_list}"
        ),
        "deposit_empty": (
            "{current_balance} No deposits yet."
        ),
        "hosting_menu": (
            "{hosting} <b>HOSTING</b>\n\n"
            "{files} Slots: {v_slots}\n"
            "{vip} Plan: {v_plan}\n\n"
            "{point_down} Choose:"
        ),
        "hosting_upload": (
            "{files} <b>Upload Bot</b>\n\n"
            "Send your <b>.py</b> file (max {v_max} MB).\n"
            "{hosting} Slots: {v_slots}\n"
            "<i>/cancel to stop</i>"
        ),
        "hosting_mybots": (
            "{hosting} <b>My Bots</b> ({v_count})\n\n"
            "🟢 Running  |  🔴 Stopped"
        ),
        "hosting_empty": (
            "{history} No bots hosted yet.\n"
            "{files} Upload your first bot!"
        ),
        "hosting_panel": (
            "{hosting} <b>Bot Panel</b>\n\n"
            "{files} <code>{v_name}</code>\n"
            "{grid_id} ID: <code>{v_id}</code>\n"
            "{v_owner_line}"
            "{global_stats} {v_status}"
        ),
        "hosting_profile": (
            "{profile} <b>Hosting Profile</b>\n\n"
            "{grid_id} ID: <code>{v_uid}</code>\n"
            "{vip} Plan: {v_plan}\n"
            "{joined_grid} Till: {v_until}\n"
            "{files} Slots: {v_slots}\n"
            "{hosting} Running: {v_running}"
        ),
        "hosting_status": (
            "{global_stats} <b>Server</b>\n\n"
            "CPU {v_cpu} · RAM {v_ram} · Disk {v_disk}\n"
            "{hosting} Active bots: {v_bots}"
        ),
        "hosting_help": (
            "{support} <b>Help</b>\n\n"
            "Upload .py (max {v_max} MB) → open it in My Hosted Bots → Start.\n"
            "Pip Install for libraries, Live Logs for errors."
        ),
        "reseller_menu": (
            "{reseller} <b>RESELLER</b>\n\n"
            "Get wholesale prices.\n"
            "{wallet} Min balance: <b>{v_min_balance}</b>\n"
            "{money_icon} Setup fee: <b>{v_setup_fee}</b>\n"
            "{current_balance} Your balance: {v_balance}"
        ),
        "reseller_active": (
            "{reseller} <b>RESELLER</b> — Active\n\n"
            "{joined_grid} Since: {v_since}\n"
            "{money_icon} Saved: {v_saved}"
        ),
        "referral": (
            "{referral} <b>REFERRAL</b>\n\n"
            "Earn <b>{v_pct}%</b> of every deposit your friends make.\n\n"
            "{telegram} <code>{v_link}</code>\n"
            "{total_referrals} Invited: {v_count}\n"
            "{money_icon} Earned: {v_earned}"
        ),
        "spin": (
            "{spin} <b>LUDO SPIN</b>\n\n"
            "{vip} Top prize: {v_top}\n"
            "{v_status}"
        ),
        "files": (
            "{files} <b>Download Files</b>\n\n"
            "{point_down} Tap a file:"
        ),
        "join_channel": (
            "{telegram} <b>Join our channel to continue</b>\n\n"
            "{point_down} Join, then tap <b>I Joined</b>."
        ),
    },
}
# ---- 4 extra UI text styles (3-6). Any text a style does not define falls back to Style 1.
UI_THEMES.update({
    # ------------------------------------------------------------------ STYLE 3 : DARK NEON
    "3": {
        "start_menu": (
            "{store_title}<b>━━ 𝗦𝗚 𝗣𝗔𝗡𝗘𝗟 𝗦𝗧𝗢𝗥𝗘 ━━</b>{store_title}\n\n"
            "<blockquote>{product_store} <b>Product Store</b> — keys &amp; instant delivery</blockquote>\n"
            "<blockquote>{profile} <b>My Profile</b> — account info</blockquote>\n"
            "<blockquote>{add_balance} <b>Add Balance</b> — secure deposit</blockquote>\n"
            "<blockquote>{history} <b>All History</b> — purchases</blockquote>\n"
            "<blockquote>{referral} <b>Referral</b> — invite &amp; earn</blockquote>\n"
            "<blockquote>{tutorial} <b>Tutorial</b> — how to use</blockquote>\n"
            "<blockquote>{support} <b>Support</b> — talk to admin</blockquote>\n"
            "<blockquote>{spin} <b>Ludo Spin</b> — win balance</blockquote>\n"
            "<blockquote>{files} <b>Downloads</b> — latest APK</blockquote>"
        ),
        "profile": (
            "<blockquote>{profile} <b>DASHBOARD</b></blockquote>\n"
            "<blockquote>{grid_id} ID: <code>{v_id}</code></blockquote>\n"
            "<blockquote>{account_level} Tier: <b>{v_tier}</b></blockquote>\n"
            "<blockquote>{current_balance} Funds: <b>{v_balance}</b></blockquote>\n"
            "<blockquote>{total_referrals} Referrals: <b>{v_refs}</b></blockquote>"
        ),
        "add_balance_menu": (
            "{add_balance} <b>ADD BALANCE</b>\n\n"
            "{upi} UPI — instant\n"
            "{binance_line}"
            "{shield_icon} Secure verification"
        ),
        "vip_menu": (
            "{vip} <b>VIP CLUB</b>\n\n"
            "{check_icon} {v_discount}% off every product\n"
            "{check_icon} Priority support\n\n"
            "{add_balance} Price: <b>{v_price}</b>\n"
            "{name} Status: {vip_status}"
        ),
        "shop_menu": (
            "{product_store} <b>PRODUCT STORE</b>\n\n"
            "{point_down} Choose a panel:"
        ),
        "referral": (
            "{referral} <b>REFERRAL</b>\n\n"
            "Earn <b>{v_pct}%</b> of every deposit your friends make.\n\n"
            "{telegram} <code>{v_link}</code>\n"
            "{total_referrals} Invited: {v_count}\n"
            "{money_icon} Earned: {v_earned}"
        ),
        "spin": (
            "{spin} <b>LUDO SPIN</b>\n\n"
            "{vip} Top prize: {v_top}\n"
            "{v_status}"
        ),
        "join_channel": (
            "{telegram} <b>Join to continue</b>\n\n"
            "{point_down} Join, then tap <b>I Joined</b>."
        ),
    },
    # ------------------------------------------------------------------ STYLE 4 : PASTEL ELEGANT
    "4": {
        "start_menu": (
            "{store_title} <b>Welcome to our Shop</b> {store_title}\n"
            "<i>Everything you need, delivered with care.</i>\n\n"
            "{product_store} <b>Products</b> — keys &amp; instant delivery\n"
            "{profile} <b>Profile</b> — your account\n"
            "{add_balance} <b>Add Balance</b> — top up securely\n"
            "{history} <b>History</b> — your purchases\n"
            "{referral} <b>Referral</b> — share &amp; earn\n"
            "{tutorial} <b>Tutorial</b> — guide\n"
            "{support} <b>Support</b> — we are here\n"
            "{spin} <b>Ludo Spin</b> — try your luck\n"
            "{files} <b>Downloads</b> — safe files"
        ),
        "profile": (
            "{profile} <b>Your Profile</b>\n\n"
            "{grid_id} ID: <code>{v_id}</code>\n"
            "{account_level} Tier: <b>{v_tier}</b>\n"
            "{current_balance} Balance: <b>{v_balance}</b>\n"
            "{total_referrals} Referrals: <b>{v_refs}</b>\n\n"
            "<i>Thank you for shopping with us.</i>"
        ),
        "add_balance_menu": (
            "{add_balance} <b>Add Balance</b>\n\n"
            "Choose how you want to pay:\n"
            "{upi} UPI\n"
            "{binance_line}"
            "{shield_icon} Safe &amp; instant"
        ),
        "vip_menu": (
            "{vip} <b>VIP Membership</b>\n\n"
            "{check_icon} {v_discount}% off on every product\n"
            "{check_icon} Priority support\n\n"
            "{add_balance} Price: <b>{v_price}</b> (lifetime)\n"
            "{name} Status: {vip_status}"
        ),
        "shop_menu": (
            "{product_store} <b>Product Store</b>\n\n"
            "{point_down} Please choose a panel:"
        ),
        "referral": (
            "{referral} <b>Referral Program</b>\n\n"
            "Invite friends and earn <b>{v_pct}%</b> of their deposits.\n\n"
            "{telegram} <code>{v_link}</code>\n"
            "{total_referrals} Friends: {v_count}\n"
            "{money_icon} Earned: {v_earned}"
        ),
        "spin": (
            "{spin} <b>Ludo Spin</b>\n\n"
            "{vip} Top prize: {v_top}\n"
            "{v_status}"
        ),
        "join_channel": (
            "{telegram} <b>Please join our channel</b>\n\n"
            "{point_down} Then tap <b>I Joined</b>."
        ),
    },
    # ------------------------------------------------------------------ STYLE 5 : SECURE BOLD
    "5": {
        "start_menu": (
            "🔐 <b>━━━ SG PANEL STORE ━━━</b> 🔐\n"
            "<b>Secure • Instant • Trusted</b>\n"
            "━━━━━━━━━━━━━━━━━━\n"
            "{product_store} <b>PRODUCTS</b>\n"
            "{profile} <b>PROFILE</b>\n"
            "{add_balance} <b>ADD BALANCE</b>\n"
            "{history} <b>HISTORY</b>\n"
            "{referral} <b>REFERRAL</b>\n"
            "{tutorial} <b>TUTORIAL</b>\n"
            "{support} <b>SUPPORT</b>\n"
            "{spin} <b>LUDO SPIN</b>\n"
            "{files} <b>DOWNLOADS</b>\n"
            "━━━━━━━━━━━━━━━━━━\n"
            "{shield_icon} <i><b>Every payment is verified.</b></i>"
        ),
        "profile": (
            "🔐 <b>━━━ PROFILE ━━━</b>\n"
            "━━━━━━━━━━━━━━━━━━\n"
            "{grid_id} <b>ID:</b> <code>{v_id}</code>\n"
            "{account_level} <b>TIER:</b> <b>{v_tier}</b>\n"
            "{current_balance} <b>BALANCE:</b> <b>{v_balance}</b>\n"
            "{total_referrals} <b>REFERRALS:</b> <b>{v_refs}</b>\n"
            "━━━━━━━━━━━━━━━━━━\n"
            "{shield_icon} <i><b>Account secured</b></i>"
        ),
        "add_balance_menu": (
            "{add_balance} <b>━━━ ADD BALANCE ━━━</b>\n\n"
            "{upi} <b>UPI</b> — instant\n"
            "{binance_line}"
            "{shield_icon} <b>100% secure verification</b>"
        ),
        "vip_menu": (
            "{vip} <b>━━━ VIP CLUB ━━━</b> {vip}\n\n"
            "{check_icon} <b>{v_discount}% OFF</b> everything\n"
            "{check_icon} <b>Priority support</b>\n\n"
            "{add_balance} <b>Price: {v_price}</b> (lifetime)\n"
            "{name} Status: <b>{vip_status}</b>"
        ),
        "shop_menu": (
            "{product_store} <b>━━━ PRODUCT STORE ━━━</b>\n\n"
            "{shield_icon} <b>Verified keys • instant delivery</b>\n"
            "{point_down} <b>Choose a panel:</b>"
        ),
        "orders": (
            "{history} <b>━━━ RECENT ORDERS ━━━</b>\n\n"
            "{v_orders_list}"
        ),
        "referral": (
            "{referral} <b>━━━ REFERRAL ━━━</b>\n\n"
            "Earn <b>{v_pct}%</b> on every deposit.\n\n"
            "{telegram} <code>{v_link}</code>\n"
            "{total_referrals} Invited: <b>{v_count}</b>\n"
            "{money_icon} Earned: <b>{v_earned}</b>"
        ),
        "spin": (
            "{spin} <b>━━━ LUDO SPIN ━━━</b>\n\n"
            "{vip} <b>Top prize: {v_top}</b>\n"
            "{v_status}"
        ),
        "tutorial": (
            "{tutorial} <b>━━━ HOW IT WORKS ━━━</b>\n\n"
            "<b>1.</b> {add_balance} Add balance\n"
            "<b>2.</b> {product_store} Open Product Store\n"
            "<b>3.</b> {shield_icon} Choose panel &amp; validity\n"
            "<b>4.</b> {check_icon} Get key instantly"
        ),
        "support": (
            "{support} <b>━━━ SUPPORT ━━━</b>\n\n"
            "{telegram}{whatsapp} <b>Help on Telegram / WhatsApp</b>"
        ),
        "join_channel": (
            "{shield_icon} <b>━━━ JOIN TO CONTINUE ━━━</b> {shield_icon}\n\n"
            "{telegram} <b>Join our channel first.</b>\n"
            "{point_down} Then tap <b>I Joined</b>."
        ),
        "files": (
            "{files} <b>━━━ DOWNLOADS ━━━</b>\n\n"
            "{shield_icon} <b>Safe &amp; verified files</b>\n"
            "{point_down} <b>Tap a file:</b>"
        ),
        "reseller_menu": (
            "{reseller} <b>━━━ RESELLER ━━━</b>\n\n"
            "{wallet} Min balance: <b>{v_min_balance}</b>\n"
            "{money_icon} Setup fee: <b>{v_setup_fee}</b>\n"
            "{current_balance} Your balance: <b>{v_balance}</b>"
        ),
    },
    # ------------------------------------------------------------------ STYLE 6 : BOLD BANNER PRO
    "6": {
        "start_menu": (
            "🔥🔥🔥 <b>SG PANEL STORE</b> 🔥🔥🔥\n"
            "<b>╔══════════════════╗</b>\n"
            "<b>   🔐 SECURE SHOP 🔐</b>\n"
            "<b>╚══════════════════╝</b>\n"
            "{product_store} <b>BUY KEYS</b> — instant\n"
            "{profile} <b>MY PROFILE</b>\n"
            "{add_balance} <b>ADD BALANCE</b>\n"
            "{history} <b>HISTORY</b>\n"
            "{referral} <b>REFERRAL</b> — earn rewards\n"
            "{tutorial} <b>TUTORIAL</b>\n"
            "{support} <b>SUPPORT</b>\n"
            "{spin} <b>LUDO SPIN</b> — win now\n"
            "{files} <b>DOWNLOADS</b>\n"
            "<b>━━━━━━━━━━━━━━━━━━</b>\n"
            "{shield_icon} <b>Verified • Secure • Fast</b>"
        ),
        "profile": (
            "<b>▶ YOUR PROFILE ◀</b>\n"
            "<b>━━━━━━━━━━━━━━━━━━</b>\n"
            "{grid_id} <b>ID:</b> <code>{v_id}</code>\n"
            "{account_level} <b>TIER:</b> <b>{v_tier}</b>\n"
            "{current_balance} <b>BALANCE:</b> <b>{v_balance}</b>\n"
            "{total_referrals} <b>REFERRALS:</b> <b>{v_refs}</b>\n"
            "<b>━━━━━━━━━━━━━━━━━━</b>\n"
            "{shield_icon} <b>Account secured</b>"
        ),
        "add_balance_menu": (
            "{add_balance} <b>ADD BALANCE NOW</b>\n\n"
            "{upi} <b>UPI</b> — fastest\n"
            "{binance_line}"
            "{shield_icon} <b>100% secure</b>"
        ),
        "vip_menu": (
            "{vip} <b>VIP — GO PREMIUM</b> {vip}\n\n"
            "{check_icon} <b>{v_discount}% OFF</b> everything\n"
            "{check_icon} <b>Priority support</b>\n\n"
            "{add_balance} <b>{v_price}</b> lifetime\n"
            "{name} Status: <b>{vip_status}</b>"
        ),
        "shop_menu": (
            "{product_store} <b>PICK YOUR PANEL</b>\n\n"
            "{shield_icon} <b>Verified keys • instant</b>\n"
            "{point_down} Tap a panel below"
        ),
        "referral": (
            "{referral} <b>EARN {v_pct}% REFERRAL</b>\n\n"
            "{telegram} <code>{v_link}</code>\n"
            "{total_referrals} Invited: <b>{v_count}</b>\n"
            "{money_icon} Earned: <b>{v_earned}</b>"
        ),
        "spin": (
            "{spin} <b>LUDO SPIN</b>\n\n"
            "{vip} <b>TOP PRIZE: {v_top}</b>\n"
            "{v_status}"
        ),
        "join_channel": (
            "{shield_icon} <b>JOIN CHANNEL TO CONTINUE</b> {shield_icon}\n\n"
            "{telegram} <b>Join first</b>\n"
            "{point_down} Then tap <b>I Joined</b>."
        ),
    },
})

UI_TEXTS = UI_THEMES["1"]   # kept for backward compatibility

# key -> (label, placeholder help) used by Admin -> Edit UI Texts
UI_EDITABLE = {
    "start_menu": ("Start Menu", "emoji slots like {product_store} {profile} {spin}"),
    "profile": ("My Profile", "{v_id} {v_name} {v_tier} {v_level} {v_balance} {v_orders} {v_spent} {v_refs} {v_joined} {v_reseller_block} + emoji slots"),
    "add_balance_menu": ("Add Balance", "{binance_line} + emoji slots"),
    "upi_menu": ("UPI Deposit", "emoji slots"),
    "shop_menu": ("Product Store", "emoji slots"),
    "orders": ("Key History", "{v_orders_list} + emoji slots"),
    "deposit_history": ("Deposit History", "{v_deposit_list} + emoji slots"),
    "deposit_empty": ("Deposit (empty)", "emoji slots"),
    "hosting_menu": ("Hosting Menu", "{v_slots} {v_plan} + emoji slots"),
    "hosting_upload": ("Hosting Upload", "{v_slots} {v_max} + emoji slots"),
    "hosting_mybots": ("Hosted Bots List", "{v_count} + emoji slots"),
    "hosting_empty": ("Hosted Bots (empty)", "emoji slots"),
    "hosting_panel": ("Bot Control Panel", "{v_name} {v_id} {v_owner_line} {v_status} + emoji slots"),
    "hosting_profile": ("Hosting Profile", "{v_uid} {v_plan} {v_until} {v_slots} {v_running} + emoji slots"),
    "hosting_status": ("Server Status", "{v_cpu} {v_ram} {v_disk} {v_bots} + emoji slots"),
    "hosting_help": ("Hosting Help", "{v_max} + emoji slots"),
    "orders_empty": ("History (empty)", "emoji slots"),
    "vip_menu": ("VIP Club", "{vip_status} {v_price} {v_discount} + emoji slots"),
    "reseller_menu": ("Reseller Upgrade", "{v_min_balance} {v_setup_fee} {v_balance} + emoji slots"),
    "reseller_active": ("Reseller Dashboard", "{v_since} {v_saved} + emoji slots"),
    "referral": ("Referral", "{v_pct} {v_link} {v_count} {v_earned} + emoji slots"),
    "spin": ("Ludo Spin", "{v_top} {v_status} + emoji slots"),
    "files": ("Download Files", "emoji slots"),
    "tutorial": ("Tutorial", "emoji slots"),
    "support": ("Support", "{telegram} {whatsapp} + emoji slots"),
    "join_channel": ("Join Channel", "emoji slots"),
}

# sample values used by Admin -> (text) -> Preview
UI_SAMPLE = {
    "v_id": "123456789", "v_name": "Demo User", "v_level": "Regular User", "v_balance": "₹250.00",
    "v_orders": "5", "v_spent": "₹1,200.00", "v_refs": "3", "v_joined": "2026-01-01 10:00:00",
    "v_reseller_block": "", "v_tier": "RESELLER", "v_deposit_list": "<b>+₹100.00</b> (UPI)\n<i>2026-01-01 10:00</i>\n━━━━━━━━━━━━━━━━\n", "vip_status": "Not Subscribed", "v_price": "₹1,000.00", "v_discount": "10",
    "v_min_balance": "₹500.00", "v_setup_fee": "₹200.00", "v_since": "2026-01-01", "v_saved": "₹300.00",
    "v_orders_list": "<b>Sample Product</b> (₹100.00)\n<code>SAMPLE-KEY-1234</code>\n<i>2026-01-01</i>\n━━━━━━━━━━━━━━━━\n",
    "v_pct": "5", "v_link": "https://t.me/example_bot?start=ref_1", "v_count": "3", "v_earned": "₹15.00",
    "v_top": "₹5.00", "v_status": "Your spin is ready!", "binance_line": "",
}

UI_SAMPLE.update({
    "v_slots": "1/2", "v_plan": "FREE", "v_max": "5", "v_owner_line": "", "v_status": "🟢 Running", "v_uid": "123456789",
    "v_until": "—", "v_running": "1", "v_cpu": "12%", "v_ram": "40%", "v_disk": "55%", "v_bots": "3",
})

def get_ui_style(key: Optional[str] = None) -> str:
    """Style of ONE ui text (its own choice), else the global default style."""
    if key:
        own = get_setting(f"uitext_style_{key}", "")
        if own in UI_THEMES:
            return own
    st = get_setting("ui_style", "1")
    return st if st in UI_THEMES else "1"

def get_ui_default(key: str, style: Optional[str] = None) -> str:
    if key.startswith("cx_"):                         # admin-created UI text
        return get_setting(f"uicustom_text_{key}", "")
    style = style or get_ui_style(key)
    return UI_THEMES.get(style, {}).get(key) or UI_THEMES["1"].get(key, "")

def get_ui_emoji_mode(key: str) -> str:
    """'premium' / 'normal' for ONE ui text (its own choice), else the global mode."""
    own = get_setting(f"uitext_emoji_{key}", "")
    return own if own in ("premium", "normal") else get_emoji_mode()

def get_ui_text(key: str, **kwargs) -> str:
    """Admin override for this text's style (ui_<style>_<key>) -> else the theme default."""
    style = get_ui_style(key)
    own_mode = get_setting(f"uitext_emoji_{key}", "")
    normal = (own_mode == "normal") or (own_mode != "premium" and get_emoji_mode() == "normal")
    template = get_setting(f"ui_{style}_{key}", "") or get_ui_default(key, style)
    if normal:
        template = _TG_EMOJI_RE.sub(r"\1", template)
    for slot in list(DEFAULT_EMOJIS) + list(NORMAL_EMOJI):      # every emoji slot works as {slot}
        tag = "{" + slot + "}"
        if tag in template:
            template = template.replace(tag, get_emoji(slot, normal=normal))
    for k, v in kwargs.items():                      # live values; stray braces never crash
        template = template.replace("{" + k + "}", str(v))
    if own_mode == "normal":
        return NORMAL_MARK + template
    if own_mode == "premium":
        return PREMIUM_MARK + template
    return template

def ui_custom_keys() -> List[str]:
    return [k for k in (get_setting("ui_custom_keys", "") or "").split(",") if k.startswith("cx_")]

def ui_editable() -> Dict[str, Tuple[str, str]]:
    """Built-in UI texts + the new ones the admin created."""
    d = dict(UI_EDITABLE)
    for k in ui_custom_keys():
        d[k] = (get_setting(f"uicustom_label_{k}", k), "{v_name} {v_id} + emoji slots")
    return d

# ---------------------------- YouTube / video link per UI text ----------------
def ui_video_link(key: str) -> str:
    link = (get_setting(f"ui_video_{key}", "") or "").strip()
    if not link and key == "tutorial":                # old "Tutorial Video" setting still works
        old = (get_setting("how_to_video", "None") or "").strip()
        link = "" if old in ("", "None") else old
    return link if link.lower().startswith(("http://", "https://")) else ""

def ui_video_button(key: str) -> Optional[InlineKeyboardButton]:
    link = ui_video_link(key)
    if not link:
        return None
    label = (get_setting(f"ui_vidlabel_{key}", "") or "Watch Video").strip()[:30]
    icon = get_emoji_icon("video")
    if icon:                                          # premium icon set
        return InlineKeyboardButton(text=label, url=link, icon_custom_emoji_id=icon, style="danger")
    return InlineKeyboardButton(text=f"{EMOJI_FALLBACK['video']} {label}", url=link, style="danger")   # normal emoji

def ui_attach_video(kb: InlineKeyboardMarkup, key: str) -> InlineKeyboardMarkup:
    """Adds the admin's video button (if any) just above the BACK row."""
    btn = ui_video_button(key)
    if not btn:
        return kb
    rows = kb.inline_keyboard
    if rows and len(rows[-1]) == 1 and (rows[-1][0].text or "").strip().upper().startswith("BACK"):
        rows.insert(len(rows) - 1, [btn])
    else:
        rows.append([btn])
    return kb

# ==============================================================================
# 4. DATABASE INITIALISATION & MIGRATION
# ==============================================================================
def init_db() -> None:
    conn = sqlite3.connect(DB_FILE)
    c = conn.cursor()
    
    c.execute('''
        CREATE TABLE IF NOT EXISTS users (
            user_id INTEGER PRIMARY KEY, 
            phone TEXT, 
            first_name TEXT, 
            username TEXT,
            balance REAL DEFAULT 0.0, 
            account_type TEXT DEFAULT 'Regular', 
            orders_count INTEGER DEFAULT 0, 
            spent REAL DEFAULT 0.0, 
            last_spin TEXT, 
            joined_date TEXT,
            is_reseller INTEGER DEFAULT 0,
            reseller_since TEXT,
            total_saved REAL DEFAULT 0.0,
            is_banned INTEGER DEFAULT 0,
            warnings INTEGER DEFAULT 0,
            is_vip INTEGER DEFAULT 0,
            vip_since TEXT
        )
    ''')
    
    c.execute('''
        CREATE TABLE IF NOT EXISTS products (
            id INTEGER PRIMARY KEY AUTOINCREMENT, 
            category TEXT, 
            panel_name TEXT DEFAULT '',
            name TEXT, 
            price_inr REAL, 
            reseller_price REAL DEFAULT 0.0,
            stock INTEGER, 
            apk_link TEXT, 
            validity TEXT DEFAULT 'Lifetime', 
            device_limit TEXT DEFAULT '1 Device',
            is_active INTEGER DEFAULT 1
        )
    ''')
    
    c.execute('''
        CREATE TABLE IF NOT EXISTS product_keys (
            id INTEGER PRIMARY KEY AUTOINCREMENT, 
            product_id INTEGER, 
            key_text TEXT, 
            is_used INTEGER DEFAULT 0
        )
    ''')
    
    c.execute('''
        CREATE TABLE IF NOT EXISTS orders (
            id INTEGER PRIMARY KEY AUTOINCREMENT, 
            user_id INTEGER, 
            product_name TEXT, 
            price_paid REAL, 
            delivered_key TEXT, 
            purchase_date TEXT,
            source TEXT DEFAULT 'LOCAL',
            api_order_id TEXT DEFAULT ''
        )
    ''')
    
    c.execute('''
        CREATE TABLE IF NOT EXISTS tickets (
            id INTEGER PRIMARY KEY AUTOINCREMENT, 
            user_id INTEGER, 
            message TEXT, 
            status TEXT DEFAULT 'Open',
            created_at TEXT
        )
    ''')
    
    c.execute('''
        CREATE TABLE IF NOT EXISTS settings (
            key TEXT PRIMARY KEY, 
            value TEXT
        )
    ''')
    
    c.execute('''
        CREATE TABLE IF NOT EXISTS coupons (
            code TEXT PRIMARY KEY, 
            amount REAL, 
            uses_left INTEGER
        )
    ''')
    
    c.execute('''
        CREATE TABLE IF NOT EXISTS redeemed (
            user_id INTEGER, 
            code TEXT
        )
    ''')
    
    c.execute('''
        CREATE TABLE IF NOT EXISTS transactions (
            order_id TEXT PRIMARY KEY, 
            user_id INTEGER, 
            amount_inr REAL, 
            status TEXT, 
            timestamp INTEGER,
            qr_url TEXT,
            upi_id TEXT,
            expires_at INTEGER
        )
    ''')
    
    c.execute('''
        CREATE TABLE IF NOT EXISTS crypto_txns (
            txid TEXT PRIMARY KEY, 
            user_id INTEGER, 
            amount_usdt REAL, 
            timestamp INTEGER
        )
    ''')
    
    c.execute('''
        CREATE TABLE IF NOT EXISTS spin_rewards (
            id INTEGER PRIMARY KEY AUTOINCREMENT, 
            amount REAL
        )
    ''')
    
    c.execute('''
        CREATE TABLE IF NOT EXISTS bot_files (
            id INTEGER PRIMARY KEY AUTOINCREMENT,
            title TEXT,
            file_id TEXT,
            file_type TEXT DEFAULT 'document',
            created_at TEXT
        )
    ''')

    c.execute('''
        CREATE TABLE IF NOT EXISTS activity_logs (
            id INTEGER PRIMARY KEY AUTOINCREMENT,
            user_id INTEGER,
            action TEXT,
            details TEXT,
            timestamp TEXT
        )
    ''')

    # Premium emoji database: saved permanently, so after every redeploy/restart the
    # emojis (and their slot assignments) come back automatically.
    c.execute('''
        CREATE TABLE IF NOT EXISTS premium_emojis (
            id INTEGER PRIMARY KEY AUTOINCREMENT,
            emoji_id TEXT UNIQUE,
            label TEXT DEFAULT '',
            slot TEXT DEFAULT '',
            created_at TEXT
        )
    ''')

    # Digital store (bot files sold for wallet balance) + manual deposit requests (GPay / Amazon / ...)
    c.execute('''
        CREATE TABLE IF NOT EXISTS digital_products (
            id INTEGER PRIMARY KEY AUTOINCREMENT,
            title TEXT,
            description TEXT DEFAULT '',
            price_inr REAL DEFAULT 0,
            file_id TEXT,
            file_type TEXT DEFAULT 'document',
            is_active INTEGER DEFAULT 1,
            sold INTEGER DEFAULT 0,
            created_at TEXT
        )
    ''')
    c.execute('''
        CREATE TABLE IF NOT EXISTS digital_orders (
            id INTEGER PRIMARY KEY AUTOINCREMENT,
            user_id INTEGER,
            product_id INTEGER,
            product_title TEXT,
            price_paid REAL,
            purchase_date TEXT
        )
    ''')
    c.execute('''
        CREATE TABLE IF NOT EXISTS deposit_requests (
            id INTEGER PRIMARY KEY AUTOINCREMENT,
            user_id INTEGER,
            method TEXT,
            amount REAL,
            utr TEXT UNIQUE,
            status TEXT DEFAULT 'pending',
            created_at TEXT
        )
    ''')

    migrations = [
        "ALTER TABLE users ADD COLUMN referred_by INTEGER",
        "ALTER TABLE users ADD COLUMN referral_earned REAL DEFAULT 0.0",
        "ALTER TABLE users ADD COLUMN is_vip INTEGER DEFAULT 0",
        "ALTER TABLE users ADD COLUMN vip_since TEXT",
        "ALTER TABLE users ADD COLUMN lang TEXT DEFAULT 'en'",
        "ALTER TABLE products ADD COLUMN is_active INTEGER DEFAULT 1",
        "ALTER TABLE tickets ADD COLUMN created_at TEXT",
        "ALTER TABLE users ADD COLUMN is_banned INTEGER DEFAULT 0",
        "ALTER TABLE users ADD COLUMN warnings INTEGER DEFAULT 0",
        "ALTER TABLE products ADD COLUMN panel_name TEXT DEFAULT ''",
        "ALTER TABLE transactions ADD COLUMN qr_url TEXT",
        "ALTER TABLE transactions ADD COLUMN upi_id TEXT",
        "ALTER TABLE transactions ADD COLUMN expires_at INTEGER",
        # --- 2-Tier Fulfillment migrations ---
        "ALTER TABLE products ADD COLUMN product_pid TEXT DEFAULT ''",
        "ALTER TABLE products ADD COLUMN duration_string TEXT DEFAULT ''",
        "ALTER TABLE products ADD COLUMN key_type TEXT DEFAULT 'V2'",
        "ALTER TABLE orders ADD COLUMN source TEXT DEFAULT 'LOCAL'",
        "ALTER TABLE orders ADD COLUMN api_order_id TEXT DEFAULT ''"
    ]
    for mig in migrations:
        try: c.execute(mig)
        except sqlite3.OperationalError: pass
    

    default_settings = [
        ('reseller_system_status', 'ON'),
        ('bot_status', 'ON'),
        ('how_to_video', 'None'),
        ('sgvip_token', SGVIP_API_TOKEN),
        ('binance_api', ''),
        ('binance_secret', ''),
        ('binance_address', ''),
        ('vip_status', 'OFF'),
        ('reseller_setup_fee', '200.0'),
        ('reseller_min_balance', '500.0'),
        ('migration_done', '0'),
        ('support_telegram', 'https://t.me/YourSupport'),
        ('support_whatsapp', 'https://wa.me/YourNumber'),
        ('ui_style', '1'),
        # --- Reseller API (live fallback) settings ---
        ('reseller_api_url', RESELLER_API_URL),
        ('reseller_api_key', RESELLER_API_KEY),
        ('reseller_master_key', RESELLER_MASTER_KEY),
        ('reseller_user_agent', RESELLER_USER_AGENT),
        ('reseller_api_status', 'ON'),
        ('referral_percent', '5'),
        ('fam_live_key', 'fam_live_b5c36184479e4238851cf93ea7237226'),
        ('required_channel', REQUIRED_CHANNEL),
        ('required_channel_url', REQUIRED_CHANNEL_URL),
        ('force_join', 'ON'),
    ]
    for slot, emoji_id in DEFAULT_EMOJIS.items():
        default_settings.append((f"emoji_{slot}", emoji_id))
    
    for key, val in default_settings:
        c.execute("INSERT OR IGNORE INTO settings (key, value) VALUES (?, ?)", (key, val))

    conn.commit()
    conn.close()


    # Removed feature settings are intentionally ignored by the UI.
    # Their old database values may remain, but no button or handler exposes them.

def migrate_categories() -> None:
    done = get_setting("migration_done", "0")
    
    # ALWAYS force update emojis and UI texts regardless of migration status
    logger.info("Forcing emoji and UI text updates...")
    
    # Seed default Ludo Spin rewards (repeat an amount to make it more likely)
    if not db_query("SELECT 1 FROM spin_rewards LIMIT 1", fetchone=True):
        for amt in (0, 0, 0, 0, 1, 1, 1, 2, 2, 5):
            db_query("INSERT INTO spin_rewards (amount) VALUES (?)", (amt,))

    # Update all emoji settings
    for slot, emoji_id in DEFAULT_EMOJIS.items():
        if emoji_id:
            set_setting(f"emoji_{slot}", emoji_id)
        else:
            db_query("INSERT OR IGNORE INTO settings (key, value) VALUES (?, '')", (f"emoji_{slot}",))
    
    logger.info("Emojis updated. UI themes are read live from UI_THEMES (ui_style setting).")
    
    # Fix any corrupted price columns (one-time cleanup)
    conn = sqlite3.connect(DB_FILE)
    c = conn.cursor()
    products = c.execute("SELECT id, price_inr, reseller_price FROM products").fetchall()
    for prod in products:
        pid = prod[0]
        for col in ['price_inr', 'reseller_price']:
            val = prod[1] if col == 'price_inr' else prod[2]
            if val is None or val == "":
                new_val = 0.0
            else:
                try:
                    new_val = float(val)
                except (ValueError, TypeError):
                    new_val = 0.0
            c.execute(f"UPDATE products SET {col}=? WHERE id=?", (new_val, pid))
    conn.commit()
    conn.close()
    logger.info("Fixed any non-numeric price columns.")
    
    if done == "1":
        return
    
    logger.info("Running category migration...")
    
    mapping = {
        "android non root panel": "ANDROID NON ROOT PANEL",
        "android root panel": "ANDROID ROOT PANEL",
        "pc panel": "PC PANEL",
    }
    for old, new in mapping.items():
        db_query("UPDATE products SET category = ? WHERE LOWER(category) = ?", (new, old))
    
    db_query("UPDATE products SET category = 'ANDROID NON ROOT PANEL' WHERE LOWER(category) NOT IN (?, ?, ?)",
             ("android non root panel", "android root panel", "pc panel"))
    
    set_setting("migration_done", "1")
    logger.info("Category migration complete.")

# ==============================================================================
# 5. MIDDLEWARES & SECURITY
# ==============================================================================
async def hacker_loading(message: Message, text: str = "Decrypting Data") -> Message:
    msg = await message.answer(f"⚡ {text}\n[□□□] 0%")
    await asyncio.sleep(0.3)
    await msg.edit_text(f"⚡ {text}\n[■□□] 33%", parse_mode='HTML')
    await asyncio.sleep(0.3)
    await msg.edit_text(f"⚡ {text}\n[■■□] 66%", parse_mode='HTML')
    await asyncio.sleep(0.3)
    await msg.edit_text(f"⚡ {text}\n[■■■] 100%", parse_mode='HTML')
    return msg

class GlobalSecurityMiddleware(BaseMiddleware):
    def __init__(self):
        super().__init__()
        self.last_action_times = {}
        self.hits: Dict[int, List[float]] = {}
        self.muted: Dict[int, float] = {}

    async def __call__(self, handler, event, data):
        if event.from_user is None:
            return
        user_id = event.from_user.id
        now = time.time()
        if user_id != ADMIN_ID:                      # flood guard: >30 actions in 10s = muted for 60s
            if self.muted.get(user_id, 0) > now:
                return
            recent = [t for t in self.hits.get(user_id, []) if now - t < 10]
            recent.append(now)
            self.hits[user_id] = recent
            if len(recent) > 30:
                self.muted[user_id] = now + 60
                sec_log("FLOOD_MUTE", user_id)
                return
            if len(self.hits) > 5000:                # keep memory small
                self.hits = {u: h for u, h in self.hits.items() if h and now - h[-1] < 10}
                self.last_action_times = {u: t for u, t in self.last_action_times.items() if now - t < 10}
        if user_id in self.last_action_times:
            if now - self.last_action_times[user_id] < 0.3:
                return
        self.last_action_times[user_id] = now

        # After a data reset an old button may be pressed: silently re-create the user row.
        if isinstance(event, CallbackQuery) and not db_query("SELECT 1 FROM users WHERE user_id=?", (user_id,), fetchone=True):
            db_query("INSERT OR IGNORE INTO users (user_id, first_name, username, joined_date) VALUES (?, ?, ?, ?)",
                     (user_id, event.from_user.first_name or "", event.from_user.username or "",
                      datetime.now().strftime("%Y-%m-%d %H:%M:%S")))

        if user_id != ADMIN_ID:
            user_info = db_query("SELECT is_banned FROM users WHERE user_id=?", (user_id,), fetchone=True)
            if user_info and user_info[0] == 1:
                msg = "🚫 <b>ACCESS DENIED</b>\nYou have been banned from using this bot.\nContact support if you think this is a mistake."
                if isinstance(event, Message): await event.answer(msg)
                elif isinstance(event, CallbackQuery): await event.answer(msg, show_alert=True)
                return
                
            status_check = db_query("SELECT value FROM settings WHERE key='bot_status'", fetchone=True)
            status = status_check[0] if status_check else 'ON'
            if status == 'OFF':
                msg = "⚠️ <b>Store Maintenance</b>\n\nThe store is currently offline for updates. Please check back later!"
                if isinstance(event, Message): await event.answer(msg)
                elif isinstance(event, CallbackQuery): await event.answer("⚠️ Bot is currently OFF for Maintenance.", show_alert=True)
                return
                
        return await handler(event, data)

dp.message.middleware(GlobalSecurityMiddleware())
dp.callback_query.middleware(GlobalSecurityMiddleware())

# ------------------------------------------------------------------------------
# ADMIN SECURITY: password login + session, and a hard wall in front of EVERY admin action
# ------------------------------------------------------------------------------
ADMIN_CB_EXACT = {
    'admin_add_file', 'admin_add_prod', 'admin_broadcast_btn', 'admin_bulk_keys', 'admin_create_coupon',
    'admin_download_userlist', 'admin_edit_emojis', 'admin_edit_reseller_price', 'admin_edit_ui_menu', 'admin_files',
    'admin_manage_prods', 'admin_panel_back', 'admin_ref_percent', 'admin_reseller_api', 'admin_reseller_menu',
    'admin_reset_data', 'admin_reset_data_yes', 'admin_set_category_emojis', 'admin_set_panel_emojis',
    'admin_set_reseller_fee', 'admin_set_reseller_min', 'admin_set_support_links', 'admin_set_telegram',
    'admin_set_video', 'admin_set_whatsapp', 'admin_setup_binance', 'admin_setup_sgvip', 'admin_spin_rewards',
    'admin_toggle_bot', 'admin_toggle_reseller_sys', 'admin_toggle_vip_sys', 'admin_ui_preview', 'admin_ui_style',
    'admin_user_control_start', 'admin_view_stats', 'admin_view_tickets', 'reseller_edit_api_key',
    'reseller_edit_master_key', 'reseller_edit_url', 'reseller_edit_user_agent', 'reseller_make', 'reseller_remove',
    'reseller_toggle_status', 'reseller_view', 'skip_local_keys', 'uitnew',
}
ADMIN_CB_PREFIX = (
    'admin_', 'uit', 'impdb_', 'addprod_cat_', 'bulkkeys_p_', 'close_ticket_', 'confirm_ban_', 'delete_p_',
    'delkey_p_', 'edit_emoji_', 'edit_p_', 'edit_reseller_', 'keytype_', 'reply_ticket_', 'set_cat_emoji_',
    'set_panel_emoji_', 'toggle_p_', 'usrctrl_', 'hst_code', 'dr_',
)

def is_admin_callback(data: str) -> bool:
    return data in ADMIN_CB_EXACT or data.startswith(ADMIN_CB_PREFIX)

ADMIN_IDLE_SECONDS = 20 * 60        # session ends after 20 minutes without admin activity
ADMIN_FRESH_SECONDS = 5 * 60        # dangerous actions need a password entered in the last 5 minutes
ADMIN_MAX_FAILS = 5
ADMIN_LOCK_SECONDS = 15 * 60
_adm = {"last": 0.0, "fresh": 0.0, "fails": 0, "locked": 0.0}
_intrusions: Dict[int, int] = {}

# No admin password: whoever has ADMIN_ID is the admin (Telegram itself proves the ID).
def admin_pw_hash() -> str:
    return ""

def admin_session_ok(touch: bool = True) -> bool:
    return True

def admin_fresh() -> bool:
    return True

def admin_login_ok() -> None:
    pass

def admin_logout() -> None:
    pass

# ------------------------------------------------------------------------------
# CO-ADMIN ACCESS. The owner (ADMIN_ID) never needs a password. Anyone else who sends
# /admin is asked for the admin password. The right one unlocks the admin panel for
# CO_ADMIN_HOURS. Unlocks live in memory only, so a bot restart locks everyone out again.
# Owner-only areas (reseller API, security, payment gateway, DB import/reset) stay locked.
# ------------------------------------------------------------------------------
CO_ADMIN_DEFAULT_PASSWORD = "karan@2010"   # change it any time: Admin panel -> Co-Admin Password
CO_ADMIN_HOURS = 12
CO_ADMIN_MAX_TRIES = 5
_co_admins: Dict[int, float] = {}          # uid -> unlock expiry (epoch seconds)
_co_fail: Dict[int, int] = {}              # uid -> wrong attempts so far

def _is_admin(uid: Optional[int]) -> bool:
    if not uid:
        return False
    if uid == ADMIN_ID:
        return True
    return _co_admins.get(uid, 0) > time.time()

def _co_pw_hash() -> str:
    stored = get_setting("co_admin_pw_hash", "")
    if not stored:
        stored = hash_password(CO_ADMIN_DEFAULT_PASSWORD)     # only the hash is saved
        set_setting("co_admin_pw_hash", stored)
    return stored

# Owner-only areas for co-admins (reseller API keys, security, gateways, DB import/reset).
_OWNER_CB_TOKENS = ("admin_reseller_api", "reseller_toggle_status", "reseller_edit_", "admin_security",
                    "admin_sec_log", "admin_setup_", "admin_pm_", "admin_import_db", "admin_reset_data")
_OWNER_STATE_TOKENS = ("wait_for_reseller_", "wait_for_sgvip", "wait_for_binance", "pm_value",
                       "import_db_", "reset")

async def _is_owner_area(event, state) -> bool:
    if isinstance(event, CallbackQuery):
        d = event.data or ""
        return any(t in d for t in _OWNER_CB_TOKENS)
    try:
        st = str(await state.get_state()) if state else ""
    except Exception:
        st = ""
    return any(t in st for t in _OWNER_STATE_TOKENS)

class AdminGuardMiddleware(BaseMiddleware):
    """Nobody except the admin (who also logged in with the password) can reach an admin function."""
    async def __call__(self, handler, event, data):
        user = getattr(event, "from_user", None)
        if user is None:
            return await handler(event, data)
        state = data.get("state")
        if isinstance(event, CallbackQuery):
            admin_flow = is_admin_callback(event.data or "")
        else:
            try:
                st = await state.get_state() if state else None
            except Exception:
                st = None
            admin_flow = bool(st and str(st).startswith("AdminStates:") and st != AdminStates.co_login.state)
        if not admin_flow:
            return await handler(event, data)
        if not _is_admin(user.id):
            return await self._intruder(user, event, state)
        if user.id != ADMIN_ID and await _is_owner_area(event, state):
            if isinstance(event, CallbackQuery):
                try: await event.answer("🔒 Owner only", show_alert=True)
                except Exception: pass
            else:
                await event.answer("🔒 Ye option sirf owner ke liye hai.")
            if state:
                await state.clear()
            return
        return await handler(event, data)

    async def _intruder(self, user, event, state):
        n = _intrusions.get(user.id, 0) + 1
        _intrusions[user.id] = n
        what = (event.data if isinstance(event, CallbackQuery) else (event.text or ""))[:60]
        sec_log("BLOCKED_ADMIN_ACCESS", user.id, f"n={n} {what}")
        if state:
            try: await state.clear()
            except Exception: pass
        if isinstance(event, CallbackQuery):
            try: await event.answer("🚫 Not allowed", show_alert=True)
            except Exception: pass
        if n in (1, 5):
            try:
                await bot.send_message(ADMIN_ID, f"🚨 <b>Blocked admin-access attempt</b>\nUser: <code>{user.id}</code> @{html_escape(user.username or '-')}\nTried: <code>{html_escape(what)}</code> (#{n})", parse_mode="HTML")
            except Exception:
                pass
        if n >= 5:
            db_query("UPDATE users SET is_banned=1 WHERE user_id=?", (user.id,))
            sec_log("AUTO_BAN", user.id)

dp.message.middleware(AdminGuardMiddleware())
dp.callback_query.middleware(AdminGuardMiddleware())

# ------------------------------------------------------------------------------
# FORCE JOIN: the user must join REQUIRED_CHANNEL before the bot does anything
# ------------------------------------------------------------------------------
_join_cache: Dict[int, float] = {}
_JOIN_CACHE_SECONDS = 120
_join_warned = False

async def is_channel_member(user_id: int) -> bool:
    global _join_warned
    if get_setting("force_join", "ON") == "OFF":
        return True
    now = time.time()
    if now - _join_cache.get(user_id, 0) < _JOIN_CACHE_SECONDS:
        return True
    try:
        member = await bot.get_chat_member(get_setting("required_channel", REQUIRED_CHANNEL), user_id)
    except Exception as e:
        # Usually: the bot is NOT an admin of the channel. Do not lock every user out.
        logger.warning(f"Force-join check failed ({e}). Make the bot an ADMIN of {REQUIRED_CHANNEL}.")
        if not _join_warned:
            _join_warned = True
            try:
                await bot.send_message(ADMIN_ID, f"⚠️ <b>Force-join is NOT working.</b>\nAdd this bot as <b>admin</b> in {REQUIRED_CHANNEL}.\n<code>{html_escape(str(e))}</code>", parse_mode="HTML")
            except Exception:
                pass
        return False
    status = getattr(member, "status", "")
    status = getattr(status, "value", status)
    ok = status in ("creator", "administrator", "member") or (status == "restricted" and bool(getattr(member, "is_member", False)))
    if ok:
        _join_cache[user_id] = now
    return ok

class ForceJoinMiddleware(BaseMiddleware):
    async def __call__(self, handler, event, data):
        user = getattr(event, "from_user", None)
        if user is None or user.is_bot or user.id == ADMIN_ID:
            return await handler(event, data)
        if isinstance(event, Message) and event.chat.type != "private":
            return await handler(event, data)
        if isinstance(event, CallbackQuery) and event.data == "check_join":
            return await handler(event, data)
        if await is_channel_member(user.id):
            return await handler(event, data)
        # ---- not joined: show the join screen and stop
        text = get_ui_text("join_channel")
        kb = ui_attach_video(join_kb(), "join_channel")
        if isinstance(event, Message):
            if event.text and event.text.startswith("/start"):      # remember ref_ / payment args
                parts = event.text.split(maxsplit=1)
                set_setting(f"pending_start_{user.id}", parts[1].strip() if len(parts) > 1 else "")
            await event.answer(text, reply_markup=kb, parse_mode="HTML")
        elif isinstance(event, CallbackQuery):
            try: await event.answer("Please join our channel first!", show_alert=True)
            except Exception: pass
            try: await event.message.answer(text, reply_markup=kb, parse_mode="HTML")
            except Exception: pass
        return

dp.message.middleware(ForceJoinMiddleware())
dp.callback_query.middleware(ForceJoinMiddleware())

# ==============================================================================
# 6. FSM STATES
# ==============================================================================
class UserStates(StatesGroup):
    wait_for_ticket = State()
    wait_for_redeem = State()
    wait_for_crypto_txid = State()
    custom_amount_input = State()
    wait_for_android_id = State()   # V1 / Device-Lock products
    pm_amount = State()
    pm_utr = State()

class HostStates(StatesGroup):
    wait_file = State()
    wait_pip = State()

class SecurityStates(StatesGroup):
    login = State()
    set_pw1 = State()
    set_pw2 = State()

class AdminStates(StatesGroup):
    host_input = State()
    import_db_file = State()
    import_db_confirm = State()
    add_prod_category = State()
    add_prod_panel_name = State()
    add_prod_name = State()
    add_prod_validity = State()
    add_prod_device_limit = State()
    add_prod_price = State()
    add_prod_reseller_price = State()
    add_prod_apk = State()
    add_prod_pid = State()
    add_prod_duration = State()
    add_prod_key_type = State()
    add_prod_keys = State()
    
    edit_prod_field = State()
    wait_for_new_value = State()
    wait_for_add_keys = State()
    wait_for_delete_key = State()
    
    broadcast_msg = State()
    add_coupon_code = State()
    add_coupon_amount = State()
    add_coupon_uses = State()
    
    # Payment Gateway (SGVIP) state
    wait_for_sgvip_token = State()
    
    # Binance states
    wait_for_binance_api = State()
    wait_for_binance_secret = State()
    wait_for_binance_address = State()
    
    ticket_reply_msg = State()
    reseller_manage_id = State()
    manage_target_user = State()
    wait_for_add_money = State()
    wait_for_minus_money = State()
    wait_for_warning = State()
    
    wait_for_howto_video = State()
    
    edit_ui_text = State()
    edit_ui_video = State()
    new_ui_label = State()
    new_ui_text = State()
    edit_ui_label = State()
    edit_reseller_price = State()
    wait_for_reseller_setup_fee = State()
    wait_for_reseller_min_balance = State()
    confirm_ban = State()
    
    wait_for_support_telegram = State()
    wait_for_support_whatsapp = State()
    wait_for_category_emoji = State()
    wait_for_panel_emoji_id = State()
    wait_for_emoji_slot = State()

    # Spin / Referral / Files
    wait_for_spin_rewards = State()
    wait_for_ref_percent = State()
    wait_for_file_upload = State()

    # Quick add balance to any user (Admin -> Add Balance to User)
    quick_addbal = State()
    ds_title = State()
    ds_price = State()
    ds_desc = State()
    ds_file = State()
    pm_value = State()
    fj_value = State()
    demo_value = State()
    demo_video = State()
    pe_import = State()
    co_login = State()
    co_setpw = State()
    rbc_msg = State()
    pdemo_value = State()
    pdemo_video = State()
    hprem_value = State()

    # Premium emoji database (Admin -> Premium Emoji DB)
    pe_add = State()
    pe_slot = State()

    # Reseller API settings
    wait_for_reseller_url = State()
    wait_for_reseller_api_key = State()
    wait_for_reseller_master_key = State()
    wait_for_reseller_user_agent = State()

# ==============================================================================
# 7. KEYBOARDS
# ==============================================================================
def get_category_emoji(category: str) -> str:
    slot_map = {
        "ANDROID NON ROOT PANEL": "category_android_non_root",
        "ANDROID ROOT PANEL": "category_android_root",
        "PC PANEL": "category_pc",
    }
    slot = slot_map.get(category)
    if slot:
        return get_emoji_icon(slot, DEFAULT_EMOJIS.get(slot, ""))
    return ""

def get_panel_emoji(panel_name: str) -> str:
    stored = get_setting(f"panel_emoji_{panel_name}", "")
    if stored and stored.isdigit():
        return stored
    return get_emoji_icon("product_store")

def contact_kb() -> ReplyKeyboardMarkup:
    return ReplyKeyboardMarkup(
        keyboard=[[KeyboardButton(text="📱 Verify Contact", request_contact=True)]], 
        resize_keyboard=True, 
        one_time_keyboard=True
    )

def _btn(text: str, cb: str, slot: Optional[str] = None, style: str = "primary") -> InlineKeyboardButton:
    icon = get_emoji_icon(slot) if slot else ""
    if slot and not icon and slot in EMOJI_FALLBACK:
        text = f"{EMOJI_FALLBACK[slot]} {text}"
    if icon:
        return InlineKeyboardButton(text=text, callback_data=cb, icon_custom_emoji_id=icon, style=style)
    return InlineKeyboardButton(text=text, callback_data=cb, style=style)

def main_menu_kb(user_id: Optional[int] = None) -> InlineKeyboardMarkup:
    sys_status = get_setting("reseller_system_status", "ON")
    vip_system = get_setting("vip_status", "OFF")
    is_reseller = False
    if user_id:
        user_check = db_query("SELECT is_reseller FROM users WHERE user_id=?", (user_id,), fetchone=True)
        if user_check:
            is_reseller = bool(user_check[0])

    rows = [
        [_btn(tr(user_id, "store"), "menu_shop", "product_store", "danger")],
        [_btn(tr(user_id, "profile"), "menu_profile", "profile"), _btn(tr(user_id, "add"), "menu_add_balance", "add_balance")],
        [_btn(tr(user_id, "history"), "menu_orders", "history", "success"), _btn(tr(user_id, "referral"), "menu_referral", "referral", "success")],
        [_btn(tr(user_id, "tutorial"), "menu_how_to", "tutorial", "success"), _btn(tr(user_id, "support"), "menu_support", "support", "danger")],
        [_btn(tr(user_id, "spin"), "menu_spin", "spin", "primary"), _btn(tr(user_id, "files"), "menu_files", "files", "primary")],
        [_btn(tr(user_id, "hosting"), "hst_menu", "hosting", "danger")],
        [_btn(tr(user_id, "demo"), "demo_view", "tutorial", "primary"), _btn(tr(user_id, "lang"), "menu_lang", "support", "primary")],
        [_btn(tr(user_id, "source"), "ds_menu", "product_store", "success")],
    ]
    extras_row = []
    if sys_status == "ON" or is_reseller:
        extras_row.append(_btn("Reseller Panel", "menu_reseller_dash", "reseller"))
    if vip_system == "ON":
        extras_row.append(_btn("VIP Club", "menu_vip_dash", "vip", "danger"))
    if extras_row:
        rows.append(extras_row)
    for ck in ui_custom_keys():     # buttons of the UI texts the admin created
        if get_setting(f"uicustom_on_{ck}", "1") == "1":
            rows.append([_btn(get_setting(f"uicustom_label_{ck}", "Page")[:30], f"cxopen_{ck}", "store_title")])
    if get_ui_style("start_menu") == "2":      # Clean Shop look: all buttons green
        rows = [[b.model_copy(update={"style": "success"}) for b in r] for r in rows]
    return InlineKeyboardMarkup(inline_keyboard=rows)

def join_kb() -> InlineKeyboardMarkup:
    return InlineKeyboardMarkup(inline_keyboard=[
        [InlineKeyboardButton(text="Join Channel", url=get_setting("required_channel_url", REQUIRED_CHANNEL_URL),
                              icon_custom_emoji_id=get_emoji_icon("telegram"), style="primary")],
        [InlineKeyboardButton(text="I Joined", callback_data="check_join",
                              icon_custom_emoji_id=get_emoji_icon("check_icon"), style="success")],
    ])

def back_kb(callback: str = "back_main") -> InlineKeyboardMarkup:
    return InlineKeyboardMarkup(
        inline_keyboard=[[
            InlineKeyboardButton(
                text="BACK", callback_data=callback,
                icon_custom_emoji_id=get_emoji_icon("back"),
                style="danger"
            )
        ]]
    )

def admin_header() -> str:
    st = UI_STYLE_NAMES.get(get_ui_style(), "")
    line = "━" * 20
    return (f"🔐 <b>{line}</b>\n"
            f"{get_emoji('admin_title')} <b><u>SG ADMIN CONTROL CENTER</u></b> {get_emoji('admin_title')}\n"
            f"<b>{line}</b>\n"
            "🛡 <i>Authorized access · secured session</i>\n"
            f"🖌 UI Style: <b>{st}</b>")

def admin_kb() -> InlineKeyboardMarkup:
    """Admin panel: thick, full-width, grouped into sections. Section titles are
    non-clickable (callback admin_noop) and every button gets a premium icon."""
    status = db_query("SELECT value FROM settings WHERE key='bot_status'", fetchone=True)
    status_val = status[0] if status else 'ON'
    vip_status = db_query("SELECT value FROM settings WHERE key='vip_status'", fetchone=True)
    vip_val = vip_status[0] if vip_status else 'OFF'
    sections = [
        ("📊 STATS & USERS", [
            ("📊 Bot Statistics", "admin_view_stats", "primary"),
            ("👥 User Control Panel", "admin_user_control_start", "primary"),
            ("💰 Add Balance to User", "admin_addbal_start", "success"),
            ("📢 Broadcast", "admin_broadcast_btn", "primary"),
            ("🎫 View Tickets", "admin_view_tickets", "primary"),
            ("🎟 Create Coupon", "admin_create_coupon", "primary"),
        ]),
        ("🛒 STORE & PRODUCTS", [
            ("➕ Add Product", "admin_add_prod", "primary"),
            ("📦 Manage Products", "admin_manage_prods", "primary"),
            ("🔑 Bulk Add Keys", "admin_bulk_keys", "success"),
            ("🛍 SOURCE CODE (Sell Bot Files)", "admin_ds_menu", "success"),
            ("🔌 Reseller API Settings", "admin_reseller_api", "primary"),
            ("👑 Reseller Mgmt", "admin_reseller_menu", "primary"),
            ("📝 Edit Reseller Price", "admin_edit_reseller_price", "primary"),
            ("💰 Reseller Fee", "admin_set_reseller_fee", "primary"),
            ("💳 Min Balance", "admin_set_reseller_min", "primary"),
        ]),
        ("💳 PAYMENTS", [
            ("💳 Payment Methods (GPay / Amazon / FamPay / FAM LIVE)", "admin_pm_menu", "success"),
            ("🧾 Payment Requests (Approve)", "admin_deposits", "success"),
            ("💳 Payment Gateway Setup", "admin_setup_sgvip", "primary"),
        ]),
        ("🎨 DESIGN & PREMIUM EMOJI", [
            ("🖌 UI Style (1-6)", "admin_ui_style", "success"),
            ("✏️ Edit UI Texts", "admin_edit_ui_menu", "primary"),
            ("🌟 Premium Emoji DB", "admin_pe_menu", "success"),
            ("🎨 Edit All Emojis", "admin_edit_emojis", "primary"),
            ("🎨 Set Category Emojis", "admin_set_category_emojis", "primary"),
            ("🖼 Set Panel Emojis", "admin_set_panel_emojis", "primary"),
            ("📞 Set Support Links", "admin_set_support_links", "primary"),
            ("📹 Tutorial Video", "admin_set_video", "primary"),
            ("🎬 Panel Demo (Video / Link)", "admin_demo_menu", "success"),
            ("🎬 Panel Demos (per panel)", "admin_pdemo_menu", "success"),
        ]),
        ("🎁 REWARDS & FILES", [
            ("🎲 Spin Rewards", "admin_spin_rewards", "primary"),
            ("🎁 Referral %", "admin_ref_percent", "primary"),
            ("📥 Download Files", "admin_files", "primary"),
        ]),
        ("🔐 SECURITY & SYSTEM", [
            ("📢 Force-Join Channel", "admin_fj_menu", "success"),
            ("🖥 Hosting Admin (files & code)", "admin_hosting", "success"),
            ("📥 Import Old Database", "admin_import_db", "success"),
            ("🔑 Co-Admin Password", "admin_co_pw", "danger"),
            ("🔐 Security", "admin_security", "primary"),
            ("🗑 Reset All User Data", "admin_reset_data", "danger"),
        ]),
    ]
    rows = []
    for title, items in sections:
        rows.append([InlineKeyboardButton(text=f"━━━ {title} ━━━", callback_data="admin_noop", style="primary")])
        for t, c, s in items:
            rows.append([InlineKeyboardButton(text=t, callback_data=c, style=s)])
    rows.append([InlineKeyboardButton(
        text=f"Bot Status: {status_val} {'🟢' if status_val == 'ON' else '🔴'}",
        callback_data="admin_toggle_bot", style="success" if status_val == 'ON' else "danger")])
    rows.append([InlineKeyboardButton(
        text=f"VIP System: {vip_val} {'🟢' if vip_val == 'ON' else '🔴'}",
        callback_data="admin_toggle_vip_sys", style="success" if vip_val == 'ON' else "danger")])
    return InlineKeyboardMarkup(inline_keyboard=rows)

def admin_back_kb() -> InlineKeyboardMarkup:
    return InlineKeyboardMarkup(inline_keyboard=[[
        InlineKeyboardButton(
            text="Back to Admin", callback_data="admin_panel_back",
            icon_custom_emoji_id=get_emoji_icon("back"),
            style="danger"
        )
    ]])

# ==============================================================================
# 8. NOTIFICATIONS
# ==============================================================================
async def send_advanced_notification(user_id: int, notif_type: str, amount: float, product: str = None, key: str = None, gateway: str = "SGVIP") -> None:
    user_info = db_query("SELECT first_name, phone, username, is_reseller, is_vip FROM users WHERE user_id=?", (user_id,), fetchone=True)
    
    name = user_info[0] if user_info else "Unknown"
    phone = user_info[1] if user_info and user_info[1] else "Not Provided"
    username = f"@{user_info[2]}" if user_info and user_info[2] else "None"
    
    tags = []
    if user_info and user_info[3]: tags.append("👑 Reseller")
    if user_info and user_info[4]: tags.append("🌟 VIP")
    tag_str = " | ".join(tags) if tags else "👤 Regular"
        
    time_now = datetime.now().strftime("%d-%m-%Y %I:%M %p")
    
    if notif_type == "ORDER":
        title = "🛒 <b>NEW ORDER PROCESSED!</b> 🛒"
        details = (f"📦 <b>Product:</b> {product}\n🔑 <b>Key:</b> <code>{key}</code>\n💰 <b>Amount Paid:</b> ₹{amount:.2f}\n📅 <b>Time:</b> {time_now}")
    else:
        title = "💰 <b>NEW WALLET DEPOSIT!</b> 💰"
        details = (f"💵 <b>Amount Added:</b> ₹{amount:.2f}\n🧾 <b>Gateway:</b> {gateway}\n🆔 <b>Reference:</b> <code>{product}</code>\n📅 <b>Time:</b> {time_now}")

    msg = f"{title}\n━━━━━━━━━━━━━━━━━━\n👤 <b>Name:</b> {name}\n🆔 <b>User ID:</b> <code>{user_id}</code>\n📱 <b>Phone:</b> {phone}\n🔗 <b>Username:</b> {username}\n🏷 <b>Status:</b> {tag_str}\n━━━━━━━━━━━━━━━━━━\n{details}"
    try: 
        await bot.send_message(ADMIN_ID, msg, parse_mode='HTML')
    except Exception as e: 
        logger.error(f"Failed to send admin notification: {e}")

async def credit_referral_bonus(user_id: int, amount: float) -> None:
    """Give the referrer a % of every deposit made by the referred user."""
    try:
        pct = safe_float(get_setting("referral_percent", "5"), 5.0)
        row = db_query("SELECT referred_by FROM users WHERE user_id=?", (user_id,), fetchone=True)
        if not row or not row[0] or pct <= 0:
            return
        bonus = round(amount * pct / 100.0, 2)
        if bonus <= 0:
            return
        referrer = row[0]
        db_query("UPDATE users SET balance = balance + ?, referral_earned = referral_earned + ? WHERE user_id=?",
                 (bonus, bonus, referrer))
        log_activity(referrer, "REFERRAL_BONUS", f"From user {user_id}: {bonus}")
        await bot.send_message(referrer, f"🎁 <b>REFERRAL BONUS!</b>\n\n💰 You earned <b>{fmt_curr(bonus)}</b> from your friend's deposit.", parse_mode="HTML")
    except Exception as e:
        logger.error(f"Referral bonus error: {e}")

# ==============================================================================
# 8B. 2-TIER STOCK FULFILLMENT ENGINE
#     Priority 1: Local Vault (product_keys)  ->  Priority 2: Reseller API
# ==============================================================================
def get_reseller_config() -> Dict[str, str]:
    """Read reseller API config from DB settings, falling back to constants."""
    return {
        "url": get_setting("reseller_api_url", RESELLER_API_URL),
        "api_key": get_setting("reseller_api_key", RESELLER_API_KEY),
        "master_key": get_setting("reseller_master_key", RESELLER_MASTER_KEY),
        "user_agent": get_setting("reseller_user_agent", RESELLER_USER_AGENT),
        "status": get_setting("reseller_api_status", "ON"),
    }


def is_reseller_api_enabled() -> bool:
    return get_reseller_config().get("status", "ON").upper() == "ON"


def product_api_ready(product_pid: Optional[str], duration_string: Optional[str]) -> bool:
    """
    True only when THIS product can be bought live:
    global API switch is ON and the product has both a PID and an exact duration.
    """
    if not is_reseller_api_enabled():
        return False
    pid = (product_pid or "").strip()
    dur = (duration_string or "").strip()
    return bool(pid) and bool(dur) and pid.lower() not in ("none", "null", "0")


def refund_balance(user_id: int, amount: float, savings: float = 0.0) -> None:
    """Reverse a charge: restore balance and undo spent/orders/saved counters."""
    if amount <= 0:
        return
    db_query(
        "UPDATE users SET balance = balance + ?, "
        "spent = MAX(spent - ?, 0), "
        "total_saved = MAX(total_saved - ?, 0), "
        "orders_count = MAX(orders_count - 1, 0) WHERE user_id=?",
        (amount, amount, savings, user_id)
    )
    log_activity(user_id, "BALANCE_REFUNDED", f"Refunded {amount}")


def take_local_keys(prod_id: int, quantity: int) -> List[Tuple[int, str]]:
    """
    Atomically reserve up to `quantity` unused keys from the local vault.
    Returns a list of (key_id, key_text). Marks them used and decrements stock.
    If fewer than `quantity` keys exist, it reserves whatever is available
    (caller decides whether to top-up via API or roll back).
    """
    if quantity <= 0:
        return []
    conn = sqlite3.connect(DB_FILE)
    try:
        c = conn.cursor()
        rows = c.execute(
            "SELECT id, key_text FROM product_keys "
            "WHERE product_id=? AND is_used=0 ORDER BY id LIMIT ?",
            (prod_id, quantity)
        ).fetchall()
        if not rows:
            conn.rollback()
            return []
        ids = [(r[0],) for r in rows]
        c.executemany("UPDATE product_keys SET is_used=1 WHERE id=?", ids)
        c.execute(
            "UPDATE products SET stock = MAX(stock - ?, 0) WHERE id=?",
            (len(rows), prod_id)
        )
        conn.commit()
        return [(r[0], r[1]) for r in rows]
    except Exception as e:
        logger.error(f"take_local_keys failed: {e}")
        conn.rollback()
        return []
    finally:
        conn.close()


def restore_local_keys(key_ids: List[int]) -> None:
    """Roll back a local reservation (used when the API top-up fails)."""
    if not key_ids:
        return
    conn = sqlite3.connect(DB_FILE)
    try:
        c = conn.cursor()
        c.executemany("UPDATE product_keys SET is_used=0 WHERE id=?", [(i,) for i in key_ids])
        conn.commit()
    except Exception as e:
        logger.error(f"restore_local_keys failed: {e}")
        conn.rollback()
    finally:
        conn.close()


def _extract_api_keys(data: Any) -> List[str]:
    """Robustly pull a list of key strings out of an API JSON response."""
    if isinstance(data, list):
        data = {"keys": data}
    if not isinstance(data, dict):
        return []
    candidates = [data.get("keys")]
    for wrapper in ("data", "result", "response"):
        node = data.get(wrapper)
        if isinstance(node, dict):
            candidates.append(node.get("keys"))
        elif isinstance(node, list):
            candidates.append(node)
    for cand in candidates:
        if isinstance(cand, list) and cand:
            out = []
            for item in cand:
                if isinstance(item, str) and item.strip():
                    out.append(item.strip())
                elif isinstance(item, dict):
                    for k in ("key", "license", "license_key", "key_text", "value"):
                        if item.get(k):
                            out.append(str(item[k]).strip())
                            break
            if out:
                return out
    return []


async def call_reseller_api(product_pid: str, duration: str, quantity: int,
                            android_id: Optional[str] = None) -> Dict[str, Any]:
    """
    POST to the reseller API to buy live key(s).
    Returns {"success": bool, "keys": [...], "error": str|None, "raw": str}.
    """
    cfg = get_reseller_config()
    if cfg["status"].upper() != "ON":
        return {"success": False, "keys": [], "error": "Reseller API is disabled by admin.", "raw": ""}
    if not cfg["api_key"]:
        return {"success": False, "keys": [],
                "error": "Reseller API key set nahi hai ya decrypt nahi ho rahi. Admin panel -> Reseller API Settings mein dobara bharo.", "raw": ""}
    if not product_pid or not duration:
        return {"success": False, "keys": [],
                "error": "Product PID / duration not configured for this package.", "raw": ""}

    payload = {
        "api_key": cfg["api_key"],
        "action": "buy",
        "product_id": str(product_pid).strip(),
        "duration": str(duration).strip(),
        "quantity": str(max(1, int(quantity))),
    }
    # android_id is ONLY required for Device-Lock / V1 products.
    if android_id:
        payload["android_id"] = str(android_id).strip()

    headers = {
        "Content-Type": "application/x-www-form-urlencoded",
        "x-master-key": cfg["master_key"],
        "User-Agent": cfg["user_agent"],
    }

    raw = ""
    try:
        timeout = aiohttp.ClientTimeout(total=RESELLER_API_TIMEOUT)
        async with aiohttp.ClientSession(timeout=timeout) as session:
            async with session.post(cfg["url"], data=payload, headers=headers) as resp:
                raw = await resp.text()
                logger.info(f"Reseller API HTTP {resp.status}: {raw[:500]}")
                if resp.status != 200:
                    return {"success": False, "keys": [],
                            "error": f"Reseller API HTTP {resp.status}. Please contact admin.", "raw": raw}
        try:
            data = json.loads(raw)
        except (json.JSONDecodeError, TypeError):
            return {"success": False, "keys": [],
                    "error": "Invalid response from reseller API.", "raw": raw}

        keys = _extract_api_keys(data)
        if keys:
            api_order_id = ""
            if isinstance(data, dict):
                api_order_id = str(data.get("order_id") or data.get("orderId") or "")
            return {"success": True, "keys": keys, "error": None, "raw": raw,
                    "api_order_id": api_order_id}

        # No keys -> surface the API's own message if present.
        msg = ""
        if isinstance(data, dict):
            msg = str(data.get("message") or data.get("error") or data.get("msg") or "").strip()
        return {"success": False, "keys": [],
                "error": msg or "Out of Stock / Please Contact Admin", "raw": raw}

    except asyncio.TimeoutError:
        logger.error("Reseller API timeout")
        return {"success": False, "keys": [],
                "error": "Reseller API timed out. Please try again / contact admin.", "raw": raw}
    except Exception as e:
        logger.error(f"Reseller API exception: {e}")
        return {"success": False, "keys": [],
                "error": "Reseller API connection failed. Please contact admin.", "raw": raw}


async def fulfill_keys(prod_id: int, quantity: int = 1,
                       android_id: Optional[str] = None) -> Dict[str, Any]:
    """
    Orchestrates the 2-tier delivery:
      1) Reserve from the local vault.
      2) If short, top-up the remainder from the reseller API.
      3) If the API fails, roll back local reservations (no stock leak).
    Returns {"success", "keys", "source", "error"}.
    """
    quantity = max(1, int(quantity))
    prod = db_query(
        "SELECT product_pid, duration_string, key_type FROM products WHERE id=?",
        (prod_id,), fetchone=True
    )
    if not prod:
        return {"success": False, "keys": [], "source": None, "error": "Product not found."}
    product_pid, duration_string, key_type = prod[0] or "", prod[1] or "", (prod[2] or "V2")

    # --- Priority 1: Local Vault ---
    local_rows = take_local_keys(prod_id, quantity)
    if len(local_rows) >= quantity:
        return {"success": True, "keys": [r[1] for r in local_rows[:quantity]],
                "source": "LOCAL", "error": None}

    need = quantity - len(local_rows)

    # --- Priority 2: Reseller API fallback ---
    api_android = android_id if str(key_type).upper() == "V1" else None
    api_res = await call_reseller_api(product_pid, duration_string, need, api_android)

    if api_res.get("success") and len(api_res.get("keys", [])) >= need:
        api_keys = api_res["keys"][:need]
        source = "LOCAL+API" if local_rows else "API"
        return {"success": True,
                "keys": [r[1] for r in local_rows] + api_keys,
                "source": source, "error": None,
                "api_order_id": api_res.get("api_order_id", "")}

    set_setting("reseller_last_error", f"{datetime.now():%m-%d %H:%M} {api_res.get('error') or 'unknown'}")
    # API failed -> release any local keys we reserved so stock is not lost.
    if local_rows:
        restore_local_keys([r[0] for r in local_rows])
        db_query("UPDATE products SET stock = stock + ? WHERE id=?", (len(local_rows), prod_id))
    return {"success": False, "keys": [], "source": None,
            "error": api_res.get("error") or "Out of Stock / Please Contact Admin"}


# ==============================================================================
# 9. SGVIP PAYMENT FUNCTIONS
# ==============================================================================

async def create_sgvip_order(user_id: int, amount: float, order_id: str, mobile: str = "9999999999") -> Dict[str, Any]:
    """Create an order on the SGVIP payment gateway."""
    token = get_setting("sgvip_token", SGVIP_API_TOKEN)
    if not token:
        return {"status": False, "message": "SGVIP API token not configured"}

    payload = {
        "customer_mobile": mobile or "9999999999",
        "user_token": token,
        "amount": str(amount),
        "order_id": order_id,
        "redirect_url": SGVIP_REDIRECT_URL,
        "remark1": f"Deposit for {user_id}",
        "remark2": "Wallet Topup",
    }

    async with aiohttp.ClientSession() as session:
        try:
            async with session.post(SGVIP_CREATE_ORDER_URL, data=payload) as resp:
                try:
                    result = await resp.json(content_type=None)
                except Exception as e:
                    logger.error(f"Error parsing SGVIP create-order response: {e}")
                    return {"status": False, "message": "Failed to parse response"}
                if resp.status != 200 and isinstance(result, dict):
                    result.setdefault("status", False)
                return result if isinstance(result, dict) else {"status": False, "message": "Invalid response"}
        except Exception as e:
            logger.error(f"SGVIP Create Order API Error: {e}")
            return {"status": False, "message": str(e)}

async def check_sgvip_order_status(order_id: str, gateway_order_id: str = None) -> Dict[str, Any]:
    """Check order status on the SGVIP payment gateway."""
    token = get_setting("sgvip_token", SGVIP_API_TOKEN)
    if not token:
        return {"status": "ERROR", "message": "SGVIP API token not configured"}

    # Try our merchant order_id first, then the gateway's own orderId if different.
    ids_to_try = [order_id]
    if gateway_order_id and gateway_order_id != order_id:
        ids_to_try.append(gateway_order_id)

    last_result: Dict[str, Any] = {"status": "ERROR", "message": "Unknown error"}
    async with aiohttp.ClientSession() as session:
        for oid in ids_to_try:
            payload = {"user_token": token, "order_id": oid}
            try:
                async with session.post(SGVIP_CHECK_STATUS_URL, data=payload) as resp:
                    try:
                        result = await resp.json(content_type=None)
                    except Exception as e:
                        logger.error(f"Error parsing SGVIP status response: {e}")
                        last_result = {"status": "ERROR", "message": "Failed to parse response"}
                        continue
                    if not isinstance(result, dict):
                        last_result = {"status": "ERROR", "message": "Invalid response"}
                        continue
                    last_result = result
                    status_val = str(result.get("status", "")).upper()
                    if status_val in ("COMPLETED", "SUCCESS", "PENDING", "PROCESSING", "FAILED", "EXPIRED"):
                        return result
            except Exception as e:
                logger.error(f"SGVIP Check Status API Error: {e}")
                last_result = {"status": "ERROR", "message": str(e)}
    return last_result

async def run_payment_verification(user_id: int, order_id: str, reply_target: Any) -> None:
    """Run payment verification with the SGVIP gateway."""
    txn = db_query("SELECT amount_inr, status, timestamp, qr_url, upi_id, expires_at FROM transactions WHERE order_id=?", (order_id,), fetchone=True)
    if not txn:
        err = "❌ Invalid or Fake Order ID detected in system!"
        if isinstance(reply_target, CallbackQuery): await reply_target.answer(err, show_alert=True)
        else: await reply_target.answer(err)
        return

    # Check if order expired
    if txn[5] and time.time() > txn[5] and txn[1] == 'pending':
        db_query("UPDATE transactions SET status='expired' WHERE order_id=?", (order_id,))
        err_msg = "⏳ <b>Order Expired!</b>\nThe payment window has expired. Please generate a new payment request."
        if isinstance(reply_target, CallbackQuery): await reply_target.message.edit_text(err_msg, reply_markup=back_kb(), parse_mode='HTML')
        else: await reply_target.answer(err_msg, reply_markup=back_kb())
        return

    if txn[1] == 'paid':
        msg = "✅ This payment has already been securely credited to your wallet."
        if isinstance(reply_target, CallbackQuery): await reply_target.answer(msg, show_alert=True)
        else: await reply_target.answer(msg)
        return
    elif txn[1] == 'expired':
        msg = "❌ This order has expired. Please create a new deposit request."
        if isinstance(reply_target, CallbackQuery): await reply_target.answer(msg, show_alert=True)
        else: await reply_target.answer(msg)
        return

    # Verify with SGVIP API (upi_id column stores the gateway order id)
    result = await check_sgvip_order_status(order_id, txn[4])
    status_val = str(result.get("status", "")).upper()

    if status_val in ("COMPLETED", "SUCCESS"):
        # Payment successful
        txn_data = result.get("result", {}) or {}
        utr = txn_data.get("utr", "N/A")
        amount_received = safe_float(txn_data.get("amount"), txn[0])
        if amount_received <= 0:
            amount_received = txn[0]
        payment_time = txn_data.get("date", "")
        gateway_ref = txn_data.get("orderId", order_id)

        db_query("UPDATE transactions SET status='paid' WHERE order_id=?", (order_id,))
        db_query("UPDATE users SET balance = balance + ? WHERE user_id=?", (amount_received, user_id))
        await credit_referral_bonus(user_id, amount_received)

        success_msg = f"🎉 <b>PAYMENT VERIFIED!</b>\n\n✅ {fmt_curr(amount_received)} has been added to your wallet.\n🧾 UTR: <code>{utr}</code>\n🆔 Order: <code>{gateway_ref}</code>\n📅 Time: {payment_time}"
        if isinstance(reply_target, CallbackQuery): await reply_target.message.edit_text(success_msg, reply_markup=back_kb(), parse_mode='HTML')
        else: await reply_target.answer(success_msg, reply_markup=back_kb())

        await send_advanced_notification(user_id, "DEPOSIT", amount_received, product=str(gateway_ref), gateway="SGVIP")
        log_activity(user_id, "DEPOSIT_SUCCESS", f"Amount: {amount_received}, Gateway: SGVIP, Order: {order_id}, UTR: {utr}")

    elif status_val in ("PENDING", "PROCESSING"):
        pending_msg = f"⏳ <b>Payment Status: PENDING</b>\n\n{result.get('message', 'Payment not received yet')}\n\n<i>Please wait a moment and verify again.</i>"
        if isinstance(reply_target, CallbackQuery): await reply_target.answer(pending_msg, show_alert=True)
        else: await reply_target.answer(pending_msg)
    elif status_val in ("FAILED", "EXPIRED"):
        fail_msg = f"❌ <b>Payment Failed/Expired</b>\n\n{result.get('message', 'This order was not completed.')}\n\n<i>Please create a new deposit request.</i>"
        if isinstance(reply_target, CallbackQuery): await reply_target.answer(fail_msg, show_alert=True)
        else: await reply_target.answer(fail_msg)
    else:
        err = f"⚠️ Gateway Error: {result.get('message', 'Unknown Error')}"
        if isinstance(reply_target, CallbackQuery): await reply_target.answer(err, show_alert=True)
        else: await reply_target.answer(err)

async def auto_verify_task() -> None:
    """Auto-verify pending SGVIP transactions every 30 seconds."""
    while True:
        await asyncio.sleep(30)  # Check every 30 seconds

        token = get_setting("sgvip_token", "")
        if not token:
            continue

        pending_txns = db_query("SELECT order_id, user_id, amount_inr, timestamp, expires_at, upi_id FROM transactions WHERE status='pending'", fetchall=True)
        if not pending_txns: continue

        for txn in pending_txns:
            order_id, user_id, amount, ts, expires_at, gateway_order_id = txn

            # Check if expired
            if expires_at and time.time() > expires_at:
                db_query("UPDATE transactions SET status='expired' WHERE order_id=?", (order_id,))
                try:
                    await bot.send_message(user_id, f"⏳ <b>Order Expired!</b>\nYour payment window for order <code>{order_id}</code> has timed out. Please generate a new payment request.", parse_mode='HTML')
                except: pass
                continue

            # Verify with SGVIP
            result = await check_sgvip_order_status(order_id, gateway_order_id)
            status_val = str(result.get("status", "")).upper()

            if status_val in ("COMPLETED", "SUCCESS"):
                txn_data = result.get("result", {}) or {}
                amount_received = safe_float(txn_data.get("amount"), amount)
                if amount_received <= 0:
                    amount_received = amount
                utr = txn_data.get("utr", "N/A")
                gateway_ref = txn_data.get("orderId", order_id)

                db_query("UPDATE transactions SET status='paid' WHERE order_id=?", (order_id,))
                db_query("UPDATE users SET balance = balance + ? WHERE user_id=?", (amount_received, user_id))
                await credit_referral_bonus(user_id, amount_received)

                try:
                    await bot.send_message(
                        user_id,
                        f"✨ <b>AUTO-VERIFIED!</b>\n\n✅ Your payment of {fmt_curr(amount_received)} was detected successfully!\n🧾 UTR: <code>{utr}</code>\n🆔 Order: <code>{gateway_ref}</code>",
                        parse_mode='HTML'
                    )
                except: pass

                await send_advanced_notification(user_id, "DEPOSIT", amount_received, product=str(gateway_ref), gateway="SGVIP Auto")
                log_activity(user_id, "DEPOSIT_AUTO_SUCCESS", f"Amount: {amount_received}, Gateway: SGVIP Auto, Order: {order_id}, UTR: {utr}")

# ==============================================================================
# 10. ONBOARDING & START
# ==============================================================================
@dp.message(CommandStart())
async def cmd_start(message: Message, state: FSMContext):
    await state.clear()
    parts = (message.text or "").split(maxsplit=1)
    await _start_flow(message.from_user, message, parts[1].strip() if len(parts) > 1 else "")

async def _start_flow(user, chat_msg: Message, arg: str):
    try: await chat_msg.answer_sticker(WELCOME_STICKER_ID)
    except: pass

    if arg.startswith("v_"):
        order_id = arg.split("v_", 1)[1]
        msg = await chat_msg.answer("🔄 <b>Verifying your payment securely...</b>\n<i>Connecting to gateway...</i>", parse_mode='HTML')
        await run_payment_verification(user.id, order_id, msg)
        return

    row = db_query("SELECT phone FROM users WHERE user_id=?", (user.id,), fetchone=True)
    is_new_user = row is None
    current_username = user.username or ""
    db_query("UPDATE users SET username=? WHERE user_id=?", (current_username, user.id))

    if not row or not row[0]:
        db_query("INSERT OR IGNORE INTO users (user_id, first_name, username, joined_date) VALUES (?, ?, ?, ?)",
                 (user.id, user.first_name, current_username, datetime.now().strftime("%Y-%m-%d %H:%M:%S")))
        log_activity(user.id, "ACCOUNT_CREATED")
        if is_new_user and arg.startswith("ref_") and arg[4:].isdigit():
            ref_id = int(arg[4:])
            if ref_id != user.id and db_query("SELECT 1 FROM users WHERE user_id=?", (ref_id,), fetchone=True):
                db_query("UPDATE users SET referred_by=? WHERE user_id=?", (ref_id, user.id))
                try:
                    await bot.send_message(ref_id, f"🎉 <b>{html_escape(user.first_name or 'Someone')}</b> joined using your referral link!", parse_mode="HTML")
                except Exception:
                    pass

    log_activity(user.id, "CMD_START")
    await send_main_menu(chat_msg, user.id)

async def send_main_menu(ctx: Any, user_id: Optional[int] = None):
    uid = user_id or ctx.from_user.id
    text = get_ui_text("start_menu")
    kb = ui_attach_video(main_menu_kb(uid), "start_menu")
    if isinstance(ctx, Message):
        await ctx.answer(text, reply_markup=kb, parse_mode='HTML')
    else:
        await ctx.message.edit_text(text, reply_markup=kb, parse_mode='HTML')

@dp.callback_query(F.data.startswith("cxopen_"))
async def custom_page_open(call: CallbackQuery):
    key = call.data[len("cxopen_"):]
    if key not in ui_custom_keys():
        return await call.answer("Page not found.", show_alert=True)
    text = get_ui_text(key, v_name=html_escape(call.from_user.first_name or ""), v_id=call.from_user.id).strip() or "—"
    kb = ui_attach_video(back_kb(), key)
    await call.message.edit_text(text, reply_markup=kb, parse_mode='HTML')

@dp.callback_query(F.data == "check_join")
async def check_join_cb(call: CallbackQuery, state: FSMContext):
    uid = call.from_user.id
    if not await is_channel_member(uid):
        return await call.answer("❌ You have not joined the channel yet! Join first, then press I Joined.", show_alert=True)
    await call.answer("✅ Verified!")
    await state.clear()
    arg = get_setting(f"pending_start_{uid}", "")
    db_query("DELETE FROM settings WHERE key=?", (f"pending_start_{uid}",))
    try: await call.message.delete()
    except Exception: pass
    await _start_flow(call.from_user, call.message, arg)

@dp.callback_query(F.data == "back_main")
async def back_main(call: CallbackQuery, state: FSMContext):
    await state.clear()
    log_activity(call.from_user.id, "RETURN_MAIN_MENU")
    await send_main_menu(call)

# ==============================================================================
# 11. ADD BALANCE
# ==============================================================================
@dp.callback_query(F.data == "menu_add_balance")
async def select_gateway_menu(call: CallbackQuery):
    log_activity(call.from_user.id, "VIEW_ADD_BALANCE")
    binance_on = bool(get_setting("binance_address") and get_setting("binance_api") and get_setting("binance_secret"))
    text = get_ui_text("add_balance_menu").replace("{binance_line}", f"┣ {get_emoji('binance')} Binance — Crypto payments {get_emoji('checkbox_icon')}\n" if binance_on else "")
    kb = InlineKeyboardMarkup(inline_keyboard=[
        [
            InlineKeyboardButton(text="UPI PAY", callback_data="gateway_inr", icon_custom_emoji_id=get_emoji_icon("upi"), style="primary")
        ],
        [
            InlineKeyboardButton(text="BACK", callback_data="back_main", icon_custom_emoji_id=get_emoji_icon("back"), style="danger")
        ]
    ])
    if binance_on:
        kb.inline_keyboard[0].append(_btn("BINANCE PAY", "gateway_crypto", "binance", "primary"))
    for code, label in PAY_METHODS:
        if pm_is_enabled(code):
            kb.inline_keyboard.append([_btn(label, f"pm_pay_{code}", "upi", "primary")])
    ui_attach_video(kb, "add_balance_menu")
    await call.message.edit_text(text, reply_markup=kb, parse_mode='HTML')

# ==============================================================================
# 12. SGVIP UPI PAYMENT FLOW
# ==============================================================================
@dp.callback_query(F.data == "gateway_inr")
async def add_balance_inr(call: CallbackQuery):
    text = get_ui_text("upi_menu")
    kb = InlineKeyboardMarkup(inline_keyboard=[
        [InlineKeyboardButton(text="₹50", callback_data="pay_50", style="primary"), InlineKeyboardButton(text="₹100", callback_data="pay_100", style="primary")],
        [InlineKeyboardButton(text="₹200", callback_data="pay_200", style="primary"), InlineKeyboardButton(text="₹500", callback_data="pay_500", style="primary")],
        [InlineKeyboardButton(text="₹1000", callback_data="pay_1000", style="primary"), InlineKeyboardButton(text="₹2000", callback_data="pay_2000", style="primary")],
        [InlineKeyboardButton(text="✏️ Custom Amount", callback_data="custom_deposit_keypad", style="primary")],
        [InlineKeyboardButton(text="Back", callback_data="menu_add_balance", icon_custom_emoji_id=get_emoji_icon("back"), style="danger")]
    ])
    ui_attach_video(kb, "upi_menu")
    await call.message.edit_text(text, reply_markup=kb, parse_mode='HTML')

@dp.callback_query(F.data == "custom_deposit_keypad")
async def show_custom_keypad(call: CallbackQuery, state: FSMContext):
    await state.set_state(UserStates.custom_amount_input)
    await state.update_data(amount_str="0")
    await show_keypad(call.message)

async def show_keypad(message: Message, amount_str: str = "0"):
    kb = InlineKeyboardMarkup(inline_keyboard=[
        [InlineKeyboardButton(text="      1      ", callback_data="kp_1", style="primary"), InlineKeyboardButton(text="      2      ", callback_data="kp_2", style="primary"), InlineKeyboardButton(text="      3      ", callback_data="kp_3", style="primary")],
        [InlineKeyboardButton(text="      4      ", callback_data="kp_4", style="primary"), InlineKeyboardButton(text="      5      ", callback_data="kp_5", style="primary"), InlineKeyboardButton(text="      6      ", callback_data="kp_6", style="primary")],
        [InlineKeyboardButton(text="      7      ", callback_data="kp_7", style="primary"), InlineKeyboardButton(text="      8      ", callback_data="kp_8", style="primary"), InlineKeyboardButton(text="      9      ", callback_data="kp_9", style="primary")],
        [InlineKeyboardButton(text="    ⌫    ", callback_data="kp_backspace", style="danger"), InlineKeyboardButton(text="      0      ", callback_data="kp_0", style="primary"), InlineKeyboardButton(text="    C    ", callback_data="kp_clear", style="danger")],
        [InlineKeyboardButton(text=f"✅ Confirm (₹{amount_str})", callback_data="kp_confirm", style="success")],
        [InlineKeyboardButton(text="Cancel", callback_data="gateway_inr", icon_custom_emoji_id=get_emoji_icon("back"), style="danger")]
    ])
    text = f"💵 <b>Enter Amount (₹):</b>\n\nCurrent: ₹{amount_str}"
    await message.edit_text(text, reply_markup=kb, parse_mode='HTML')

@dp.callback_query(F.data.startswith("kp_"), UserStates.custom_amount_input)
async def keypad_handler(call: CallbackQuery, state: FSMContext):
    data = await state.get_data()
    amount_str = data.get("amount_str", "0")
    action = call.data.split("_")[1]
    if action == "confirm":
        if amount_str == "0":
            await call.answer("Amount cannot be zero.", show_alert=True)
            return
        try:
            amount = float(amount_str)
            if amount < 1:
                await call.answer("Minimum deposit is ₹1.", show_alert=True)
                return
            await state.clear()
            await call.message.edit_text("⏳ <b>Creating Payment Order...</b>", parse_mode='HTML')
            await generate_sgvip_order(call.from_user.id, amount, call.message)
        except ValueError:
            await call.answer("Invalid amount.", show_alert=True)
        return
    if action == "backspace":
        if len(amount_str) > 1: amount_str = amount_str[:-1]
        else: amount_str = "0"
    elif action == "clear":
        amount_str = "0"
    else:
        if amount_str == "0": amount_str = action
        else: amount_str += action
        if len(amount_str) > 6: amount_str = amount_str[:6]
    await state.update_data(amount_str=amount_str)
    await show_keypad(call.message, amount_str)
    await call.answer()

@dp.callback_query(F.data.startswith("pay_"))
async def process_sgvip_payment_callback(call: CallbackQuery):
    inr_amount = float(call.data.split("_")[1])
    await call.message.edit_text("⏳ <b>Creating Payment Order...</b>", parse_mode='HTML')
    await generate_sgvip_order(call.from_user.id, inr_amount, call.message)

async def generate_sgvip_order(user_id: int, inr_amount: float, message_obj: Message) -> None:
    """Create an SGVIP payment order and show the payment link."""
    token = get_setting("sgvip_token", "")
    if not token:
        return await message_obj.edit_text("⚠️ Payment Gateway is currently offline. Admin needs to set the API Token.", reply_markup=back_kb("gateway_inr"), parse_mode='HTML')

    current_time = int(time.time())
    order_id = f"SGVIP{user_id}{current_time}"

    # Fetch user's mobile number for the gateway (falls back to a dummy if missing)
    user_row = db_query("SELECT phone FROM users WHERE user_id=?", (user_id,), fetchone=True)
    mobile = user_row[0] if user_row and user_row[0] else "9999999999"

    # Create order on SGVIP
    result = await create_sgvip_order(user_id, inr_amount, order_id, mobile)

    status_ok = result.get("status")
    if status_ok is not True and str(status_ok).lower() not in ("true", "success"):
        error_msg = result.get("message", "Unknown error")
        return await message_obj.edit_text(f"❌ <b>Gateway Error:</b> {error_msg}", reply_markup=back_kb("gateway_inr"), parse_mode='HTML')

    data = result.get("result", {}) or {}
    payment_url = data.get("payment_url")
    gateway_order_id = str(data.get("orderId", order_id))

    if not payment_url:
        return await message_obj.edit_text("❌ <b>Gateway Error:</b> Payment link was not generated. Please try again.", reply_markup=back_kb("gateway_inr"), parse_mode='HTML')

    # Order is valid for 30 minutes
    expires_timestamp = int(time.time() + SGVIP_ORDER_TIMEOUT_MINUTES * 60)
    expires_at_str = (datetime.now() + timedelta(minutes=SGVIP_ORDER_TIMEOUT_MINUTES)).strftime("%d-%m-%Y %H:%M:%S")
    created_at = datetime.now().strftime("%d-%m-%Y %H:%M:%S")

    # Save transaction (qr_url stores the payment link, upi_id stores the gateway order id)
    db_query("INSERT INTO transactions (order_id, user_id, amount_inr, status, timestamp, qr_url, upi_id, expires_at) VALUES (?, ?, ?, 'pending', ?, ?, ?, ?)",
             (order_id, user_id, inr_amount, current_time, payment_url, gateway_order_id, expires_timestamp))

    # Payment link + verify buttons
    kb = InlineKeyboardMarkup(inline_keyboard=[
        [InlineKeyboardButton(text="💳 Pay Now", url=payment_url, style="success")],
        [InlineKeyboardButton(text="🔄 Verify Payment", callback_data=f"verify_{order_id}", style="primary")],
        [InlineKeyboardButton(text="Cancel Transaction", callback_data="menu_add_balance", icon_custom_emoji_id=get_emoji_icon("back"), style="danger")]
    ])

    text = (
        f"🧾 <b>PAYMENT ORDER CREATED</b>\n\n"
        f"💵 <b>Amount:</b> {fmt_curr(inr_amount)}\n"
        f"🆔 <b>Order ID:</b> <code>{order_id}</code>\n"
        f"⏳ <b>Expires:</b> {expires_at_str}\n"
        f"📅 <b>Created:</b> {created_at}\n\n"
        f"📱 <b>How to Pay:</b>\n"
        f"1️⃣ Tap <b>Pay Now</b> to open the payment page\n"
        f"2️⃣ Complete the payment of {fmt_curr(inr_amount)}\n"
        f"3️⃣ Click <b>Verify Payment</b> after paying\n"
        f"4️⃣ Auto-verify will also detect your payment!"
    )

    log_activity(user_id, "GENERATE_INVOICE_SGVIP", f"Amount: {inr_amount}, Order ID: {order_id}")
    await message_obj.edit_text(text, reply_markup=kb, parse_mode='HTML')

@dp.callback_query(F.data.startswith("verify_"))
async def manual_verify_callback(call: CallbackQuery):
    order_id = call.data.split("_", 1)[1]
    await run_payment_verification(call.from_user.id, order_id, call)

# ==============================================================================
# 13. BINANCE CRYPTO PAYMENT
# ==============================================================================
@dp.callback_query(F.data == "gateway_crypto")
async def add_balance_crypto(call: CallbackQuery, state: FSMContext):
    address_check = db_query("SELECT value FROM settings WHERE key='binance_address'", fetchone=True)
    if not address_check or not address_check[0]:
        return await call.message.edit_text("⚠️ Binance Gateway is currently offline. Admin has not set a deposit address.", reply_markup=back_kb("menu_add_balance"), parse_mode='HTML')
    deposit_address = address_check[0]
    msg = (f"🪙 <b>— BINANCE USDT DEPOSIT —</b> 🪙\n\n💵 <b>Exchange Rate:</b> 1 USDT = ₹{USDT_TO_INR}\n⚠️ <b>Network:</b> Please send via <b>TRC20</b> or <b>BEP20</b>.\n\n👇 <b>Send your USDT to this exact address:</b>\n<code>{deposit_address}</code>\n\n━━━━━━━━━━━━━━━━━━\n✅ <b>After sending the USDT, reply to this message with your exact TxID (Transaction Hash) to instantly claim your balance.</b>")
    kb = InlineKeyboardMarkup(inline_keyboard=[[InlineKeyboardButton(text="Cancel", callback_data="menu_add_balance", icon_custom_emoji_id=get_emoji_icon("back"), style="danger")]])
    await call.message.edit_text(msg, reply_markup=kb, parse_mode='HTML')
    await state.set_state(UserStates.wait_for_crypto_txid)

@dp.message(UserStates.wait_for_crypto_txid)
async def process_crypto_txid(m: Message, state: FSMContext):
    txid = m.text.strip()
    user_id = m.from_user.id
    if len(txid) < 10: return await m.answer("❌ That doesn't look like a valid TxID. Please try again.")
    if db_query("SELECT txid FROM crypto_txns WHERE txid=?", (txid,), fetchone=True):
        return await m.answer("⚠️ This Transaction ID has already been claimed in the system!", reply_markup=back_kb("menu_add_balance"), parse_mode='HTML')
    api_key_check = (get_setting("binance_api"),) if get_setting("binance_api") else None
    secret_key_check = (get_setting("binance_secret"),) if get_setting("binance_secret") else None
    if not api_key_check or not secret_key_check:
        return await m.answer("⚠️ Binance API is missing on the server. Contact Support.", reply_markup=back_kb("menu_add_balance"), parse_mode='HTML')
    await m.answer("🔄 <b>Verifying your TxID with Binance Blockchain...</b>\n<i>This may take up to 30 seconds...</i>", parse_mode='HTML')
    api_key = api_key_check[0]; secret_key = secret_key_check[0]
    timestamp = int(time.time() * 1000)
    query_string = f"timestamp={timestamp}"
    signature = hmac.new(secret_key.encode('utf-8'), query_string.encode('utf-8'), hashlib.sha256).hexdigest()
    headers = {'X-MBX-APIKEY': api_key}
    url = f"https://api.binance.com/sapi/v1/capital/deposit/hisrec?{query_string}&signature={signature}"
    async with aiohttp.ClientSession() as session:
        try:
            async with session.get(url, headers=headers) as resp:
                if resp.status == 200:
                    try: history = await resp.json(content_type=None)
                    except: history = []
                    found = False
                    for deposit in history:
                        if deposit.get("txId") == txid and deposit.get("status") == 1:
                            found = True
                            usdt_amount = float(deposit.get("amount"))
                            inr_amount = usdt_amount * USDT_TO_INR
                            db_query("INSERT INTO crypto_txns (txid, user_id, amount_usdt, timestamp) VALUES (?, ?, ?, ?)", (txid, user_id, usdt_amount, int(time.time())))
                            db_query("UPDATE users SET balance = balance + ? WHERE user_id=?", (inr_amount, user_id))
                            await credit_referral_bonus(user_id, inr_amount)
                            await m.answer(f"🎉 <b>CRYPTO DEPOSIT SUCCESSFUL!</b>\n\n✅ We safely received <b>{usdt_amount} USDT</b>.\n💰 <b>{fmt_curr(inr_amount)}</b> has been added to your balance!", reply_markup=main_menu_kb(m.from_user.id), parse_mode='HTML')
                            await send_advanced_notification(user_id, "DEPOSIT", inr_amount, product=txid, gateway="Binance Crypto")
                            log_activity(user_id, "CRYPTO_DEPOSIT", f"TxID: {txid}, Amount: {inr_amount}")
                            await state.clear()
                            break
                    if not found: await m.answer("❌ <b>TxID Not Found or Still Pending!</b>\nMake sure the transaction is fully confirmed. Try again in 5 mins.", reply_markup=back_kb("menu_add_balance"), parse_mode='HTML')
                else: await m.answer(f"⚠️ <b>Binance Server Error:</b> HTTP {resp.status}.", reply_markup=back_kb("menu_add_balance"), parse_mode='HTML')
        except Exception as e: await m.answer(f"⚠️ <b>Connection Error:</b> {str(e)}", reply_markup=back_kb("menu_add_balance"), parse_mode='HTML')

# ==============================================================================
# 14. SHOP – with uppercase categories and new point_down emoji
# ==============================================================================
@dp.callback_query(F.data == "menu_shop")
async def view_shop_panels(call: CallbackQuery):
    log_activity(call.from_user.id, "VIEW_SHOP")
    kb = InlineKeyboardMarkup(inline_keyboard=[])
    text = get_ui_text("shop_menu")
    for cat in FIXED_CATEGORIES:
        count = db_query("SELECT COUNT(*) FROM products WHERE category LIKE ? AND is_active=1", (cat + '%',), fetchone=True)[0]
        emoji_id = get_category_emoji(cat)
        kb.inline_keyboard.append([InlineKeyboardButton(text=cat, callback_data=f"cat_{cat[:30]}", icon_custom_emoji_id=emoji_id, style="primary")])
    kb.inline_keyboard.append([InlineKeyboardButton(text="BACK", callback_data="back_main", icon_custom_emoji_id=get_emoji_icon("back"), style="danger")])
    ui_attach_video(kb, "shop_menu")
    await call.message.edit_text(text, reply_markup=kb, parse_mode='HTML')

@dp.callback_query(F.data.startswith("cat_"))
async def view_panel_names(call: CallbackQuery):
    category = call.data.split("cat_", 1)[1]
    panel_names = db_query("SELECT DISTINCT panel_name FROM products WHERE category LIKE ? AND is_active=1 AND panel_name != ''", (category + '%',), fetchall=True)
    if not panel_names:
        prods = db_query("SELECT id, name, price_inr, stock, reseller_price, validity, device_limit, product_pid, duration_string FROM products WHERE category LIKE ? AND is_active=1", (category + '%',), fetchall=True)
        if not prods: return await call.answer("❌ No products available in this category yet.", show_alert=True)
        await show_products_for_panel(call, prods, category)
        return
    kb = InlineKeyboardMarkup(inline_keyboard=[])
    text = f"{get_emoji('product_store')} <b><u>{category.upper()} PANELS</u></b>\n━━━━━━━━━━━━━━━━━━\n\n{get_emoji('point_down')} <b>Choose a panel name:</b>"
    for pn in panel_names:
        panel = pn[0]
        emoji_id = get_panel_emoji(panel) or get_emoji_icon("product_store")
        kb.inline_keyboard.append([InlineKeyboardButton(text=panel, callback_data=f"pnl_{category[:30]}_{panel[:30]}", icon_custom_emoji_id=emoji_id, style="primary")])
    kb.inline_keyboard.append([InlineKeyboardButton(text="BACK TO PANELS", callback_data="menu_shop", icon_custom_emoji_id=get_emoji_icon("back"), style="danger")])
    await call.message.edit_text(text, reply_markup=kb, parse_mode='HTML')

@dp.callback_query(F.data.startswith("pnl_"))
async def view_products_for_panel(call: CallbackQuery):
    parts = call.data.split("pnl_", 1)[1].split("_", 1)
    if len(parts) != 2: return await call.answer("Invalid selection.", show_alert=True)
    category, panel_name = parts[0], parts[1]
    prods = db_query("SELECT id, name, price_inr, stock, reseller_price, validity, device_limit, product_pid, duration_string FROM products WHERE category LIKE ? AND panel_name LIKE ? AND is_active=1", (category + '%', panel_name + '%'), fetchall=True)
    if not prods: return await call.answer("No products found for this panel.", show_alert=True)
    await show_products_for_panel(call, prods, f"{category} - {panel_name}", panel=panel_name)

async def show_products_for_panel(call: CallbackQuery, prods: List[Tuple], header: str, panel: str = ""):
    user = db_query("SELECT is_reseller, is_vip FROM users WHERE user_id=?", (call.from_user.id,), fetchone=True)
    is_reseller = bool(user[0]) if user else False
    is_vip = bool(user[1]) if user else False
    kb = InlineKeyboardMarkup(inline_keyboard=[])
    text = f"{get_emoji('product_store')} <b><u>{header.upper()} PACKAGES</u></b>\n━━━━━━━━━━━━━━━━━━\n\n"
    for p in prods:
        prod_id, package_name, normal_price, stock, reseller_price, validity, device = p[:7]
        product_pid = p[7] if len(p) > 7 else ""
        duration_string = p[8] if len(p) > 8 else ""
        stock = stock or 0
        normal_price = safe_float(normal_price)
        reseller_price = safe_float(reseller_price)
        base_price = reseller_price if is_reseller else normal_price
        if is_vip: display_price = base_price - (base_price * (VIP_DISCOUNT_PERCENTAGE / 100))
        else: display_price = base_price
        # Per-product check: a package is buyable if it has local stock OR a valid live API binding.
        api_ready = product_api_ready(product_pid, duration_string)
        if stock > 0:
            stock_status = "✅ In Stock"
        elif api_ready:
            stock_status = "⚡ Live API Available"
        else:
            stock_status = "❌ Out of Stock"
        text += f"{get_emoji('product_store')} ⏱ <b>Validity: {package_name}</b>\n"
        if is_reseller or is_vip:
            text += f"💰 Regular Price: <s>{fmt_curr(normal_price)}</s>\n"
            if is_reseller and not is_vip: text += f"👑 <b>Reseller Price: {fmt_curr(display_price)}</b>\n"
            elif is_vip and not is_reseller: text += f"🌟 <b>VIP Price: {fmt_curr(display_price)}</b>\n"
            else: text += f"👑🌟 <b>Super Price: {fmt_curr(display_price)}</b>\n"
        else: text += f"💰 Price: {fmt_curr(normal_price)}\n"
        text += f"📱 Limit: {device} | 📦 {stock_status}\n\n"
        if stock > 0 or api_ready:
            # Never show "(Out of Stock)" when a live API binding exists.
            kb.inline_keyboard.append([InlineKeyboardButton(text=f"Buy {package_name} - {fmt_curr(display_price)}", callback_data=f"buy_{prod_id}", icon_custom_emoji_id=get_emoji_icon("product_store"), style="success")])
        else:
            kb.inline_keyboard.append([InlineKeyboardButton(text=f"❌ {package_name} (Out of Stock)", callback_data="ignore_stock_click", style="danger")])
    if panel:
        _pd = _pdemo_get(panel)
        if _pd and (_pd[0] or _pd[1]):
            kb.inline_keyboard.insert(0, [InlineKeyboardButton(text="🎬 Panel Demo", callback_data=f"pdm_{_pkey(panel)}", style="primary")])
    text += f"{get_emoji('point_down')} <b>Select package below to instantly purchase:</b>"
    kb.inline_keyboard.append([InlineKeyboardButton(text="BACK TO PANELS", callback_data="menu_shop", icon_custom_emoji_id=get_emoji_icon("back"), style="danger")])
    await call.message.edit_text(text, reply_markup=kb, parse_mode='HTML')

@dp.callback_query(F.data == "ignore_stock_click")
async def ignore_stock_click(call: CallbackQuery):
    await call.answer("⚠️ This duration is completely Out of Stock! Admins have been notified to refill.", show_alert=True)

@dp.callback_query(F.data.startswith("buy_"))
async def process_buy(call: CallbackQuery, state: FSMContext):
    prod_id = int(call.data.split("_")[1])
    prod = db_query("SELECT name, price_inr, stock, apk_link, validity, device_limit, category, reseller_price, panel_name, key_type FROM products WHERE id=?", (prod_id,), fetchone=True)
    user = db_query("SELECT balance, is_reseller, total_saved, is_vip FROM users WHERE user_id=?", (call.from_user.id,), fetchone=True)
    if not prod: return await call.answer("❌ Critical Error: Item not found in DB!", show_alert=True)
    if not user: return await call.answer("❌ User profile not found. Please /start again.", show_alert=True)
    normal_price = safe_float(prod[1])
    reseller_price = safe_float(prod[7])
    is_reseller = bool(user[1]); is_vip = bool(user[3])
    base_price = reseller_price if is_reseller else normal_price
    final_price = base_price - (base_price * (VIP_DISCOUNT_PERCENTAGE / 100)) if is_vip else base_price
    if user[0] < final_price:
        return await call.answer(f"❌ Insufficient Balance! You need {fmt_curr(final_price)}.\nPlease Top Up your wallet.", show_alert=True)

    # V1 / Device-Lock products need an android_id before a live API purchase.
    if str(prod[9] or "V2").upper() == "V1":
        await state.update_data(pending_buy_prod=prod_id)
        await state.set_state(UserStates.wait_for_android_id)
        await call.message.edit_text(
            "📱 <b>Device-Lock Product</b>\n━━━━━━━━━━━━━━━━━━\n"
            "This package requires a <b>Device / Android ID</b> to generate your license.\n\n"
            "Please send your <b>Android ID</b> now (or type <code>skip</code> to try without it):",
            reply_markup=back_kb("menu_shop"), parse_mode='HTML'
        )
        return

    await call.answer()
    await finalize_purchase(call.message, call.from_user.id, prod_id, android_id=None)


@dp.message(UserStates.wait_for_android_id)
async def process_android_id(m: Message, state: FSMContext):
    data = await state.get_data()
    prod_id = data.get("pending_buy_prod")
    await state.clear()
    if not prod_id:
        return await m.answer("❌ Session expired. Please open the shop again.", reply_markup=main_menu_kb(m.from_user.id), parse_mode='HTML')
    android_id = None if m.text.strip().lower() == "skip" else m.text.strip()
    await finalize_purchase(m, m.from_user.id, prod_id, android_id=android_id)


async def finalize_purchase(target_message: Message, user_id: int, prod_id: int, android_id: Optional[str] = None):
    """
    Secure a key FIRST (local vault -> API fallback), then deduct balance.
    If fulfilment fails, the user is NOT charged.
    """
    prod = db_query(
        "SELECT name, price_inr, stock, apk_link, validity, device_limit, category, reseller_price, panel_name, key_type "
        "FROM products WHERE id=?", (prod_id,), fetchone=True)
    user = db_query("SELECT balance, is_reseller, total_saved, is_vip FROM users WHERE user_id=?", (user_id,), fetchone=True)
    if not prod or not user:
        return await target_message.edit_text("❌ Critical Error: Product/User not found.", reply_markup=back_kb("menu_shop"), parse_mode='HTML')

    normal_price = safe_float(prod[1])
    reseller_price = safe_float(prod[7])
    is_reseller = bool(user[1]); is_vip = bool(user[3])
    base_price = reseller_price if is_reseller else normal_price
    final_price = base_price - (base_price * (VIP_DISCOUNT_PERCENTAGE / 100)) if is_vip else base_price
    savings = normal_price - final_price
    if user[0] < final_price:
        return await target_message.edit_text(f"❌ <b>Insufficient Balance!</b>\nYou need {fmt_curr(final_price)}.", reply_markup=back_kb("menu_shop"), parse_mode='HTML')

    # ---- 2-TIER FULFILLMENT (keys secured BEFORE any balance deduction) ----
    result = await fulfill_keys(prod_id, 1, android_id=android_id)
    if not result.get("success"):
        # Nothing was charged: fulfilment happens before deduction, so the
        # wallet is already intact. We still surface the exact refund wording.
        log_activity(user_id, "PURCHASE_FAILED", f"Product ID {prod_id}: {result.get('error')}")
        fail_msg = (
            "❌ <b>Stock currently unavailable. Amount refunded.</b>\n━━━━━━━━━━━━━━━━━━\n"
            "We could not secure a license key right now.\n\n"
            f"📦 <b>Package:</b> {prod[0]}\n"
            f"⚠️ <b>Reason:</b> {result.get('error')}\n\n"
            f"💳 <b>Your balance is safe:</b> {fmt_curr(user[0])} (no amount was deducted)\n"
            f"Please try again later or contact: {ADMIN_CONTACT}"
        )
        return await target_message.edit_text(fail_msg, reply_markup=back_kb("menu_shop"), parse_mode='HTML')

    delivered_keys = result["keys"]
    delivered_key = "\n".join(delivered_keys)
    source = result.get("source", "LOCAL")
    product_full_name = f"{prod[6]} - {prod[8]} ({prod[0]})"

    # ---- Deduct balance only after successful fulfilment ----
    charged = False
    try:
        db_query("UPDATE users SET balance=?, spent=spent+?, orders_count=orders_count+1, total_saved=total_saved+? WHERE user_id=?",
                 (user[0] - final_price, final_price, savings, user_id))
        charged = True
        db_query("INSERT INTO orders (user_id, product_name, price_paid, delivered_key, purchase_date, source, api_order_id) VALUES (?, ?, ?, ?, ?, ?, ?)",
                 (user_id, product_full_name, final_price, delivered_key, datetime.now().strftime("%Y-%m-%d %H:%M:%S"), source, result.get("api_order_id", "")))
        log_activity(user_id, "PURCHASE_SUCCESS", f"Product: {product_full_name}, Paid: {final_price}, Source: {source}")
        await send_advanced_notification(user_id, "ORDER", final_price, product=product_full_name, key=delivered_key)
    except Exception as e:
        logger.error(f"Post-payment failure for user {user_id}: {e}")
        if charged:
            refund_balance(user_id, final_price, savings)
        return await target_message.edit_text(
            "❌ <b>Stock currently unavailable. Amount refunded.</b>\n"
            f"Your balance has been restored. Please contact: {ADMIN_CONTACT}",
            reply_markup=back_kb("menu_shop"), parse_mode='HTML')

    source_label = {"LOCAL": "🔐 Local Vault", "API": "⚡ Live API", "LOCAL+API": "🔐⚡ Vault + Live API"}.get(source, source)
    msg = (f"✅ <b>PURCHASE SUCCESSFUL!</b>\n━━━━━━━━━━━━━━━━━━\n"
           f"📦 <b>Panel:</b> {prod[6]}\n📁 <b>Panel Name:</b> {prod[8]}\n⏱ <b>Package:</b> {prod[0]}\n"
           f"💸 <b>Amount Deducted:</b> {fmt_curr(final_price)}\n📱 <b>Device Limit:</b> {prod[5]}\n"
           f"🚀 <b>Delivered From:</b> {source_label}\n━━━━━━━━━━━━━━━━━━\n")
    if prod[3] and prod[3].startswith("http"):
        msg += f"📥 <b>APK Link:</b> <a href='{prod[3]}'>Click Here to Download</a>\n\n"
    msg += f"🔑 <b>Your Exclusive Key:</b>\n<code>{delivered_key}</code>\n\n<i>For any issues or guide, tap Support or contact: {ADMIN_CONTACT}</i>"
    await target_message.edit_text(msg, reply_markup=back_kb("menu_shop"), disable_web_page_preview=True, parse_mode='HTML')

# ==============================================================================
# 15. USER DASHBOARD, FILES, VIP, RESELLER, ORDERS, PROFILE
# ==============================================================================

@dp.callback_query(F.data == "menu_vip_dash")
async def vip_dashboard(call: CallbackQuery):
    u = db_query("SELECT balance, is_vip, vip_since FROM users WHERE user_id=?", (call.from_user.id,), fetchone=True)
    is_vip = bool(u[1])
    status_str = f"{get_emoji('check_icon')} Active (Lifetime)" if is_vip else f"{get_emoji('info_icon')} Not Subscribed"
    text = get_ui_text("vip_menu", vip_status=status_str, v_price=fmt_curr(VIP_PRICE_INR), v_discount=f"{VIP_DISCOUNT_PERCENTAGE:g}")
    kb = InlineKeyboardMarkup(inline_keyboard=[])
    if is_vip:
        text += f"\n{get_emoji('joined_grid')} <b>Member Since:</b> {u[2]}\n\nEnjoy your permanent {VIP_DISCOUNT_PERCENTAGE:g}% discount!"
    else:
        text += f"\n\n{get_emoji('wallet')} <b>Your Current Balance:</b> {fmt_curr(u[0])}\n"
        if u[0] >= VIP_PRICE_INR: kb.inline_keyboard.append([InlineKeyboardButton(text=f"✅ Purchase VIP for {fmt_curr(VIP_PRICE_INR)}", callback_data="execute_vip_upgrade", style="success")])
        else:
            kb.inline_keyboard.append([InlineKeyboardButton(text=f"❌ Need {fmt_curr(VIP_PRICE_INR)} to Upgrade", callback_data="ignore_stock_click", style="danger")])
            kb.inline_keyboard.append([InlineKeyboardButton(text="💳 Add Balance Now", callback_data="menu_add_balance", style="primary")])
    kb.inline_keyboard.append([InlineKeyboardButton(text="BACK", callback_data="back_main", icon_custom_emoji_id=get_emoji_icon("back"), style="danger")])
    ui_attach_video(kb, "vip_menu")
    await call.message.edit_text(text, reply_markup=kb, parse_mode='HTML')

@dp.callback_query(F.data == "execute_vip_upgrade")
async def execute_vip_upgrade(call: CallbackQuery):
    u = db_query("SELECT balance, is_vip FROM users WHERE user_id=?", (call.from_user.id,), fetchone=True)
    if u[1]: return await call.answer("⚠️ You are already a VIP Member!", show_alert=True)
    if u[0] < VIP_PRICE_INR: return await call.answer(f"❌ Your balance dropped below {VIP_PRICE_INR}.", show_alert=True)
    new_balance = u[0] - VIP_PRICE_INR
    now_date = datetime.now().strftime("%Y-%m-%d")
    db_query("UPDATE users SET balance=?, is_vip=1, vip_since=? WHERE user_id=?", (new_balance, now_date, call.from_user.id))
    log_activity(call.from_user.id, "UPGRADED_VIP")
    try: await bot.send_message(ADMIN_ID, f"🌟 <b>NEW VIP UPGRADE</b>\n👤 User ID: <code>{call.from_user.id}</code>", parse_mode='HTML')
    except: pass
    await call.answer("🎉 Upgrade Successful! You are now a VIP Member.", show_alert=True)
    await vip_dashboard(call)

@dp.callback_query(F.data == "menu_reseller_dash")
async def reseller_dashboard(call: CallbackQuery):
    u = db_query("SELECT balance, is_reseller, reseller_since, total_saved FROM users WHERE user_id=?", (call.from_user.id,), fetchone=True)
    status_check = db_query("SELECT value FROM settings WHERE key='reseller_system_status'", fetchone=True)
    system_status = status_check[0] if status_check else "ON"
    setup_fee = safe_float(get_setting("reseller_setup_fee", "200.0"))
    min_balance = safe_float(get_setting("reseller_min_balance", "500.0"))
    if u[1]:
        text = get_ui_text("reseller_active", v_since=u[2], v_saved=fmt_curr(u[3]))
        kb = InlineKeyboardMarkup(inline_keyboard=[[InlineKeyboardButton(text="BACK", callback_data="back_main", icon_custom_emoji_id=get_emoji_icon("back"), style="danger")]])
        ui_attach_video(kb, "reseller_active")
        await call.message.edit_text(text, reply_markup=kb, parse_mode='HTML')
        return
    if system_status == "OFF": return await call.answer("⚠️ Wholesale / Reseller registrations are currently closed by Admin.", show_alert=True)
    text = get_ui_text("reseller_menu", v_min_balance=fmt_curr(min_balance), v_setup_fee=fmt_curr(setup_fee), v_balance=fmt_curr(u[0]))
    kb = InlineKeyboardMarkup(inline_keyboard=[])
    if u[0] >= min_balance: kb.inline_keyboard.append([InlineKeyboardButton(text=f"✅ Request Reseller · fee {fmt_curr(setup_fee)}", callback_data="execute_reseller_upgrade", style="success")])
    else:
        kb.inline_keyboard.append([InlineKeyboardButton(text=f"❌ Insufficient Balance (Need {fmt_curr(min_balance)})", callback_data="ignore_stock_click", style="danger")])
        kb.inline_keyboard.append([InlineKeyboardButton(text="💳 Add Balance", callback_data="menu_add_balance", style="primary")])
    kb.inline_keyboard.append([InlineKeyboardButton(text="BACK", callback_data="back_main", icon_custom_emoji_id=get_emoji_icon("back"), style="danger")])
    ui_attach_video(kb, "reseller_menu")
    await call.message.edit_text(text, reply_markup=kb, parse_mode='HTML')

@dp.callback_query(F.data == "execute_reseller_upgrade")
async def execute_reseller_upgrade(call: CallbackQuery):
    """User pays the setup fee and sends a request. The admin approves it (Admin -> Reseller Mgmt -> Requests)."""
    setup_fee = safe_float(get_setting("reseller_setup_fee", "200.0"))
    min_balance = safe_float(get_setting("reseller_min_balance", "500.0"))
    uid = call.from_user.id
    u = db_query("SELECT balance, is_reseller FROM users WHERE user_id=?", (uid,), fetchone=True)
    if not u:
        return await call.answer("❌ User profile not found. Please /start again.", show_alert=True)
    if u[1]:
        return await call.answer("⚠️ You are already a Reseller!", show_alert=True)
    if db_query("SELECT 1 FROM reseller_requests WHERE user_id=? AND status='pending'", (uid,), fetchone=True):
        return await call.answer("⏳ Aapki reseller request pehle se admin ke paas pending hai.", show_alert=True)
    if u[0] < min_balance:
        return await call.answer(f"❌ Your balance dropped below {fmt_curr(min_balance)}. Please top up.", show_alert=True)
    conn = sqlite3.connect(DB_FILE, timeout=15)
    try:
        cur = conn.execute("UPDATE users SET balance = balance - ? WHERE user_id=? AND balance >= ?", (setup_fee, uid, setup_fee))
        conn.commit()
        ok = cur.rowcount == 1
    finally:
        conn.close()
    if not ok:
        return await call.answer("❌ Balance kam hai. Pehle top up karo.", show_alert=True)
    rid = db_insert("INSERT INTO reseller_requests (user_id, fee, status, created_at) VALUES (?, ?, 'pending', ?)",
                    (uid, setup_fee, datetime.now().strftime("%Y-%m-%d %H:%M:%S")))
    log_activity(uid, "RESELLER_REQUEST", f"#{rid} fee={setup_fee}")
    try:
        await bot.send_message(
            ADMIN_ID,
            f"👑 <b>NEW RESELLER REQUEST #{rid}</b>\n👤 User: <code>{uid}</code>\n💵 Fee held: {fmt_curr(setup_fee)}",
            reply_markup=InlineKeyboardMarkup(inline_keyboard=[[
                InlineKeyboardButton(text="✅ Approve", callback_data=f"rr_ok_{rid}", style="success"),
                InlineKeyboardButton(text="❌ Reject", callback_data=f"rr_no_{rid}", style="danger")]]),
            parse_mode='HTML')
    except Exception:
        pass
    await call.answer("📨 Request admin ko bhej di gayi. Approve hone par aap Reseller ban jaoge.", show_alert=True)
    await reseller_dashboard(call)

async def _render_orders(call: CallbackQuery, back_cb: str):
    orders = db_query("SELECT product_name, delivered_key, purchase_date, price_paid FROM orders WHERE user_id=? ORDER BY id DESC LIMIT 10", (call.from_user.id,), fetchall=True)
    if not orders:
        kb = ui_attach_video(back_kb(back_cb), "orders_empty")
        return await call.message.edit_text(get_ui_text("orders_empty"), reply_markup=kb, parse_mode='HTML')
    lst = ""
    for o in orders:
        lst += (f"{get_emoji('total_orders')} <b>{html_escape(str(o[0]))}</b> ({fmt_curr(o[3])})\n"
                f"{get_emoji('shield_icon')} <code>{html_escape(str(o[1]))}</code>\n"
                f"{get_emoji('joined_grid')} <i>{o[2]}</i>\n━━━━━━━━━━━━━━━━\n")
    text = get_ui_text("orders", v_orders_list=lst)
    kb = ui_attach_video(back_kb(back_cb), "orders")
    await call.message.edit_text(text, reply_markup=kb, parse_mode='HTML')

@dp.callback_query(F.data == "menu_orders")
async def my_orders(call: CallbackQuery):
    await _render_orders(call, "back_main")

@dp.callback_query(F.data == "menu_keyhist")
async def key_history(call: CallbackQuery):
    await _render_orders(call, "menu_profile")

def _fmt_ts(ts) -> str:
    try:
        ts = float(ts)
        if ts > 1e11:
            ts /= 1000.0
        return datetime.fromtimestamp(ts).strftime("%Y-%m-%d %H:%M")
    except Exception:
        return "-"

@dp.callback_query(F.data == "menu_deposit_hist")
async def deposit_history(call: CallbackQuery):
    uid = call.from_user.id
    items = []
    for amt, ts, oid in (db_query("SELECT amount_inr, timestamp, order_id FROM transactions WHERE user_id=? AND status='paid' ORDER BY timestamp DESC LIMIT 10", (uid,), fetchall=True) or []):
        items.append((float(ts or 0), f"{get_emoji('money_icon')} <b>+{fmt_curr(amt)}</b> (UPI)\n{get_emoji('joined_grid')} <i>{_fmt_ts(ts)}</i>\n{get_emoji('shield_icon')} <code>{html_escape(str(oid))}</code>\n━━━━━━━━━━━━━━━━\n"))
    for amt, ts, txid in (db_query("SELECT amount_usdt, timestamp, txid FROM crypto_txns WHERE user_id=? ORDER BY timestamp DESC LIMIT 10", (uid,), fetchall=True) or []):
        t = float(ts or 0)
        items.append((t / 1000.0 if t > 1e11 else t, f"{get_emoji('binance')} <b>+{safe_float(amt):g} USDT</b> (Binance)\n{get_emoji('joined_grid')} <i>{_fmt_ts(ts)}</i>\n{get_emoji('shield_icon')} <code>{html_escape(str(txid))[:24]}</code>\n━━━━━━━━━━━━━━━━\n"))
    items.sort(key=lambda x: x[0], reverse=True)
    if not items:
        kb = ui_attach_video(back_kb("menu_profile"), "deposit_empty")
        return await call.message.edit_text(get_ui_text("deposit_empty"), reply_markup=kb, parse_mode='HTML')
    text = get_ui_text("deposit_history", v_deposit_list="".join(i[1] for i in items[:10]))
    kb = ui_attach_video(back_kb("menu_profile"), "deposit_history")
    await call.message.edit_text(text, reply_markup=kb, parse_mode='HTML')

@dp.callback_query(F.data == "menu_profile")
async def show_profile(call: CallbackQuery):
    uid = call.from_user.id
    cols = "user_id, first_name, account_type, balance, orders_count, spent, joined_date, is_reseller, reseller_since, total_saved, is_vip"
    u = db_query(f"SELECT {cols} FROM users WHERE user_id=?", (uid,), fetchone=True)
    if not u:
        db_query("INSERT OR IGNORE INTO users (user_id, first_name, username, joined_date) VALUES (?, ?, ?, ?)",
                 (uid, call.from_user.first_name or "", call.from_user.username or "", datetime.now().strftime("%Y-%m-%d %H:%M:%S")))
        u = db_query(f"SELECT {cols} FROM users WHERE user_id=?", (uid,), fetchone=True)
    ref_row = db_query("SELECT COUNT(*) FROM users WHERE referred_by=?", (uid,), fetchone=True)
    total_refs = ref_row[0] if ref_row else 0

    levels = []
    if u[7]: levels.append(f"{get_emoji('reseller')} Reseller")
    if u[10]: levels.append(f"{get_emoji('vip')} VIP")
    level_str = " | ".join(levels) if levels else f"{get_emoji('regular_user')} Regular User"
    tier = " | ".join(t for t, on in (("RESELLER", u[7]), ("VIP", u[10])) if on) or "REGULAR"
    reseller_block = ""
    if u[7]:
        reseller_block = (f"{get_emoji('shield_icon')} <b>— RESELLER METRICS —</b> {get_emoji('shield_icon')}\n"
                          f"{get_emoji('money_icon')} <b>Total Saved via Reseller:</b> {fmt_curr(u[9])}\n\n")
    text = get_ui_text(
        "profile",
        v_id=u[0], v_name=html_escape(str(u[1] or "")), v_tier=tier, v_level=level_str,
        v_balance=fmt_curr(u[3]), v_orders=u[4], v_spent=fmt_curr(u[5]),
        v_refs=total_refs, v_joined=u[6], v_reseller_block=reseller_block,
    )
    kb = InlineKeyboardMarkup(inline_keyboard=[
        [InlineKeyboardButton(text="Key History", callback_data="menu_keyhist",
                              icon_custom_emoji_id=get_emoji_icon('shield_icon'), style="success")],
        [InlineKeyboardButton(text="Deposit History", callback_data="menu_deposit_hist",
                              icon_custom_emoji_id=get_emoji_icon('current_balance'), style="success")],
        [InlineKeyboardButton(text="Redeem Promo Code", callback_data="redeem_coupon",
                              icon_custom_emoji_id=get_emoji_icon('redeem_icon'), style="success")],
        [InlineKeyboardButton(text="Back to Main Terminal", callback_data="back_main",
                              icon_custom_emoji_id=get_emoji_icon("back"), style="danger")]
    ])
    ui_attach_video(kb, "profile")
    await call.message.edit_text(text, reply_markup=kb, parse_mode='HTML')

@dp.callback_query(F.data == "redeem_coupon")
async def redeem_coupon_start(call: CallbackQuery, state: FSMContext):
    await call.message.edit_text("🎟 <b>Please enter your VIP / Promo redeem code below:</b>", reply_markup=back_kb("menu_profile"), parse_mode='HTML')
    await state.set_state(UserStates.wait_for_redeem)

@dp.message(UserStates.wait_for_redeem)
async def process_redeem(m: Message, state: FSMContext):
    code = m.text.strip().upper()
    user_id = m.from_user.id
    if db_query("SELECT * FROM redeemed WHERE user_id=? AND code=?", (user_id, code), fetchone=True):
        await m.answer("❌ Anti-Fraud Alert: You already redeemed this unique code!", reply_markup=main_menu_kb(m.from_user.id), parse_mode='HTML')
        await state.clear()
        return
    coupon = db_query("SELECT amount, uses_left FROM coupons WHERE code=?", (code,), fetchone=True)
    if not coupon: await m.answer("❌ Invalid or Expired Code!", reply_markup=main_menu_kb(m.from_user.id), parse_mode='HTML')
    elif coupon[1] <= 0: await m.answer("❌ This code's usage limit has been fully claimed by other users.", reply_markup=main_menu_kb(m.from_user.id), parse_mode='HTML')
    else:
        db_query("UPDATE users SET balance = balance + ? WHERE user_id=?", (coupon[0], user_id))
        db_query("UPDATE coupons SET uses_left = uses_left - 1 WHERE code=?", (code,))
        db_query("INSERT INTO redeemed (user_id, code) VALUES (?, ?)", (user_id, code))
        log_activity(user_id, "PROMO_REDEEMED", f"Code: {code}, Amount: {coupon[0]}")
        await m.answer(f"🎉 <b>Success!</b>\nSafely added {fmt_curr(coupon[0])} to your balance!", reply_markup=main_menu_kb(m.from_user.id), parse_mode='HTML')
        try:
            user_info = db_query("SELECT first_name FROM users WHERE user_id=?", (user_id,), fetchone=True)
            uname = user_info[0] if user_info else "Unknown User"
            await bot.send_message(ADMIN_ID, f"🎟 <b>PROMO CODE REDEEMED!</b>\n👤 User: {uname} (<code>{user_id}</code>)\n🔖 Code: <b>{code}</b>\n💵 Amount: {fmt_curr(coupon[0])}", parse_mode='HTML')
        except Exception: pass
    await state.clear()

@dp.callback_query(F.data == "menu_how_to")
async def tutorial_system(call: CallbackQuery):
    text = get_ui_text("tutorial")
    kb = InlineKeyboardMarkup(inline_keyboard=[])
    kb.inline_keyboard.append([InlineKeyboardButton(text="BACK", callback_data="back_main", icon_custom_emoji_id=get_emoji_icon("back"), style="danger")])
    ui_attach_video(kb, "tutorial")     # YouTube link set by admin (old Tutorial Video setting also works)
    await call.message.edit_text(text, reply_markup=kb, parse_mode='HTML')

@dp.callback_query(F.data == "menu_support")
async def support_center(call: CallbackQuery):
    telegram_link = get_setting("support_telegram", "https://t.me/YourSupport")
    whatsapp_link = get_setting("support_whatsapp", "https://wa.me/YourNumber")
    kb = InlineKeyboardMarkup(inline_keyboard=[
        [InlineKeyboardButton(text="Contact on Telegram", url=telegram_link, icon_custom_emoji_id=get_emoji_icon("telegram"), style="primary")],
        [InlineKeyboardButton(text="Contact on WhatsApp", url=whatsapp_link, icon_custom_emoji_id=get_emoji_icon("whatsapp"), style="primary")],
        [InlineKeyboardButton(text="🎫 Open New Ticket", callback_data="open_ticket", style="primary"), InlineKeyboardButton(text="📋 My Open Tickets", callback_data="my_tickets", style="primary")], 
        [InlineKeyboardButton(text="BACK", callback_data="back_main", icon_custom_emoji_id=get_emoji_icon("back"), style="danger")]
    ])
    ui_attach_video(kb, "support")
    await call.message.edit_text(get_ui_text("support"), reply_markup=kb, parse_mode='HTML')

@dp.callback_query(F.data == "my_tickets")
async def view_my_tickets(call: CallbackQuery):
    tickets = db_query("SELECT id, message, status, created_at FROM tickets WHERE user_id=? ORDER BY id DESC LIMIT 5", (call.from_user.id,), fetchall=True)
    if not tickets: return await call.message.edit_text("📋 You do not have any active or previous support tickets.", reply_markup=back_kb("menu_support"), parse_mode='HTML')
    text = "📋 <b><u>— Your Recent Tickets —</u></b> 📋\n\n"
    for t in tickets:
        status_icon = "🟢" if t[2] == 'Open' else "🔴"
        text += f"🎫 <b>Ticket #{t[0]}</b> | Status: {status_icon} <b>{t[2]}</b>\n📅 <i>{t[3]}</i>\n📝 <i>{t[1][:80]}...</i>\n\n"
    await call.message.edit_text(text, reply_markup=back_kb("menu_support"), parse_mode='HTML')

@dp.callback_query(F.data == "open_ticket")
async def open_ticket_start(call: CallbackQuery, state: FSMContext):
    await call.message.edit_text("📝 <b>Please type your issue/message below in detail:</b>", reply_markup=back_kb("menu_support"), parse_mode='HTML')
    await state.set_state(UserStates.wait_for_ticket)

@dp.message(UserStates.wait_for_ticket)
async def process_ticket(m: Message, state: FSMContext):
    db_query("INSERT INTO tickets (user_id, message, created_at) VALUES (?, ?, ?)", (m.from_user.id, m.text, datetime.now().strftime("%Y-%m-%d %H:%M:%S")))
    await m.answer("✅ <b>Ticket Submitted Successfully!</b> Admins will reply soon.", reply_markup=main_menu_kb(m.from_user.id), parse_mode='HTML')
    try: await bot.send_message(ADMIN_ID, f"🚨 <b>NEW SUPPORT TICKET</b>\nFrom: <code>{m.from_user.id}</code>\nMsg: {m.text}", parse_mode='HTML')
    except: pass
    log_activity(m.from_user.id, "OPENED_TICKET")
    await state.clear()

# ==============================================================================
# 18. ADMIN PANEL
# ==============================================================================
async def _require_fresh(call: CallbackQuery, state: FSMContext) -> bool:
    return True      # no password step any more

@dp.message(Command("admin"))
async def admin_panel(message: Message, state: FSMContext):
    await state.clear()
    if _is_admin(message.from_user.id):
        return await message.answer(admin_header(), reply_markup=admin_kb(), parse_mode='HTML')
    sec_log("ADMIN_PW_PROMPT", message.from_user.id)
    await state.set_state(AdminStates.co_login)
    await message.answer("🔐 <b>Admin password</b> bhejo.\n<i>(/cancel to abort)</i>", parse_mode='HTML')

@dp.callback_query(F.data == "admin_security")
async def admin_security_menu(call: CallbackQuery):
    if call.from_user.id != ADMIN_ID: return
    text = ("🔐 <b>SECURITY CENTER</b>\n\n"
            "• Admin panel: <b>only ADMIN_ID can open it</b> (no password)\n"
            f"• Bot token stored in: <b>{html_escape(_TOKEN_SRC[0])}</b>\n"
            f"• Start-password vault: <b>{'yes' if os.path.exists(VAULT_FILE) else 'no'}</b>\n"
            "• API keys encrypted in database: <b>yes</b>\n"
            f"• Force-join channel: <b>{html_escape(REQUIRED_CHANNEL)}</b>\n"
            "• Flood guard, intruder auto-ban, log redaction: <b>on</b>")
    kb = InlineKeyboardMarkup(inline_keyboard=[
        [InlineKeyboardButton(text="📜 Security Log", callback_data="admin_sec_log", style="primary")],
        [InlineKeyboardButton(text="Back to Admin", callback_data="admin_panel_back", icon_custom_emoji_id=get_emoji_icon("back"), style="danger")],
    ])
    await call.message.edit_text(text, reply_markup=kb, parse_mode='HTML')

@dp.callback_query(F.data == "admin_sec_log")
async def admin_sec_log_view(call: CallbackQuery):
    if call.from_user.id != ADMIN_ID: return
    try:
        lines = open(os.path.join(BASE_DIR, "security.log"), encoding="utf-8", errors="ignore").read().splitlines()[-15:]
    except OSError:
        lines = []
    body = html_escape("\n".join(lines)) if lines else "No events yet."
    await call.answer()
    await call.message.answer(f"📜 <b>Last security events</b>\n<pre>{body[-3500:]}</pre>", parse_mode='HTML')

@dp.callback_query(F.data == "admin_panel_back")
async def back_to_admin(call: CallbackQuery, state: FSMContext):
    await state.clear()
    await call.message.edit_text(admin_header(), reply_markup=admin_kb(), parse_mode='HTML')

@dp.callback_query(F.data == "admin_toggle_vip_sys")
async def toggle_vip_sys(call: CallbackQuery):
    if not _is_admin(call.from_user.id): return
    res = db_query("SELECT value FROM settings WHERE key='vip_status'", fetchone=True)
    current = res[0] if res else 'OFF'
    new_status = 'ON' if current == 'OFF' else 'OFF'
    db_query("INSERT OR REPLACE INTO settings (key, value) VALUES ('vip_status', ?)", (new_status,))
    await call.message.edit_reply_markup(reply_markup=admin_kb())

@dp.callback_query(F.data == "admin_user_control_start")
async def admin_user_control_start(call: CallbackQuery, state: FSMContext):
    if not _is_admin(call.from_user.id): return
    kb = InlineKeyboardMarkup(inline_keyboard=[
        [InlineKeyboardButton(text="📋 Download Full User List", callback_data="admin_download_userlist", style="success")],
        [InlineKeyboardButton(text="Back to Admin", callback_data="admin_panel_back", icon_custom_emoji_id=get_emoji_icon("back"), style="danger")]
    ])
    await call.message.edit_text("💻 <b>User Control Terminal</b>\n\n✏️ Enter the <b>User ID</b> or <b>@Username</b> you want to investigate or manage:\n\n👇 <b>OR</b> download the full user CSV format list:", reply_markup=kb, parse_mode='HTML')
    await state.set_state(AdminStates.manage_target_user)

@dp.callback_query(F.data == "admin_download_userlist")
async def admin_download_userlist(call: CallbackQuery):
    if not _is_admin(call.from_user.id): return
    users = db_query("SELECT username, user_id, phone, balance, orders_count, is_vip, is_reseller FROM users", fetchall=True)
    if not users: return await call.answer("❌ No users found in the database.", show_alert=True)
    file_content = "FULL DATABASE DUMP\n" + "="*100 + "\n"
    for u in users:
        uname = u[0] if u[0] else "No_Username"
        uid = u[1]
        phone = u[2] if u[2] else "No_Phone"
        bal = u[3]
        orders = u[4]
        vip_status = "YES" if u[5] else "NO"
        res_status = "YES" if u[6] else "NO"
        file_content += f"UID: {uid} | UNAME: {uname} | PHONE: {phone} | BAL: ₹{bal:.2f} | BUY: {orders} | VIP: {vip_status} | RES: {res_status}\n"
    doc = BufferedInputFile(file_content.encode('utf-8'), filename=f"DB_{datetime.now().strftime('%Y%m%d')}.txt")
    await call.message.answer_document(document=doc, caption="📋 <b>Database export complete.</b>", parse_mode='HTML')
    await call.answer()

@dp.message(AdminStates.manage_target_user)
async def process_user_lookup(m: Message, state: FSMContext):
    target = m.text.strip()
    if target.startswith('@'): target = target[1:]
    loader_msg = await hacker_loading(m, "Querying User Database")
    user_q = db_query("SELECT user_id, first_name, username, balance, is_reseller, orders_count, spent, joined_date, is_banned, warnings, is_vip FROM users WHERE user_id=? OR username=? COLLATE NOCASE", (target, target), fetchone=True)
    if not user_q: return await loader_msg.edit_text("❌ Target not found in the grid. Check ID/Username syntax.", reply_markup=admin_back_kb(), parse_mode='HTML')
    u_id, u_name, u_user, bal, is_res, orders, spent, joined, is_banned, warnings, is_vip = user_q
    await state.update_data(target_u_id=u_id)
    status_emoji = "🔴 BANNED" if is_banned else "🟢 ACTIVE"
    tags = []
    if is_res: tags.append("👑 Reseller")
    if is_vip: tags.append("🌟 VIP")
    type_str = " | ".join(tags) if tags else "👤 Regular"
    text = (f"🛡 <b><u>USER CONTROL TERMINAL</u></b> 🛡\n━━━━━━━━━━━━━━━━━━\n📛 <b>Name:</b> {u_name} (@{u_user})\n🆔 <b>ID:</b> <code>{u_id}</code>\n📊 <b>Status:</b> {status_emoji}\n🔰 <b>Type:</b> {type_str}\n⚠️ <b>Warnings Issued:</b> {warnings}\n━━━━━━━━━━━━━━━━━━\n💰 <b>Wallet Balance:</b> {fmt_curr(bal)}\n📦 <b>Orders:</b> {orders} | 💸 <b>Total Spent:</b> {fmt_curr(spent)}\n📅 <b>Joined:</b> {joined}")
    ban_btn_text = "Unban ✅" if is_banned else "Ban 🚫"
    kb = InlineKeyboardMarkup(inline_keyboard=[
        [InlineKeyboardButton(text="Add Funds ➕", callback_data=f"usrctrl_add_{u_id}", style="success"), InlineKeyboardButton(text="Minus Funds ➖", callback_data=f"usrctrl_min_{u_id}", style="danger")],
        [InlineKeyboardButton(text=ban_btn_text, callback_data=f"usrctrl_ban_{u_id}", style="danger"), InlineKeyboardButton(text="Warn User ⚠️", callback_data=f"usrctrl_warn_{u_id}", style="danger")],
        [InlineKeyboardButton(text="Give VIP 🌟" if not is_vip else "Remove VIP 🚫", callback_data=f"usrctrl_vip_{u_id}", style="success")],
        [InlineKeyboardButton(text="Back to Admin", callback_data="admin_panel_back", icon_custom_emoji_id=get_emoji_icon("back"), style="danger")]
    ])
    await loader_msg.edit_text(text, reply_markup=kb, parse_mode='HTML')

@dp.callback_query(F.data.startswith("usrctrl_"))
async def handle_user_actions(call: CallbackQuery, state: FSMContext):
    if not _is_admin(call.from_user.id): return
    action = call.data.split("_")[1]
    u_id = int(call.data.split("_")[2])
    await state.update_data(target_u_id=u_id)
    if action == "ban":
        current_status = db_query("SELECT is_banned FROM users WHERE user_id=?", (u_id,), fetchone=True)[0]
        if current_status == 0:
            kb = InlineKeyboardMarkup(inline_keyboard=[
                [InlineKeyboardButton(text="✅ Yes, Ban", callback_data=f"confirm_ban_{u_id}", style="danger"), InlineKeyboardButton(text="❌ Cancel", callback_data="admin_user_control_start", style="danger")]
            ])
            await call.message.edit_text(f"⚠️ Are you sure you want to <b>BAN</b> user <code>{u_id}</code>?", reply_markup=kb, parse_mode='HTML')
            await state.set_state(AdminStates.confirm_ban)
        else:
            db_query("UPDATE users SET is_banned=0 WHERE user_id=?", (u_id,))
            await call.answer("✅ User unbanned successfully!", show_alert=True)
            m = call.message; m.text = str(u_id); await process_user_lookup(m, state)
    elif action == "vip":
        current_status = db_query("SELECT is_vip FROM users WHERE user_id=?", (u_id,), fetchone=True)[0]
        if current_status == 1:
            db_query("UPDATE users SET is_vip=0 WHERE user_id=?", (u_id,))
            await call.answer("✅ VIP Removed!", show_alert=True)
        else:
            db_query("UPDATE users SET is_vip=1, vip_since=? WHERE user_id=?", (datetime.now().strftime("%Y-%m-%d"), u_id))
            await call.answer("✅ VIP Granted!", show_alert=True)
        m = call.message; m.text = str(u_id); await process_user_lookup(m, state)
    elif action == "add":
        await call.message.edit_text("💰 Enter the amount to <b>ADD</b> to this user's wallet:", reply_markup=admin_back_kb(), parse_mode='HTML')
        await state.set_state(AdminStates.wait_for_add_money)
    elif action == "min":
        await call.message.edit_text("💸 Enter the amount to <b>DEDUCT</b> from this user's wallet:", reply_markup=admin_back_kb(), parse_mode='HTML')
        await state.set_state(AdminStates.wait_for_minus_money)
    elif action == "warn":
        await call.message.edit_text("⚠️ Type the strict warning message you want to send directly to this user:", reply_markup=admin_back_kb(), parse_mode='HTML')
        await state.set_state(AdminStates.wait_for_warning)

@dp.callback_query(F.data.startswith("confirm_ban_"))
async def confirm_ban(call: CallbackQuery, state: FSMContext):
    if not _is_admin(call.from_user.id): return
    u_id = int(call.data.split("_")[2])
    db_query("UPDATE users SET is_banned=1 WHERE user_id=?", (u_id,))
    await call.answer("🔴 User has been banned!", show_alert=True)
    await state.clear()
    m = call.message; m.text = str(u_id); await process_user_lookup(m, state)

@dp.message(AdminStates.wait_for_add_money)
async def exec_add_money(m: Message, state: FSMContext):
    try:
        amt = float(m.text)
        data = await state.get_data()
        u_id = data['target_u_id']
        db_query("UPDATE users SET balance = balance + ? WHERE user_id=?", (amt, u_id))
        await m.answer(f"✅ Successfully added {fmt_curr(amt)} to target <code>{u_id}</code>.", reply_markup=admin_kb(), parse_mode='HTML')
        try: await bot.send_message(u_id, f"💰 <b>Wallet Top-up!</b>\nAdmin has manually added {fmt_curr(amt)} to your wallet.", parse_mode='HTML')
        except: pass
        await state.clear()
    except ValueError: await m.answer("❌ Critical Error: Input must be a valid number.")

@dp.message(AdminStates.wait_for_minus_money)
async def exec_minus_money(m: Message, state: FSMContext):
    try:
        amt = float(m.text)
        data = await state.get_data()
        u_id = data['target_u_id']
        db_query("UPDATE users SET balance = balance - ? WHERE user_id=?", (amt, u_id))
        await m.answer(f"✅ Successfully deducted {fmt_curr(amt)} from target <code>{u_id}</code>.", reply_markup=admin_kb(), parse_mode='HTML')
        await state.clear()
    except ValueError: await m.answer("❌ Critical Error: Input must be a valid number.")

@dp.message(AdminStates.wait_for_warning)
async def exec_warn_user(m: Message, state: FSMContext):
    data = await state.get_data()
    u_id = data['target_u_id']
    warn_text = m.text
    db_query("UPDATE users SET warnings = warnings + 1 WHERE user_id=?", (u_id,))
    await m.answer(f"✅ Official warning dispatched to <code>{u_id}</code>.", reply_markup=admin_kb(), parse_mode='HTML')
    try: await bot.send_message(u_id, f"⚠️ <b>OFFICIAL WARNING FROM SYSTEM ADMIN:</b>\n\n{warn_text}\n\n<i>Subsequent infractions may lead to an automated grid ban.</i>", parse_mode='HTML')
    except: pass
    await state.clear()

# ==============================================================================
# 19. ADMIN STATISTICS
# ==============================================================================
@dp.callback_query(F.data == "admin_view_stats")
async def admin_dashboard_stats(call: CallbackQuery):
    if not _is_admin(call.from_user.id): return
    t_users = db_query("SELECT COUNT(*) FROM users", fetchone=True)[0]
    t_resellers = db_query("SELECT COUNT(*) FROM users WHERE is_reseller=1", fetchone=True)[0]
    t_vip = db_query("SELECT COUNT(*) FROM users WHERE is_vip=1", fetchone=True)[0]
    t_prods = db_query("SELECT COUNT(*) FROM products", fetchone=True)[0]
    t_keys = db_query("SELECT COUNT(*) FROM product_keys WHERE is_used=0", fetchone=True)[0]
    t_rev = db_query("SELECT SUM(spent) FROM users", fetchone=True)[0] or 0.0
    today_str = datetime.now().strftime("%Y-%m-%d")
    msg = (f"📊 <b><u>GRID INTELLIGENCE DASHBOARD</u></b> 📊\n━━━━━━━━━━━━━━━━━━\n👥 <b>Total Grid Users:</b> {t_users}\n👑 <b>Wholesale Resellers:</b> {t_resellers}\n🌟 <b>Elite VIP Members:</b> {t_vip}\n━━━━━━━━━━━━━━━━━━\n📦 <b>Active Products:</b> {t_prods}\n🔑 <b>Unused Keys in Vault:</b> {t_keys}\n💰 <b>Total Gross Revenue:</b> {fmt_curr(t_rev)}\n━━━━━━━━━━━━━━━━━━")
    await call.message.edit_text(msg, reply_markup=admin_back_kb(), parse_mode='HTML')

# ==============================================================================
# 20. ADMIN PRODUCT MANAGEMENT
# ==============================================================================
@dp.callback_query(F.data == "admin_add_prod")
async def add_prod_start(call: CallbackQuery, state: FSMContext):
    if not _is_admin(call.from_user.id): return
    kb = InlineKeyboardMarkup(inline_keyboard=[])
    for cat in FIXED_CATEGORIES:
        emoji_id = get_category_emoji(cat)
        kb.inline_keyboard.append([InlineKeyboardButton(text=cat, callback_data=f"addprod_cat_{cat}", icon_custom_emoji_id=emoji_id, style="primary")])
    kb.inline_keyboard.append([InlineKeyboardButton(text="Cancel", callback_data="admin_panel_back", icon_custom_emoji_id=get_emoji_icon("back"), style="danger")])
    await call.message.edit_text("📦 <b>Step 1:</b> Choose the <b>Category</b> for this product:", reply_markup=kb, parse_mode='HTML')

@dp.callback_query(F.data.startswith("addprod_cat_"))
async def add_prod_category_selected(call: CallbackQuery, state: FSMContext):
    if not _is_admin(call.from_user.id): return
    category = call.data.split("addprod_cat_", 1)[1]
    await state.update_data(cat=category)
    await call.message.edit_text(f"🛒 <b>Step 2:</b> Enter <b>PANEL NAME</b>\n(e.g., 'MST PANEL', 'DRIP PANEL'):", reply_markup=admin_back_kb(), parse_mode='HTML')
    await state.set_state(AdminStates.add_prod_panel_name)

@dp.message(AdminStates.add_prod_panel_name)
async def add_prod_panel_name(m: Message, state: FSMContext):
    await state.update_data(panel_name=m.text)
    await m.answer("⏳ <b>Step 3:</b> Enter <b>PACKAGE DURATION/DATE NAME</b>\n(e.g., '7 Days', '1 Month'):", parse_mode='HTML')
    await state.set_state(AdminStates.add_prod_name)

@dp.message(AdminStates.add_prod_name)
async def add_prod_name(m: Message, state: FSMContext):
    await state.update_data(name=m.text)
    await m.answer("⏳ Enter Time Validity String (e.g., '24 Hours'):", parse_mode='HTML')
    await state.set_state(AdminStates.add_prod_validity)

@dp.message(AdminStates.add_prod_validity)
async def add_prod_validity(m: Message, state: FSMContext):
    await state.update_data(validity=m.text)
    await m.answer("📱 Enter strict Device Enforcement Limit (e.g., '1 Device HWID'):", parse_mode='HTML')
    await state.set_state(AdminStates.add_prod_device_limit)

@dp.message(AdminStates.add_prod_device_limit)
async def add_prod_device_limit(m: Message, state: FSMContext):
    await state.update_data(device_limit=m.text)
    await m.answer("💰 Enter standard **User Price** in Rupees (₹) (e.g., 500):", parse_mode='HTML')
    await state.set_state(AdminStates.add_prod_price)

@dp.message(AdminStates.add_prod_price)
async def add_prod_price(m: Message, state: FSMContext):
    try:
        await state.update_data(price=float(m.text))
        await m.answer("👑 Enter wholesale **Reseller Price** in Rupees (₹) (e.g., 300):", parse_mode='HTML')
        await state.set_state(AdminStates.add_prod_reseller_price)
    except ValueError: await m.answer("❌ Invalid input datatype! Must be numerical.")

@dp.message(AdminStates.add_prod_reseller_price)
async def add_prod_reseller_price(m: Message, state: FSMContext):
    try:
        await state.update_data(reseller_price=float(m.text))
        await m.answer("🔗 Enter direct APK/Payload Download Link (or type 'none' to omit):", parse_mode='HTML')
        await state.set_state(AdminStates.add_prod_apk)
    except ValueError: await m.answer("❌ Invalid input datatype! Must be numerical.")

@dp.message(AdminStates.add_prod_apk)
async def add_prod_apk(m: Message, state: FSMContext):
    await state.update_data(apk="" if m.text.lower() == 'none' else m.text)
    await m.answer(
        "🔌 <b>Step:</b> Enter the <b>Reseller Product PID</b> for this package.\n"
        "(e.g., <code>166</code>, <code>155</code>). Used for live API fallback.\n"
        "Type <code>none</code> to skip (local-only product).",
        parse_mode='HTML')
    await state.set_state(AdminStates.add_prod_pid)

@dp.message(AdminStates.add_prod_pid)
async def add_prod_pid(m: Message, state: FSMContext):
    pid = "" if m.text.strip().lower() == 'none' else m.text.strip()
    await state.update_data(product_pid=pid)
    await m.answer(
        "⏱ <b>Step:</b> Enter the <b>Exact Duration String</b> sent to the API.\n"
        "Must match the reseller exactly, e.g. <code>1 Hours</code>, <code>3 Hours</code>, "
        "<code>1 Day</code>, <code>7 Days</code>, <code>30 Days</code>.",
        parse_mode='HTML')
    await state.set_state(AdminStates.add_prod_duration)

@dp.message(AdminStates.add_prod_duration)
async def add_prod_duration(m: Message, state: FSMContext):
    await state.update_data(duration_string=m.text.strip())
    kb = InlineKeyboardMarkup(inline_keyboard=[
        [InlineKeyboardButton(text="V2 / Direct Key (No android_id)", callback_data="keytype_V2", style="primary")],
        [InlineKeyboardButton(text="V1 / Device-Lock (android_id required)", callback_data="keytype_V1", style="primary")],
    ])
    await m.answer("🔐 <b>Step:</b> Select the <b>Key Type</b> for this package:", reply_markup=kb, parse_mode='HTML')

@dp.callback_query(F.data.startswith("keytype_"))
async def add_prod_key_type(call: CallbackQuery, state: FSMContext):
    if not _is_admin(call.from_user.id): return
    kt = call.data.split("_", 1)[1]
    await state.update_data(key_type=kt)
    kb = InlineKeyboardMarkup(inline_keyboard=[
        [InlineKeyboardButton(text="⏭ API-only Product (Skip Local Keys)", callback_data="skip_local_keys", style="success")],
    ])
    await call.message.edit_text(
        "📥 <b>Vault Injection Phase</b>\n\n"
        "Paste all the license <b>Keys</b> exactly as formatted (1 key per newline).\n\n"
        "No local keys? Tap the button below, or simply send <code>none</code> / <code>skip</code>.",
        reply_markup=kb, parse_mode='HTML')
    await state.set_state(AdminStates.add_prod_keys)
    await call.answer()


def _persist_new_product(data: Dict[str, Any], keys: List[str]) -> int:
    """Insert a new product + its local keys. Returns the new product id."""
    stock = len(keys)
    conn = sqlite3.connect(DB_FILE)
    try:
        c = conn.cursor()
        c.execute(
            "INSERT INTO products (category, panel_name, name, price_inr, reseller_price, stock, apk_link, validity, device_limit, product_pid, duration_string, key_type) "
            "VALUES (?, ?, ?, ?, ?, ?, ?, ?, ?, ?, ?, ?)",
            (data['cat'], data['panel_name'], data['name'], data['price'], data['reseller_price'],
             stock, data['apk'], data['validity'], data['device_limit'],
             data.get('product_pid', ''), data.get('duration_string', ''), data.get('key_type', 'V2'))
        )
        prod_id = c.lastrowid
        for k in keys:
            c.execute("INSERT INTO product_keys (product_id, key_text) VALUES (?, ?)", (prod_id, k))
        conn.commit()
        return prod_id
    except Exception as e:
        conn.rollback()
        logger.error(f"_persist_new_product failed: {e}")
        raise
    finally:
        conn.close()


def _new_product_success_text(data: Dict[str, Any], stock: int, skipped: bool) -> str:
    header = "✅ <b>Data Deployment Successful!</b>"
    if skipped:
        header += "\n⏭ <b>Local stock skipped. Product configured as API-only.</b>"
    return (
        f"{header}\n\n"
        f"📦 Panel '{data['cat']}' -> Panel Name '{data['panel_name']}' -> Package '{data['name']}'\n"
        f"🔌 PID: {data.get('product_pid') or '—'} | ⏱ Duration: {data.get('duration_string') or '—'} | 🔐 Type: {data.get('key_type', 'V2')}\n"
        f"🔒 Vault Stock: {stock} Keys injected.\n"
        f"💰 User Price: {fmt_curr(data['price'])} | 👑 Reseller: {fmt_curr(data['reseller_price'])}"
    )


@dp.message(AdminStates.add_prod_keys)
async def add_prod_keys(m: Message, state: FSMContext):
    raw = (m.text or "").strip()
    skip_words = {"none", "skip", "no", "0", "-"}
    if not raw or raw.lower() in skip_words:
        keys = []
    else:
        keys = [k.strip() for k in raw.split('\n') if k.strip()]
    data = await state.get_data()
    try:
        _persist_new_product(data, keys)
    except Exception as e:
        return await m.answer(f"❌ Failed to save product: {e}", reply_markup=admin_kb(), parse_mode='HTML')
    await m.answer(_new_product_success_text(data, len(keys), skipped=(len(keys) == 0)),
                   reply_markup=admin_kb(), parse_mode='HTML')
    await state.clear()


@dp.callback_query(F.data == "skip_local_keys", AdminStates.add_prod_keys)
async def skip_local_keys(call: CallbackQuery, state: FSMContext):
    if not _is_admin(call.from_user.id): return
    data = await state.get_data()
    try:
        _persist_new_product(data, [])
    except Exception as e:
        return await call.message.edit_text(f"❌ Failed to save product: {e}", reply_markup=admin_back_kb(), parse_mode='HTML')
    await call.message.edit_text(_new_product_success_text(data, 0, skipped=True),
                                 reply_markup=admin_kb(), parse_mode='HTML')
    await state.clear()
    await call.answer("API-only product saved.")

@dp.callback_query(F.data == "admin_manage_prods")
async def admin_manage_prods(call: CallbackQuery):
    if not _is_admin(call.from_user.id): return
    prods = db_query("SELECT id, name, category, panel_name, stock, is_active FROM products ORDER BY category, panel_name", fetchall=True)
    if not prods: return await call.message.edit_text("📦 Store Database is completely empty.", reply_markup=admin_back_kb(), parse_mode='HTML')
    kb = InlineKeyboardMarkup(inline_keyboard=[])
    for p in prods:
        status_dot = "🟢" if p[5] else "🔴"
        panel_name = p[3] if p[3] is not None else ""
        kb.inline_keyboard.append([InlineKeyboardButton(text=f"{status_dot} [{p[2]}] {panel_name} - {p[1]} (Stock: {p[4]})", callback_data=f"admin_view_p_{p[0]}", style="primary")])
    kb.inline_keyboard.append([InlineKeyboardButton(text="Back to Admin", callback_data="admin_panel_back", icon_custom_emoji_id=get_emoji_icon("back"), style="danger")])
    await call.message.edit_text("📦 <b>Database Editor: Select Node to modify</b>", reply_markup=kb, parse_mode='HTML')

@dp.callback_query(F.data.startswith("admin_view_p_"))
async def admin_view_product(call: CallbackQuery):
    if not _is_admin(call.from_user.id): return
    try:
        p_id = int(call.data.split("_")[3])
        prod = db_query("SELECT * FROM products WHERE id=?", (p_id,), fetchone=True)
        if not prod: return await call.answer("❌ Architecture fault: Node lost!", show_alert=True)
        panel_name = prod[2] if prod[2] is not None else ""
        price_inr = safe_float(prod[4])
        reseller_price = safe_float(prod[5])
        text = (f"📦 <b><u>NODE DEEP DIVE DETAILS</u></b>\n━━━━━━━━━━━━━━━━━━\n<b>ID:</b> <code>{prod[0]}</code>\n<b>Panel Group:</b> {prod[1]}\n<b>Panel Name:</b> {panel_name}\n<b>Package Date/Time:</b> {prod[3]}\n<b>Standard Price:</b> {fmt_curr(price_inr)}\n👑 <b>Wholesale Price:</b> {fmt_curr(reseller_price)}\n<b>Vault Stock:</b> {prod[6]}\n<b>Payload Link:</b> {prod[7] if prod[7] else 'None'}\n<b>Time Config:</b> {prod[8]}\n<b>HWID Limit:</b> {prod[9]}\n<b>Visibility:</b> {'Active' if prod[10] else 'Hidden'}\n━━━━━━━━━━━━━━━━━━")
        toggle_btn_text = "Hide Product 👁‍🗨" if prod[10] else "Unhide Product 👁"
        kb = InlineKeyboardMarkup(inline_keyboard=[
            [InlineKeyboardButton(text="Edit Panel Group 🏷️", callback_data=f"edit_p_{p_id}_cat", style="primary"), InlineKeyboardButton(text="Edit Panel Name 🏷️", callback_data=f"edit_p_{p_id}_panel_name", style="primary")],
            [InlineKeyboardButton(text="Edit Package Name ✏️", callback_data=f"edit_p_{p_id}_name", style="primary")],
            [InlineKeyboardButton(text="Edit Price 💰", callback_data=f"edit_p_{p_id}_price", style="primary"), InlineKeyboardButton(text="Edit R-Price 👑", callback_data=f"edit_p_{p_id}_rprice", style="primary")],
            [InlineKeyboardButton(text="Edit Validity ⏳", callback_data=f"edit_p_{p_id}_validity", style="primary"), InlineKeyboardButton(text="Edit Device 📱", callback_data=f"edit_p_{p_id}_device", style="primary")],
            [InlineKeyboardButton(text="Edit APK Link 🔗", callback_data=f"edit_p_{p_id}_apk", style="primary"), InlineKeyboardButton(text="Add Keys ➕", callback_data=f"edit_p_{p_id}_keys", style="success")],
            [InlineKeyboardButton(text="Edit PID 🔌", callback_data=f"edit_p_{p_id}_pid", style="primary"), InlineKeyboardButton(text="Edit Duration ⏱", callback_data=f"edit_p_{p_id}_duration", style="primary")],
            [InlineKeyboardButton(text="Edit Key Type 🔐", callback_data=f"edit_p_{p_id}_keytype", style="primary")],
            [InlineKeyboardButton(text="Delete Key 🗑", callback_data=f"delkey_p_{p_id}", style="danger"), InlineKeyboardButton(text=toggle_btn_text, callback_data=f"toggle_p_{p_id}", style="danger")],
            [InlineKeyboardButton(text="Nuke Full Node 🗑", callback_data=f"delete_p_{p_id}", style="danger"), InlineKeyboardButton(text="BACK", callback_data="admin_manage_prods", icon_custom_emoji_id=get_emoji_icon("back"), style="danger")]
        ])
        await call.message.edit_text(text, reply_markup=kb, disable_web_page_preview=True, parse_mode='HTML')
    except Exception as e:
        logger.error(f"Error in admin_view_product: {e}")
        await call.message.edit_text(f"❌ Error loading product: {str(e)}", reply_markup=admin_back_kb(), parse_mode='HTML')

@dp.callback_query(F.data.startswith("toggle_p_"))
async def admin_toggle_product(call: CallbackQuery):
    if not _is_admin(call.from_user.id): return
    p_id = int(call.data.split("_")[2])
    current = db_query("SELECT is_active FROM products WHERE id=?", (p_id,), fetchone=True)[0]
    new_val = 0 if current == 1 else 1
    db_query("UPDATE products SET is_active=? WHERE id=?", (new_val, p_id))
    await call.answer("Visibility updated successfully!", show_alert=True)
    await admin_view_product(call)

# ==============================================================================
# FIX: Edit product field – correctly handle different data types and multi-word fields
# ==============================================================================
@dp.callback_query(F.data.startswith("edit_p_"))
async def start_edit_product(call: CallbackQuery, state: FSMContext):
    if not _is_admin(call.from_user.id): return
    # Use split with maxsplit=3 to keep field name intact (may contain underscores)
    parts = call.data.split("_", 3)
    if len(parts) < 4:
        return await call.answer("Invalid callback data.", show_alert=True)
    p_id = int(parts[2])
    field = parts[3]
    await state.update_data(edit_p_id=p_id, edit_field=field)
    if field == 'keys':
        await call.message.edit_text("📥 <b>Vault Injection</b>\nPaste the <b>NEW KEYS</b> to append to the stock (1 key per line):", reply_markup=admin_back_kb(), parse_mode='HTML')
        await state.set_state(AdminStates.wait_for_add_keys)
    else:
        field_name_map = {'cat': 'New Panel Group/Category Name', 'panel_name': 'New Panel Name', 'name': 'New Package/Date Name', 'price': 'New Standard Price in ₹', 'rprice': 'New Reseller Price in ₹', 'validity': 'New Time Validity String', 'device': 'New HWID Limit String', 'apk': 'New Payload Link (or type "none")'}
        await call.message.edit_text(f"✏️ Input the required data for: <b>{field_name_map.get(field, field)}</b>", reply_markup=admin_back_kb(), parse_mode='HTML')
        await state.set_state(AdminStates.wait_for_new_value)

@dp.message(AdminStates.wait_for_new_value)
async def process_edit_value(m: Message, state: FSMContext):
    data = await state.get_data()
    p_id = data['edit_p_id']; field = data['edit_field']; new_val = m.text.strip()
    
    # Convert price fields to float, others remain strings
    if field in ['price', 'rprice']:
        try:
            new_val = float(new_val)
        except ValueError:
            return await m.answer("❌ Invalid number format. Please enter a valid price (e.g., 500).")
    elif field == 'apk':
        new_val = "" if new_val.lower() == 'none' else new_val
    elif field == 'pid':
        new_val = "" if new_val.lower() == 'none' else new_val
    elif field == 'keytype':
        new_val = new_val.upper()
        if new_val not in ('V1', 'V2'):
            return await m.answer("❌ Invalid Key Type. Enter V1 (Device-Lock) or V2 (Direct).")
    # For panel_name, cat, name, validity, device, duration – keep as string
    
    db_col_map = {'cat': 'category', 'panel_name': 'panel_name', 'name': 'name', 'price': 'price_inr', 'rprice': 'reseller_price', 'validity': 'validity', 'device': 'device_limit', 'apk': 'apk_link', 'pid': 'product_pid', 'duration': 'duration_string', 'keytype': 'key_type'}
    db_query(f"UPDATE products SET {db_col_map[field]}=? WHERE id=?", (new_val, p_id))
    await m.answer("✅ <b>Node updated gracefully!</b>", reply_markup=admin_kb(), parse_mode='HTML')
    await state.clear()

@dp.message(AdminStates.wait_for_add_keys)
async def process_add_keys(m: Message, state: FSMContext):
    data = await state.get_data()
    p_id = data['edit_p_id']
    keys = [k.strip() for k in m.text.strip().split('\n') if k.strip()]
    if len(keys) == 0: return await m.answer("❌ Protocol breach: Zero valid keys found.", reply_markup=admin_kb(), parse_mode='HTML')
    conn = sqlite3.connect(DB_FILE)
    c = conn.cursor()
    for k in keys: c.execute("INSERT INTO product_keys (product_id, key_text) VALUES (?, ?)", (p_id, k))
    c.execute("UPDATE products SET stock = stock + ? WHERE id=?", (len(keys), p_id))
    conn.commit(); conn.close()
    await m.answer(f"✅ <b>Vault Secure!</b> {len(keys)} new keys appended and encrypted.", reply_markup=admin_kb(), parse_mode='HTML')
    await state.clear()

# ==============================================================================
# 20B. BULK KEY VAULT INGESTION (dedicated admin menu)
# ==============================================================================
@dp.callback_query(F.data == "admin_bulk_keys")
async def admin_bulk_keys(call: CallbackQuery):
    if not _is_admin(call.from_user.id): return
    prods = db_query("SELECT id, name, category, panel_name, stock FROM products ORDER BY category, panel_name", fetchall=True)
    if not prods:
        return await call.message.edit_text("📦 No products exist yet. Add a product first.", reply_markup=admin_back_kb(), parse_mode='HTML')
    kb = InlineKeyboardMarkup(inline_keyboard=[])
    for p in prods:
        kb.inline_keyboard.append([InlineKeyboardButton(
            text=f"[{p[2]}] {p[3]} - {p[1]} (Stock: {p[4]})",
            callback_data=f"bulkkeys_p_{p[0]}", style="primary")])
    kb.inline_keyboard.append([InlineKeyboardButton(text="Back to Admin", callback_data="admin_panel_back", icon_custom_emoji_id=get_emoji_icon("back"), style="danger")])
    await call.message.edit_text("🔑 <b>Bulk Key Vault Ingestion</b>\nSelect a product to inject keys into:", reply_markup=kb, parse_mode='HTML')

@dp.callback_query(F.data.startswith("bulkkeys_p_"))
async def admin_bulk_keys_select(call: CallbackQuery, state: FSMContext):
    if not _is_admin(call.from_user.id): return
    p_id = int(call.data.split("_")[2])
    prod = db_query("SELECT name, category, panel_name FROM products WHERE id=?", (p_id,), fetchone=True)
    if not prod: return await call.answer("Product not found.", show_alert=True)
    await state.update_data(edit_p_id=p_id)
    await state.set_state(AdminStates.wait_for_add_keys)
    await call.message.edit_text(
        f"🔑 <b>Bulk Ingestion → {prod[1]} / {prod[2]} / {prod[0]}</b>\n\n"
        "Paste the keys now (1 key per newline). They will be appended to the vault:",
        reply_markup=admin_back_kb(), parse_mode='HTML')
    await call.answer()

# ==============================================================================
# 20C. RESELLER API SETTINGS (global credentials)
# ==============================================================================
@dp.callback_query(F.data == "admin_reseller_api")
async def admin_reseller_api(call: CallbackQuery):
    if call.from_user.id != ADMIN_ID: return
    cfg = get_reseller_config()
    api_key = cfg["api_key"] or ""
    master_key = cfg["master_key"] or ""
    masked_key = (api_key[:6] + "..." + api_key[-4:]) if len(api_key) > 10 else (api_key or "—")
    masked_master = (master_key[:6] + "..." + master_key[-4:]) if len(master_key) > 10 else (master_key or "—")
    status = cfg["status"].upper()
    text = (f"🔌 <b><u>RESELLER API SETTINGS</u></b>\n━━━━━━━━━━━━━━━━━━\n"
            f"🌐 <b>Endpoint:</b> {cfg['url']}\n"
            f"🔑 <b>API Key:</b> <code>{masked_key}</code>\n"
            f"🛡 <b>Master Key:</b> <code>{masked_master}</code>\n"
            f"🧭 <b>User-Agent:</b> {cfg['user_agent'][:55]}...\n"
            f"📡 <b>Status:</b> {'🟢 ON' if status == 'ON' else '🔴 OFF'}\n"
            "━━━━━━━━━━━━━━━━━━\n"
            "<i>Used for Priority-2 live key purchases when the local vault is empty.</i>" + _reseller_diag())
    kb = InlineKeyboardMarkup(inline_keyboard=[
        [InlineKeyboardButton(text="Edit Endpoint", callback_data="reseller_edit_url", style="primary")],
        [InlineKeyboardButton(text="Edit API Key", callback_data="reseller_edit_api_key", style="primary")],
        [InlineKeyboardButton(text="Edit Master Key", callback_data="reseller_edit_master_key", style="primary")],
        [InlineKeyboardButton(text="Edit User-Agent", callback_data="reseller_edit_user_agent", style="primary")],
        [InlineKeyboardButton(text=f"Toggle Status ({'ON' if status == 'ON' else 'OFF'})", callback_data="reseller_toggle_status", style="success" if status == 'ON' else "danger")],
        [InlineKeyboardButton(text="Back to Admin", callback_data="admin_panel_back", icon_custom_emoji_id=get_emoji_icon("back"), style="danger")],
    ])
    await call.message.edit_text(text, reply_markup=kb, parse_mode='HTML')

@dp.callback_query(F.data == "reseller_toggle_status")
async def reseller_toggle_status(call: CallbackQuery):
    if call.from_user.id != ADMIN_ID: return
    cur = get_setting("reseller_api_status", "ON").upper()
    set_setting("reseller_api_status", "OFF" if cur == "ON" else "ON")
    await admin_reseller_api(call)

@dp.callback_query(F.data == "reseller_edit_url")
async def reseller_edit_url(call: CallbackQuery, state: FSMContext):
    if call.from_user.id != ADMIN_ID: return
    await call.message.edit_text("🌐 Send the new <b>Reseller API Endpoint URL</b>:", reply_markup=admin_back_kb(), parse_mode='HTML')
    await state.set_state(AdminStates.wait_for_reseller_url)

@dp.message(AdminStates.wait_for_reseller_url)
async def save_reseller_url(m: Message, state: FSMContext):
    set_setting("reseller_api_url", m.text.strip())
    await m.answer("✅ Reseller API endpoint updated.", reply_markup=admin_kb(), parse_mode='HTML')
    await state.clear()

@dp.callback_query(F.data == "reseller_edit_api_key")
async def reseller_edit_api_key(call: CallbackQuery, state: FSMContext):
    if call.from_user.id != ADMIN_ID: return
    await call.message.edit_text("🔑 Send the new <b>Reseller API Key</b> (api_key):", reply_markup=admin_back_kb(), parse_mode='HTML')
    await state.set_state(AdminStates.wait_for_reseller_api_key)

@dp.message(AdminStates.wait_for_reseller_api_key)
async def save_reseller_api_key(m: Message, state: FSMContext):
    set_setting("reseller_api_key", m.text.strip())
    await m.answer("✅ Reseller API key updated.", reply_markup=admin_kb(), parse_mode='HTML')
    await state.clear()

@dp.callback_query(F.data == "reseller_edit_master_key")
async def reseller_edit_master_key(call: CallbackQuery, state: FSMContext):
    if call.from_user.id != ADMIN_ID: return
    await call.message.edit_text("🛡 Send the new <b>Master Key</b> (x-master-key header):", reply_markup=admin_back_kb(), parse_mode='HTML')
    await state.set_state(AdminStates.wait_for_reseller_master_key)

@dp.message(AdminStates.wait_for_reseller_master_key)
async def save_reseller_master_key(m: Message, state: FSMContext):
    set_setting("reseller_master_key", m.text.strip())
    await m.answer("✅ Master key updated.", reply_markup=admin_kb(), parse_mode='HTML')
    await state.clear()

@dp.callback_query(F.data == "reseller_edit_user_agent")
async def reseller_edit_user_agent(call: CallbackQuery, state: FSMContext):
    if call.from_user.id != ADMIN_ID: return
    await call.message.edit_text("🧭 Send the new <b>User-Agent</b> string:", reply_markup=admin_back_kb(), parse_mode='HTML')
    await state.set_state(AdminStates.wait_for_reseller_user_agent)

@dp.message(AdminStates.wait_for_reseller_user_agent)
async def save_reseller_user_agent(m: Message, state: FSMContext):
    set_setting("reseller_user_agent", m.text.strip())
    await m.answer("✅ User-Agent updated.", reply_markup=admin_kb(), parse_mode='HTML')
    await state.clear()

@dp.callback_query(F.data.startswith("delete_p_"))
async def admin_delete_product(call: CallbackQuery):
    if not _is_admin(call.from_user.id): return
    p_id = int(call.data.split("_")[2])
    db_query("DELETE FROM products WHERE id=?", (p_id,))
    db_query("DELETE FROM product_keys WHERE product_id=?", (p_id,))
    await call.answer("☢️ Nuclear wipe successful! Node and vault deleted.", show_alert=True)
    await admin_manage_prods(call)

@dp.callback_query(F.data.startswith("delkey_p_"))
async def admin_delete_key_start(call: CallbackQuery, state: FSMContext):
    if not _is_admin(call.from_user.id): return
    p_id = int(call.data.split("_")[2])
    await state.update_data(del_p_id=p_id)
    await call.message.edit_text("🗑 Send the <b>exact string match</b> of the key you wish to purge from the vault:", reply_markup=admin_back_kb(), parse_mode='HTML')
    await state.set_state(AdminStates.wait_for_delete_key)

@dp.message(AdminStates.wait_for_delete_key)
async def process_delete_key(m: Message, state: FSMContext):
    data = await state.get_data()
    p_id = data['del_p_id']
    key_to_delete = m.text.strip()
    key_data = db_query("SELECT id, is_used FROM product_keys WHERE product_id=? AND key_text=?", (p_id, key_to_delete), fetchone=True)
    if not key_data: return await m.answer("❌ Key not found. Check logs and try again.", reply_markup=admin_back_kb(), parse_mode='HTML')
    if key_data[1] == 1: return await m.answer("⚠️ Action Blocked: This key has already been dispatched to a user.", reply_markup=admin_back_kb(), parse_mode='HTML')
    db_query("DELETE FROM product_keys WHERE id=?", (key_data[0],))
    db_query("UPDATE products SET stock = stock - 1 WHERE id=?", (p_id,))
    await m.answer(f"✅ Key <code>{key_to_delete}</code> securely purged from vault.\n📦 Database indices updated.", reply_markup=admin_kb(), parse_mode='HTML')
    await state.clear()

# ==============================================================================
# 21. ADMIN TICKETS, BROADCAST, COUPONS
# ==============================================================================
@dp.callback_query(F.data == "admin_view_tickets")
async def admin_view_tickets(call: CallbackQuery):
    if not _is_admin(call.from_user.id): return
    tickets = db_query("SELECT id, user_id, message, created_at FROM tickets WHERE status='Open' LIMIT 1", fetchall=True)
    if not tickets: return await call.answer("✅ Zero pending issues. Grid is clean!", show_alert=True)
    t = tickets[0]
    text = (f"🎫 <b><u>ACTIVE TICKET #{t[0]}</u></b>\n👤 <b>Origin UID:</b> <code>{t[1]}</code>\n📅 <b>Timestamp:</b> {t[3]}\n\n📝 <b>Payload:</b>\n{t[2]}")
    kb = InlineKeyboardMarkup(inline_keyboard=[
        [InlineKeyboardButton(text="💬 Formulate Reply", callback_data=f"reply_ticket_{t[0]}_{t[1]}", style="primary")],
        [InlineKeyboardButton(text="❌ Force Close Ticket", callback_data=f"close_ticket_{t[0]}", style="danger")],
        [InlineKeyboardButton(text="Back to Admin", callback_data="admin_panel_back", icon_custom_emoji_id=get_emoji_icon("back"), style="danger")]
    ])
    await call.message.edit_text(text, reply_markup=kb, parse_mode='HTML')

@dp.callback_query(F.data.startswith("close_ticket_"))
async def close_ticket(call: CallbackQuery):
    ticket_id = call.data.split("_")[2]
    db_query("UPDATE tickets SET status='Closed' WHERE id=?", (ticket_id,))
    await call.answer("✅ Status set to Closed.", show_alert=True)
    await admin_view_tickets(call) 

@dp.callback_query(F.data.startswith("reply_ticket_"))
async def reply_ticket_start(call: CallbackQuery, state: FSMContext):
    data = call.data.split("_")
    ticket_id, user_id = data[2], data[3]
    await state.update_data(ticket_id=ticket_id, user_id=user_id)
    await call.message.edit_text(f"💬 Formulating reply for node <code>{user_id}</code>.\n\nType your message payload:", reply_markup=admin_back_kb(), parse_mode='HTML')
    await state.set_state(AdminStates.ticket_reply_msg)

@dp.message(AdminStates.ticket_reply_msg)
async def send_ticket_reply(m: Message, state: FSMContext):
    data = await state.get_data()
    try:
        await bot.send_message(data['user_id'], f"📞 <b>Admin Reply (Ref #{data['ticket_id']}):</b>\n\n{m.text}", parse_mode='HTML')
        db_query("UPDATE tickets SET status='Closed' WHERE id=?", (data['ticket_id'],))
        await m.answer("✅ Payload delivered and connection closed successfully.", reply_markup=admin_kb(), parse_mode='HTML')
    except Exception as e: await m.answer(f"❌ Transmission Error: {e}", reply_markup=admin_kb(), parse_mode='HTML')
    await state.clear()

@dp.callback_query(F.data == "admin_broadcast_btn")
async def admin_broadcast_start(call: CallbackQuery, state: FSMContext):
    if not _is_admin(call.from_user.id): return
    await call.message.edit_text("📢 <b>Mass Broadcast Protocol</b>\n\nSend the rich message payload you wish to transmit globally across the grid:", reply_markup=admin_back_kb(), parse_mode='HTML')
    await state.set_state(AdminStates.broadcast_msg)

@dp.callback_query(F.data == "admin_create_coupon")
async def admin_create_coupon_start(call: CallbackQuery, state: FSMContext):
    if not _is_admin(call.from_user.id): return
    await call.message.edit_text("🎟 Enter a highly secure alphanumeric sequence for the Promo Code:", reply_markup=admin_back_kb(), parse_mode='HTML')
    await state.set_state(AdminStates.add_coupon_code)

@dp.message(AdminStates.add_coupon_code)
async def admin_coupon_code(m: Message, state: FSMContext):
    await state.update_data(code=m.text.strip().upper())
    await m.answer("💰 Enter the monetary reward payload in <b>RUPEES (₹)</b>:", parse_mode='HTML')
    await state.set_state(AdminStates.add_coupon_amount)

@dp.message(AdminStates.add_coupon_amount)
async def admin_coupon_amount(m: Message, state: FSMContext):
    try:
        await state.update_data(amount=float(m.text)) 
        await m.answer("👥 Enter the exact maximum threshold uses for this code:", parse_mode='HTML')
        await state.set_state(AdminStates.add_coupon_uses)
    except ValueError: await m.answer("❌ Non-numerical data detected. Aborting.")

@dp.message(AdminStates.add_coupon_uses)
async def admin_coupon_uses(m: Message, state: FSMContext):
    try:
        uses = int(m.text)
        data = await state.get_data()
        db_query("INSERT OR REPLACE INTO coupons (code, amount, uses_left) VALUES (?, ?, ?)", (data['code'], data['amount'], uses))
        await m.answer(f"✅ Protocol <b>{data['code']}</b> encoded!\nReward Vector: {fmt_curr(data['amount'])}\nThreshold Limit: {uses} executions.", reply_markup=admin_kb(), parse_mode='HTML')
        await state.clear()
    except ValueError: await m.answer("❌ Non-numerical data detected. Aborting.")

# ==============================================================================
# 22. ADMIN RESELLER & SPIN SETTINGS
# ==============================================================================
@dp.callback_query(F.data == "admin_reseller_menu")
async def admin_reseller_menu(call: CallbackQuery):
    if not _is_admin(call.from_user.id): return
    status_check = db_query("SELECT value FROM settings WHERE key='reseller_system_status'", fetchone=True)
    sys_status = status_check[0] if status_check else "ON"
    kb = InlineKeyboardMarkup(inline_keyboard=[
        [InlineKeyboardButton(text="➕ Grant Reseller Rights", callback_data="reseller_make", style="success"), InlineKeyboardButton(text="➖ Revoke Reseller", callback_data="reseller_remove", style="danger")],
        [InlineKeyboardButton(text="📥 Reseller Requests (Approve)", callback_data="admin_rr_list", style="success")],
        [InlineKeyboardButton(text="📢 Reseller Broadcast", callback_data="admin_rbc_start", style="primary")],
        [InlineKeyboardButton(text="📋 Audit Active Resellers", callback_data="reseller_view", style="primary")],
        [InlineKeyboardButton(text=f"{'🟢' if sys_status == 'ON' else '🔴'} Auto-Upgrade System: {sys_status}", callback_data="admin_toggle_reseller_sys", style="success" if sys_status == 'ON' else "danger")], 
        [InlineKeyboardButton(text="Back to Admin", callback_data="admin_panel_back", icon_custom_emoji_id=get_emoji_icon("back"), style="danger")]
    ])
    await call.message.edit_text("👑 <b>Wholesale Reseller Protocols</b>\nSelect administrative action:", reply_markup=kb, parse_mode='HTML')

@dp.callback_query(F.data == "admin_toggle_reseller_sys")
async def toggle_reseller_sys(call: CallbackQuery):
    if not _is_admin(call.from_user.id): return
    res = db_query("SELECT value FROM settings WHERE key='reseller_system_status'", fetchone=True)
    current = res[0] if res else 'ON'
    new_status = 'OFF' if current == 'ON' else 'ON'
    db_query("INSERT OR REPLACE INTO settings (key, value) VALUES ('reseller_system_status', ?)", (new_status,))
    await admin_reseller_menu(call)

@dp.callback_query(F.data.in_(["reseller_make", "reseller_remove"]))
async def reseller_prompt_id(call: CallbackQuery, state: FSMContext):
    action = call.data
    await state.update_data(reseller_action=action)
    await call.message.edit_text("👤 Identify target node. Input <b>User ID</b> or <b>@username</b>:", reply_markup=admin_back_kb(), parse_mode='HTML')
    await state.set_state(AdminStates.reseller_manage_id)

@dp.message(AdminStates.reseller_manage_id)
async def process_reseller_manage(m: Message, state: FSMContext):
    data = await state.get_data()
    target = m.text.strip()
    if target.startswith('@'): target = target[1:]
    user_q = db_query("SELECT user_id, first_name FROM users WHERE user_id=? OR username=? COLLATE NOCASE", (target, target), fetchone=True)
    if not user_q: return await m.answer("❌ Target completely ghosted. Not in database.", reply_markup=admin_back_kb(), parse_mode='HTML')
    u_id, u_name = user_q[0], user_q[1]
    if data['reseller_action'] == "reseller_make":
        db_query("UPDATE users SET is_reseller=1, reseller_since=?, account_type='Reseller' WHERE user_id=?", (datetime.now().strftime("%Y-%m-%d"), u_id))
        await m.answer(f"✅ Credentials upgraded. <b>{u_name}</b> (<code>{u_id}</code>) has reseller rights.", reply_markup=admin_kb(), parse_mode='HTML')
    else:
        db_query("UPDATE users SET is_reseller=0, account_type='Regular' WHERE user_id=?", (u_id,))
        await m.answer(f"✅ Credentials revoked. <b>{u_name}</b> (<code>{u_id}</code>) is back to regular user.", reply_markup=admin_kb(), parse_mode='HTML')
    await state.clear()

@dp.callback_query(F.data == "reseller_view")
async def reseller_view(call: CallbackQuery):
    resellers = db_query("SELECT user_id, first_name, username FROM users WHERE is_reseller=1", fetchall=True)
    if not resellers: return await call.message.edit_text("📋 Zero active resellers found.", reply_markup=admin_back_kb(), parse_mode='HTML')
    text = "👑 <b><u>ACTIVE RESELLER AUDIT LOG</u></b> 👑\n━━━━━━━━━━━━━━━━━━\n"
    for r in resellers:
        uname = f"(@{r[2]})" if r[2] else ""
        text += f"👤 {r[1]} {uname}\n🆔 <code>{r[0]}</code>\n\n"
    await call.message.edit_text(text, reply_markup=admin_back_kb(), parse_mode='HTML')


@dp.callback_query(F.data == "admin_toggle_bot")
async def toggle_bot(call: CallbackQuery):
    if not _is_admin(call.from_user.id): return
    res = db_query("SELECT value FROM settings WHERE key='bot_status'", fetchone=True)
    current = res[0] if res else 'ON'
    new_status = 'OFF' if current == 'ON' else 'ON'
    db_query("INSERT OR REPLACE INTO settings (key, value) VALUES ('bot_status', ?)", (new_status,))
    await call.message.edit_reply_markup(reply_markup=admin_kb())


@dp.callback_query(F.data == "admin_set_video")
async def admin_set_video_start(call: CallbackQuery, state: FSMContext):
    if not _is_admin(call.from_user.id): return
    await call.message.edit_text("📹 Input direct streaming / YouTube Link for Tutorial system:\n<i>(Or type 'None' to clear registry):</i>\n<i>Tip: every UI text now has its own video link in Edit UI Texts.</i>", reply_markup=admin_back_kb(), parse_mode='HTML')
    await state.set_state(AdminStates.wait_for_howto_video)

@dp.message(AdminStates.wait_for_howto_video)
async def exec_set_video(m: Message, state: FSMContext):
    link = m.text.strip()
    db_query("INSERT OR REPLACE INTO settings (key, value) VALUES ('how_to_video', ?)", (link,))
    await m.answer("✅ Routing complete. Video linked.", reply_markup=admin_kb(), parse_mode='HTML')
    await state.clear()


@dp.callback_query(F.data == "admin_edit_emojis")
async def admin_edit_emojis(call: CallbackQuery):
    if not _is_admin(call.from_user.id): return
    rows = db_query("SELECT key, value FROM settings WHERE key LIKE 'emoji_%' ORDER BY key", fetchall=True) or []
    saved = {r[0].replace("emoji_", ""): r[1] for r in rows}
    all_slots = sorted(set(DEFAULT_EMOJIS.keys()) | set(saved.keys()))
    kb = InlineKeyboardMarkup(inline_keyboard=[])
    for slot in all_slots:
        current_id = saved.get(slot) or DEFAULT_EMOJIS.get(slot) or "Not set"
        row_icon = get_emoji_icon(slot)
        btn = InlineKeyboardButton(text=f"{slot} (ID: {current_id})", callback_data=f"edit_emoji_{slot}", style="primary")
        if row_icon:
            btn = btn.model_copy(update={"icon_custom_emoji_id": row_icon})
        kb.inline_keyboard.append([btn])
    kb.inline_keyboard.append([InlineKeyboardButton(text="Back to Admin", callback_data="admin_panel_back", icon_custom_emoji_id=get_emoji_icon("back"), style="danger")])
    await call.message.edit_text("🎨 <b>Edit All Emojis</b>\nChoose an emoji slot to change its ID:", reply_markup=kb, parse_mode='HTML')

@dp.callback_query(F.data.startswith("edit_emoji_"))
async def admin_edit_emoji_prompt(call: CallbackQuery, state: FSMContext):
    if not _is_admin(call.from_user.id): return
    slot = call.data.split("edit_emoji_", 1)[1]
    await state.update_data(emoji_slot=slot)
    current = get_setting(f"emoji_{slot}", "Not set")
    await call.message.edit_text(f"✏️ Send the <b>premium emoji</b> itself (or its numeric ID) for <b>{slot}</b>:\nCurrent: {current}\n(Leave empty to reset to default)", reply_markup=admin_back_kb(), parse_mode='HTML')
    await state.set_state(AdminStates.wait_for_emoji_slot)

@dp.message(AdminStates.wait_for_emoji_slot)
async def save_emoji_slot(m: Message, state: FSMContext):
    data = await state.get_data()
    slot = data['emoji_slot']
    new_id = (m.text or "").strip()
    for ent in (m.entities or []):
        if ent.type == "custom_emoji" and ent.custom_emoji_id:
            new_id = ent.custom_emoji_id
            break
    if new_id == "":
        db_query("DELETE FROM settings WHERE key=?", (f"emoji_{slot}",))
        await m.answer(f"✅ Reset emoji for '{slot}' to default.", reply_markup=admin_kb(), parse_mode='HTML')
    else:
        if not new_id.isdigit():
            await m.answer("❌ Invalid ID! Must be numeric.", reply_markup=admin_kb(), parse_mode='HTML')
            return
        set_setting(f"emoji_{slot}", new_id)
        await m.answer(f"✅ Emoji for '{slot}' updated to ID {new_id}.", reply_markup=admin_kb(), parse_mode='HTML')
    await state.clear()

@dp.callback_query(F.data == "admin_ui_style")
async def admin_ui_style_menu(call: CallbackQuery):
    if not _is_admin(call.from_user.id): return
    cur = get_ui_style()
    mode = get_emoji_mode()
    kb = InlineKeyboardMarkup(inline_keyboard=[
        [InlineKeyboardButton(text=("✅ " if cur == k else "") + name.split(" ", 1)[1], callback_data=f"admin_ui_set_{k}",
                              style="success" if cur == k else "primary")]
        for k, name in UI_STYLE_NAMES.items()
    ])
    kb.inline_keyboard.append([
        InlineKeyboardButton(text=("✅ " if mode == "premium" else "") + "Premium Emoji", callback_data="admin_emoji_mode_premium", style="success" if mode == "premium" else "primary"),
        InlineKeyboardButton(text=("✅ " if mode == "normal" else "") + "Normal Emoji", callback_data="admin_emoji_mode_normal", style="success" if mode == "normal" else "primary"),
    ])
    kb.inline_keyboard.append([InlineKeyboardButton(text="👁 Preview Start Menu", callback_data="admin_ui_preview", style="primary")])
    kb.inline_keyboard.append([InlineKeyboardButton(text="Back to Admin", callback_data="admin_panel_back", icon_custom_emoji_id=get_emoji_icon("back"), style="danger")])
    await call.message.edit_text(
        "🖌 <b>UI STYLE &amp; EMOJI MODE</b>\n\n"
        "<b>Style 1 — Premium Box:</b> decorative bold text, dividers, mixed button colours.\n"
        "<b>Style 2 — Clean Shop:</b> simple lines, all buttons green.\n"
        "<b>Style 3 — Dark Neon</b>, <b>Style 4 — Pastel Elegant</b>, <b>Style 5 — Minimal Pro</b>, <b>Style 6 — Bold Banner</b>.\n\n"
        f"Default style: <b>{UI_STYLE_NAMES[cur]}</b>\n"
        f"Default emoji: <b>{'Premium' if mode == 'premium' else 'Normal'}</b>\n\n"
        "These are the DEFAULTS. Every UI text can have its own style / emoji / video link in <b>Edit UI Texts</b>.",
        reply_markup=kb, parse_mode='HTML')

@dp.callback_query(F.data.startswith("admin_ui_set_"))
async def admin_ui_style_set(call: CallbackQuery):
    if not _is_admin(call.from_user.id): return
    k = call.data.rsplit("_", 1)[1]
    if k not in UI_THEMES:
        return await call.answer("Unknown style", show_alert=True)
    set_setting("ui_style", k)
    await call.answer(f"Style {k} activated")
    await admin_ui_style_menu(call)

@dp.callback_query(F.data.startswith("admin_emoji_mode_"))
async def admin_emoji_mode_set(call: CallbackQuery):
    if not _is_admin(call.from_user.id): return
    mode = call.data.rsplit("_", 1)[1]
    if mode not in ("premium", "normal"):
        return await call.answer("Unknown mode", show_alert=True)
    set_setting("emoji_mode", mode)
    _icon_cache.clear()
    await call.answer(f"{mode.title()} emoji mode ON")
    await admin_ui_style_menu(call)

@dp.callback_query(F.data == "admin_ui_preview")
async def admin_ui_preview(call: CallbackQuery):
    if not _is_admin(call.from_user.id): return
    await call.answer()
    await call.message.answer(get_ui_text("start_menu"), reply_markup=ui_attach_video(main_menu_kb(call.from_user.id), "start_menu"), parse_mode='HTML')

# ------------------------------------------------------------------------------
# EDIT UI TEXTS - every UI text has its OWN admin page:
#   style 1/2 | premium / normal emoji | edit text | YouTube link | preview | reset
# and the admin can create NEW UI texts (they become a button on the start menu).
# ------------------------------------------------------------------------------
def _ui_back_row(cb: str = "admin_edit_ui_menu", text: str = "Back"):
    return [InlineKeyboardButton(text=text, callback_data=cb, icon_custom_emoji_id=get_emoji_icon("back"), style="danger")]

def _ui_has_custom_text(key: str) -> bool:
    if key.startswith("cx_"):
        return True
    return bool(get_setting(f"ui_{get_ui_style(key)}_{key}", ""))

async def _safe_edit(call: CallbackQuery, text: str, kb: InlineKeyboardMarkup):
    try:
        await call.message.edit_text(text, reply_markup=kb, parse_mode='HTML', disable_web_page_preview=True)
    except Exception as e:
        if "not modified" not in str(e).lower():
            logger.warning(f"UI page edit failed: {e}")

@dp.callback_query(F.data == "admin_edit_ui_menu")
async def admin_edit_ui_menu(call: CallbackQuery):
    if not _is_admin(call.from_user.id): return
    kb = InlineKeyboardMarkup(inline_keyboard=[
        [InlineKeyboardButton(text="➕ Add New UI Text", callback_data="uitnew", style="success")]
    ])
    row = []
    for key, (label, _h) in ui_editable().items():
        marks = ""
        if key.startswith("cx_"): marks += " ⭐"
        if get_setting(f"ui_{get_ui_style(key)}_{key}", ""): marks += " ✏️"
        if ui_video_link(key): marks += " ▶️"
        row.append(InlineKeyboardButton(text=f"{label} · S{get_ui_style(key)}{marks}", callback_data=f"uitp_{key}", style="primary"))
        if len(row) == 2:
            kb.inline_keyboard.append(row); row = []
    if row: kb.inline_keyboard.append(row)
    kb.inline_keyboard.append(_ui_back_row("admin_panel_back", "Back to Admin"))
    await _safe_edit(call,
        "✏️ <b>Edit User Interface Texts</b>\n\n"
        "Tap any text to open its own admin page.\n"
        "S1 / S2 = its style  •  ✏️ = custom text  •  ▶️ = YouTube link  •  ⭐ = text you created",
        kb)

async def _ui_page(call: CallbackQuery, key: str):
    items = ui_editable()
    label, help_txt = items[key]
    style = get_ui_style(key)
    own_style = get_setting(f"uitext_style_{key}", "") in UI_THEMES
    own_mode = get_setting(f"uitext_emoji_{key}", "")
    link = ui_video_link(key)
    def mk(text, cb, active=False):
        return InlineKeyboardButton(text=("✅ " if active else "") + text, callback_data=cb, style="success" if active else "primary")
    style_btns = [mk(f"Style {k}", f"uits_{k}_{key}", own_style and style == k) for k in UI_THEMES]
    rows = [
        style_btns[:3],
        style_btns[3:] + [mk("Default", f"uitsd_{key}", not own_style)],
        [mk("Premium Emoji", f"uitm_premium_{key}", own_mode == "premium"), mk("Normal Emoji", f"uitm_normal_{key}", own_mode == "normal"), mk("Global", f"uitm_default_{key}", own_mode == "")],
        [mk("Edit Text", f"uite_{key}"), mk("Preview", f"uitw_{key}")],
        [mk("Set YouTube Link", f"uitv_{key}"), InlineKeyboardButton(text="Remove Link", callback_data=f"uitvx_{key}", style="danger")],
        [mk("Emoji Slots", f"uitl_{key}"), InlineKeyboardButton(text="Reset Text", callback_data=f"uitr_{key}", style="danger")],
    ]
    if key.startswith("cx_"):
        on = get_setting(f"uicustom_on_{key}", "1") == "1"
        rows.append([mk("Rename Button", f"uitn_{key}"), mk("Show on Menu", f"uitt_{key}", on)])
        rows.append([InlineKeyboardButton(text="Delete This Text", callback_data=f"uitd_{key}", style="danger")])
    rows.append(_ui_back_row())
    mode_txt = {"premium": "Premium", "normal": "Normal"}.get(own_mode, f"Global ({get_emoji_mode().title()})")
    await _safe_edit(call,
        f"📝 <b>{html_escape(label)}</b>\n\n"
        f"🖌 Style: <b>{UI_STYLE_NAMES[style]}</b> {'(own)' if own_style else '(default)'}\n"
        f"✨ Emoji: <b>{mode_txt}</b>\n"
        f"▶️ YouTube link: {html_escape(link) if link else '<i>not set</i>'}\n"
        f"✏️ Custom text: <b>{'yes' if _ui_has_custom_text(key) else 'no (built-in)'}</b>\n\n"
        f"Placeholders: <code>{html_escape(help_txt)}</code>",
        InlineKeyboardMarkup(inline_keyboard=rows))

@dp.callback_query(F.data.startswith("uitp_"))
async def admin_ui_text_page(call: CallbackQuery, state: FSMContext):
    if not _is_admin(call.from_user.id): return
    key = call.data[len("uitp_"):]
    if key not in ui_editable():
        return await call.answer("Unknown text", show_alert=True)
    await state.clear()
    await call.answer()
    await _ui_page(call, key)

@dp.callback_query(F.data.startswith("uits_"))
async def admin_ui_text_style(call: CallbackQuery):
    if not _is_admin(call.from_user.id): return
    style, _, key = call.data[len("uits_"):].partition("_")
    if style not in UI_THEMES or key not in ui_editable():
        return await call.answer("Unknown", show_alert=True)
    set_setting(f"uitext_style_{key}", style)
    await call.answer(f"Style {style} set for this text")
    await _ui_page(call, key)

@dp.callback_query(F.data.startswith("uitsd_"))
async def admin_ui_text_style_default(call: CallbackQuery):
    if not _is_admin(call.from_user.id): return
    key = call.data[len("uitsd_"):]
    if key not in ui_editable(): return await call.answer("Unknown", show_alert=True)
    db_query("DELETE FROM settings WHERE key=?", (f"uitext_style_{key}",))
    await call.answer("Using the default style")
    await _ui_page(call, key)

@dp.callback_query(F.data.startswith("uitm_"))
async def admin_ui_text_emoji_mode(call: CallbackQuery):
    if not _is_admin(call.from_user.id): return
    mode, _, key = call.data[len("uitm_"):].partition("_")
    if mode not in ("premium", "normal", "default") or key not in ui_editable():
        return await call.answer("Unknown", show_alert=True)
    if mode == "default":
        db_query("DELETE FROM settings WHERE key=?", (f"uitext_emoji_{key}",))
    else:
        set_setting(f"uitext_emoji_{key}", mode)
    await call.answer({"premium": "Premium emoji", "normal": "Normal emoji", "default": "Global emoji mode"}[mode])
    await _ui_page(call, key)

@dp.callback_query(F.data.startswith("uitl_"))
async def admin_ui_slots_list(call: CallbackQuery):
    if not _is_admin(call.from_user.id): return
    await call.answer()
    names = " ".join("{" + s + "}" for s in sorted(set(DEFAULT_EMOJIS) | set(NORMAL_EMOJI)))
    await call.message.answer(
        "🎨 <b>Emoji slots</b> - write any of these inside your text, it becomes that premium emoji "
        "(or the normal emoji when no premium ID is set):\n\n<code>" + html_escape(names) + "</code>\n\n"
        "You can also just send a premium emoji or a normal emoji directly in the text.", parse_mode='HTML')

# ---- edit the text itself
@dp.callback_query(F.data.startswith("uite_"))
async def admin_edit_ui_prompt(call: CallbackQuery, state: FSMContext):
    if not _is_admin(call.from_user.id): return
    key = call.data[len("uite_"):]
    items = ui_editable()
    if key not in items:
        return await call.answer("Unknown text", show_alert=True)
    style = get_ui_style(key)
    label, help_txt = items[key]
    current = get_setting(f"ui_{style}_{key}", "") or get_ui_default(key, style)
    await state.update_data(ui_key=key)
    kb = InlineKeyboardMarkup(inline_keyboard=[
        [InlineKeyboardButton(text="Reset to default", callback_data=f"uitr_{key}", style="danger")],
        _ui_back_row(f"uitp_{key}", "Cancel"),
    ])
    shown = current if len(current) < 2200 else current[:2200] + "\n…"
    await call.answer()
    await _safe_edit(call,
        f"📝 <b>{html_escape(label)}</b> — {UI_STYLE_NAMES[style]}\n\n"
        f"Send the new text (HTML / bold / premium emoji / normal emoji all allowed).\n"
        f"Placeholders: <code>{html_escape(help_txt)}</code>\n\n"
        f"Current template:\n<pre>{html_escape(shown)}</pre>", kb)
    await state.set_state(AdminStates.edit_ui_text)

@dp.callback_query(F.data.startswith("uitr_"))
async def admin_reset_ui_text(call: CallbackQuery, state: FSMContext):
    if not _is_admin(call.from_user.id): return
    key = call.data[len("uitr_"):]
    if key not in ui_editable(): return await call.answer("Unknown", show_alert=True)
    if key.startswith("cx_"):
        return await call.answer("This is your own text - use Edit Text to change it.", show_alert=True)
    db_query("DELETE FROM settings WHERE key=?", (f"ui_{get_ui_style(key)}_{key}",))
    await state.clear()
    await call.answer("Reset to default")
    await _ui_page(call, key)

@dp.message(AdminStates.edit_ui_text)
async def admin_save_ui_text(m: Message, state: FSMContext):
    data = await state.get_data()
    key = data.get('ui_key')
    if (m.text or "").strip() == "/cancel":
        await state.clear()
        return await m.answer("Cancelled.", reply_markup=admin_kb(), parse_mode='HTML')
    new_text = (m.html_text or "").strip()
    if key not in ui_editable() or not new_text:
        await state.clear()
        return await m.answer("❌ Nothing saved.", reply_markup=admin_kb(), parse_mode='HTML')
    if len(new_text) > 3500:
        return await m.answer("❌ Too long (max 3500 characters). Send a shorter text.", parse_mode='HTML')
    if key.startswith("cx_"):
        set_setting(f"uicustom_text_{key}", new_text)
        db_query("DELETE FROM settings WHERE key IN (?, ?)", (f"ui_1_{key}", f"ui_2_{key}"))
    else:
        set_setting(f"ui_{get_ui_style(key)}_{key}", new_text)
    await state.clear()
    await m.answer(f"✅ <b>{html_escape(ui_editable()[key][0])}</b> updated!",
                   reply_markup=InlineKeyboardMarkup(inline_keyboard=[_ui_back_row(f"uitp_{key}", "Back to this text")]), parse_mode='HTML')

# ---- YouTube / video link
@dp.callback_query(F.data.startswith("uitv_"))
async def admin_ui_video_prompt(call: CallbackQuery, state: FSMContext):
    if not _is_admin(call.from_user.id): return
    key = call.data[len("uitv_"):]
    if key not in ui_editable(): return await call.answer("Unknown", show_alert=True)
    await state.update_data(ui_key=key)
    await call.answer()
    await _safe_edit(call,
        f"▶️ <b>YouTube link for: {html_escape(ui_editable()[key][0])}</b>\n\n"
        "Send the video link. Users get a <b>Watch Video</b> button under this text.\n"
        "Optional button name: <code>https://youtu.be/xxxx | Watch Tutorial</code>\n\n"
        "Send <code>None</code> to remove the link.  /cancel to abort.",
        InlineKeyboardMarkup(inline_keyboard=[_ui_back_row(f"uitp_{key}", "Cancel")]))
    await state.set_state(AdminStates.edit_ui_video)

def _ui_video_remove(key: str) -> None:
    db_query("DELETE FROM settings WHERE key IN (?, ?)", (f"ui_video_{key}", f"ui_vidlabel_{key}"))
    if key == "tutorial":
        set_setting("how_to_video", "None")

@dp.callback_query(F.data.startswith("uitvx_"))
async def admin_ui_video_remove(call: CallbackQuery):
    if not _is_admin(call.from_user.id): return
    key = call.data[len("uitvx_"):]
    if key not in ui_editable(): return await call.answer("Unknown", show_alert=True)
    _ui_video_remove(key)
    await call.answer("Video link removed")
    await _ui_page(call, key)

@dp.message(AdminStates.edit_ui_video)
async def admin_save_ui_video(m: Message, state: FSMContext):
    data = await state.get_data()
    key = data.get('ui_key')
    raw = (m.text or "").strip()
    if raw == "/cancel" or key not in ui_editable():
        await state.clear()
        return await m.answer("Cancelled.", reply_markup=admin_kb(), parse_mode='HTML')
    back = InlineKeyboardMarkup(inline_keyboard=[_ui_back_row(f"uitp_{key}", "Back to this text")])
    if raw.lower() in ("none", "remove", "delete"):
        _ui_video_remove(key)
        await state.clear()
        return await m.answer("✅ Video link removed.", reply_markup=back, parse_mode='HTML')
    link, _, label = raw.partition("|")
    link, label = link.strip(), label.strip()
    if not re.match(r"^https?://\S+$", link):
        return await m.answer("❌ Send a valid link that starts with https://  (or /cancel)", parse_mode='HTML')
    set_setting(f"ui_video_{key}", link)
    if label:
        set_setting(f"ui_vidlabel_{key}", label[:30])
    else:
        db_query("DELETE FROM settings WHERE key=?", (f"ui_vidlabel_{key}",))
    await state.clear()
    await m.answer("✅ <b>YouTube link saved.</b> The Watch Video button now shows under this text.", reply_markup=back, parse_mode='HTML')

# ---- preview
@dp.callback_query(F.data.startswith("uitw_"))
async def admin_ui_preview_text(call: CallbackQuery):
    if not _is_admin(call.from_user.id): return
    key = call.data[len("uitw_"):]
    if key not in ui_editable(): return await call.answer("Unknown", show_alert=True)
    await call.answer()
    kb = ui_attach_video(InlineKeyboardMarkup(inline_keyboard=[[InlineKeyboardButton(text="BACK", callback_data=f"uitp_{key}", style="danger")]]), key)
    try:
        await call.message.answer(get_ui_text(key, **UI_SAMPLE).strip() or "—", reply_markup=kb, parse_mode='HTML')
    except Exception as e:
        await call.message.answer(f"❌ Preview failed - check your HTML tags.\n<code>{html_escape(str(e))[:300]}</code>", parse_mode='HTML')

# ---- create / rename / show-hide / delete the admin's own UI texts
@dp.callback_query(F.data == "uitnew")
async def admin_ui_new(call: CallbackQuery, state: FSMContext):
    if not _is_admin(call.from_user.id): return
    await call.answer()
    await _safe_edit(call,
        "➕ <b>New UI Text</b>\n\nStep 1/2 — send the <b>button name</b> users will see on the start menu.\n"
        "Example: <code>🎬 Movie Zone</code>   (max 30 characters)\n\n/cancel to abort.",
        InlineKeyboardMarkup(inline_keyboard=[_ui_back_row("admin_edit_ui_menu", "Cancel")]))
    await state.set_state(AdminStates.new_ui_label)

@dp.message(AdminStates.new_ui_label)
async def admin_ui_new_label(m: Message, state: FSMContext):
    raw = (m.text or "").strip()
    if raw == "/cancel":
        await state.clear()
        return await m.answer("Cancelled.", reply_markup=admin_kb(), parse_mode='HTML')
    if not raw or len(raw) > 30:
        return await m.answer("❌ Send a button name (1-30 characters).", parse_mode='HTML')
    await state.update_data(new_label=raw)
    await m.answer("Step 2/2 — now send the <b>text</b> users will see when they tap that button.\n"
                   "HTML / bold / premium emoji / YouTube link text all allowed.\n\n/cancel to abort.", parse_mode='HTML')
    await state.set_state(AdminStates.new_ui_text)

@dp.message(AdminStates.new_ui_text)
async def admin_ui_new_text(m: Message, state: FSMContext):
    if (m.text or "").strip() == "/cancel":
        await state.clear()
        return await m.answer("Cancelled.", reply_markup=admin_kb(), parse_mode='HTML')
    body = (m.html_text or "").strip()
    if not body or len(body) > 3500:
        return await m.answer("❌ Send the text (max 3500 characters).", parse_mode='HTML')
    data = await state.get_data()
    key = f"cx_{int(time.time())}"
    keys = ui_custom_keys() + [key]
    set_setting("ui_custom_keys", ",".join(keys))
    set_setting(f"uicustom_label_{key}", data.get("new_label", "Page"))
    set_setting(f"uicustom_text_{key}", body)
    set_setting(f"uicustom_on_{key}", "1")
    await state.clear()
    await m.answer("✅ <b>New UI text created!</b> It is now a button on the start menu.\n"
                   "Open it from the list to set its style, emoji mode or YouTube link.",
                   reply_markup=InlineKeyboardMarkup(inline_keyboard=[
                       [InlineKeyboardButton(text="Open its admin page", callback_data=f"uitp_{key}", style="success")],
                       _ui_back_row("admin_edit_ui_menu", "UI Texts list")]), parse_mode='HTML')

@dp.callback_query(F.data.startswith("uitn_"))
async def admin_ui_rename_prompt(call: CallbackQuery, state: FSMContext):
    if not _is_admin(call.from_user.id): return
    key = call.data[len("uitn_"):]
    if key not in ui_custom_keys(): return await call.answer("Unknown", show_alert=True)
    await state.update_data(ui_key=key)
    await call.answer()
    await _safe_edit(call, "✏️ Send the new <b>button name</b> (max 30 characters).  /cancel to abort.",
                     InlineKeyboardMarkup(inline_keyboard=[_ui_back_row(f"uitp_{key}", "Cancel")]))
    await state.set_state(AdminStates.edit_ui_label)

@dp.message(AdminStates.edit_ui_label)
async def admin_ui_rename_save(m: Message, state: FSMContext):
    data = await state.get_data()
    key = data.get("ui_key")
    raw = (m.text or "").strip()
    if raw == "/cancel" or key not in ui_custom_keys():
        await state.clear()
        return await m.answer("Cancelled.", reply_markup=admin_kb(), parse_mode='HTML')
    if not raw or len(raw) > 30:
        return await m.answer("❌ Send a button name (1-30 characters).", parse_mode='HTML')
    set_setting(f"uicustom_label_{key}", raw)
    await state.clear()
    await m.answer("✅ Button renamed.", reply_markup=InlineKeyboardMarkup(inline_keyboard=[_ui_back_row(f"uitp_{key}", "Back to this text")]), parse_mode='HTML')

@dp.callback_query(F.data.startswith("uitt_"))
async def admin_ui_toggle_visible(call: CallbackQuery):
    if not _is_admin(call.from_user.id): return
    key = call.data[len("uitt_"):]
    if key not in ui_custom_keys(): return await call.answer("Unknown", show_alert=True)
    on = get_setting(f"uicustom_on_{key}", "1") == "1"
    set_setting(f"uicustom_on_{key}", "0" if on else "1")
    await call.answer("Hidden from menu" if on else "Shown on menu")
    await _ui_page(call, key)

@dp.callback_query(F.data.startswith("uitd_"))
async def admin_ui_delete_ask(call: CallbackQuery):
    if not _is_admin(call.from_user.id): return
    key = call.data[len("uitd_"):]
    if key not in ui_custom_keys(): return await call.answer("Unknown", show_alert=True)
    await call.answer()
    await _safe_edit(call, f"🗑 Delete <b>{html_escape(ui_editable()[key][0])}</b> for ever?",
                     InlineKeyboardMarkup(inline_keyboard=[
                         [InlineKeyboardButton(text="Yes, delete", callback_data=f"uitdy_{key}", style="danger")],
                         _ui_back_row(f"uitp_{key}", "No, keep it")]))

@dp.callback_query(F.data.startswith("uitdy_"))
async def admin_ui_delete_yes(call: CallbackQuery):
    if not _is_admin(call.from_user.id): return
    key = call.data[len("uitdy_"):]
    if key not in ui_custom_keys(): return await call.answer("Unknown", show_alert=True)
    set_setting("ui_custom_keys", ",".join(k for k in ui_custom_keys() if k != key))
    for sk in (f"uicustom_label_{key}", f"uicustom_text_{key}", f"uicustom_on_{key}", f"ui_1_{key}", f"ui_2_{key}",
               f"uitext_style_{key}", f"uitext_emoji_{key}", f"ui_video_{key}", f"ui_vidlabel_{key}"):
        db_query("DELETE FROM settings WHERE key=?", (sk,))
    await call.answer("Deleted")
    await admin_edit_ui_menu(call)

@dp.callback_query(F.data == "admin_edit_reseller_price")
async def admin_edit_reseller_price_start(call: CallbackQuery, state: FSMContext):
    if not _is_admin(call.from_user.id): return
    prods = db_query("SELECT id, name, category, panel_name, reseller_price FROM products ORDER BY category, panel_name", fetchall=True)
    if not prods: return await call.message.edit_text("📭 No products to edit.", reply_markup=admin_back_kb(), parse_mode='HTML')
    kb = InlineKeyboardMarkup(inline_keyboard=[])
    for p in prods:
        panel_name = p[3] if p[3] is not None else ""
        r_price = safe_float(p[4])
        kb.inline_keyboard.append([InlineKeyboardButton(text=f"{p[2]} - {panel_name} - {p[1]} (₹{r_price:.2f})", callback_data=f"edit_reseller_{p[0]}", style="primary")])
    kb.inline_keyboard.append([InlineKeyboardButton(text="Back to Admin", callback_data="admin_panel_back", icon_custom_emoji_id=get_emoji_icon("back"), style="danger")])
    await call.message.edit_text("👑 <b>Edit Reseller Price per Product</b>\nSelect a product to change its wholesale price:", reply_markup=kb, parse_mode='HTML')

@dp.callback_query(F.data.startswith("edit_reseller_"))
async def admin_edit_reseller_price_prompt(call: CallbackQuery, state: FSMContext):
    if not _is_admin(call.from_user.id): return
    prod_id = int(call.data.split("_")[2])
    await state.update_data(edit_reseller_prod_id=prod_id)
    await call.message.edit_text("💰 Enter the new <b>Reseller Price</b> in Rupees (₹) for this product:", reply_markup=admin_back_kb(), parse_mode='HTML')
    await state.set_state(AdminStates.edit_reseller_price)

@dp.message(AdminStates.edit_reseller_price)
async def admin_save_reseller_price(m: Message, state: FSMContext):
    try:
        new_price = float(m.text)
        data = await state.get_data()
        prod_id = data['edit_reseller_prod_id']
        db_query("UPDATE products SET reseller_price=? WHERE id=?", (new_price, prod_id))
        await m.answer(f"✅ Reseller price updated to {fmt_curr(new_price)} for product ID {prod_id}.", reply_markup=admin_kb(), parse_mode='HTML')
        await state.clear()
    except ValueError: await m.answer("❌ Invalid number. Please enter a valid price.")

@dp.callback_query(F.data == "admin_set_reseller_fee")
async def admin_set_reseller_fee(call: CallbackQuery, state: FSMContext):
    if not _is_admin(call.from_user.id): return
    await call.message.edit_text("💰 Enter the new <b>Reseller Setup Fee</b> in Rupees (₹):\nCurrent: " + get_setting("reseller_setup_fee", "200.0"), reply_markup=admin_back_kb(), parse_mode='HTML')
    await state.set_state(AdminStates.wait_for_reseller_setup_fee)

@dp.message(AdminStates.wait_for_reseller_setup_fee)
async def admin_save_reseller_fee(m: Message, state: FSMContext):
    try:
        fee = float(m.text)
        set_setting("reseller_setup_fee", str(fee))
        await m.answer(f"✅ Reseller setup fee updated to {fmt_curr(fee)}.", reply_markup=admin_kb(), parse_mode='HTML')
        await state.clear()
    except ValueError: await m.answer("❌ Invalid number. Please enter a valid amount.")

@dp.callback_query(F.data == "admin_set_reseller_min")
async def admin_set_reseller_min(call: CallbackQuery, state: FSMContext):
    if not _is_admin(call.from_user.id): return
    await call.message.edit_text("💳 Enter the new <b>Minimum Balance</b> required to become reseller (₹):\nCurrent: " + get_setting("reseller_min_balance", "500.0"), reply_markup=admin_back_kb(), parse_mode='HTML')
    await state.set_state(AdminStates.wait_for_reseller_min_balance)

@dp.message(AdminStates.wait_for_reseller_min_balance)
async def admin_save_reseller_min(m: Message, state: FSMContext):
    try:
        min_bal = float(m.text)
        set_setting("reseller_min_balance", str(min_bal))
        await m.answer(f"✅ Minimum reseller balance updated to {fmt_curr(min_bal)}.", reply_markup=admin_kb(), parse_mode='HTML')
        await state.clear()
    except ValueError: await m.answer("❌ Invalid number. Please enter a valid amount.")

@dp.callback_query(F.data == "admin_set_support_links")
async def admin_set_support_links(call: CallbackQuery, state: FSMContext):
    if not _is_admin(call.from_user.id): return
    kb = InlineKeyboardMarkup(inline_keyboard=[
        [InlineKeyboardButton(text="📞 Set Telegram Link", callback_data="admin_set_telegram", style="primary")],
        [InlineKeyboardButton(text="📱 Set WhatsApp Link", callback_data="admin_set_whatsapp", style="primary")],
        [InlineKeyboardButton(text="Back to Admin", callback_data="admin_panel_back", icon_custom_emoji_id=get_emoji_icon("back"), style="danger")]
    ])
    await call.message.edit_text("📌 <b>Support Contact Links</b>\nSet the URLs for Telegram and WhatsApp support:", reply_markup=kb, parse_mode='HTML')

@dp.callback_query(F.data == "admin_set_telegram")
async def admin_set_telegram(call: CallbackQuery, state: FSMContext):
    if not _is_admin(call.from_user.id): return
    await call.message.edit_text("✈️ Enter the Telegram contact URL (e.g., https://t.me/YourSupport):", reply_markup=admin_back_kb(), parse_mode='HTML')
    await state.set_state(AdminStates.wait_for_support_telegram)

@dp.message(AdminStates.wait_for_support_telegram)
async def save_telegram_link(m: Message, state: FSMContext):
    link = m.text.strip()
    set_setting("support_telegram", link)
    await m.answer("✅ Telegram support link updated!", reply_markup=admin_kb(), parse_mode='HTML')
    await state.clear()

@dp.callback_query(F.data == "admin_set_whatsapp")
async def admin_set_whatsapp(call: CallbackQuery, state: FSMContext):
    if not _is_admin(call.from_user.id): return
    await call.message.edit_text("📱 Enter the WhatsApp contact URL (e.g., https://wa.me/1234567890):", reply_markup=admin_back_kb(), parse_mode='HTML')
    await state.set_state(AdminStates.wait_for_support_whatsapp)

@dp.message(AdminStates.wait_for_support_whatsapp)
async def save_whatsapp_link(m: Message, state: FSMContext):
    link = m.text.strip()
    set_setting("support_whatsapp", link)
    await m.answer("✅ WhatsApp support link updated!", reply_markup=admin_kb(), parse_mode='HTML')
    await state.clear()

@dp.callback_query(F.data == "admin_set_category_emojis")
async def admin_set_category_emojis(call: CallbackQuery, state: FSMContext):
    if not _is_admin(call.from_user.id): return
    kb = InlineKeyboardMarkup(inline_keyboard=[])
    for cat in FIXED_CATEGORIES:
        current = get_setting(f"cat_emoji_{cat}", "Not set")
        btn = InlineKeyboardButton(text=f"{cat} (ID: {current})", callback_data=f"set_cat_emoji_{cat}", style="primary")
        if get_category_emoji(cat):
            btn = btn.model_copy(update={"icon_custom_emoji_id": get_category_emoji(cat)})
        kb.inline_keyboard.append([btn])
    kb.inline_keyboard.append([InlineKeyboardButton(text="Back to Admin", callback_data="admin_panel_back", icon_custom_emoji_id=get_emoji_icon("back"), style="danger")])
    await call.message.edit_text("🎨 <b>Set Category Emojis</b>\nChoose a category to set its custom emoji ID:", reply_markup=kb, parse_mode='HTML')

@dp.callback_query(F.data.startswith("set_cat_emoji_"))
async def admin_set_category_emoji_prompt(call: CallbackQuery, state: FSMContext):
    if not _is_admin(call.from_user.id): return
    category = call.data.split("set_cat_emoji_", 1)[1]
    await state.update_data(cat_emoji_category=category)
    await call.message.edit_text(f"🎨 Enter the emoji ID for <b>{category}</b>:\n(Leave empty to reset to default)", reply_markup=admin_back_kb(), parse_mode='HTML')
    await state.set_state(AdminStates.wait_for_category_emoji)

@dp.message(AdminStates.wait_for_category_emoji)
async def save_category_emoji(m: Message, state: FSMContext):
    data = await state.get_data()
    category = data['cat_emoji_category']
    emoji_id = m.text.strip()
    if emoji_id == "":
        db_query("DELETE FROM settings WHERE key=?", (f"cat_emoji_{category}",))
        await m.answer(f"✅ Reset emoji for {category} to default.", reply_markup=admin_kb(), parse_mode='HTML')
    else:
        if not emoji_id.isdigit():
            await m.answer("❌ Invalid ID! Must be numeric.", reply_markup=admin_kb(), parse_mode='HTML')
            return
        set_setting(f"cat_emoji_{category}", emoji_id)
        await m.answer(f"✅ Emoji set for {category} successfully!", reply_markup=admin_kb(), parse_mode='HTML')
    await state.clear()

@dp.callback_query(F.data == "admin_set_panel_emojis")
async def admin_set_panel_emojis(call: CallbackQuery):
    if not _is_admin(call.from_user.id): return
    panels = db_query("SELECT DISTINCT panel_name FROM products WHERE panel_name != '' ORDER BY panel_name", fetchall=True)
    if not panels:
        await call.message.edit_text("📭 No panel names found in products.", reply_markup=admin_back_kb(), parse_mode='HTML')
        return
    kb = InlineKeyboardMarkup(inline_keyboard=[])
    for p in panels:
        panel = p[0]
        current = get_setting(f"panel_emoji_{panel}", "Not set")
        btn = InlineKeyboardButton(text=f"{panel} (ID: {current})", callback_data=f"set_panel_emoji_{panel}", style="primary")
        if get_panel_emoji(panel):
            btn = btn.model_copy(update={"icon_custom_emoji_id": get_panel_emoji(panel)})
        kb.inline_keyboard.append([btn])
    kb.inline_keyboard.append([InlineKeyboardButton(text="Back to Admin", callback_data="admin_panel_back", icon_custom_emoji_id=get_emoji_icon("back"), style="danger")])
    await call.message.edit_text("🖼 <b>Set Panel Emojis</b>\nChoose a panel name to set its custom emoji ID:", reply_markup=kb, parse_mode='HTML')

@dp.callback_query(F.data.startswith("set_panel_emoji_"))
async def admin_set_panel_emoji_prompt(call: CallbackQuery, state: FSMContext):
    if not _is_admin(call.from_user.id): return
    panel_name = call.data.split("set_panel_emoji_", 1)[1]
    await state.update_data(panel_emoji_name=panel_name)
    await call.message.edit_text(f"🎨 Enter the emoji ID for panel <b>{panel_name}</b>:\n(Leave empty to reset to default)", reply_markup=admin_back_kb(), parse_mode='HTML')
    await state.set_state(AdminStates.wait_for_panel_emoji_id)

@dp.message(AdminStates.wait_for_panel_emoji_id)
async def save_panel_emoji(m: Message, state: FSMContext):
    data = await state.get_data()
    panel_name = data['panel_emoji_name']
    emoji_id = m.text.strip()
    if emoji_id == "":
        db_query("DELETE FROM settings WHERE key=?", (f"panel_emoji_{panel_name}",))
        await m.answer(f"✅ Reset emoji for panel '{panel_name}'.", reply_markup=admin_kb(), parse_mode='HTML')
    else:
        if not emoji_id.isdigit():
            await m.answer("❌ Invalid ID! Must be numeric.", reply_markup=admin_kb(), parse_mode='HTML')
            return
        set_setting(f"panel_emoji_{panel_name}", emoji_id)
        await m.answer(f"✅ Emoji set for panel '{panel_name}'!", reply_markup=admin_kb(), parse_mode='HTML')
    await state.clear()

# ==============================================================================
# 23. ADMIN PAYMENT GATEWAY (SGVIP) SETUP
# ==============================================================================
@dp.callback_query(F.data == "admin_setup_sgvip")
async def setup_sgvip_start(call: CallbackQuery, state: FSMContext):
    if call.from_user.id != ADMIN_ID: return
    current_token = get_setting("sgvip_token", "Not set")
    await call.message.edit_text(
        f"⚙️ <b>SGVIP PAYMENT GATEWAY SETUP</b>\n\n"
        f"🔑 Current API Token: {current_token[:8] if current_token != 'Not set' else 'Not set'}... (hidden)\n\n"
        f"Send the new <b>SGVIP API Token</b>:\n<i>(Type /cancel to abort)</i>",
        reply_markup=admin_back_kb(), parse_mode='HTML'
    )
    await state.set_state(AdminStates.wait_for_sgvip_token)

@dp.message(AdminStates.wait_for_sgvip_token)
async def setup_sgvip_token(m: Message, state: FSMContext):
    if m.text == '/cancel':
        await state.clear()
        return await m.answer("Sequence killed.", reply_markup=admin_kb(), parse_mode='HTML')
    token = m.text.strip()
    if len(token) < 8:
        return await m.answer("❌ Invalid API Token! Please send a valid token.", parse_mode='HTML')
    set_setting("sgvip_token", token)
    await m.answer(f"✅ <b>SGVIP Payment Gateway configured successfully!</b>\n\n🔑 API Token: Saved\n\nGateway is now ready for payments.", reply_markup=admin_kb(), parse_mode='HTML')
    await state.clear()

# ==============================================================================
# 24. ADMIN BINANCE SETUP
# ==============================================================================
@dp.callback_query(F.data == "admin_setup_binance")
async def setup_binance_start(call: CallbackQuery, state: FSMContext):
    if call.from_user.id != ADMIN_ID: return
    await call.message.edit_text("🪙 <b>CRYPTO NODE INIT: Step 1/3</b>\nInput Master <b>Binance API Key</b>:\n<i>(Type /cancel to halt protocol)</i>", reply_markup=admin_back_kb(), parse_mode='HTML')
    await state.set_state(AdminStates.wait_for_binance_api)

@dp.message(AdminStates.wait_for_binance_api)
async def setup_binance_api(m: Message, state: FSMContext):
    if m.text == '/cancel':
        await state.clear()
        return await m.answer("Sequence aborted.", reply_markup=admin_kb(), parse_mode='HTML')
    set_setting("binance_api", m.text.strip())
    await m.answer("🪙 <b>CRYPTO NODE INIT: Step 2/3</b>\nNow inject the highly secure <b>Binance Secret Key</b>:", parse_mode='HTML')
    await state.set_state(AdminStates.wait_for_binance_secret)

@dp.message(AdminStates.wait_for_binance_secret)
async def setup_binance_secret(m: Message, state: FSMContext):
    set_setting("binance_secret", m.text.strip())
    await m.answer("🪙 <b>CRYPTO NODE INIT: Step 3/3</b>\nFinal variable: Set the public <b>USDT Deposit Address (TRC20/BEP20)</b>\nUsers will broadcast to this ledger:", parse_mode='HTML')
    await state.set_state(AdminStates.wait_for_binance_address)

@dp.message(AdminStates.wait_for_binance_address)
async def setup_binance_address(m: Message, state: FSMContext):
    db_query("INSERT OR REPLACE INTO settings (key, value) VALUES ('binance_address', ?)", (m.text.strip(),))
    await m.answer("✅ <b>Blockchain node synchronized.</b> Crypto gateway is fully armed.", reply_markup=admin_kb(), parse_mode='HTML')
    await state.clear()

# ==============================================================================
# 24B. REFERRAL, LUDO SPIN & DOWNLOAD FILES
# ==============================================================================
SPIN_COOLDOWN = 24 * 60 * 60  # one free spin every 24 hours

def _fmt_wait(seconds: float) -> str:
    seconds = max(0, int(seconds))
    return f"{seconds // 3600}h {seconds % 3600 // 60}m"

def _spin_seconds_left(user_id: int) -> float:
    row = db_query("SELECT last_spin FROM users WHERE user_id=?", (user_id,), fetchone=True)
    try:
        last = float(row[0]) if row and row[0] else 0.0
    except (ValueError, TypeError):
        last = 0.0
    return max(0.0, last + SPIN_COOLDOWN - time.time())

def _claim_spin(user_id: int) -> bool:
    """Atomically claim today's spin. Returns False if the cooldown is still running."""
    now_ts = time.time()
    conn = sqlite3.connect(DB_FILE)
    try:
        cur = conn.execute(
            "UPDATE users SET last_spin=? WHERE user_id=? AND "
            "(last_spin IS NULL OR last_spin='' OR CAST(last_spin AS REAL) <= ?)",
            (str(now_ts), user_id, now_ts - SPIN_COOLDOWN))
        conn.commit()
        return cur.rowcount == 1
    except Exception as e:
        logger.error(f"Spin claim error: {e}")
        return False
    finally:
        conn.close()

# ---------------------------- REFERRAL ----------------------------------------
@dp.callback_query(F.data == "menu_referral")
async def referral_dashboard(call: CallbackQuery):
    uid = call.from_user.id
    row = db_query("SELECT referral_earned FROM users WHERE user_id=?", (uid,), fetchone=True)
    earned = safe_float(row[0]) if row else 0.0
    cnt_row = db_query("SELECT COUNT(*) FROM users WHERE referred_by=?", (uid,), fetchone=True)
    count = cnt_row[0] if cnt_row else 0
    pct = get_setting("referral_percent", "5")
    link = f"https://t.me/{BOT_USERNAME.lstrip('@')}?start=ref_{uid}"
    share = "https://t.me/share/url?" + urllib.parse.urlencode({"url": link, "text": "Join this store and get premium keys instantly!"})
    text = get_ui_text("referral", v_pct=pct, v_link=link, v_count=count, v_earned=fmt_curr(earned))
    kb = InlineKeyboardMarkup(inline_keyboard=[
        [InlineKeyboardButton(text="📤 Share Link", url=share, style="success")],
        [InlineKeyboardButton(text="BACK", callback_data="back_main", icon_custom_emoji_id=get_emoji_icon("back"), style="danger")]
    ])
    ui_attach_video(kb, "referral")
    await call.message.edit_text(text, reply_markup=kb, parse_mode='HTML', disable_web_page_preview=True)

# ---------------------------- LUDO SPIN ---------------------------------------
@dp.callback_query(F.data == "menu_spin")
async def spin_menu(call: CallbackQuery):
    left = _spin_seconds_left(call.from_user.id)
    rewards = [r[0] for r in (db_query("SELECT amount FROM spin_rewards", fetchall=True) or [])]
    top = fmt_curr(max(rewards)) if rewards else fmt_curr(0)
    kb = InlineKeyboardMarkup(inline_keyboard=[])
    if left <= 0:
        status = f"{get_emoji('check_icon')} <b>Your spin is ready!</b>"
        kb.inline_keyboard.append([InlineKeyboardButton(text="🎲 SPIN NOW", callback_data="do_spin", style="success")])
    else:
        status = f"{get_emoji('info_icon')} <b>Next spin in:</b> {_fmt_wait(left)}"
    text = get_ui_text("spin", v_top=top, v_status=status)
    kb.inline_keyboard.append([InlineKeyboardButton(text="BACK", callback_data="back_main", icon_custom_emoji_id=get_emoji_icon("back"), style="danger")])
    ui_attach_video(kb, "spin")
    await call.message.edit_text(text, reply_markup=kb, parse_mode='HTML')

@dp.callback_query(F.data == "do_spin")
async def do_spin(call: CallbackQuery):
    uid = call.from_user.id
    if not _claim_spin(uid):
        return await call.answer(f"⏳ Next spin in {_fmt_wait(_spin_seconds_left(uid))}", show_alert=True)
    await call.answer()
    rewards = [r[0] for r in (db_query("SELECT amount FROM spin_rewards", fetchall=True) or [])] or [0, 1, 2, 5]
    amount = safe_float(random.choice(rewards))
    if amount > 0:
        db_query("UPDATE users SET balance = balance + ? WHERE user_id=?", (amount, uid))
    log_activity(uid, "LUDO_SPIN", f"Won {amount}")
    chat_id = call.message.chat.id
    try:
        await bot.send_dice(chat_id, emoji="🎲")
        await asyncio.sleep(4)
    except Exception:
        pass
    bal_row = db_query("SELECT balance FROM users WHERE user_id=?", (uid,), fetchone=True)
    bal = safe_float(bal_row[0]) if bal_row else 0.0
    head = f"🎉 <b>YOU WON {fmt_curr(amount)}!</b>" if amount > 0 else "😅 <b>Better luck next time!</b>"
    await bot.send_message(chat_id, f"{head}\n\n💰 <b>Balance:</b> {fmt_curr(bal)}\n⏳ Come back in 24 hours.",
                           reply_markup=back_kb(), parse_mode='HTML')

# ---------------------------- DOWNLOAD FILES ----------------------------------
@dp.callback_query(F.data == "menu_files")
async def files_menu(call: CallbackQuery):
    rows = db_query("SELECT id, title FROM bot_files ORDER BY id DESC", fetchall=True) or []
    if not rows:
        return await call.answer("📭 No files uploaded yet.", show_alert=True)
    kb = InlineKeyboardMarkup(inline_keyboard=[])
    for fid, title in rows:
        kb.inline_keyboard.append([InlineKeyboardButton(text=f"📥 {title[:40]}", callback_data=f"dlfile_{fid}", style="primary")])
    kb.inline_keyboard.append([InlineKeyboardButton(text="BACK", callback_data="back_main", icon_custom_emoji_id=get_emoji_icon("back"), style="danger")])
    ui_attach_video(kb, "files")
    await call.message.edit_text(get_ui_text("files"), reply_markup=kb, parse_mode='HTML')

@dp.callback_query(F.data.startswith("dlfile_"))
async def send_file(call: CallbackQuery):
    fid = call.data.split("_", 1)[1]
    row = db_query("SELECT title, file_id, file_type FROM bot_files WHERE id=?", (fid,), fetchone=True) if fid.isdigit() else None
    if not row:
        return await call.answer("File not found.", show_alert=True)
    await call.answer("📤 Sending...")
    title, file_id, ftype = row
    cap = f"📥 <b>{html_escape(title)}</b>"
    try:
        if ftype == "video": await bot.send_video(call.message.chat.id, file_id, caption=cap, parse_mode='HTML')
        elif ftype == "audio": await bot.send_audio(call.message.chat.id, file_id, caption=cap, parse_mode='HTML')
        else: await bot.send_document(call.message.chat.id, file_id, caption=cap, parse_mode='HTML')
    except Exception as e:
        logger.error(f"File send error: {e}")
        await call.message.answer("⚠️ Could not send this file. Please contact support.")

# ---------------------------- ADMIN: FILES / SPIN / REFERRAL ------------------
@dp.callback_query(F.data == "admin_files")
async def admin_files_menu(call: CallbackQuery):
    if not _is_admin(call.from_user.id): return
    rows = db_query("SELECT id, title FROM bot_files ORDER BY id DESC", fetchall=True) or []
    kb = InlineKeyboardMarkup(inline_keyboard=[])
    for fid, title in rows:
        kb.inline_keyboard.append([InlineKeyboardButton(text=f"🗑 {title[:40]}", callback_data=f"admin_delfile_{fid}", style="danger")])
    kb.inline_keyboard.append([InlineKeyboardButton(text="➕ Upload File", callback_data="admin_add_file", style="success")])
    kb.inline_keyboard.append([InlineKeyboardButton(text="Back to Admin", callback_data="admin_panel_back", icon_custom_emoji_id=get_emoji_icon("back"), style="danger")])
    await call.message.edit_text("📥 <b>DOWNLOAD FILES</b>\nTap 🗑 to delete a file.", reply_markup=kb, parse_mode='HTML')

@dp.callback_query(F.data.startswith("admin_delfile_"))
async def admin_delete_file(call: CallbackQuery):
    if not _is_admin(call.from_user.id): return
    fid = call.data.rsplit("_", 1)[1]
    if fid.isdigit():
        db_query("DELETE FROM bot_files WHERE id=?", (int(fid),))
    await call.answer("🗑 Deleted")
    await admin_files_menu(call)

@dp.callback_query(F.data == "admin_add_file")
async def admin_add_file_start(call: CallbackQuery, state: FSMContext):
    if not _is_admin(call.from_user.id): return
    await call.message.edit_text("📤 Send the file now (APK / document / video / audio).\nThe <b>caption</b> becomes the button title.\n\n/cancel to abort.", reply_markup=admin_back_kb(), parse_mode='HTML')
    await state.set_state(AdminStates.wait_for_file_upload)

@dp.message(AdminStates.wait_for_file_upload)
async def admin_save_file(m: Message, state: FSMContext):
    if m.text and m.text.strip() == "/cancel":
        await state.clear()
        return await m.answer("Cancelled.", reply_markup=admin_kb(), parse_mode='HTML')
    if m.document: file_id, ftype, default = m.document.file_id, "document", m.document.file_name
    elif m.video: file_id, ftype, default = m.video.file_id, "video", m.video.file_name
    elif m.audio: file_id, ftype, default = m.audio.file_id, "audio", m.audio.file_name
    else:
        return await m.answer("❌ Please send a file (document / APK / video / audio).")
    title = (m.caption or default or "File").strip()[:60]
    db_query("INSERT INTO bot_files (title, file_id, file_type, created_at) VALUES (?, ?, ?, ?)",
             (title, file_id, ftype, datetime.now().strftime("%Y-%m-%d %H:%M:%S")))
    await m.answer(f"✅ File saved: <b>{html_escape(title)}</b>", reply_markup=admin_kb(), parse_mode='HTML')
    await state.clear()

@dp.callback_query(F.data == "admin_spin_rewards")
async def admin_spin_rewards(call: CallbackQuery, state: FSMContext):
    if not _is_admin(call.from_user.id): return
    rewards = [str(int(r[0]) if float(r[0]).is_integer() else r[0]) for r in (db_query("SELECT amount FROM spin_rewards ORDER BY id", fetchall=True) or [])]
    await call.message.edit_text(
        "🎲 <b>SPIN REWARDS</b>\n\nCurrent list:\n<code>" + (",".join(rewards) or "empty") + "</code>\n\n"
        "Send new amounts separated by commas. <b>Repeat</b> an amount to make it more likely.\n"
        "Example: <code>0,0,0,1,1,2,5,10</code>\n\n/cancel to abort.", reply_markup=admin_back_kb(), parse_mode='HTML')
    await state.set_state(AdminStates.wait_for_spin_rewards)

@dp.message(AdminStates.wait_for_spin_rewards)
async def admin_save_spin_rewards(m: Message, state: FSMContext):
    if (m.text or "").strip() == "/cancel":
        await state.clear()
        return await m.answer("Cancelled.", reply_markup=admin_kb(), parse_mode='HTML')
    try:
        amounts = [float(x) for x in (m.text or "").replace(" ", "").split(",") if x != ""]
        assert amounts and all(a >= 0 for a in amounts)
    except Exception:
        return await m.answer("❌ Invalid. Send numbers like: <code>0,1,2,5</code>", parse_mode='HTML')
    db_query("DELETE FROM spin_rewards")
    for a in amounts:
        db_query("INSERT INTO spin_rewards (amount) VALUES (?)", (a,))
    await m.answer(f"✅ Saved {len(amounts)} spin outcomes.", reply_markup=admin_kb(), parse_mode='HTML')
    await state.clear()

@dp.callback_query(F.data == "admin_ref_percent")
async def admin_ref_percent(call: CallbackQuery, state: FSMContext):
    if not _is_admin(call.from_user.id): return
    await call.message.edit_text(f"🎁 <b>REFERRAL %</b>\n\nCurrent: <b>{get_setting('referral_percent', '5')}%</b> of every deposit.\nSend the new percentage (0 to disable).\n\n/cancel to abort.", reply_markup=admin_back_kb(), parse_mode='HTML')
    await state.set_state(AdminStates.wait_for_ref_percent)

@dp.message(AdminStates.wait_for_ref_percent)
async def admin_save_ref_percent(m: Message, state: FSMContext):
    if (m.text or "").strip() == "/cancel":
        await state.clear()
        return await m.answer("Cancelled.", reply_markup=admin_kb(), parse_mode='HTML')
    try:
        pct = float((m.text or "").strip().replace("%", ""))
        assert 0 <= pct <= 100
    except Exception:
        return await m.answer("❌ Send a number between 0 and 100.")
    set_setting("referral_percent", str(pct))
    await m.answer(f"✅ Referral bonus set to <b>{pct}%</b>.", reply_markup=admin_kb(), parse_mode='HTML')
    await state.clear()

# ==============================================================================
# 24C. FULL USER DATA RESET (users, balances, orders, history, referrals, tickets)
# ==============================================================================
# True  -> on the NEXT start the bot wipes all user data ONCE (a backup is taken first)
#          and then never does it again automatically.
RESET_USERS_ON_NEXT_START = False   # safety: never wipe data automatically (use Admin -> Reset, it asks for your password)
RESET_FLAG_KEY = "fresh_start_v1"        # change this value to allow one more auto-reset
_RESET_TABLES = ["users", "orders", "transactions", "crypto_txns", "redeemed", "tickets", "activity_logs"]

def backup_database(tag: str = "before_reset") -> Optional[str]:
    if not os.path.exists(DB_FILE):
        return None
    name = f"backup_{tag}_{datetime.now().strftime('%Y%m%d_%H%M%S')}.db"
    src_conn = sqlite3.connect(DB_FILE)
    dst_conn = sqlite3.connect(name)
    try:
        src_conn.backup(dst_conn)
    finally:
        dst_conn.close()
        src_conn.close()
    return name

def reset_all_user_data() -> Dict[str, int]:
    """Deletes ALL user data + balance/order/payment history. Products, keys, settings,
    emojis, coupons, files and spin rewards are kept."""
    counts: Dict[str, int] = {}
    conn = sqlite3.connect(DB_FILE)
    try:
        for t in _RESET_TABLES:
            try:
                counts[t] = conn.execute(f"SELECT COUNT(*) FROM {t}").fetchone()[0]
                conn.execute(f"DELETE FROM {t}")
                conn.execute("DELETE FROM sqlite_sequence WHERE name=?", (t,))
            except sqlite3.OperationalError:
                pass
        conn.commit()
    finally:
        conn.close()
    return counts

@dp.callback_query(F.data == "admin_reset_data")
async def admin_reset_data_ask(call: CallbackQuery, state: FSMContext):
    if call.from_user.id != ADMIN_ID: return
    if not await _require_fresh(call, state): return
    kb = InlineKeyboardMarkup(inline_keyboard=[
        [InlineKeyboardButton(text="✅ YES, DELETE EVERYTHING", callback_data="admin_reset_data_yes", style="danger")],
        [InlineKeyboardButton(text="Cancel", callback_data="admin_panel_back", icon_custom_emoji_id=get_emoji_icon("back"), style="success")],
    ])
    await call.message.edit_text(
        "⚠️ <b>RESET ALL USER DATA?</b>\n\n"
        "This permanently deletes ALL users, balances, orders, payment history, "
        "referrals, redeem history, tickets and logs.\n"
        "Products, keys, settings, emojis and coupons are kept.\n\n"
        "A backup file is created and sent to you first.",
        reply_markup=kb, parse_mode='HTML')

@dp.callback_query(F.data == "admin_reset_data_yes")
async def admin_reset_data_run(call: CallbackQuery, state: FSMContext):
    if call.from_user.id != ADMIN_ID: return
    if not await _require_fresh(call, state): return
    await state.clear()
    sec_log("RESET_ALL_USER_DATA", call.from_user.id)
    backup = backup_database()
    counts = reset_all_user_data()
    set_setting(RESET_FLAG_KEY, "1")
    summary = "\n".join(f"• {t}: {n}" for t, n in counts.items())
    await call.message.edit_text(f"✅ <b>All user data deleted. Fresh start!</b>\n\n{summary}",
                                 reply_markup=admin_kb(), parse_mode='HTML')
    if backup:
        try: await bot.send_document(ADMIN_ID, FSInputFile(backup), caption="📦 Backup of the data before reset")
        except Exception as e: logger.error(f"Backup send failed: {e}")

# ==============================================================================
# 24D. IMPORT OLD DATABASE (admin only, password re-check, automatic backup first)
#      Accepts: SQLite file (.db/.sqlite/.sqlite3)  or  CSV with users.
#      Never imported on purpose: settings, logs, file_ids (they belong to the old bot).
# ==============================================================================
IMPORT_DIR = os.path.join(BASE_DIR, "imports")
IMPORT_SERVER_FILE = os.path.join(BASE_DIR, "import_old.db")
IMPORT_MAX_BYTES = 20 * 1024 * 1024
IMPORT_ORDER = ["users", "products", "product_keys", "orders", "transactions", "crypto_txns", "redeemed", "coupons", "tickets"]
_IMP_REAL = {"balance", "spent", "total_saved", "referral_earned", "price_paid", "amount_inr", "amount_usdt", "amount", "price_inr", "reseller_price"}
_IMP_INT = {"id", "user_id", "orders_count", "is_reseller", "is_banned", "warnings", "is_vip", "referred_by", "uses_left",
            "timestamp", "expires_at", "is_used", "product_id", "stock", "is_active"}
_IMP_NULLABLE = {"referred_by", "expires_at", "timestamp"}
_CSV_ALIASES = {"id": "user_id", "userid": "user_id", "telegram_id": "user_id", "tg_id": "user_id",
                "name": "first_name", "wallet": "balance", "funds": "balance", "referrer": "referred_by"}

def _imp_clean(col: str, v):
    if isinstance(v, (bytes, bytearray, memoryview)):
        return None
    if col in _IMP_REAL:
        try: f = float(v)
        except (TypeError, ValueError): return 0.0
        return f if f == f and abs(f) != float("inf") else 0.0
    if col in _IMP_INT:
        if v is None or v == "":
            return None if col in _IMP_NULLABLE else 0
        try: return int(float(v))
        except (TypeError, ValueError): return None if col in _IMP_NULLABLE else 0
    return None if v is None else str(v)[:4000]

def _q(cols) -> str:
    return ", ".join('"' + c + '"' for c in cols)

def _imp_insert(dst, table: str, rec: dict) -> None:
    cols = list(rec)
    dst.execute(f'INSERT INTO "{table}" ({_q(cols)}) VALUES ({",".join("?" * len(cols))})', tuple(rec.values()))

def _imp_row(dst, t: str, rec: dict, overwrite: bool, r: Dict[str, int], pid_map: dict, touched: set) -> None:
    if t == "users":
        uid = rec.get("user_id")
        if not isinstance(uid, int) or uid <= 0:
            r["invalid"] += 1; return
        if not dst.execute("SELECT 1 FROM users WHERE user_id=?", (uid,)).fetchone():
            _imp_insert(dst, t, rec); r["added"] += 1
        elif overwrite:
            sets = [c for c in rec if c != "user_id"]
            if sets:
                dst.execute(f'UPDATE users SET {", ".join(chr(34) + c + chr(34) + "=?" for c in sets)} WHERE user_id=?',
                            tuple(rec[c] for c in sets) + (uid,))
            r["updated"] += 1
        else:
            r["skipped"] += 1
    elif t == "products":
        old_id = rec.pop("id", None)
        if not rec.get("name"):
            r["invalid"] += 1; return
        row = dst.execute("SELECT id FROM products WHERE category IS ? AND panel_name IS ? AND name IS ?",
                          (rec.get("category"), rec.get("panel_name", ""), rec.get("name"))).fetchone()
        if row:
            pid_map[old_id] = row[0]; r["skipped"] += 1
        else:
            _imp_insert(dst, t, rec)
            pid_map[old_id] = dst.execute("SELECT last_insert_rowid()").fetchone()[0]; r["added"] += 1
    elif t == "product_keys":
        rec.pop("id", None)
        pid = pid_map.get(rec.get("product_id"))
        if pid is None or not rec.get("key_text"):
            r["invalid"] += 1; return
        rec["product_id"] = pid
        if dst.execute("SELECT 1 FROM product_keys WHERE product_id=? AND key_text=?", (pid, rec["key_text"])).fetchone():
            r["skipped"] += 1
        else:
            _imp_insert(dst, t, rec); touched.add(pid); r["added"] += 1
    elif t in ("orders", "tickets"):
        rec.pop("id", None)
        keys = ("user_id", "product_name", "delivered_key", "purchase_date") if t == "orders" else ("user_id", "message", "created_at")
        where = " AND ".join(f'"{k}" IS ?' for k in keys)
        if dst.execute(f'SELECT 1 FROM "{t}" WHERE {where}', tuple(rec.get(k) for k in keys)).fetchone():
            r["skipped"] += 1
        else:
            _imp_insert(dst, t, rec); r["added"] += 1
    elif t == "transactions":
        if not rec.get("order_id"):
            r["invalid"] += 1; return
        if dst.execute("SELECT 1 FROM transactions WHERE order_id=?", (rec["order_id"],)).fetchone():
            r["skipped"] += 1; return
        if str(rec.get("status", "")).lower() == "pending":      # never let an old pending order be credited again
            rec["status"] = "expired"
        _imp_insert(dst, t, rec); r["added"] += 1
    elif t == "crypto_txns":
        if not rec.get("txid"):
            r["invalid"] += 1; return
        if dst.execute("SELECT 1 FROM crypto_txns WHERE txid=?", (rec["txid"],)).fetchone():
            r["skipped"] += 1
        else:
            _imp_insert(dst, t, rec); r["added"] += 1
    elif t == "redeemed":
        if dst.execute("SELECT 1 FROM redeemed WHERE user_id IS ? AND code IS ?", (rec.get("user_id"), rec.get("code"))).fetchone():
            r["skipped"] += 1
        else:
            _imp_insert(dst, t, rec); r["added"] += 1
    elif t == "coupons":
        if not rec.get("code"):
            r["invalid"] += 1; return
        if not dst.execute("SELECT 1 FROM coupons WHERE code=?", (rec["code"],)).fetchone():
            _imp_insert(dst, t, rec); r["added"] += 1
        elif overwrite:
            dst.execute("UPDATE coupons SET amount=?, uses_left=? WHERE code=?", (rec.get("amount", 0.0), rec.get("uses_left", 0), rec["code"]))
            r["updated"] += 1
        else:
            r["skipped"] += 1

def _imp_open_dst():
    dst = sqlite3.connect(DB_FILE, timeout=30)
    dst.isolation_level = None            # we control BEGIN / COMMIT ourselves
    return dst

def _import_sqlite(path: str, overwrite: bool) -> Dict[str, Dict[str, int]]:
    src_db = sqlite3.connect(f"file:{path}?mode=ro", uri=True)
    dst = _imp_open_dst()
    report: Dict[str, Dict[str, int]] = {}
    try:
        src_tables = {r[0] for r in src_db.execute("SELECT name FROM sqlite_master WHERE type='table'")}
        dst.execute("BEGIN IMMEDIATE")
        pid_map: dict = {}
        touched: set = set()
        for t in IMPORT_ORDER:
            if t not in src_tables:
                continue
            dcols = [r[1] for r in dst.execute(f'PRAGMA table_info("{t}")')]
            scols = {r[1] for r in src_db.execute(f'PRAGMA table_info("{t}")')}
            cols = [c for c in dcols if c in scols]            # only columns that exist in BOTH databases
            if not cols:
                continue
            r = report[t] = {"added": 0, "updated": 0, "skipped": 0, "invalid": 0}
            for row in src_db.execute(f'SELECT {_q(cols)} FROM "{t}"'):
                _imp_row(dst, t, {c: _imp_clean(c, v) for c, v in zip(cols, row)}, overwrite, r, pid_map, touched)
        for pid in touched:                                    # stock = number of unused keys
            dst.execute("UPDATE products SET stock=(SELECT COUNT(*) FROM product_keys WHERE product_id=? AND is_used=0) WHERE id=?", (pid, pid))
        dst.execute("COMMIT")
    except Exception:
        try: dst.execute("ROLLBACK")
        except Exception: pass
        raise
    finally:
        src_db.close(); dst.close()
    return report

def _import_csv_users(path: str, overwrite: bool) -> Dict[str, Dict[str, int]]:
    dst = _imp_open_dst()
    r = {"added": 0, "updated": 0, "skipped": 0, "invalid": 0}
    try:
        dcols = [c[1] for c in dst.execute('PRAGMA table_info("users")')]
        dst.execute("BEGIN IMMEDIATE")
        with open(path, "r", encoding="utf-8-sig", newline="") as fh:
            rdr = csv.DictReader(fh)
            mapping = {}
            for h in (rdr.fieldnames or []):
                key = _CSV_ALIASES.get(h.strip().lower(), h.strip().lower())
                if key in dcols:
                    mapping[h] = key
            if "user_id" not in mapping.values():
                raise ValueError("CSV needs a user_id column (also accepted: id, telegram_id)")
            for i, row in enumerate(rdr):
                if i >= 200000:
                    break
                _imp_row(dst, "users", {col: _imp_clean(col, row.get(h)) for h, col in mapping.items()}, overwrite, r, {}, set())
        dst.execute("COMMIT")
    except Exception:
        try: dst.execute("ROLLBACK")
        except Exception: pass
        raise
    finally:
        dst.close()
    return {"users": r}

def _import_summary(rep: Dict[str, Dict[str, int]]) -> str:
    if not rep:
        return "• nothing importable found"
    return "\n".join(f"• <b>{t}</b>: +{v['added']} new, {v['updated']} updated, {v['skipped']} skipped" + (f", {v['invalid']} invalid" if v['invalid'] else "")
                     for t, v in rep.items())

@dp.callback_query(F.data == "admin_import_db")
async def admin_import_db_start(call: CallbackQuery, state: FSMContext):
    if call.from_user.id != ADMIN_ID: return
    if not await _require_fresh(call, state): return
    await state.clear()
    rows = []
    if os.path.exists(IMPORT_SERVER_FILE):
        rows.append([InlineKeyboardButton(text="📂 Use server file import_old.db", callback_data="impdb_server", style="success")])
    rows.append([InlineKeyboardButton(text="Cancel", callback_data="admin_panel_back", icon_custom_emoji_id=get_emoji_icon("back"), style="danger")])
    await call.message.edit_text(
        "📥 <b>IMPORT OLD DATABASE</b>\n\n"
        "Send your old data as a <b>file</b> (📎 → File):\n"
        "• SQLite database: <code>.db / .sqlite / .sqlite3</code>\n"
        "• or a <code>.csv</code> with users (user_id, balance, first_name, ...)\n\n"
        "Imported: users, balances, referrals, orders, keys, products, payments, coupons, tickets.\n"
        "<i>Not imported: settings, logs, file IDs.</i>\n"
        "A backup of the current data is made automatically first.\n\n"
        f"Telegram allows bot uploads up to 20 MB. For a bigger file, copy it to the bot folder as <code>{os.path.basename(IMPORT_SERVER_FILE)}</code> and tap the button.",
        reply_markup=InlineKeyboardMarkup(inline_keyboard=rows), parse_mode='HTML')
    await state.set_state(AdminStates.import_db_file)

async def _import_preview(msg: Message, state: FSMContext, path: str, keep_file: bool) -> None:
    try:
        if path.lower().endswith(".csv"):
            with open(path, "r", encoding="utf-8-sig", newline="") as fh:
                n = max(0, sum(1 for _ in fh) - 1)
            info = f"• CSV with about <b>{n}</b> user row(s)"
        else:
            with open(path, "rb") as fh:
                if fh.read(16) != b"SQLite format 3\x00":
                    raise ValueError("this is not a SQLite database file")
            s = sqlite3.connect(f"file:{path}?mode=ro", uri=True)
            try:
                tables = {r[0] for r in s.execute("SELECT name FROM sqlite_master WHERE type='table'")}
                lines = [f"• <b>{t}</b>: {s.execute(f'SELECT COUNT(*) FROM {chr(34)}{t}{chr(34)}').fetchone()[0]} rows" for t in IMPORT_ORDER if t in tables]
            finally:
                s.close()
            if not lines:
                raise ValueError("no users / orders / products tables found in this file")
            info = "\n".join(lines)
    except Exception as e:
        if not keep_file:
            try: os.remove(path)
            except OSError: pass
        return await msg.answer(f"❌ Cannot read this file: <code>{html_escape(str(e))[:200]}</code>\nSend another file or /cancel.", parse_mode='HTML')
    await state.update_data(import_path=path, import_keep=keep_file)
    await state.set_state(AdminStates.import_db_confirm)
    kb = InlineKeyboardMarkup(inline_keyboard=[
        [InlineKeyboardButton(text="➕ Add missing only (safe)", callback_data="impdb_safe", style="success")],
        [InlineKeyboardButton(text="♻️ Add + overwrite existing users", callback_data="impdb_over", style="primary")],
        [InlineKeyboardButton(text="Cancel", callback_data="admin_panel_back", icon_custom_emoji_id=get_emoji_icon("back"), style="danger")],
    ])
    await msg.answer("📥 <b>File ready to import</b>\n\n" + info +
                     "\n\n<b>Add missing only</b> keeps everything that already exists.\n"
                     "<b>Overwrite</b> replaces balances/status of users that exist in both.", reply_markup=kb, parse_mode='HTML')

@dp.message(AdminStates.import_db_file, F.document)
async def admin_import_db_file(m: Message, state: FSMContext):
    doc = m.document
    ext = os.path.splitext((doc.file_name or "").lower())[1]
    if ext not in (".db", ".sqlite", ".sqlite3", ".csv"):
        return await m.answer("❌ Send a .db / .sqlite / .sqlite3 / .csv file.")
    if (doc.file_size or 0) > IMPORT_MAX_BYTES:
        return await m.answer("❌ File is bigger than 20 MB. Put it in the bot folder as import_old.db and use the server-file button.")
    os.makedirs(IMPORT_DIR, exist_ok=True)
    path = os.path.join(IMPORT_DIR, f"imp_{int(time.time())}{ext}")
    await bot.download(doc, destination=path)
    await _import_preview(m, state, path, keep_file=False)

@dp.message(AdminStates.import_db_file)
async def admin_import_db_wrong(m: Message, state: FSMContext):
    if (m.text or "").strip() == "/cancel":
        await state.clear()
        return await m.answer("Cancelled.", reply_markup=admin_kb())
    await m.answer("Please send the old database as a <b>file</b> (📎 → File), or /cancel.", parse_mode='HTML')

@dp.callback_query(F.data == "impdb_server")
async def admin_import_server_file(call: CallbackQuery, state: FSMContext):
    if not _is_admin(call.from_user.id): return
    if not await _require_fresh(call, state): return
    if not os.path.exists(IMPORT_SERVER_FILE):
        return await call.answer("import_old.db not found in the bot folder", show_alert=True)
    await call.answer()
    await _import_preview(call.message, state, IMPORT_SERVER_FILE, keep_file=True)

@dp.callback_query(F.data.in_({"impdb_safe", "impdb_over"}))
async def admin_import_run(call: CallbackQuery, state: FSMContext):
    if not _is_admin(call.from_user.id): return
    data = await state.get_data()
    path, keep = data.get("import_path"), data.get("import_keep", False)
    if not path or not os.path.exists(path):
        await state.clear()
        return await call.answer("Upload the file again.", show_alert=True)
    if not await _require_fresh(call, state): return
    overwrite = call.data == "impdb_over"
    await call.answer("Importing...")
    await call.message.edit_text("⏳ <b>Making a backup and importing...</b> please wait.", parse_mode='HTML')
    backup = await asyncio.to_thread(backup_database, "before_import")
    try:
        if path.lower().endswith(".csv"):
            rep = await asyncio.to_thread(_import_csv_users, path, overwrite)
        else:
            rep = await asyncio.to_thread(_import_sqlite, path, overwrite)
    except Exception as e:
        logger.error(f"DB import failed: {e}")
        sec_log("DB_IMPORT_FAILED", call.from_user.id, str(e))
        await state.clear()
        return await call.message.answer(f"❌ <b>Import failed - nothing was changed.</b>\n<code>{html_escape(str(e))[:300]}</code>",
                                         reply_markup=admin_kb(), parse_mode='HTML')
    finally:
        if not keep:
            try: os.remove(path)
            except OSError: pass
    set_setting(RESET_FLAG_KEY, "1")          # make sure no automatic wipe can ever follow an import
    await state.clear()
    sec_log("DB_IMPORT", call.from_user.id, f"overwrite={overwrite} " + json.dumps(rep))
    await call.message.answer("✅ <b>Old data imported!</b>\n\n" + _import_summary(rep) +
                              "\n\nUsers can use the bot with their old balance right now.", reply_markup=admin_kb(), parse_mode='HTML')
    if backup:
        try: await bot.send_document(ADMIN_ID, FSInputFile(backup), caption="📦 Backup of the data before import")
        except Exception as e: logger.error(f"Backup send failed: {e}")

# ---------------------------- ADMIN: PREMIUM EMOJI ID FINDER ------------------
@dp.message(F.from_user.id == ADMIN_ID, StateFilter(None))
async def admin_emoji_id_finder(m: Message, state: FSMContext):
    """Admin sends premium emoji(s) (or a 15+ digit emoji ID) outside other flows -> they are
    SAVED to the premium emoji database automatically. Sending the 10-emoji welcome message
    still imports all 10 slots at once (old behaviour)."""
    if await state.get_state() is not None:
        return
    if not admin_session_ok():
        return
    from_entities = any(e.type == "custom_emoji" for e in (m.entities or []))
    ids = [e.custom_emoji_id for e in (m.entities or []) if e.type == "custom_emoji" and e.custom_emoji_id]
    if not ids:
        ids = re.findall(r"(?<!\d)\d{15,}(?!\d)", m.text or "")
    if not ids:
        return
    welcome_order = ["store_title", "product_store", "profile", "add_balance", "history",
                     "referral", "tutorial", "support", "spin", "files"]
    if from_entities and len(ids) >= len(welcome_order):
        done = []
        for slot, eid in zip(welcome_order, ids):
            set_setting(f"emoji_{slot}", str(eid))
            done.append(f"• {slot}: <code>{eid}</code>")
        _icon_cache.clear()
        await m.answer("✅ <b>Premium emojis imported from that message:</b>\n" + "\n".join(done) +
                       "\n\nAb /start karke check karo. Koi galat lage to Admin → Edit All Emojis se badal do.",
                       parse_mode='HTML')
        return
    saved, skipped = 0, 0
    for eid in dict.fromkeys(str(x) for x in ids):
        if db_query("SELECT 1 FROM premium_emojis WHERE emoji_id=?", (eid,), fetchone=True):
            skipped += 1
            continue
        db_query("INSERT INTO premium_emojis (emoji_id, label, slot, created_at) VALUES (?, ?, '', ?)",
                 (eid, f"Emoji {eid[-4:]}", _hnow()))
        saved += 1
    note = f"\n⚠️ {skipped} pehle se database mein thi." if skipped else ""
    await m.answer(f"✅ <b>{saved} premium emoji database mein save ho gayi.</b>{note}\n\n"
                   "Ab Admin → 🌟 Premium Emoji DB kholo, emoji par tap karke slot (profile, spin, vip...) chuno.",
                   reply_markup=InlineKeyboardMarkup(inline_keyboard=[[
                       InlineKeyboardButton(text="🌟 Open Premium Emoji DB", callback_data="admin_pe_menu", style="success")]]),
                   parse_mode='HTML')

# ==============================================================================
# 24E. HOSTING  -  users upload their own .py bot, the ADMIN can see every file / code
#      Flow: /start -> join channel -> menu -> [Hosting] -> hosting menu.
#      Hosted code runs in its own folder with a CLEAN environment (no tokens), CPU/RAM/file
#      limits, and - when bubblewrap or HOST_RUN_AS_USER is available - in a real sandbox.
# ==============================================================================
HOST_DIR = os.path.join(BASE_DIR, "hosted_files")
HOST_FREE_LIMIT = 2
HOST_PREMIUM_LIMIT = 10
HOST_FREE_LOG_LINES = 30
HOST_PREMIUM_LOG_LINES = 100
HOST_MAX_CRASH_RESTARTS = 5
HOST_MAX_UPLOAD_MB = 5
HOST_MEM_MB = int(os.getenv("HOST_MEM_MB", "512"))
HOST_RUN_AS_USER = os.getenv("HOST_RUN_AS_USER", "")          # optional: OS user that runs hosted code (bot must run as root)
HOST_SANDBOX_MODE = os.getenv("HOST_SANDBOX", "auto")         # auto | off
HOST_FORBIDDEN = ("cuibcc", "bot_secrets", ".bot_data_key", "/proc/", "hosted_files", "security.log", "bot_activity.log")
_HOST_SANDBOX: Dict[str, Any] = {"mode": "none", "bwrap": None}

def host_init_db() -> None:
    db_query("CREATE TABLE IF NOT EXISTS host_users (user_id INTEGER PRIMARY KEY, is_premium INTEGER DEFAULT 0, premium_until TEXT, is_banned INTEGER DEFAULT 0, joined_at TEXT DEFAULT '')")
    db_query("CREATE TABLE IF NOT EXISTS hosted_bots (id INTEGER PRIMARY KEY AUTOINCREMENT, user_id INTEGER, bot_name TEXT, file_path TEXT, status TEXT DEFAULT 'Stopped', auto_restart INTEGER DEFAULT 0, created_at TEXT DEFAULT '', pid INTEGER DEFAULT 0, size INTEGER DEFAULT 0)")
    os.makedirs(HOST_DIR, exist_ok=True)

def _hnow() -> str:
    return datetime.now().strftime("%Y-%m-%d %H:%M")

def _host_premium(u: dict) -> bool:
    if not u.get("is_premium"):
        return False
    until = u.get("premium_until")
    if not until:
        return True
    try:
        return datetime.fromisoformat(until) > datetime.now()
    except ValueError:
        return False

def host_user(uid: int) -> dict:
    db_query("INSERT OR IGNORE INTO host_users (user_id, joined_at) VALUES (?, ?)", (uid, _hnow()))
    keys = ("user_id", "is_premium", "premium_until", "is_banned", "joined_at")
    row = db_query("SELECT user_id, is_premium, premium_until, is_banned, joined_at FROM host_users WHERE user_id=?", (uid,), fetchone=True)
    u = dict(zip(keys, row)) if row else dict(zip(keys, (uid, 0, None, 0, "")))
    u["premium"] = _host_premium(u)
    u["banned"] = bool(u["is_banned"])
    return u

def _is_host_prem(uid: int) -> bool:
    return uid == ADMIN_ID or host_user(uid)["premium"]

def host_limit(u: dict) -> int:
    key, default = ("host_premium_limit", HOST_PREMIUM_LIMIT) if u["premium"] else ("host_free_limit", HOST_FREE_LIMIT)
    try:
        return max(1, int(get_setting(key, str(default))))
    except ValueError:
        return default

def host_count(uid: int) -> int:
    r = db_query("SELECT COUNT(*) FROM hosted_bots WHERE user_id=?", (uid,), fetchone=True)
    return r[0] if r else 0

_HB_KEYS = ("id", "user_id", "bot_name", "file_path", "status", "auto_restart", "created_at", "size")

def host_get_bot(bot_id: Optional[int]) -> Optional[dict]:
    if bot_id is None:
        return None
    r = db_query("SELECT id, user_id, bot_name, file_path, status, auto_restart, created_at, size FROM hosted_bots WHERE id=?", (bot_id,), fetchone=True)
    return dict(zip(_HB_KEYS, r)) if r else None

def host_insert_bot(uid: int, name: str, path: str, auto: int, size: int) -> Optional[int]:
    conn = sqlite3.connect(DB_FILE, timeout=15)
    try:
        cur = conn.execute("INSERT INTO hosted_bots (user_id, bot_name, file_path, auto_restart, created_at, size) VALUES (?,?,?,?,?,?)",
                           (uid, name, path, auto, _hnow(), size))
        conn.commit()
        return cur.lastrowid
    except Exception as e:
        logger.error(f"host insert failed: {e}")
        return None
    finally:
        conn.close()

def _host_path_ok(path: str) -> bool:
    """Only files that really live inside hosted_files/ are ever read, run or deleted."""
    try:
        root = os.path.realpath(HOST_DIR)
        rp = os.path.realpath(path)
        return rp.startswith(root + os.sep)
    except Exception:
        return False

def _host_set_status(bot_id: int, status: str, pid: int = 0) -> None:
    db_query("UPDATE hosted_bots SET status=?, pid=? WHERE id=?", (status, pid, bot_id))

def host_scan(raw: bytes, filename: str) -> Optional[str]:
    """Quick safety check of an uploaded file. Returns a reason when it must be rejected.
    (A deterrent only - real protection is the sandbox / separate OS user.)"""
    try:
        text = raw.decode("utf-8")
    except UnicodeDecodeError:
        return "File UTF-8 text nahi hai (sirf .py source file bhejo)."
    low = text.lower()
    for bad in HOST_FORBIDDEN:
        if bad in low:
            return f"File me '{bad}' mila - ye hosting server ki private cheez hai, allowed nahi."
    if BOT_TOKEN in text:
        return "Aapne is Store/Hosting bot ka hi token file me daal diya hai! @BotFather se NAYA bot banao aur uska token use karo."
    try:
        compile(text, filename, "exec")
    except SyntaxError as e:
        return f"Syntax error (line {e.lineno}): {e.msg}"
    except (ValueError, RecursionError, MemoryError):
        return "File valid Python nahi hai."
    return None

# ---------------------------- process isolation ----------------------------
def _host_env(workdir: str) -> Dict[str, str]:
    """A CLEAN environment: hosted code never sees BOT_TOKEN, vault password, API keys ..."""
    env = {
        "PATH": os.environ.get("PATH", "/usr/local/bin:/usr/bin:/bin"),
        "HOME": workdir, "TMPDIR": workdir, "LANG": "C.UTF-8",
        "PYTHONUNBUFFERED": "1", "PYTHONDONTWRITEBYTECODE": "1",
        "PYTHONPATH": os.path.join(workdir, ".pylibs"),
    }
    for k in ("VIRTUAL_ENV", "LD_LIBRARY_PATH", "SSL_CERT_FILE", "TZ"):
        if k in os.environ:
            env[k] = os.environ[k]
    return env

def _host_preexec() -> None:
    try:
        import resource as _r
        mem = HOST_MEM_MB * 1024 * 1024
        _r.setrlimit(_r.RLIMIT_AS, (mem, mem))
        _r.setrlimit(_r.RLIMIT_FSIZE, (256 << 20, 256 << 20))
        _r.setrlimit(_r.RLIMIT_NOFILE, (512, 512))
        _r.setrlimit(_r.RLIMIT_CORE, (0, 0))
        os.nice(5)
    except Exception:
        pass

def _bwrap_cmd(bw: str, workdir: str, argv: List[str]) -> List[str]:
    cmd = [bw, "--unshare-pid", "--unshare-ipc", "--unshare-uts", "--die-with-parent", "--new-session"]
    for p in ("/usr", "/lib", "/lib64", "/bin", "/sbin"):
        if os.path.exists(p):
            cmd += ["--ro-bind", p, p]
    for p in ("/etc/resolv.conf", "/etc/hosts", "/etc/nsswitch.conf", "/etc/ssl", "/etc/ca-certificates",
              "/etc/localtime", "/etc/passwd", "/etc/group", "/run/systemd/resolve"):
        if os.path.exists(p):
            cmd += ["--ro-bind", p, p]
    extra = {sys.prefix, sys.base_prefix, sys.exec_prefix}
    try:
        import site
        extra.add(site.getusersitepackages())
    except Exception:
        pass
    for p in sorted(extra):
        if p and os.path.exists(p) and not p.startswith(("/usr", "/lib", "/bin")):
            cmd += ["--ro-bind", p, p]
    cmd += ["--proc", "/proc", "--dev", "/dev", "--tmpfs", "/tmp", "--bind", workdir, workdir, "--chdir", workdir, "--"]
    return cmd + argv

async def host_detect_sandbox() -> None:
    """Uses bubblewrap when it is installed AND works (self-test), else falls back safely."""
    if HOST_SANDBOX_MODE == "off":
        return
    bw = shutil.which("bwrap")
    if not bw:
        return
    tmp = os.path.join(HOST_DIR, ".selftest")
    os.makedirs(tmp, exist_ok=True)
    try:
        proc = await asyncio.create_subprocess_exec(*_bwrap_cmd(bw, tmp, [sys.executable, "-c", "print('sandbox-ok')"]),
                                                    stdout=asyncio.subprocess.PIPE, stderr=asyncio.subprocess.PIPE)
        out, err = await asyncio.wait_for(proc.communicate(), timeout=20)
        if proc.returncode == 0 and b"sandbox-ok" in out:
            _HOST_SANDBOX.update(mode="bwrap", bwrap=bw)
            logger.info("Hosting sandbox: bubblewrap ACTIVE")
        else:
            logger.warning(f"bubblewrap self-test failed, hosted code runs WITHOUT sandbox: {err.decode(errors='ignore')[:200]}")
    except Exception as e:
        logger.warning(f"bubblewrap self-test error: {e}")

def _host_run_as() -> Optional[Tuple[int, int]]:
    if not HOST_RUN_AS_USER or not hasattr(os, "getuid") or os.getuid() != 0:
        return None
    try:
        import pwd
        pw = pwd.getpwnam(HOST_RUN_AS_USER)
        return pw.pw_uid, pw.pw_gid
    except Exception as e:
        logger.error(f"HOST_RUN_AS_USER invalid: {e}")
        return None

def host_sandbox_label() -> str:
    if _HOST_SANDBOX["mode"] == "bwrap":
        return "bubblewrap sandbox ON"
    if _host_run_as():
        return f"separate OS user ({HOST_RUN_AS_USER})"
    return "NO isolation (env scrub + limits only)"

def _harden_process() -> None:
    """Linux: other processes of the same user can no longer read this process' memory / environment."""
    try:
        import ctypes
        ctypes.CDLL(None).prctl(4, 0, 0, 0, 0)         # PR_SET_DUMPABLE = 0
    except Exception:
        pass

def _kill_group(proc, sig=signal.SIGTERM) -> None:
    try:
        os.killpg(proc.pid, sig)
    except Exception:
        try: proc.send_signal(sig)
        except Exception: pass

class HostInstance:
    def __init__(self, bot_id: int, user_id: int, file_path: str, auto_restart: bool):
        self.bot_id, self.user_id, self.file_path, self.auto_restart = bot_id, user_id, file_path, auto_restart
        self.process: Optional[asyncio.subprocess.Process] = None
        self.logs: deque = deque(maxlen=300)
        self.is_running = False
        self.should_run = False
        self.crashes = 0
        self.started_at = 0.0

    def log(self, text: str) -> None:
        self.logs.append(text[:2000])

    async def clear_webhook(self) -> None:
        try:
            with open(self.file_path, "r", encoding="utf-8", errors="ignore") as f:
                content = f.read(2_000_000)
            m = re.search(r"[0-9]{8,10}:[a-zA-Z0-9_-]{35}", content)
            if m and m.group(0) != BOT_TOKEN:
                async with aiohttp.ClientSession() as session:
                    await session.get(f"https://api.telegram.org/bot{m.group(0)}/deleteWebhook?drop_pending_updates=true",
                                      timeout=aiohttp.ClientTimeout(total=10))
                self.log("✅ Webhook cleared.")
        except Exception:
            pass

    async def start(self) -> bool:
        if self.is_running:
            return True
        self.should_run = True
        self.logs.clear()
        self.log("⏳ Booting process...")
        if not _host_path_ok(self.file_path) or not os.path.exists(self.file_path):
            self.log("❌ Error: File not found.")
            return False
        await self.clear_webhook()
        workdir = os.path.dirname(self.file_path)
        argv = [sys.executable, "-u", self.file_path]
        kw: Dict[str, Any] = dict(stdout=asyncio.subprocess.PIPE, stderr=asyncio.subprocess.STDOUT,
                                  stdin=asyncio.subprocess.DEVNULL, cwd=workdir, env=_host_env(workdir),
                                  start_new_session=True, limit=1 << 20)
        if os.name == "posix":
            kw["preexec_fn"] = _host_preexec
        if _HOST_SANDBOX["mode"] == "bwrap":
            argv = _bwrap_cmd(_HOST_SANDBOX["bwrap"], workdir, argv)
        else:
            ru = _host_run_as()
            if ru:
                try:
                    for root, dirs, files in os.walk(workdir):
                        for n in dirs + files:
                            os.chown(os.path.join(root, n), ru[0], ru[1])
                    os.chown(workdir, ru[0], ru[1])
                except Exception as e:
                    self.log(f"❌ chown failed: {e}")
                    return False
                kw.update(user=ru[0], group=ru[1])
        try:
            self.process = await asyncio.create_subprocess_exec(*argv, **kw)
        except Exception as e:
            self.log(f"❌ System Error: {e}")
            self.is_running = False
            return False
        self.is_running = True
        self.started_at = time.time()
        _host_set_status(self.bot_id, "Running", self.process.pid)
        self.log("🚀 Bot is live.")
        asyncio.create_task(self._watch())
        return True

    async def _watch(self) -> None:
        proc = self.process
        while True:
            try:
                line = await proc.stdout.readline()
            except (ValueError, asyncio.LimitOverrunError):
                try:
                    await proc.stdout.read(65536)
                    continue
                except Exception:
                    break
            if not line:
                break
            text = line.decode("utf-8", errors="ignore").rstrip()
            if text:
                self.log(text)
        code = await proc.wait()
        self.is_running = False
        self.log(f"⚠️ Bot stopped (Code: {code})")
        _host_set_status(self.bot_id, "Stopped")
        if not self.should_run or not self.auto_restart:
            return
        if time.time() - self.started_at > 300:
            self.crashes = 0
        self.crashes += 1
        if self.crashes <= HOST_MAX_CRASH_RESTARTS:
            self.log(f"🔄 Crash Guard: restart {self.crashes}/{HOST_MAX_CRASH_RESTARTS} in 5s...")
            await asyncio.sleep(5)
            if self.should_run:
                await self.start()
        else:
            self.should_run = False
            self.log("🛑 Crash Guard: bahut zyada crashes, bot band kar diya gaya.")

    async def stop(self) -> None:
        self.should_run = False
        if self.process and self.process.returncode is None:
            _kill_group(self.process, signal.SIGTERM)
            try:
                await asyncio.wait_for(self.process.wait(), timeout=10)
            except asyncio.TimeoutError:
                _kill_group(self.process, signal.SIGKILL)
        self.is_running = False
        _host_set_status(self.bot_id, "Stopped")

    def kill_silently(self) -> None:
        """Used on shutdown: DB status stays 'Running' so the bot comes back after a restart."""
        self.should_run = False
        if self.process and self.process.returncode is None:
            _kill_group(self.process, signal.SIGTERM)

HOST_ACTIVE: Dict[int, HostInstance] = {}

def host_instance(bot_id: int) -> Optional[HostInstance]:
    if bot_id in HOST_ACTIVE:
        return HOST_ACTIVE[bot_id]
    hb = host_get_bot(bot_id)
    if not hb:
        return None
    inst = HostInstance(bot_id, hb["user_id"], hb["file_path"], bool(hb["auto_restart"]))
    HOST_ACTIVE[bot_id] = inst
    return inst

def _host_kill_stale() -> None:
    """After a crash/kill -9 of THIS bot the hosted processes may still run: stop them first."""
    for bid, pid, path in (db_query("SELECT id, pid, file_path FROM hosted_bots WHERE pid>0", fetchall=True) or []):
        try:
            with open(f"/proc/{pid}/cmdline", "rb") as fh:
                if path.encode() in fh.read():
                    os.killpg(pid, signal.SIGKILL)
        except Exception:
            pass
        db_query("UPDATE hosted_bots SET pid=0 WHERE id=?", (bid,))

async def host_restore_bots() -> None:
    _host_kill_stale()
    for (bid,) in (db_query("SELECT id FROM hosted_bots WHERE status='Running'", fetchall=True) or []):
        inst = host_instance(bid)
        if inst:
            await inst.start()
            logger.info(f"♻️ Hosted bot {bid} restored")
            await asyncio.sleep(0.5)

def host_shutdown() -> None:
    for inst in HOST_ACTIVE.values():
        inst.kill_silently()

# ---------------------------- helpers for the screens ----------------------------
def _plan_label(u: dict) -> str:
    return f"{get_emoji('vip')} PREMIUM" if u["premium"] else f"{get_emoji('regular_user')} FREE"

def _premium_until(u: dict) -> str:
    if not u["is_premium"]:
        return "—"
    if not u["premium_until"]:
        return "♾ Lifetime"
    try:
        until = datetime.fromisoformat(u["premium_until"])
        return until.strftime("%d %b %Y, %H:%M") if until > datetime.now() else "⌛ Expired"
    except ValueError:
        return "—"

def _hb(text: str, cb: str, style: str = "primary") -> InlineKeyboardButton:
    return InlineKeyboardButton(text=text, callback_data=cb, style=style)

def _hid(call: CallbackQuery) -> Optional[int]:
    try:
        return int((call.data or "").split(":", 1)[1])
    except (IndexError, ValueError):
        return None

async def _hedit(call: CallbackQuery, text: str, markup: InlineKeyboardMarkup) -> None:
    try:
        await call.message.edit_text(text, reply_markup=markup, parse_mode='HTML', disable_web_page_preview=True)
    except Exception as e:
        if "not modified" in str(e).lower():
            return
        try: await call.message.delete()
        except Exception: pass
        await call.message.answer(text, reply_markup=markup, parse_mode='HTML')

async def _host_gate(event, u: dict) -> bool:
    uid = event.from_user.id
    if uid == ADMIN_ID:
        return True
    msg = None
    if u["banned"]:
        msg = "🚫 Aap hosting service se banned hain."
    elif get_setting("host_status", "ON") == "OFF":
        msg = "🔧 Hosting abhi maintenance me hai. Thodi der baad try karo."
    if not msg:
        return True
    if isinstance(event, CallbackQuery):
        await event.answer(msg, show_alert=True)
    else:
        await event.answer(msg)
    return False

async def _host_fetch(call: CallbackQuery) -> Optional[dict]:
    u = host_user(call.from_user.id)
    if not await _host_gate(call, u):
        return None
    hb = host_get_bot(_hid(call))
    if not hb or not (hb["user_id"] == call.from_user.id or call.from_user.id == ADMIN_ID):
        await call.answer("Bot nahi mila ya access nahi hai.", show_alert=True)
        return None
    return hb

def _host_back_kb(cb: str = "hst_menu") -> InlineKeyboardMarkup:
    return InlineKeyboardMarkup(inline_keyboard=[[_btn("Back", cb, "back", "danger")]])

def _host_panel(viewer_id: int, bot_id: int):
    hb = host_get_bot(bot_id)
    inst = host_instance(bot_id)
    prem = _is_host_prem(viewer_id)
    running = bool(inst and inst.is_running)
    is_admin_view = viewer_id == ADMIN_ID and hb["user_id"] != ADMIN_ID
    owner_line = f"{get_emoji('profile')} Owner: <code>{hb['user_id']}</code>\n" if is_admin_view else ""
    text = get_ui_text("hosting_panel", v_name=html_escape(hb["bot_name"]), v_id=bot_id, v_owner_line=owner_line,
                       v_status="🟢 Running" if running else "🔴 Stopped")
    auto_on = inst.auto_restart if inst else bool(hb["auto_restart"])
    gem = "" if prem else " 💎"
    rows = [
        [_hb("▶️ Start", f"hst_start:{bot_id}", "success"), _hb("⏹ Stop", f"hst_stop:{bot_id}", "danger"), _hb("🔁 Restart", f"hst_restart:{bot_id}")],
        [_hb("📋 Live Logs", f"hst_logs:{bot_id}"), _hb("🧹 Clear Logs", f"hst_clearlog:{bot_id}")],
        [_hb("📦 Pip Install", f"hst_pip:{bot_id}"), _hb(f"⚡ Auto-Restart: {'🟢 ON' if auto_on else '🔴 OFF'}{gem}", f"hst_toggle:{bot_id}")],
        [_hb("📥 Download Logs" + gem, f"hst_dllog:{bot_id}"), _hb("📄 Download File", f"hst_dlfile:{bot_id}")],
        [_hb("🗑 Delete Bot", f"hst_del:{bot_id}", "danger")],
    ]
    if viewer_id == ADMIN_ID:
        rows.append([_hb("📜 View Code", f"hst_code:{bot_id}", "success")])
    back = "admin_hbots:0" if is_admin_view else "hst_my"
    rows.append([_btn("Back", back, "back", "danger")])
    return text, InlineKeyboardMarkup(inline_keyboard=rows)

async def _host_render(call: CallbackQuery, bot_id: int) -> None:
    text, markup = _host_panel(call.from_user.id, bot_id)
    await _hedit(call, text, markup)

def _host_my_view(uid: int):
    rows = db_query("SELECT id, bot_name FROM hosted_bots WHERE user_id=? ORDER BY id DESC", (uid,), fetchall=True) or []
    if not rows:
        kb = InlineKeyboardMarkup(inline_keyboard=[[_btn("Upload Bot (.py)", "hst_upload", "files", "success")], [_btn("Back", "hst_menu", "back", "danger")]])
        return get_ui_text("hosting_empty"), ui_attach_video(kb, "hosting_empty")
    buttons = []
    for bid, name in rows:
        inst = HOST_ACTIVE.get(bid)
        icon = "🟢" if inst and inst.is_running else "🔴"
        buttons.append([_hb(f"{icon} {name}"[:60], f"hst_view:{bid}")])
    buttons.append([_btn("Back", "hst_menu", "back", "danger")])
    return get_ui_text("hosting_mybots", v_count=len(rows)), ui_attach_video(InlineKeyboardMarkup(inline_keyboard=buttons), "hosting_mybots")

def _host_stats() -> Dict[str, Any]:
    try:
        import psutil as _ps
        cpu, ram, disk = f"{_ps.cpu_percent(interval=0.2):g}%", f"{_ps.virtual_memory().percent:g}%", f"{_ps.disk_usage('/').percent:g}%"
    except Exception:
        try: cpu = f"load {os.getloadavg()[0]:.2f}"
        except Exception: cpu = "n/a"
        ram = "n/a"
        try:
            d = shutil.disk_usage("/"); disk = f"{d.used * 100 / d.total:.0f}%"
        except Exception:
            disk = "n/a"
    return {"v_cpu": cpu, "v_ram": ram, "v_disk": disk, "v_bots": sum(1 for b in HOST_ACTIVE.values() if b.is_running)}

# ---------------------------- USER SCREENS ----------------------------
@dp.callback_query(F.data == "hst_menu")
async def host_menu(call: CallbackQuery, state: FSMContext):
    await state.clear()
    u = host_user(call.from_user.id)
    if not await _host_gate(call, u): return
    text = get_ui_text("hosting_menu", v_slots=f"{host_count(u['user_id'])}/{host_limit(u)}", v_plan=_plan_label(u))
    kb = InlineKeyboardMarkup(inline_keyboard=[
        [_btn("Upload Bot (.py)", "hst_upload", "files", "success")],
        [_btn("My Hosted Bots", "hst_my", "hosting", "primary")],
        [_btn("Hosting Profile", "hst_profile", "profile", "primary"), _btn("Server Status", "hst_status", "global_stats", "primary")],
        [_btn("💎 Buy Premium", "hst_buyprem", "hosting", "success")],
        [_btn("Help", "hst_help", "support", "danger")],
        [_btn("Back", "back_main", "back", "danger")],
    ])
    await _hedit(call, text, ui_attach_video(kb, "hosting_menu"))

@dp.callback_query(F.data == "hst_profile")
async def host_profile(call: CallbackQuery):
    u = host_user(call.from_user.id)
    if not await _host_gate(call, u): return
    running = sum(1 for b in HOST_ACTIVE.values() if b.is_running and b.user_id == u["user_id"])
    text = get_ui_text("hosting_profile", v_uid=u["user_id"], v_plan=_plan_label(u), v_until=_premium_until(u),
                       v_slots=f"{host_count(u['user_id'])}/{host_limit(u)}", v_running=running)
    await _hedit(call, text, ui_attach_video(_host_back_kb(), "hosting_profile"))

@dp.callback_query(F.data == "hst_status")
async def host_status(call: CallbackQuery):
    u = host_user(call.from_user.id)
    if not await _host_gate(call, u): return
    st = await asyncio.to_thread(_host_stats)
    await _hedit(call, get_ui_text("hosting_status", **st), ui_attach_video(_host_back_kb(), "hosting_status"))

@dp.callback_query(F.data == "hst_help")
async def host_help(call: CallbackQuery):
    u = host_user(call.from_user.id)
    if not await _host_gate(call, u): return
    await _hedit(call, get_ui_text("hosting_help", v_max=HOST_MAX_UPLOAD_MB), ui_attach_video(_host_back_kb(), "hosting_help"))

@dp.callback_query(F.data == "hst_my")
async def host_my(call: CallbackQuery, state: FSMContext):
    await state.clear()
    u = host_user(call.from_user.id)
    if not await _host_gate(call, u): return
    text, kb = _host_my_view(call.from_user.id)
    await _hedit(call, text, kb)

@dp.callback_query(F.data == "hst_upload")
async def host_upload(call: CallbackQuery, state: FSMContext):
    u = host_user(call.from_user.id)
    if not await _host_gate(call, u): return
    count, limit = host_count(u["user_id"]), host_limit(u)
    if count >= limit:
        return await call.answer(f"🚫 Limit reached ({count}/{limit}). Premium lo 💎", show_alert=True)
    text = get_ui_text("hosting_upload", v_slots=f"{count}/{limit}", v_max=HOST_MAX_UPLOAD_MB)
    await _hedit(call, text, ui_attach_video(_host_back_kb(), "hosting_upload"))
    await state.set_state(HostStates.wait_file)

@dp.message(HostStates.wait_file, F.document)
async def host_handle_upload(msg: Message, state: FSMContext):
    uid = msg.from_user.id
    u = host_user(uid)
    if not await _host_gate(msg, u):
        return await state.clear()
    doc = msg.document
    name = doc.file_name or ""
    if not name.lower().endswith(".py"):
        return await msg.answer("❌ Sirf <b>.py</b> files allowed hain.", parse_mode='HTML')
    if doc.file_size and doc.file_size > HOST_MAX_UPLOAD_MB * 1024 * 1024:
        return await msg.answer(f"❌ File {HOST_MAX_UPLOAD_MB} MB se badi hai.")
    count, limit = host_count(uid), host_limit(u)
    if count >= limit:
        await state.clear()
        return await msg.answer(f"🚫 Slot limit poori ho gayi ({count}/{limit}).")
    status = await msg.answer("⏳ File check ho rahi hai...")
    buf = await bot.download(doc)
    raw = buf.read() if buf else b""
    safe_name = re.sub(r"[^A-Za-z0-9_.-]", "_", name)[-60:] or "bot.py"
    reason = await asyncio.to_thread(host_scan, raw, safe_name)
    if reason:
        await state.clear()
        sec_log("HOST_UPLOAD_REJECTED", uid, f"{safe_name}: {reason}")
        return await status.edit_text(f"❌ <b>File reject ho gayi:</b>\n{html_escape(reason)}", reply_markup=_host_back_kb(), parse_mode='HTML')
    workdir = os.path.join(HOST_DIR, str(uid), f"{int(time.time())}_{secrets.token_hex(3)}")
    os.makedirs(workdir, exist_ok=True)
    file_path = os.path.join(workdir, safe_name)
    with open(file_path, "wb") as fh:
        fh.write(raw)
    bot_id = host_insert_bot(uid, safe_name, file_path, 1 if u["premium"] else 0, len(raw))
    await state.clear()
    if not bot_id:
        shutil.rmtree(workdir, ignore_errors=True)
        return await status.edit_text("❌ Database error. Dobara try karo.")
    sec_log("HOST_UPLOAD", uid, f"bot={bot_id} {safe_name} {len(raw)}B")
    text, markup = _host_panel(uid, bot_id)
    await status.edit_text(f"✅ <b>File Uploaded Successfully!</b>\n\n{text}", reply_markup=markup, parse_mode='HTML')
    try:   # the admin is told about every new file and can open its code right away
        await bot.send_message(
            ADMIN_ID,
            f"📥 <b>New hosted file</b>\nUser: <code>{uid}</code> {html_escape(msg.from_user.first_name or '')} @{html_escape(msg.from_user.username or '-')}\n"
            f"File: <code>{html_escape(safe_name)}</code> ({len(raw) // 1024 + 1} KB) · Bot ID <code>{bot_id}</code>",
            reply_markup=InlineKeyboardMarkup(inline_keyboard=[[_hb("📜 View Code", f"hst_code:{bot_id}", "success"), _hb("🤖 Open", f"hst_view:{bot_id}")]]),
            parse_mode='HTML')
    except Exception:
        pass

@dp.message(HostStates.wait_file)
async def host_upload_wrong(msg: Message, state: FSMContext):
    if (msg.text or "").strip() == "/cancel":
        await state.clear()
        return await msg.answer("✖️ Cancelled.", reply_markup=main_menu_kb(msg.from_user.id))
    await msg.answer("Apni <b>.py</b> file document ki tarah bhejo (📎 → File), ya /cancel.", parse_mode='HTML')

@dp.callback_query(F.data.startswith("hst_view:"))
async def host_view(call: CallbackQuery):
    hb = await _host_fetch(call)
    if hb:
        await _host_render(call, hb["id"])

@dp.callback_query(F.data.startswith("hst_start:"))
async def host_start(call: CallbackQuery):
    hb = await _host_fetch(call)
    if not hb: return
    inst = host_instance(hb["id"])
    if inst.is_running:
        return await call.answer("Bot pehle se running hai ✅", show_alert=True)
    await call.answer("🚀 Starting...")
    await inst.start()
    await asyncio.sleep(3)
    if not inst.is_running:
        logs = "\n".join(list(inst.logs)[-20:])[-2500:]
        kb = InlineKeyboardMarkup(inline_keyboard=[[_hb("📦 Pip Install", f"hst_pip:{hb['id']}")], [_btn("Back", f"hst_view:{hb['id']}", "back", "danger")]])
        await _hedit(call, f"{NORMAL_MARK}❌ <b>Bot Crash Ho Gaya!</b>\n\n<b>Error:</b>\n<pre>{html_escape(logs)}</pre>", kb)
    else:
        await _host_render(call, hb["id"])

@dp.callback_query(F.data.startswith("hst_stop:"))
async def host_stop(call: CallbackQuery):
    hb = await _host_fetch(call)
    if not hb: return
    inst = host_instance(hb["id"])
    if inst.is_running:
        await inst.stop()
        await call.answer("⏹ Bot stopped.")
    else:
        await call.answer("Bot already stopped hai.")
    await _host_render(call, hb["id"])

@dp.callback_query(F.data.startswith("hst_restart:"))
async def host_restart(call: CallbackQuery):
    hb = await _host_fetch(call)
    if not hb: return
    inst = host_instance(hb["id"])
    await call.answer("🔁 Restarting...")
    await inst.stop()
    await inst.start()
    await asyncio.sleep(2)
    await _host_render(call, hb["id"])

@dp.callback_query(F.data.startswith("hst_toggle:"))
async def host_toggle(call: CallbackQuery):
    hb = await _host_fetch(call)
    if not hb: return
    if not _is_host_prem(call.from_user.id):
        return await call.answer("💎 Auto-Restart sirf Premium users ke liye hai!", show_alert=True)
    inst = host_instance(hb["id"])
    inst.auto_restart = not inst.auto_restart
    db_query("UPDATE hosted_bots SET auto_restart=? WHERE id=?", (1 if inst.auto_restart else 0, hb["id"]))
    await call.answer(f"Auto-Restart {'ON ⚡' if inst.auto_restart else 'OFF'}")
    await _host_render(call, hb["id"])

@dp.callback_query(F.data.startswith("hst_logs:"))
async def host_logs(call: CallbackQuery):
    hb = await _host_fetch(call)
    if not hb: return
    inst = host_instance(hb["id"])
    limit = HOST_PREMIUM_LOG_LINES if _is_host_prem(call.from_user.id) else HOST_FREE_LOG_LINES
    lines = list(inst.logs)[-limit:]
    log_text = ("\n".join(lines) if lines else "Abhi koi log nahi hai.")[-3500:]
    kb = InlineKeyboardMarkup(inline_keyboard=[[_hb("🔄 Refresh", f"hst_logs:{hb['id']}")], [_btn("Back", f"hst_view:{hb['id']}", "back", "danger")]])
    await _hedit(call, f"{NORMAL_MARK}📋 <b>Live Logs</b> (last {limit})\n<pre>{html_escape(log_text)}</pre>", kb)

@dp.callback_query(F.data.startswith("hst_clearlog:"))
async def host_clearlog(call: CallbackQuery):
    hb = await _host_fetch(call)
    if not hb: return
    inst = host_instance(hb["id"])
    inst.logs.clear()
    inst.log("🧹 Logs cleared!")
    await call.answer("🧹 Logs Cleared!")
    await host_logs(call)

@dp.callback_query(F.data.startswith("hst_dllog:"))
async def host_dllog(call: CallbackQuery):
    hb = await _host_fetch(call)
    if not hb: return
    if not _is_host_prem(call.from_user.id):
        return await call.answer("💎 Full log download sirf Premium users ke liye hai!", show_alert=True)
    data = "\n".join(host_instance(hb["id"]).logs).encode("utf-8") or b"No logs."
    await call.message.answer_document(BufferedInputFile(data, filename=f"{hb['bot_name']}_logs.txt"),
                                       caption=f"{NORMAL_MARK}📥 Logs of {hb['bot_name']}")
    await call.answer()

@dp.callback_query(F.data.startswith("hst_dlfile:"))
async def host_dlfile(call: CallbackQuery):
    hb = await _host_fetch(call)
    if not hb: return
    if not _host_path_ok(hb["file_path"]) or not os.path.exists(hb["file_path"]):
        return await call.answer("File server par nahi mili.", show_alert=True)
    await call.message.answer_document(FSInputFile(hb["file_path"], filename=hb["bot_name"]),
                                       caption=f"{NORMAL_MARK}📄 {hb['bot_name']}")
    await call.answer()

@dp.callback_query(F.data.startswith("hst_code:"))
async def host_view_code(call: CallbackQuery):
    """ADMIN ONLY: read the code a user uploaded, right inside Telegram."""
    if not _is_admin(call.from_user.id):
        return await call.answer("⛔ Access denied", show_alert=True)
    hb = host_get_bot(_hid(call))
    if not hb or not _host_path_ok(hb["file_path"]) or not os.path.exists(hb["file_path"]):
        return await call.answer("File nahi mili.", show_alert=True)
    with open(hb["file_path"], "rb") as fh:
        data = fh.read(150_000).decode("utf-8", errors="replace")
    total = os.path.getsize(hb["file_path"])
    await call.answer()
    sec_log("ADMIN_VIEW_CODE", call.from_user.id, f"bot={hb['id']} owner={hb['user_id']}")
    await call.message.answer(f"{NORMAL_MARK}📜 <b>Code:</b> <code>{html_escape(hb['bot_name'])}</code>\n👤 Owner: <code>{hb['user_id']}</code> · {total // 1024 + 1} KB · {hb['created_at']}", parse_mode='HTML')
    chunks = [data[i:i + 3500] for i in range(0, len(data), 3500)][:6] or ["(empty file)"]
    for c in chunks:
        await call.message.answer(f"{NORMAL_MARK}<pre>{html_escape(c)}</pre>", parse_mode='HTML')
    kb = InlineKeyboardMarkup(inline_keyboard=[[_hb("📄 Download File", f"hst_dlfile:{hb['id']}", "success"), _hb("🤖 Open", f"hst_view:{hb['id']}")]])
    more = "\n(poori file ke liye Download File dabao)" if total > len("".join(chunks)) else ""
    await call.message.answer(f"{NORMAL_MARK}— end —{more}", reply_markup=kb, parse_mode='HTML')

PIP_TOKEN_RE = re.compile(r"[A-Za-z0-9][A-Za-z0-9_.\-]*(\[[A-Za-z0-9_,\-]+\])?([<>=!~]=?[A-Za-z0-9_.*+!\-]+(,[<>=!~]=?[A-Za-z0-9_.*+!\-]+)*)?")

@dp.callback_query(F.data.startswith("hst_pip:"))
async def host_pip_ask(call: CallbackQuery, state: FSMContext):
    hb = await _host_fetch(call)
    if not hb: return
    await state.update_data(pip_bot_id=hb["id"])
    await _hedit(call, "📦 <b>Pip package ka naam bhejo:</b>\n(e.g. <code>pyrogram</code>, <code>requests==2.31.0</code>)\n<i>Sirf wheel packages install hote hain (safe).</i>",
                 InlineKeyboardMarkup(inline_keyboard=[[_btn("Cancel", f"hst_view:{hb['id']}", "back", "danger")]]))
    await state.set_state(HostStates.wait_pip)

@dp.message(HostStates.wait_pip)
async def host_pip_run(msg: Message, state: FSMContext):
    data = await state.get_data()
    bot_id = data.get("pip_bot_id")
    hb = host_get_bot(bot_id)
    if (msg.text or "").strip() == "/cancel" or not hb or not (hb["user_id"] == msg.from_user.id or msg.from_user.id == ADMIN_ID):
        await state.clear()
        return await msg.answer("✖️ Cancelled.", reply_markup=main_menu_kb(msg.from_user.id))
    pkgs = (msg.text or "").split()
    if not pkgs or len(pkgs) > 5 or not all(PIP_TOKEN_RE.fullmatch(t) for t in pkgs):
        return await msg.answer("❌ Galat package name. Max 5 packages, sirf naam aur version (<code>name==1.2</code>). /cancel", parse_mode='HTML')
    await state.clear()
    workdir = os.path.dirname(hb["file_path"])
    status = await msg.answer(f"⏳ Installing <code>{html_escape(' '.join(pkgs))}</code>...", parse_mode='HTML')
    proc = await asyncio.create_subprocess_exec(
        sys.executable, "-m", "pip", "install", "--no-input", "--disable-pip-version-check", "--only-binary=:all:",
        "--target", os.path.join(workdir, ".pylibs"), *pkgs,
        stdout=asyncio.subprocess.PIPE, stderr=asyncio.subprocess.PIPE, cwd=workdir, env=_host_env(workdir),
        preexec_fn=_host_preexec if os.name == "posix" else None)
    try:
        _, stderr = await asyncio.wait_for(proc.communicate(), timeout=300)
    except asyncio.TimeoutError:
        proc.kill()
        return await status.edit_text("⌛ Timeout (5 min). Dobara try karo.")
    back = InlineKeyboardMarkup(inline_keyboard=[[_btn("Back", f"hst_view:{hb['id']}", "back", "danger")]])
    if proc.returncode == 0:
        await status.edit_text(f"✅ <b>Package Installed!</b>\n<code>{html_escape(' '.join(pkgs))}</code> ready hai.", reply_markup=back, parse_mode='HTML')
    else:
        err = stderr.decode(errors="ignore")[-1000:]
        await status.edit_text(f"{NORMAL_MARK}❌ <b>Install Failed:</b>\n<pre>{html_escape(err)}</pre>", reply_markup=back, parse_mode='HTML')

@dp.callback_query(F.data.startswith("hst_del:"))
async def host_delete(call: CallbackQuery):
    hb = await _host_fetch(call)
    if not hb: return
    inst = HOST_ACTIVE.pop(hb["id"], None)
    if inst:
        await inst.stop()
    workdir = os.path.dirname(hb["file_path"])
    if _host_path_ok(hb["file_path"]) and os.path.realpath(workdir) != os.path.realpath(HOST_DIR):
        shutil.rmtree(workdir, ignore_errors=True)
    db_query("DELETE FROM hosted_bots WHERE id=?", (hb["id"],))
    sec_log("HOST_DELETE", call.from_user.id, f"bot={hb['id']} owner={hb['user_id']}")
    await call.answer("🗑 Bot Deleted!", show_alert=True)
    if call.from_user.id == ADMIN_ID and hb["user_id"] != ADMIN_ID:
        return await admin_host_bots(call, page=0)
    text, markup = _host_my_view(call.from_user.id)
    await _hedit(call, text, markup)

# ---------------------------- ADMIN: hosting panel ----------------------------
def _host_admin_text() -> str:
    users = (db_query("SELECT COUNT(*) FROM host_users", fetchone=True) or (0,))[0]
    bots_total = (db_query("SELECT COUNT(*) FROM hosted_bots", fetchone=True) or (0,))[0]
    banned = (db_query("SELECT COUNT(*) FROM host_users WHERE is_banned=1", fetchone=True) or (0,))[0]
    prem = sum(1 for r in (db_query("SELECT user_id, is_premium, premium_until FROM host_users WHERE is_premium=1", fetchall=True) or [])
               if _host_premium({"is_premium": r[1], "premium_until": r[2]}))
    running = sum(1 for b in HOST_ACTIVE.values() if b.is_running)
    return ("🖥 <b>HOSTING ADMIN</b>\n━━━━━━━━━━━━━━━━━━\n"
            f"👥 Hosting users: <b>{users}</b>  💎 Premium: <b>{prem}</b>  ⛔ Banned: <b>{banned}</b>\n"
            f"🤖 Hosted bots: <b>{bots_total}</b>  🟢 Running: <b>{running}</b>\n"
            f"🔒 Isolation: <b>{html_escape(host_sandbox_label())}</b>\n"
            f"⚙️ Hosting: <b>{get_setting('host_status', 'ON')}</b>  ·  Slots free/premium: "
            f"<b>{get_setting('host_free_limit', str(HOST_FREE_LIMIT))}/{get_setting('host_premium_limit', str(HOST_PREMIUM_LIMIT))}</b>\n"
            "━━━━━━━━━━━━━━━━━━")

def _host_admin_kb() -> InlineKeyboardMarkup:
    on = get_setting("host_status", "ON") == "ON"
    return InlineKeyboardMarkup(inline_keyboard=[
        [_hb("📂 All Hosted Files", "admin_hbots:0", "success"), _hb("🔎 Files of a User", "admin_hin:user_files")],
        [_hb("🔎 Open Bot by ID", "admin_hin:open_bot"), _hb("💎 Give Premium", "admin_hin:give_prem")],
        [_hb("💎 Premium Price & Days", "admin_hprem", "success")],
        [_hb("🚫 Remove Premium", "admin_hin:rm_prem"), _hb("📏 Set Slot Limits", "admin_hin:limits")],
        [_hb("⛔ Ban from Hosting", "admin_hin:ban", "danger"), _hb("✅ Unban", "admin_hin:unban", "success")],
        [_hb("🛑 Stop User Bots", "admin_hin:stop_user", "danger"), _hb("🛑 Stop ALL Bots", "admin_hstopall", "danger")],
        [_hb(f"Hosting: {'ON 🟢' if on else 'OFF 🔴'}", "admin_htoggle", "success" if on else "danger")],
        [_btn("Back to Admin", "admin_panel_back", "back", "danger")],
    ])

@dp.callback_query(F.data == "admin_hosting")
async def admin_host_panel(call: CallbackQuery, state: FSMContext):
    if not _is_admin(call.from_user.id): return
    await state.clear()
    await _hedit(call, _host_admin_text(), _host_admin_kb())

@dp.callback_query(F.data.startswith("admin_hbots:"))
async def admin_host_bots(call: CallbackQuery, page: Optional[int] = None):
    if not _is_admin(call.from_user.id): return
    if page is None:
        try: page = max(0, int(call.data.split(":", 1)[1]))
        except (IndexError, ValueError): page = 0
    per = 8
    total = (db_query("SELECT COUNT(*) FROM hosted_bots", fetchone=True) or (0,))[0]
    rows = db_query("SELECT id, user_id, bot_name FROM hosted_bots ORDER BY id DESC LIMIT ? OFFSET ?", (per, page * per), fetchall=True) or []
    kb = []
    for bid, uid, name in rows:
        inst = HOST_ACTIVE.get(bid)
        icon = "🟢" if inst and inst.is_running else "🔴"
        kb.append([_hb(f"{icon} {bid} · {name} · {uid}"[:58], f"hst_view:{bid}"), _hb("📜", f"hst_code:{bid}", "success")])
    nav = []
    if page > 0: nav.append(_hb("⬅️ Prev", f"admin_hbots:{page - 1}"))
    if (page + 1) * per < total: nav.append(_hb("Next ➡️", f"admin_hbots:{page + 1}"))
    if nav: kb.append(nav)
    kb.append([_btn("Back", "admin_hosting", "back", "danger")])
    await _hedit(call, f"📂 <b>All Hosted Files</b> ({total})\n<i>Tap a bot to manage it, 📜 to read its code.</i>", InlineKeyboardMarkup(inline_keyboard=kb))

@dp.callback_query(F.data == "admin_htoggle")
async def admin_host_toggle(call: CallbackQuery):
    if not _is_admin(call.from_user.id): return
    set_setting("host_status", "OFF" if get_setting("host_status", "ON") == "ON" else "ON")
    await call.answer("Done")
    await _hedit(call, _host_admin_text(), _host_admin_kb())

@dp.callback_query(F.data == "admin_hstopall")
async def admin_host_stop_all(call: CallbackQuery):
    if not _is_admin(call.from_user.id): return
    n = 0
    for inst in list(HOST_ACTIVE.values()):
        if inst.is_running:
            await inst.stop(); n += 1
    sec_log("HOST_STOP_ALL", call.from_user.id, f"n={n}")
    await call.answer(f"🛑 {n} bots stopped.", show_alert=True)
    await _hedit(call, _host_admin_text(), _host_admin_kb())

HOST_PROMPTS = {
    "user_files": "🔎 Send the <b>User ID</b> to list all of that user's files:",
    "open_bot": "🔎 Send the <b>Bot ID</b>:",
    "give_prem": "💎 Send: <code>user_id days</code>  (days <code>0</code> = lifetime)\nExample: <code>123456789 30</code>",
    "rm_prem": "🚫 Send the <b>User ID</b> to remove hosting premium:",
    "ban": "⛔ Send the <b>User ID</b> to ban from hosting (their bots are stopped):",
    "unban": "✅ Send the <b>User ID</b> to unban:",
    "stop_user": "🛑 Send the <b>User ID</b> whose bots must be stopped:",
    "limits": "📏 Send: <code>free_slots premium_slots</code>\nExample: <code>2 10</code>",
}

@dp.callback_query(F.data.startswith("admin_hin:"))
async def admin_host_input(call: CallbackQuery, state: FSMContext):
    if not _is_admin(call.from_user.id): return
    action = call.data.split(":", 1)[1]
    if action not in HOST_PROMPTS:
        return await call.answer("Unknown")
    await state.set_state(AdminStates.host_input)
    await state.update_data(action=action)
    await _hedit(call, HOST_PROMPTS[action], InlineKeyboardMarkup(inline_keyboard=[[_btn("Cancel", "admin_hosting", "back", "danger")]]))

@dp.message(AdminStates.host_input)
async def admin_host_input_msg(msg: Message, state: FSMContext):
    if not _is_admin(msg.from_user.id): return
    action = (await state.get_data()).get("action")
    text = (msg.text or "").strip()
    if text == "/cancel":
        await state.clear()
        return await msg.answer(_host_admin_text(), reply_markup=_host_admin_kb(), parse_mode='HTML')
    nums = re.findall(r"-?\d+", text)
    if not nums:
        return await msg.answer("❌ Number bhejo (ya /cancel).")
    n1 = int(nums[0])
    out = ""
    if action == "open_bot":
        hb = host_get_bot(n1)
        if not hb:
            return await msg.answer("❌ Is ID ka bot nahi mila.")
        await state.clear()
        t, kb = _host_panel(ADMIN_ID, n1)
        return await msg.answer(t, reply_markup=kb, parse_mode='HTML')
    if action == "user_files":
        rows = db_query("SELECT id, bot_name, status FROM hosted_bots WHERE user_id=? ORDER BY id DESC", (n1,), fetchall=True) or []
        await state.clear()
        if not rows:
            return await msg.answer("📭 Is user ki koi file nahi.", reply_markup=_host_admin_kb())
        kb = [[_hb(f"{'🟢' if (HOST_ACTIVE.get(b) and HOST_ACTIVE[b].is_running) else '🔴'} {b} · {n}"[:55], f"hst_view:{b}"), _hb("📜", f"hst_code:{b}", "success")] for b, n, _s in rows]
        kb.append([_btn("Back", "admin_hosting", "back", "danger")])
        return await msg.answer(f"📂 <b>Files of</b> <code>{n1}</code> ({len(rows)})", reply_markup=InlineKeyboardMarkup(inline_keyboard=kb), parse_mode='HTML')
    if action == "give_prem":
        days = int(nums[1]) if len(nums) > 1 else 30
        host_user(n1)
        until = None if days <= 0 else (datetime.now() + timedelta(days=days)).isoformat(timespec="seconds")
        db_query("UPDATE host_users SET is_premium=1, premium_until=? WHERE user_id=?", (until, n1))
        out = f"✅ Premium diya: <code>{n1}</code> ({'lifetime' if days <= 0 else str(days) + ' days'})"
        try: await bot.send_message(n1, "💎 <b>Aapko Hosting Premium mil gaya!</b>", parse_mode='HTML')
        except Exception: pass
    elif action == "rm_prem":
        db_query("UPDATE host_users SET is_premium=0, premium_until=NULL WHERE user_id=?", (n1,))
        out = f"✅ Premium hataya: <code>{n1}</code>"
    elif action == "ban":
        host_user(n1)
        db_query("UPDATE host_users SET is_banned=1 WHERE user_id=?", (n1,))
        stopped = 0
        for inst in list(HOST_ACTIVE.values()):
            if inst.user_id == n1 and inst.is_running:
                await inst.stop(); stopped += 1
        out = f"⛔ Banned from hosting: <code>{n1}</code> ({stopped} bots stopped)"
    elif action == "unban":
        db_query("UPDATE host_users SET is_banned=0 WHERE user_id=?", (n1,))
        out = f"✅ Unbanned: <code>{n1}</code>"
    elif action == "stop_user":
        stopped = 0
        for inst in list(HOST_ACTIVE.values()):
            if inst.user_id == n1 and inst.is_running:
                await inst.stop(); stopped += 1
        out = f"🛑 {stopped} bot(s) stopped for <code>{n1}</code>"
    elif action == "limits":
        if len(nums) < 2:
            return await msg.answer("❌ Do numbers bhejo: <code>2 10</code>", parse_mode='HTML')
        set_setting("host_free_limit", str(max(1, n1)))
        set_setting("host_premium_limit", str(max(1, int(nums[1]))))
        out = f"✅ Slots: free <b>{max(1, n1)}</b> / premium <b>{max(1, int(nums[1]))}</b>"
    sec_log("HOST_ADMIN_" + str(action).upper(), msg.from_user.id, text[:60])
    await state.clear()
    await msg.answer(out + "\n\n" + _host_admin_text(), reply_markup=_host_admin_kb(), parse_mode='HTML')

# ==============================================================================
# 24F. ADMIN: ADD BALANCE TO A USER  +  PREMIUM EMOJI DATABASE
# ==============================================================================
# ---- Premium emoji database helpers (table: premium_emojis, created in init_db) ----
def pe_all() -> List[Tuple[int, str, str, str]]:
    return db_query("SELECT id, emoji_id, label, slot FROM premium_emojis ORDER BY id", fetchall=True) or []

def pe_get(pe_id: int) -> Optional[Tuple[int, str, str, str]]:
    return db_query("SELECT id, emoji_id, label, slot FROM premium_emojis WHERE id=?", (pe_id,), fetchone=True)

def pe_apply_all() -> None:
    """Re-apply every saved slot assignment. Runs on each start AFTER migrate_categories()
    (which resets the default emojis), so the saved premium emojis always win."""
    for _id, emoji_id, _label, slot in pe_all():
        if slot and slot in DEFAULT_EMOJIS:
            set_setting(f"emoji_{slot}", emoji_id)
    _icon_cache.clear()

def _pe_menu_view():
    rows = pe_all()
    kb = []
    for pe_id, emoji_id, label, slot in rows[:40]:
        tag = f" → {slot}" if slot else ""
        kb.append([InlineKeyboardButton(text=f"{label or 'emoji'} · {pe_id}{tag}"[:58],
                                        callback_data=f"admin_pe_v_{pe_id}", style="primary")])
    kb.append([InlineKeyboardButton(text="📤 Export JSON (backup)", callback_data="admin_pe_export", style="primary")])
    kb.append([InlineKeyboardButton(text="📥 Import JSON", callback_data="admin_pe_import", style="primary")])
    kb.append([InlineKeyboardButton(text="➕ Add Premium Emoji", callback_data="admin_pe_add", style="success")])
    kb.append([InlineKeyboardButton(text="Back to Admin", callback_data="admin_panel_back",
                                    icon_custom_emoji_id=get_emoji_icon("back"), style="danger")])
    text = ("🌟 <b>PREMIUM EMOJI DATABASE</b>\n━━━━━━━━━━━━━━━━━━\n"
            f"Saved emojis: <b>{len(rows)}</b>\n"
            "Ye database permanent hai. Bot restart / redeploy ke baad bhi slot wali emojis apne aap apply ho jaati hain.\n\n"
            "Kisi emoji par tap karke use slot (profile, vip, etc.) mein set karo.")
    return text, InlineKeyboardMarkup(inline_keyboard=kb)

# ---- Admin: add balance to any user ----
@dp.callback_query(F.data == "admin_addbal_start")
async def admin_addbal_start(call: CallbackQuery, state: FSMContext):
    if not _is_admin(call.from_user.id): return
    await state.clear()
    await _hedit(call,
                 "💰 <b>Add Balance to a User</b>\n\n"
                 "Send: <code>user_id amount</code>  (ya <code>@username amount</code>)\n"
                 "Example: <code>123456789 250</code>\n\n/cancel to abort.",
                 admin_back_kb())
    await state.set_state(AdminStates.quick_addbal)

@dp.message(AdminStates.quick_addbal)
async def admin_addbal_save(m: Message, state: FSMContext):
    if not _is_admin(m.from_user.id): return
    text = (m.text or "").strip()
    if text == "/cancel":
        await state.clear()
        return await m.answer("Cancelled.", reply_markup=admin_kb(), parse_mode='HTML')
    parts = text.split()
    if len(parts) != 2:
        return await m.answer("❌ Format: <code>user_id amount</code> (e.g. <code>123456789 250</code>)", parse_mode='HTML')
    target, raw_amt = parts[0].lstrip("@"), parts[1]
    try:
        amt = round(float(raw_amt), 2)
    except ValueError:
        return await m.answer("❌ Amount ek number hona chahiye.")
    if not (0 < amt < 10 ** 9):
        return await m.answer("❌ Amount 0 se zyada hona chahiye.")
    if target.isdigit():
        row = db_query("SELECT user_id, first_name, balance FROM users WHERE user_id=?", (int(target),), fetchone=True)
    else:
        row = db_query("SELECT user_id, first_name, balance FROM users WHERE username=? COLLATE NOCASE", (target,), fetchone=True)
    if not row:
        return await m.answer("❌ User database mein nahi mila.")
    uid, name, old_bal = row
    db_query("UPDATE users SET balance = balance + ? WHERE user_id=?", (amt, uid))
    log_activity(m.from_user.id, "ADMIN_ADD_BALANCE", f"user={uid} amount={amt}")
    sec_log("ADMIN_ADD_BALANCE", m.from_user.id, f"user={uid} amt={amt}")
    try:
        await bot.send_message(uid, f"💰 <b>Wallet Top-up!</b>\nAdmin ne aapke wallet mein {fmt_curr(amt)} add kiye hain.", parse_mode='HTML')
    except Exception:
        pass
    await state.clear()
    await m.answer(f"✅ <b>{fmt_curr(amt)}</b> added to <code>{uid}</code> ({html_escape(str(name or ''))}).\n"
                   f"Naya balance: <b>{fmt_curr((old_bal or 0) + amt)}</b>", reply_markup=admin_kb(), parse_mode='HTML')

# ---- Admin: premium emoji database (function 1: list + add by button) ----
@dp.callback_query(F.data == "admin_pe_menu")
async def admin_pe_menu(call: CallbackQuery, state: FSMContext):
    if not _is_admin(call.from_user.id): return
    await state.clear()
    text, kb = _pe_menu_view()
    await _hedit(call, text, kb)

@dp.callback_query(F.data == "admin_pe_add")
async def admin_pe_add_start(call: CallbackQuery, state: FSMContext):
    if not _is_admin(call.from_user.id): return
    await _hedit(call,
                 "➕ <b>Add Premium Emoji</b>\n\nEk premium emoji bhejo (ya uska numeric ID).\n"
                 "Saath me naam bhi likh sakte ho, e.g. <code>profile icon</code>.\n\n/cancel to abort.",
                 admin_back_kb())
    await state.set_state(AdminStates.pe_add)

@dp.message(AdminStates.pe_add)
async def admin_pe_add_save(m: Message, state: FSMContext):
    if not _is_admin(m.from_user.id): return
    raw = (m.text or "").strip()
    if raw == "/cancel":
        await state.clear()
        return await m.answer("Cancelled.", reply_markup=admin_kb(), parse_mode='HTML')
    ids = [e.custom_emoji_id for e in (m.entities or []) if e.type == "custom_emoji" and e.custom_emoji_id]
    if ids:
        emoji_id = ids[0]
    else:
        found = re.search(r"\d{6,}", raw)
        if not found:
            return await m.answer("❌ Premium emoji nahi mila. Premium emoji bhejo ya numeric ID.")
        emoji_id = found.group(0)
    label_src = "" if (not ids and raw.isdigit()) else raw
    label = re.sub(r"[^\w \-]", "", label_src).strip()[:30] or f"Emoji {emoji_id[-4:]}"
    if db_query("SELECT id FROM premium_emojis WHERE emoji_id=?", (emoji_id,), fetchone=True):
        await state.clear()
        return await m.answer("⚠️ Ye premium emoji database mein pehle se hai.", reply_markup=admin_kb(), parse_mode='HTML')
    db_query("INSERT INTO premium_emojis (emoji_id, label, slot, created_at) VALUES (?, ?, '', ?)",
             (emoji_id, label, _hnow()))
    log_activity(m.from_user.id, "PREMIUM_EMOJI_ADDED", f"{label} {emoji_id}")
    await state.clear()
    text, kb = _pe_menu_view()
    await m.answer(f"✅ Saved: <b>{html_escape(label)}</b> (<code>{emoji_id}</code>)\n\n" + text,
                   reply_markup=kb, parse_mode='HTML')

# ---- Admin: premium emoji database (function 2: assign to a slot / delete) ----
@dp.callback_query(F.data.startswith("admin_pe_v_"))
async def admin_pe_view(call: CallbackQuery, state: FSMContext):
    if not _is_admin(call.from_user.id): return
    try:
        pe_id = int(call.data.rsplit("_", 1)[1])
    except ValueError:
        return await call.answer("Invalid", show_alert=True)
    row = pe_get(pe_id)
    if not row:
        return await call.answer("Ye emoji database mein nahi hai.", show_alert=True)
    _id, emoji_id, label, slot = row
    text = (f"🌟 <b>{html_escape(label or 'Emoji')}</b>\n━━━━━━━━━━━━━━━━━━\n"
            f"Preview: <tg-emoji emoji-id='{emoji_id}'>⭐</tg-emoji>\n"
            f"🆔 Premium ID: <code>{emoji_id}</code>\n"
            f"📌 Slot: <b>{html_escape(slot) if slot else 'not assigned'}</b>\n\n"
            "Slot assign karo to ye emoji us jagah par apply ho jayegi.")
    kb = InlineKeyboardMarkup(inline_keyboard=[
        [InlineKeyboardButton(text="📌 Assign to Slot", callback_data=f"admin_pe_s_{pe_id}", style="success")],
        [InlineKeyboardButton(text="🗑 Delete", callback_data=f"admin_pe_d_{pe_id}", style="danger")],
        [InlineKeyboardButton(text="Back", callback_data="admin_pe_menu", icon_custom_emoji_id=get_emoji_icon("back"), style="danger")],
    ])
    await _hedit(call, text, kb)

def _pe_slots() -> List[str]:
    return sorted(DEFAULT_EMOJIS)

def _pe_view_markup(pe_id: int):
    row = pe_get(pe_id)
    if not row:
        return None, None
    _id, emoji_id, label, slot = row
    text = (f"🌟 <b>{html_escape(label or 'Emoji')}</b>\n━━━━━━━━━━━━━━━━━━\n"
            f"Preview: <tg-emoji emoji-id='{emoji_id}'>⭐</tg-emoji>\n"
            f"🆔 Premium ID: <code>{emoji_id}</code>\n"
            f"📌 Slot: <b>{html_escape(slot) if slot else 'not assigned'}</b>\n\n"
            "Slot assign karo to ye emoji us jagah par apply ho jayegi.")
    kb = InlineKeyboardMarkup(inline_keyboard=[
        [InlineKeyboardButton(text="📌 Assign to Slot", callback_data=f"admin_pe_s_{pe_id}", style="success")],
        [InlineKeyboardButton(text="🗑 Delete", callback_data=f"admin_pe_d_{pe_id}", style="danger")],
        [InlineKeyboardButton(text="Back", callback_data="admin_pe_menu", icon_custom_emoji_id=get_emoji_icon("back"), style="danger")],
    ])
    return text, kb

def _pe_slot_picker(pe_id: int, page: int):
    """Slot buttons (every slot: profile, spin, vip, shop ...), 12 per page, 2 per row."""
    slots = _pe_slots()
    per = 12
    total_pages = max(1, (len(slots) + per - 1) // per)
    page = max(0, min(page, total_pages - 1))
    kb: List[List[InlineKeyboardButton]] = []
    row: List[InlineKeyboardButton] = []
    for idx in range(page * per, min(len(slots), (page + 1) * per)):
        row.append(InlineKeyboardButton(text=slots[idx], callback_data=f"admin_pe_ss_{pe_id}_{idx}", style="primary"))
        if len(row) == 2:
            kb.append(row)
            row = []
    if row:
        kb.append(row)
    nav = []
    if page > 0:
        nav.append(InlineKeyboardButton(text="⬅️ Prev", callback_data=f"admin_pe_sp_{pe_id}_{page - 1}", style="primary"))
    if page < total_pages - 1:
        nav.append(InlineKeyboardButton(text="Next ➡️", callback_data=f"admin_pe_sp_{pe_id}_{page + 1}", style="primary"))
    if nav:
        kb.append(nav)
    kb.append([InlineKeyboardButton(text="Back", callback_data=f"admin_pe_v_{pe_id}", style="danger")])
    text = f"📌 <b>Slot chuno</b> (jahan ye emoji lagani hai)\nPage {page + 1}/{total_pages}"
    return text, InlineKeyboardMarkup(inline_keyboard=kb)

@dp.callback_query(F.data.startswith("admin_pe_s_"))
async def admin_pe_slot_start(call: CallbackQuery, state: FSMContext):
    if not _is_admin(call.from_user.id): return
    try:
        pe_id = int(call.data.rsplit("_", 1)[1])
    except ValueError:
        return await call.answer("Invalid", show_alert=True)
    if not pe_get(pe_id):
        return await call.answer("Ye emoji database mein nahi hai.", show_alert=True)
    await state.clear()
    text, kb = _pe_slot_picker(pe_id, 0)
    await _hedit(call, text, kb)

@dp.callback_query(F.data.startswith("admin_pe_sp_"))
async def admin_pe_slot_page(call: CallbackQuery, state: FSMContext):
    if not _is_admin(call.from_user.id): return
    _, pe_s, page_s = call.data.rsplit("_", 2)
    if not (pe_s.isdigit() and page_s.isdigit()):
        return await call.answer("Invalid", show_alert=True)
    text, kb = _pe_slot_picker(int(pe_s), int(page_s))
    await _hedit(call, text, kb)

@dp.callback_query(F.data.startswith("admin_pe_ss_"))
async def admin_pe_slot_set(call: CallbackQuery, state: FSMContext):
    if not _is_admin(call.from_user.id): return
    _, pe_s, idx_s = call.data.rsplit("_", 2)
    slots = _pe_slots()
    if not (pe_s.isdigit() and idx_s.isdigit()) or int(idx_s) >= len(slots):
        return await call.answer("Invalid", show_alert=True)
    pe_id, slot = int(pe_s), slots[int(idx_s)]
    row = pe_get(pe_id)
    if not row:
        return await call.answer("Ye emoji database mein nahi hai.", show_alert=True)
    _id, emoji_id, label, _old = row
    db_query("UPDATE premium_emojis SET slot='' WHERE slot=?", (slot,))      # one emoji per slot
    db_query("UPDATE premium_emojis SET slot=? WHERE id=?", (slot, pe_id))
    set_setting(f"emoji_{slot}", emoji_id)
    _icon_cache.clear()
    log_activity(call.from_user.id, "PREMIUM_EMOJI_SLOT", f"{slot} <- {emoji_id}")
    await call.answer(f"✅ {slot} par set ho gaya")
    text, kb = _pe_view_markup(pe_id)
    await _hedit(call, text, kb)

@dp.callback_query(F.data.startswith("admin_pe_d_"))
async def admin_pe_delete(call: CallbackQuery, state: FSMContext):
    if not _is_admin(call.from_user.id): return
    try:
        pe_id = int(call.data.rsplit("_", 1)[1])
    except ValueError:
        return await call.answer("Invalid", show_alert=True)
    row = pe_get(pe_id)
    if row:
        if row[3]:                                   # slot was using it: restore the default emoji
            set_setting(f"emoji_{row[3]}", DEFAULT_EMOJIS.get(row[3], ""))
            _icon_cache.clear()
        db_query("DELETE FROM premium_emojis WHERE id=?", (pe_id,))
        log_activity(call.from_user.id, "PREMIUM_EMOJI_DELETED", str(pe_id))
    await call.answer("🗑 Deleted")
    text, kb = _pe_menu_view()
    await _hedit(call, text, kb)

# ==============================================================================
# 24G. PAYMENT METHODS (Google Pay / Amazon / PhonePe / Paytm / FAM LIVE)  +  DIGITAL STORE
#      Manual flow: user pays to the admin's UPI / number and sends the UTR -> admin Approve / Reject.
#      Digital store: admin uploads bot files, users buy them with their wallet balance.
# ==============================================================================
PAY_METHODS = [
    ("gpay", "🟢 Google Pay"),
    ("amazon", "🟠 Amazon Pay"),
    ("phonepe", "🟣 PhonePe"),
    ("paytm", "🔵 Paytm"),
    ("famlive", "🪙 FAM LIVE"),
    ("fampay", "🟡 FamPay"),
]
PAY_LABEL = dict(PAY_METHODS)

def pm_value(code: str) -> str:
    return (get_setting(f"pm_{code}", "") or "").strip()

def pm_is_enabled(code: str) -> bool:
    return bool(pm_value(code))

def db_insert(query: str, params: tuple = ()) -> Optional[int]:
    conn = sqlite3.connect(DB_FILE, timeout=15)
    try:
        cur = conn.execute(query, params)
        conn.commit()
        return cur.lastrowid
    except Exception as e:
        conn.rollback()
        logger.error(f"db_insert failed: {e}")
        return None
    finally:
        conn.close()

async def _cancel_to_admin(m: Message, state: FSMContext) -> None:
    await state.clear()
    await m.answer("Cancelled.", reply_markup=admin_kb(), parse_mode='HTML')

# ---------------------------- USER: manual payment (keypad -> QR -> I have paid -> UTR) ----------------------------
def _upi_qr_url(pa: str, amt: float) -> str:
    """QR image for a UPI ID. The payment app reads the upi:// link inside the QR."""
    uri = f"upi://pay?pa={urllib.parse.quote(pa, safe='@.')}&pn=Payment&am={amt:.2f}&cu=INR"
    return "https://api.qrserver.com/v1/create-qr-code/?size=512x512&data=" + urllib.parse.quote(uri, safe="")

def _pm_keypad_view(code: str, buf: str):
    shown = buf or "0"
    text = (f"{PAY_LABEL[code]}\n━━━━━━━━━━━━━━━━━━\n"
            f"💵 Amount: <b>₹{html_escape(shown)}</b>\n\n"
            "<i>Keypad se amount dabao, phir ✅ Confirm.</i>\n"
            "Min ₹1 · Max ₹1,00,000")
    def b(t: str, cb: str, st: str = "primary") -> InlineKeyboardButton:
        return InlineKeyboardButton(text=t, callback_data=cb, style=st)
    kb = InlineKeyboardMarkup(inline_keyboard=[
        [b("₹100", "pmk_q_100"), b("₹500", "pmk_q_500"), b("₹1000", "pmk_q_1000")],
        [b("1", "pmk_d_1"), b("2", "pmk_d_2"), b("3", "pmk_d_3")],
        [b("4", "pmk_d_4"), b("5", "pmk_d_5"), b("6", "pmk_d_6")],
        [b("7", "pmk_d_7"), b("8", "pmk_d_8"), b("9", "pmk_d_9")],
        [b("⌫", "pmk_del", "danger"), b("0", "pmk_d_0"), b("✅ Confirm", "pmk_ok", "success")],
        [InlineKeyboardButton(text="BACK", callback_data="menu_add_balance",
                              icon_custom_emoji_id=get_emoji_icon("back"), style="danger")],
    ])
    return text, kb

async def _pm_show_pay(uid: int, chat_id: int, state: FSMContext, code: str, amt: float, old_msg: Optional[Message] = None) -> None:
    """Creates a waiting request and shows the pay page (QR for UPI IDs, plain ID for numbers)."""
    pa = pm_value(code)
    rid = db_insert("INSERT INTO deposit_requests (user_id, method, amount, utr, status, created_at) VALUES (?, ?, ?, NULL, 'awaiting_payment', ?)",
                    (uid, code, amt, datetime.now().strftime("%Y-%m-%d %H:%M:%S")))
    await state.clear()
    if not rid:
        return await bot.send_message(chat_id, "❌ Request save nahi hui. Dobara try karo.", reply_markup=main_menu_kb(uid))
    log_activity(uid, "DEPOSIT_START", f"#{rid} {code} {amt}")
    text = (f"{PAY_LABEL[code]} · Request <b>#{rid}</b>\n━━━━━━━━━━━━━━━━━━\n"
            f"💵 Amount: <b>{fmt_curr(amt)}</b>\n"
            f"🏦 Pay to: <code>{html_escape(pa)}</code>\n\n"
            "1️⃣ Upar amount is ID par pay karo (QR scan karke ya ID daal ke)\n"
            "2️⃣ Payment ke baad <b>I have paid</b> dabao\n"
            "3️⃣ Apna <b>UTR / Transaction ID</b> bhejo\n\n"
            "<i>Admin verify karke wallet mein balance add karega.</i>")
    kb = InlineKeyboardMarkup(inline_keyboard=[
        [InlineKeyboardButton(text="✅ I have paid", callback_data=f"pm_paid_{rid}", style="success")],
        [InlineKeyboardButton(text="❌ Cancel", callback_data="pm_cancel", style="danger")],
    ])
    sent = False
    if "@" in pa:      # a UPI ID -> show a QR code
        try:
            await bot.send_photo(chat_id, photo=_upi_qr_url(pa, amt), caption=text, reply_markup=kb, parse_mode='HTML')
            sent = True
        except Exception as e:
            logger.warning(f"QR send failed, falling back to text: {e}")
    if not sent:
        await bot.send_message(chat_id, text, reply_markup=kb, parse_mode='HTML')
    if old_msg is not None:
        try: await old_msg.delete()
        except Exception: pass

@dp.callback_query(F.data.startswith("pm_pay_"))
async def pm_pay_start(call: CallbackQuery, state: FSMContext):
    code = call.data[len("pm_pay_"):]
    if code not in PAY_LABEL or not pm_is_enabled(code):
        return await call.answer("Ye payment method abhi band hai.", show_alert=True)
    await state.clear()
    await state.update_data(pm_code=code, pm_buf="")
    await state.set_state(UserStates.pm_amount)
    text, kb = _pm_keypad_view(code, "")
    await call.answer()
    await _hedit(call, text, kb)

@dp.callback_query(F.data.startswith("pmk_"))
async def pm_keypad(call: CallbackQuery, state: FSMContext):
    data = await state.get_data()
    code = data.get("pm_code")
    if not code or code not in PAY_LABEL or not pm_is_enabled(code):
        return await call.answer("Session expire ho gaya. Add Balance se dobara try karo.", show_alert=True)
    buf = str(data.get("pm_buf") or "")
    action = call.data[len("pmk_"):]
    if action == "ok":
        try:
            amt = round(float(buf), 2)
        except ValueError:
            amt = 0
        if not (1 <= amt <= 100000):
            return await call.answer("Amount ₹1 se ₹1,00,000 ke beech hona chahiye.", show_alert=True)
        await call.answer()
        return await _pm_show_pay(call.from_user.id, call.message.chat.id, state, code, amt, old_msg=call.message)
    if action == "del":
        buf = buf[:-1]
    elif action.startswith("q_") and action[2:].isdigit():
        buf = action[2:]
    elif action.startswith("d_") and action[2:].isdigit() and len(buf) < 6:
        buf = (buf + action[2:]).lstrip("0")
    await state.update_data(pm_buf=buf)
    text, kb = _pm_keypad_view(code, buf)
    await call.answer()
    try:
        await _hedit(call, text, kb)
    except Exception:
        pass

@dp.callback_query(F.data == "pm_cancel")
async def pm_cancel(call: CallbackQuery, state: FSMContext):
    await state.clear()
    try: await call.message.delete()
    except Exception: pass
    await send_main_menu(call.message, call.from_user.id)

@dp.message(UserStates.pm_amount)
async def pm_amount_msg(m: Message, state: FSMContext):
    raw = (m.text or "").strip()
    if raw == "/cancel":
        await state.clear()
        return await m.answer("Cancelled.", reply_markup=main_menu_kb(m.from_user.id))
    try:
        amt = round(float(raw), 2)
    except ValueError:
        return await m.answer("❌ Sirf amount number mein bhejo (e.g. 250), ya /cancel.")
    if not (1 <= amt <= 100000):
        return await m.answer("❌ Amount ₹1 se ₹1,00,000 ke beech hona chahiye.")
    code = (await state.get_data()).get("pm_code")
    if not code or code not in PAY_LABEL or not pm_is_enabled(code):
        await state.clear()
        return await m.answer("❌ Session expire ho gaya. Add Balance se dobara try karo.", reply_markup=main_menu_kb(m.from_user.id))
    await _pm_show_pay(m.from_user.id, m.chat.id, state, code, amt)

@dp.callback_query(F.data.startswith("pm_paid_"))
async def pm_paid_start(call: CallbackQuery, state: FSMContext):
    rid_s = call.data[len("pm_paid_"):]
    if not rid_s.isdigit():
        return await call.answer("Invalid", show_alert=True)
    row = db_query("SELECT user_id, status FROM deposit_requests WHERE id=?", (int(rid_s),), fetchone=True)
    if not row or row[0] != call.from_user.id or row[1] != "awaiting_payment":
        return await call.answer("Ye request ab valid nahi hai.", show_alert=True)
    await state.clear()
    await state.update_data(pm_rid=int(rid_s))
    await state.set_state(UserStates.pm_utr)
    await call.answer()
    await call.message.answer(f"🧾 Request <b>#{rid_s}</b> ke liye <b>UTR / Transaction ID</b> bhejo.\n/cancel to abort.",
                              parse_mode='HTML')

@dp.message(UserStates.pm_utr)
async def pm_utr_msg(m: Message, state: FSMContext):
    utr = (m.text or "").strip()
    if utr == "/cancel":
        await state.clear()
        return await m.answer("Cancelled.", reply_markup=main_menu_kb(m.from_user.id))
    if len(utr) < 6 or len(utr) > 40 or not re.fullmatch(r"[A-Za-z0-9\-_/]+", utr):
        return await m.answer("❌ Sahi UTR / Transaction ID bhejo (6-40 characters, sirf letters aur numbers).")
    if db_query("SELECT 1 FROM deposit_requests WHERE utr=?", (utr,), fetchone=True):
        await state.clear()
        return await m.answer("⚠️ Ye UTR pehle hi submit ho chuka hai.", reply_markup=main_menu_kb(m.from_user.id))
    rid = (await state.get_data()).get("pm_rid")
    await state.clear()
    if not rid:
        return await m.answer("❌ Session expire ho gaya. Add Balance se dobara try karo.", reply_markup=main_menu_kb(m.from_user.id))
    ok = False
    conn = sqlite3.connect(DB_FILE, timeout=15)
    try:
        cur = conn.execute("UPDATE deposit_requests SET utr=?, status='pending' WHERE id=? AND user_id=? AND status='awaiting_payment'",
                           (utr, int(rid), m.from_user.id))
        conn.commit()
        ok = cur.rowcount == 1
    except sqlite3.IntegrityError:
        conn.rollback()
    finally:
        conn.close()
    if not ok:
        return await m.answer("❌ Ye request ab valid nahi hai (ya UTR pehle use ho chuka hai).", reply_markup=main_menu_kb(m.from_user.id))
    code, amt = db_query("SELECT method, amount FROM deposit_requests WHERE id=?", (int(rid),), fetchone=True)
    log_activity(m.from_user.id, "DEPOSIT_REQUEST", f"#{rid} {code} {amt} {utr}")
    await m.answer(f"✅ <b>Request submit ho gayi!</b>\n🆔 #{rid} · {PAY_LABEL.get(code, code)} · {fmt_curr(amt)}\n"
                   f"UTR: <code>{html_escape(utr)}</code>\n\nAdmin verify karke balance add kar dega.",
                   reply_markup=main_menu_kb(m.from_user.id), parse_mode='HTML')
    try:
        await bot.send_message(
            ADMIN_ID,
            f"💳 <b>NEW DEPOSIT REQUEST #{rid}</b>\n━━━━━━━━━━━━━━━━━━\n"
            f"👤 {html_escape(m.from_user.first_name or '')} (<code>{m.from_user.id}</code>)\n"
            f"🏦 {PAY_LABEL.get(code, code)}\n💵 {fmt_curr(amt)}\n🧾 UTR: <code>{html_escape(utr)}</code>",
            reply_markup=InlineKeyboardMarkup(inline_keyboard=[[
                InlineKeyboardButton(text="✅ Approve", callback_data=f"dr_ok_{rid}", style="success"),
                InlineKeyboardButton(text="❌ Reject", callback_data=f"dr_no_{rid}", style="danger")]]),
            parse_mode='HTML')
    except Exception:
        pass

# ---------------------------- ADMIN: approve / reject deposit requests ----------------------------
@dp.callback_query(F.data.startswith("dr_"))
async def dr_decide(call: CallbackQuery):
    if not _is_admin(call.from_user.id):
        return await call.answer("⛔ Not allowed", show_alert=True)
    action, _, rid_s = call.data[3:].partition("_")
    if action not in ("ok", "no") or not rid_s.isdigit():
        return await call.answer("Invalid", show_alert=True)
    rid = int(rid_s)
    row = db_query("SELECT user_id, amount, status, method, utr FROM deposit_requests WHERE id=?", (rid,), fetchone=True)
    if not row:
        return await call.answer("Request nahi mili.", show_alert=True)
    uid, amt, status, method, utr = row
    if status != "pending":
        return await call.answer(f"Ye request pehle se {status} hai.", show_alert=True)
    if action == "ok":
        db_query("UPDATE deposit_requests SET status='approved' WHERE id=? AND status='pending'", (rid,))
        db_query("UPDATE users SET balance = balance + ? WHERE user_id=?", (amt, uid))
        await credit_referral_bonus(uid, amt)
        verdict = "✅ APPROVED"
        user_msg = f"💰 <b>Deposit approved!</b>\n#{rid} · {fmt_curr(amt)} aapke wallet mein add ho gaya."
    else:
        db_query("UPDATE deposit_requests SET status='rejected' WHERE id=? AND status='pending'", (rid,))
        verdict = "❌ REJECTED"
        user_msg = f"❌ <b>Deposit request rejected</b>\n#{rid} · UTR <code>{html_escape(str(utr))}</code>\nGalat payment ho to Support se contact karo."
    log_activity(uid, "DEPOSIT_" + ("APPROVED" if action == "ok" else "REJECTED"), f"#{rid} {method} {amt}")
    sec_log("DEPOSIT_DECISION", call.from_user.id, f"#{rid} {action} user={uid} amt={amt}")
    try:
        await bot.send_message(uid, user_msg, parse_mode='HTML')
    except Exception:
        pass
    await call.answer("Done")
    try:
        await call.message.edit_reply_markup(reply_markup=None)
    except Exception:
        pass
    await call.message.answer(f"#{rid} → <b>{verdict}</b>", parse_mode='HTML')

# ---------------------------- ADMIN: payment methods setup ----------------------------
@dp.callback_query(F.data == "admin_pm_menu")
async def admin_pm_menu(call: CallbackQuery, state: FSMContext):
    if call.from_user.id != ADMIN_ID: return
    await state.clear()
    kb = []
    for code, label in PAY_METHODS:
        v = pm_value(code)
        kb.append([InlineKeyboardButton(text=f"{label}: {v[:20] if v else 'OFF'}", callback_data=f"admin_pm_set_{code}",
                                        style="success" if v else "danger")])
    key_on = bool(get_setting("fam_live_key", ""))
    kb.append([InlineKeyboardButton(text=f"🔑 FAM LIVE API Key: {'SET' if key_on else 'OFF'}",
                                    callback_data="admin_pm_set_key", style="primary")])
    kb.append([InlineKeyboardButton(text="Back to Admin", callback_data="admin_panel_back",
                                    icon_custom_emoji_id=get_emoji_icon("back"), style="danger")])
    text = ("💳 <b>PAYMENT METHODS</b>\n━━━━━━━━━━━━━━━━━━\n"
            "Har method par tap karke uski UPI ID / number set karo. <code>none</code> bhejo to band ho jayega.\n\n"
            "User Add Balance mein ye buttons dekhega, pay karega aur UTR bhejega. "
            "Aap <b>Approve</b> karoge tabhi balance add hoga.")
    await _hedit(call, text, InlineKeyboardMarkup(inline_keyboard=kb))

@dp.callback_query(F.data.startswith("admin_pm_set_"))
async def admin_pm_set_start(call: CallbackQuery, state: FSMContext):
    if call.from_user.id != ADMIN_ID: return
    code = call.data[len("admin_pm_set_"):]
    if code == "key":
        prompt = "🔑 <b>FAM LIVE API key</b> bhejo (encrypted save hogi)."
    elif code in PAY_LABEL:
        prompt = f"💳 <b>{PAY_LABEL[code]}</b> ki UPI ID / number / details bhejo.\n<i>'none' bhejo to ye method band ho jayega.</i>"
    else:
        return await call.answer("Unknown", show_alert=True)
    await state.clear()
    await state.update_data(pm_code=code)
    await _hedit(call, prompt + "\n\n/cancel to abort.", admin_back_kb())
    await state.set_state(AdminStates.pm_value)

@dp.message(AdminStates.pm_value)
async def admin_pm_save(m: Message, state: FSMContext):
    if m.from_user.id != ADMIN_ID: return
    raw = (m.text or "").strip()
    if raw == "/cancel":
        return await _cancel_to_admin(m, state)
    if not raw:
        return await m.answer("❌ Kuch bhejo, ya 'none' likho.")
    code = (await state.get_data()).get("pm_code")
    off = raw.lower() == "none"
    if code == "key":
        set_setting("fam_live_key", "" if off else raw)
        sec_log("ADMIN_SET_FAM_KEY", m.from_user.id)
        msg = "🔑 FAM LIVE API key save ho gayi (encrypted)."
    elif code in PAY_LABEL:
        set_setting(f"pm_{code}", "" if off else raw)
        msg = f"✅ <b>{PAY_LABEL[code]}</b> {'band kar diya' if off else 'set ho gaya'}."
    else:
        return await _cancel_to_admin(m, state)
    await state.clear()
    await m.answer(msg + "\n\nPayment Methods mein wapas jaake check karo.", reply_markup=admin_kb(), parse_mode='HTML')

# ---------------------------- USER: digital store (bot files for wallet balance) ----------------------------
def _ds_product(pid: int):
    return db_query("SELECT id, title, price_inr, description, file_type FROM digital_products WHERE id=? AND is_active=1",
                    (pid,), fetchone=True)

def _ds_balance(uid: int) -> float:
    r = db_query("SELECT balance FROM users WHERE user_id=?", (uid,), fetchone=True)
    return safe_float(r[0]) if r else 0.0

@dp.callback_query(F.data == "ds_menu")
async def ds_menu(call: CallbackQuery, state: FSMContext):
    await state.clear()
    rows = db_query("SELECT id, title, price_inr FROM digital_products WHERE is_active=1 ORDER BY id DESC", fetchall=True) or []
    text = ("🛍 <b><u>SOURCE CODE</u></b> 🛍\n━━━━━━━━━━━━━━━━━━\n"
            "Bot files aur digital products apne wallet balance se buy karo.\n"
            "Purchase ke baad file turant chat mein mil jayegi.\n\n")
    text += "<i>Abhi koi product nahi hai.</i>" if not rows else "👇 Product chuno:"
    kb = [[InlineKeyboardButton(text=f"📦 {t} · {fmt_curr(safe_float(p))}"[:60], callback_data=f"ds_view_{pid}", style="primary")]
          for pid, t, p in rows[:30]]
    kb.append([InlineKeyboardButton(text="📋 My Purchases", callback_data="ds_mine", style="primary")])
    kb.append([InlineKeyboardButton(text="BACK", callback_data="back_main", icon_custom_emoji_id=get_emoji_icon("back"), style="danger")])
    await _hedit(call, text, InlineKeyboardMarkup(inline_keyboard=kb))

@dp.callback_query(F.data.startswith("ds_view_"))
async def ds_view(call: CallbackQuery):
    pid = call.data.rsplit("_", 1)[1]
    if not pid.isdigit():
        return await call.answer("Invalid", show_alert=True)
    prod = _ds_product(int(pid))
    if not prod:
        return await call.answer("❌ Ye product ab available nahi hai.", show_alert=True)
    _id, title, price, desc, ftype = prod
    text = (f"📦 <b>{html_escape(title)}</b>\n━━━━━━━━━━━━━━━━━━\n"
            f"{html_escape(desc or 'Details jald aayengi.')}\n\n"
            f"💰 Price: <b>{fmt_curr(safe_float(price))}</b>\n"
            f"📁 Type: {html_escape(ftype or 'file')}\n\n"
            "<i>Buy karne par amount wallet se katega aur file chat mein mil jayegi.</i>")
    kb = InlineKeyboardMarkup(inline_keyboard=[
        [InlineKeyboardButton(text=f"🛒 Buy Now · {fmt_curr(safe_float(price))}", callback_data=f"ds_buy_{pid}", style="success")],
        [InlineKeyboardButton(text="BACK", callback_data="ds_menu", icon_custom_emoji_id=get_emoji_icon("back"), style="danger")],
    ])
    await _hedit(call, text, kb)

@dp.callback_query(F.data.startswith("ds_buy_"))
async def ds_buy_confirm(call: CallbackQuery):
    pid = call.data.rsplit("_", 1)[1]
    if not pid.isdigit():
        return await call.answer("Invalid", show_alert=True)
    prod = _ds_product(int(pid))
    if not prod:
        return await call.answer("❌ Ye product ab available nahi hai.", show_alert=True)
    _id, title, price, _d, _f = prod
    price = safe_float(price)
    bal = _ds_balance(call.from_user.id)
    if bal < price:
        return await call.answer(f"❌ Balance kam hai. Need {fmt_curr(price)}, aapke paas {fmt_curr(bal)}. Add Balance karo.",
                                 show_alert=True)
    kb = InlineKeyboardMarkup(inline_keyboard=[
        [InlineKeyboardButton(text=f"✅ Confirm · {fmt_curr(price)}", callback_data=f"ds_ok_{pid}", style="success")],
        [InlineKeyboardButton(text="Cancel", callback_data=f"ds_view_{pid}", style="danger")],
    ])
    await _hedit(call, f"🧾 <b>Confirm purchase</b>\n\n📦 {html_escape(title)}\n💰 Amount: <b>{fmt_curr(price)}</b>\n"
                       f"💳 Wallet balance: {fmt_curr(bal)}\n\nConfirm karoge to balance se amount katega aur file mil jayegi.", kb)

@dp.callback_query(F.data.startswith("ds_ok_"))
async def ds_buy_do(call: CallbackQuery):
    pid = call.data.rsplit("_", 1)[1]
    if not pid.isdigit():
        return await call.answer("Invalid", show_alert=True)
    row = db_query("SELECT title, price_inr, file_id, file_type FROM digital_products WHERE id=? AND is_active=1",
                   (int(pid),), fetchone=True)
    if not row or not row[2]:
        return await call.answer("❌ Ye product ab available nahi hai.", show_alert=True)
    title, price, file_id, ftype = row
    price = safe_float(price)
    uid = call.from_user.id
    # Charge atomically: only succeeds if the balance is still enough (protects against double taps)
    conn = sqlite3.connect(DB_FILE, timeout=15)
    try:
        cur = conn.execute("UPDATE users SET balance = balance - ?, spent = spent + ? WHERE user_id=? AND balance >= ?",
                           (price, price, uid, price))
        conn.commit()
        charged = cur.rowcount == 1
    finally:
        conn.close()
    if not charged:
        return await call.answer("❌ Balance kam hai. Add Balance karo.", show_alert=True)
    caption = f"📥 <b>{html_escape(title)}</b>\n✅ Thanks for buying!"
    try:
        if ftype == "video":
            await bot.send_video(uid, file_id, caption=caption, parse_mode='HTML')
        elif ftype == "audio":
            await bot.send_audio(uid, file_id, caption=caption, parse_mode='HTML')
        else:
            await bot.send_document(uid, file_id, caption=caption, parse_mode='HTML')
    except Exception as e:
        logger.error(f"Digital send failed: {e}")
        db_query("UPDATE users SET balance = balance + ?, spent = MAX(spent - ?, 0) WHERE user_id=?", (price, price, uid))
        return await call.answer("⚠️ File bhej nahi paye. Amount wapas kar diya gaya.", show_alert=True)
    db_query("INSERT INTO digital_orders (user_id, product_id, product_title, price_paid, purchase_date) VALUES (?, ?, ?, ?, ?)",
             (uid, int(pid), title, price, datetime.now().strftime("%Y-%m-%d %H:%M:%S")))
    db_query("UPDATE digital_products SET sold = sold + 1 WHERE id=?", (int(pid),))
    log_activity(uid, "DIGITAL_PURCHASE", f"{title} {price}")
    await call.answer("✅ File bhej di gayi!")
    kb = InlineKeyboardMarkup(inline_keyboard=[[InlineKeyboardButton(
        text="BACK", callback_data="ds_menu", icon_custom_emoji_id=get_emoji_icon("back"), style="danger")]])
    await _hedit(call, f"✅ <b>Purchase successful!</b>\n\n📦 {html_escape(title)}\n💰 Paid: {fmt_curr(price)}\n"
                       f"💳 Balance: {fmt_curr(_ds_balance(uid))}\n\nFile upar chat mein bhej di gayi hai.", kb)
    try:
        await bot.send_message(ADMIN_ID, f"🛍 <b>Digital sale</b>\n👤 <code>{uid}</code> · {html_escape(title)} · {fmt_curr(price)}",
                               parse_mode='HTML')
    except Exception:
        pass

@dp.callback_query(F.data == "ds_mine")
async def ds_mine(call: CallbackQuery):
    rows = db_query("SELECT product_title, price_paid, purchase_date FROM digital_orders WHERE user_id=? ORDER BY id DESC LIMIT 10",
                    (call.from_user.id,), fetchall=True) or []
    if not rows:
        text = "📋 Abhi koi digital purchase nahi hai."
    else:
        text = "📋 <b>My Purchases</b> (last 10)\n━━━━━━━━━━━━━━━━━━\n" + "".join(
            f"📦 <b>{html_escape(t or '')}</b> · {fmt_curr(safe_float(p))}\n<i>{html_escape(str(d))}</i>\n\n" for t, p, d in rows)
    kb = InlineKeyboardMarkup(inline_keyboard=[[InlineKeyboardButton(
        text="BACK", callback_data="ds_menu", icon_custom_emoji_id=get_emoji_icon("back"), style="danger")]])
    await _hedit(call, text, kb)

# ---------------------------- ADMIN: digital store (upload / manage bot files) ----------------------------
@dp.callback_query(F.data == "admin_ds_menu")
async def admin_ds_menu(call: CallbackQuery, state: FSMContext):
    if not _is_admin(call.from_user.id): return
    await state.clear()
    rows = db_query("SELECT id, title, price_inr, is_active, sold FROM digital_products ORDER BY id DESC", fetchall=True) or []
    kb = []
    for pid, t, p, act, sold in rows[:30]:
        kb.append([InlineKeyboardButton(text=f"{'🟢' if act else '🔴'} {t} · {fmt_curr(safe_float(p))} · sold {sold or 0}"[:60],
                                        callback_data=f"admin_ds_v_{pid}", style="primary")])
    kb.append([InlineKeyboardButton(text="➕ Upload New Product", callback_data="admin_ds_add", style="success")])
    kb.append([InlineKeyboardButton(text="Back to Admin", callback_data="admin_panel_back",
                                    icon_custom_emoji_id=get_emoji_icon("back"), style="danger")])
    text = ("🛍 <b>SOURCE CODE — ADMIN</b>\n━━━━━━━━━━━━━━━━━━\n"
            "Bot files / digital products upload karo, price set karo. Users wallet se buy karenge.\n"
            "🟢 = live   🔴 = hidden")
    await _hedit(call, text, InlineKeyboardMarkup(inline_keyboard=kb))

@dp.callback_query(F.data.startswith("admin_ds_v_"))
async def admin_ds_view(call: CallbackQuery, state: FSMContext):
    if not _is_admin(call.from_user.id): return
    try:
        pid = int(call.data.rsplit("_", 1)[1])
    except ValueError:
        return await call.answer("Invalid", show_alert=True)
    row = db_query("SELECT id, title, price_inr, description, file_type, is_active, sold FROM digital_products WHERE id=?", (pid,), fetchone=True)
    if not row:
        return await call.answer("Product nahi mila.", show_alert=True)
    _id, t, p, d, ft, act, sold = row
    sales = db_query("SELECT COUNT(*), COALESCE(SUM(price_paid), 0) FROM digital_orders WHERE product_id=?", (pid,), fetchone=True) or (0, 0)
    text = (f"🛍 <b>{html_escape(t or '')}</b>\n━━━━━━━━━━━━━━━━━━\n"
            f"💰 Price: <b>{fmt_curr(safe_float(p))}</b>\n📁 Type: {html_escape(ft or 'file')}\n"
            f"📊 Status: {'🟢 Live' if act else '🔴 Hidden'}\n"
            f"🧾 Sold: <b>{sales[0]}</b> · Revenue: <b>{fmt_curr(safe_float(sales[1]))}</b>\n\n"
            f"{html_escape(d or '')}")
    kb = InlineKeyboardMarkup(inline_keyboard=[
        [InlineKeyboardButton(text="👁 Hide" if act else "🟢 Make Live", callback_data=f"admin_ds_t_{pid}", style="primary")],
        [InlineKeyboardButton(text="🗑 Delete Product", callback_data=f"admin_ds_d_{pid}", style="danger")],
        [InlineKeyboardButton(text="Back", callback_data="admin_ds_menu", icon_custom_emoji_id=get_emoji_icon("back"), style="danger")],
    ])
    await _hedit(call, text, kb)

@dp.callback_query(F.data.startswith("admin_ds_t_"))
async def admin_ds_toggle(call: CallbackQuery, state: FSMContext):
    if not _is_admin(call.from_user.id): return
    try:
        pid = int(call.data.rsplit("_", 1)[1])
    except ValueError:
        return await call.answer("Invalid", show_alert=True)
    db_query("UPDATE digital_products SET is_active = CASE WHEN is_active=1 THEN 0 ELSE 1 END WHERE id=?", (pid,))
    await call.answer("Updated")
    await admin_ds_view(call, state)

@dp.callback_query(F.data.startswith("admin_ds_d_"))
async def admin_ds_delete(call: CallbackQuery, state: FSMContext):
    if not _is_admin(call.from_user.id): return
    try:
        pid = int(call.data.rsplit("_", 1)[1])
    except ValueError:
        return await call.answer("Invalid", show_alert=True)
    db_query("DELETE FROM digital_products WHERE id=?", (pid,))           # past purchases stay in history
    log_activity(call.from_user.id, "DIGITAL_PRODUCT_DELETED", str(pid))
    await call.answer("🗑 Deleted")
    await admin_ds_menu(call, state)

@dp.callback_query(F.data == "admin_ds_add")
async def admin_ds_add_start(call: CallbackQuery, state: FSMContext):
    if not _is_admin(call.from_user.id): return
    await state.clear()
    await _hedit(call, "🛍 <b>Upload New Digital Product</b>\n\nStep 1/4: Product ka <b>naam</b> bhejo (e.g. <code>Premium Panel Bot v2</code>).\n\n/cancel to abort.",
                 admin_back_kb())
    await state.set_state(AdminStates.ds_title)

@dp.message(AdminStates.ds_title)
async def admin_ds_title(m: Message, state: FSMContext):
    if not _is_admin(m.from_user.id): return
    raw = (m.text or "").strip()
    if raw == "/cancel":
        return await _cancel_to_admin(m, state)
    if not raw or len(raw) > 60:
        return await m.answer("❌ Naam 1-60 characters ka bhejo.")
    await state.update_data(ds_title=raw)
    await m.answer("Step 2/4: Price <b>rupees</b> mein bhejo (e.g. <code>500</code>).", parse_mode='HTML')
    await state.set_state(AdminStates.ds_price)

@dp.message(AdminStates.ds_price)
async def admin_ds_price(m: Message, state: FSMContext):
    if not _is_admin(m.from_user.id): return
    raw = (m.text or "").strip()
    if raw == "/cancel":
        return await _cancel_to_admin(m, state)
    try:
        price = round(float(raw), 2)
    except ValueError:
        return await m.answer("❌ Price number mein bhejo.")
    if not (0 < price < 10 ** 7):
        return await m.answer("❌ Price 0 se zyada hona chahiye.")
    await state.update_data(ds_price=price)
    await m.answer("Step 3/4: Product ki <b>description</b> bhejo (ya <code>none</code>).", parse_mode='HTML')
    await state.set_state(AdminStates.ds_desc)

@dp.message(AdminStates.ds_desc)
async def admin_ds_desc(m: Message, state: FSMContext):
    if not _is_admin(m.from_user.id): return
    raw = (m.text or "").strip()
    if raw == "/cancel":
        return await _cancel_to_admin(m, state)
    await state.update_data(ds_desc="" if raw.lower() == "none" else raw[:800])
    await m.answer("Step 4/4: Ab product ki <b>file</b> bhejo (📎 → File). Bot file, APK, zip — kuch bhi.", parse_mode='HTML')
    await state.set_state(AdminStates.ds_file)

@dp.message(AdminStates.ds_file)
async def admin_ds_file(m: Message, state: FSMContext):
    if not _is_admin(m.from_user.id): return
    if (m.text or "").strip() == "/cancel":
        return await _cancel_to_admin(m, state)
    if m.document:
        fid, ftype = m.document.file_id, "document"
    elif m.video:
        fid, ftype = m.video.file_id, "video"
    elif m.audio:
        fid, ftype = m.audio.file_id, "audio"
    else:
        return await m.answer("❌ File bhejo (document / video / audio), ya /cancel.")
    data = await state.get_data()
    pid = db_insert("INSERT INTO digital_products (title, description, price_inr, file_id, file_type, is_active, sold, created_at) "
                    "VALUES (?, ?, ?, ?, ?, 1, 0, ?)",
                    (data.get("ds_title", "Product"), data.get("ds_desc", ""), data.get("ds_price", 0.0), fid, ftype, _hnow()))
    await state.clear()
    if not pid:
        return await m.answer("❌ Save nahi hua. Dobara try karo.", reply_markup=admin_kb())
    log_activity(m.from_user.id, "DIGITAL_PRODUCT_ADDED", f"#{pid}")
    await m.answer(f"✅ <b>Product live!</b> #{pid}\nUser ab Digital Store mein buy kar sakte hain.",
                   reply_markup=admin_kb(), parse_mode='HTML')

# ==============================================================================
# 24H. ADMIN: FORCE-JOIN CHANNEL (set from the panel, no code edit)  +  panel helpers
# ==============================================================================
@dp.callback_query(F.data == "admin_noop")
async def admin_noop(call: CallbackQuery):
    await call.answer()          # section titles in the admin panel do nothing

def _fj_parse(raw: str):
    """Accepts @name, name, t.me/name or https://t.me/name. Returns (@name, url) or None."""
    s = raw.strip()
    found = re.search(r"(?:https?://)?t\.me/([A-Za-z0-9_]{4,})", s)
    name = found.group(1) if found else s.lstrip("@")
    if not re.fullmatch(r"[A-Za-z0-9_]{4,}", name):
        return None
    return "@" + name, f"https://t.me/{name}"

def _fj_menu_view():
    ch = get_setting("required_channel", REQUIRED_CHANNEL)
    on = get_setting("force_join", "ON") == "ON"
    text = ("📢 <b>━━━ FORCE-JOIN CHANNEL ━━━</b>\n━━━━━━━━━━━━━━━━━━\n"
            f"🔗 Channel: <b>{html_escape(ch)}</b>\n"
            f"📊 Status: <b>{'🟢 ON' if on else '🔴 OFF'}</b>\n\n"
            "⚠️ Bot ko is channel ka <b>ADMIN</b> banana zaroori hai, warna membership check nahi hogi.")
    kb = InlineKeyboardMarkup(inline_keyboard=[
        [InlineKeyboardButton(text="✏️ Change Channel", callback_data="admin_fj_set", style="success")],
        [InlineKeyboardButton(text=("🔴 Turn OFF" if on else "🟢 Turn ON"), callback_data="admin_fj_toggle",
                              style="danger" if on else "success")],
        [InlineKeyboardButton(text="Back to Admin", callback_data="admin_panel_back",
                              icon_custom_emoji_id=get_emoji_icon("back"), style="danger")],
    ])
    return text, kb

@dp.callback_query(F.data == "admin_fj_menu")
async def admin_fj_menu(call: CallbackQuery, state: FSMContext):
    if not _is_admin(call.from_user.id): return
    await state.clear()
    text, kb = _fj_menu_view()
    await _hedit(call, text, kb)

@dp.callback_query(F.data == "admin_fj_set")
async def admin_fj_set_start(call: CallbackQuery, state: FSMContext):
    if not _is_admin(call.from_user.id): return
    await state.clear()
    await _hedit(call, "✏️ <b>Naya channel bhejo</b>\nFormat: <code>@channelname</code> ya <code>https://t.me/channelname</code>\n\n/cancel to abort.",
                 admin_back_kb())
    await state.set_state(AdminStates.fj_value)

@dp.message(AdminStates.fj_value)
async def admin_fj_save(m: Message, state: FSMContext):
    if not _is_admin(m.from_user.id): return
    raw = (m.text or "").strip()
    if raw == "/cancel":
        return await _cancel_to_admin(m, state)
    parsed = _fj_parse(raw)
    if not parsed:
        return await m.answer("❌ Galat channel. <code>@name</code> ya <code>https://t.me/name</code> bhejo, ya /cancel.", parse_mode='HTML')
    username, url = parsed
    set_setting("required_channel", username)
    set_setting("required_channel_url", url)
    _join_cache.clear()
    sec_log("ADMIN_SET_CHANNEL", m.from_user.id, username)
    await state.clear()
    await m.answer(f"✅ Force-join channel set: <b>{html_escape(username)}</b>\n<i>Bot ko is channel ka admin banana mat bhoolna.</i>",
                   reply_markup=admin_kb(), parse_mode='HTML')

@dp.callback_query(F.data == "admin_fj_toggle")
async def admin_fj_toggle(call: CallbackQuery, state: FSMContext):
    if not _is_admin(call.from_user.id): return
    on = get_setting("force_join", "ON") == "ON"
    set_setting("force_join", "OFF" if on else "ON")
    _join_cache.clear()
    await call.answer("Updated")
    text, kb = _fj_menu_view()
    await _hedit(call, text, kb)

# ==============================================================================
# 24I. LANGUAGE (en / hi / bn for main-menu buttons)  +  PANEL DEMO  +  PREMIUM EMOJI JSON  +  STARTUP BACKUPS
# ==============================================================================
I18N = {
    "en": {"store": "Product Store", "profile": "My Profile", "add": "Add Balance", "history": "All History",
           "referral": "Referral", "tutorial": "Tutorials", "support": "Support", "spin": "Ludo Spin",
           "files": "Download Files", "hosting": "Hosting", "demo": "Panel Demo", "lang": "🌐 Language",
           "source": "SOURCE CODE"},
    "hi": {"store": "प्रोडक्ट स्टोर", "profile": "मेरी प्रोफ़ाइल", "add": "बैलेंस जोड़ें", "history": "पूरा इतिहास",
           "referral": "रेफरल", "tutorial": "ट्यूटोरियल", "support": "सपोर्ट", "spin": "लूडो स्पिन",
           "files": "डाउनलोड फ़ाइलें", "hosting": "होस्टिंग", "demo": "पैनल डेमो", "lang": "🌐 भाषा",
           "source": "SOURCE CODE"},
    "bn": {"store": "প্রোডাক্ট স্টোর", "profile": "আমার প্রোফাইল", "add": "ব্যালেন্স যোগ করুন", "history": "সব ইতিহাস",
           "referral": "রেফারেল", "tutorial": "টিউটোরিয়াল", "support": "সাপোর্ট", "spin": "লুডো স্পিন",
           "files": "ডাউনলোড ফাইল", "hosting": "হোস্টিং", "demo": "প্যানেল ডেমো", "lang": "🌐 ভাষা",
           "source": "SOURCE CODE"},
}
LANG_NAMES = {"en": "English", "hi": "हिन्दी", "bn": "বাংলা"}

def get_user_lang(uid: Optional[int]) -> str:
    if not uid:
        return "en"
    r = db_query("SELECT lang FROM users WHERE user_id=?", (uid,), fetchone=True)
    return r[0] if r and r[0] in I18N else "en"

def tr(uid: Optional[int], key: str) -> str:
    lang = get_user_lang(uid)
    return I18N.get(lang, I18N["en"]).get(key) or I18N["en"].get(key, key)

@dp.callback_query(F.data == "menu_lang")
async def menu_lang(call: CallbackQuery, state: FSMContext):
    await state.clear()
    text = "🌐 <b>Language</b>\n━━━━━━━━━━━━━━━━━━\nApni language chuno:\n\n🌐 <b>Language</b> · <b>भाषा</b> · <b>ভাষা</b>"
    kb = InlineKeyboardMarkup(inline_keyboard=[
        [InlineKeyboardButton(text="English", callback_data="lang_set_en", style="primary"),
         InlineKeyboardButton(text="हिन्दी", callback_data="lang_set_hi", style="primary"),
         InlineKeyboardButton(text="বাংলা", callback_data="lang_set_bn", style="primary")],
        [InlineKeyboardButton(text="BACK", callback_data="back_main", icon_custom_emoji_id=get_emoji_icon("back"), style="danger")],
    ])
    await _hedit(call, text, kb)

@dp.callback_query(F.data.startswith("lang_set_"))
async def lang_set(call: CallbackQuery, state: FSMContext):
    code = call.data[len("lang_set_"):]
    if code not in I18N:
        return await call.answer("Unknown", show_alert=True)
    await state.clear()
    db_query("UPDATE users SET lang=? WHERE user_id=?", (code, call.from_user.id))
    log_activity(call.from_user.id, "LANG_SET", code)
    await call.answer("✅")
    await send_main_menu(call, call.from_user.id)

# ---- Panel Demo: user view ----
@dp.callback_query(F.data == "demo_view")
async def demo_view(call: CallbackQuery, state: FSMContext):
    await state.clear()
    vid = get_setting("demo_video", "")
    link = get_setting("demo_link", "")
    if vid:
        await call.answer()
        try:
            await call.message.answer_video(vid, caption="🎬 <b>Panel Demo</b>", parse_mode='HTML')
        except Exception as e:
            logger.error(f"demo video send failed: {e}")
            return await call.answer("Demo abhi nahi chal raha.", show_alert=True)
        return await send_main_menu(call.message, call.from_user.id)
    if link:
        text = "🎬 <b>Panel Demo</b>\n━━━━━━━━━━━━━━━━━━\nNeeche button se demo dekho."
        kb = InlineKeyboardMarkup(inline_keyboard=[
            [InlineKeyboardButton(text="▶ Open Demo", url=link, style="success")],
            [InlineKeyboardButton(text="BACK", callback_data="back_main", icon_custom_emoji_id=get_emoji_icon("back"), style="danger")],
        ])
        return await _hedit(call, text, kb)
    await call.answer("Demo abhi set nahi hai.", show_alert=True)

# ---- Panel Demo: admin ----
def _demo_admin_view():
    link = get_setting("demo_link", "")
    vid = get_setting("demo_video", "")
    cur = "🎬 video uploaded" if vid else (f"🔗 {link}" if link else "OFF")
    text = ("🎬 <b>PANEL DEMO</b>\n━━━━━━━━━━━━━━━━━━\n"
            f"Current: <b>{html_escape(cur)}</b>\n\n"
            "User ke main menu mein <b>Panel Demo</b> button aayega. Video upload karo ya YouTube / video link set karo.")
    kb = InlineKeyboardMarkup(inline_keyboard=[
        [InlineKeyboardButton(text="🔗 Set Link (YouTube / video link)", callback_data="admin_demo_link", style="success")],
        [InlineKeyboardButton(text="🎬 Upload Video", callback_data="admin_demo_upload", style="primary")],
        [InlineKeyboardButton(text="🗑 Clear Demo", callback_data="admin_demo_clear", style="danger")],
        [InlineKeyboardButton(text="Back to Admin", callback_data="admin_panel_back",
                              icon_custom_emoji_id=get_emoji_icon("back"), style="danger")],
    ])
    return text, kb

@dp.callback_query(F.data == "admin_demo_menu")
async def admin_demo_menu(call: CallbackQuery, state: FSMContext):
    if not _is_admin(call.from_user.id): return
    await state.clear()
    text, kb = _demo_admin_view()
    await _hedit(call, text, kb)

@dp.callback_query(F.data == "admin_demo_link")
async def admin_demo_link_start(call: CallbackQuery, state: FSMContext):
    if not _is_admin(call.from_user.id): return
    await state.clear()
    await _hedit(call, "🔗 <b>Demo link</b> bhejo (https://...).\n<i>'none' bhejo to demo band ho jayega.</i>\n\n/cancel to abort.",
                 admin_back_kb())
    await state.set_state(AdminStates.demo_value)

@dp.message(AdminStates.demo_value)
async def admin_demo_link_save(m: Message, state: FSMContext):
    if not _is_admin(m.from_user.id): return
    raw = (m.text or "").strip()
    if raw == "/cancel":
        return await _cancel_to_admin(m, state)
    if raw.lower() == "none":
        set_setting("demo_link", ""); set_setting("demo_video", "")
        msg = "🎬 Panel Demo band kar diya."
    elif re.fullmatch(r"https?://\S+", raw):
        set_setting("demo_link", raw); set_setting("demo_video", "")
        msg = f"✅ Demo link set: <code>{html_escape(raw)}</code>"
    else:
        return await m.answer("❌ https:// se shuru hone wala link bhejo, ya 'none', ya /cancel.")
    await state.clear()
    await m.answer(msg, reply_markup=admin_kb(), parse_mode='HTML')

@dp.callback_query(F.data == "admin_demo_upload")
async def admin_demo_upload_start(call: CallbackQuery, state: FSMContext):
    if not _is_admin(call.from_user.id): return
    await state.clear()
    await _hedit(call, "🎬 <b>Demo video</b> bhejo (video file).\n\n/cancel to abort.", admin_back_kb())
    await state.set_state(AdminStates.demo_video)

@dp.message(AdminStates.demo_video)
async def admin_demo_video_save(m: Message, state: FSMContext):
    if not _is_admin(m.from_user.id): return
    if (m.text or "").strip() == "/cancel":
        return await _cancel_to_admin(m, state)
    fid = None
    if m.video:
        fid = m.video.file_id
    elif m.document and (m.document.mime_type or "").startswith("video/"):
        fid = m.document.file_id
    if not fid:
        return await m.answer("❌ Video file bhejo, ya /cancel.")
    set_setting("demo_video", fid); set_setting("demo_link", "")
    await state.clear()
    await m.answer("✅ Demo video save ho gaya.", reply_markup=admin_kb(), parse_mode='HTML')

@dp.callback_query(F.data == "admin_demo_clear")
async def admin_demo_clear(call: CallbackQuery, state: FSMContext):
    if not _is_admin(call.from_user.id): return
    await state.clear()
    set_setting("demo_link", ""); set_setting("demo_video", "")
    await call.answer("Cleared")
    text, kb = _demo_admin_view()
    await _hedit(call, text, kb)

# ---- Premium emoji DB: JSON export / import ----
def _pe_backup_file() -> str:
    data = [{"emoji_id": e, "label": l, "slot": s} for _id, e, l, s in pe_all()]
    path = os.path.join(BASE_DIR, "premium_emoji_backup.json")
    with open(path, "w", encoding="utf-8") as fh:
        json.dump(data, fh, ensure_ascii=False, indent=2)
    return path

@dp.callback_query(F.data == "admin_pe_export")
async def admin_pe_export(call: CallbackQuery, state: FSMContext):
    if not _is_admin(call.from_user.id): return
    await state.clear()
    path = _pe_backup_file()
    await call.message.answer_document(FSInputFile(path),
                                       caption=f"🌟 Premium emoji DB backup · {len(pe_all())} emojis")
    await call.answer("Exported")

@dp.callback_query(F.data == "admin_pe_import")
async def admin_pe_import_start(call: CallbackQuery, state: FSMContext):
    if not _is_admin(call.from_user.id): return
    await state.clear()
    await _hedit(call, "📥 <b>Premium emoji JSON import</b>\nExport wali <code>.json</code> file bhejo.\n"
                       "Jo emoji pehle se hain wo skip hongi; slot wali update ho jaayengi.\n\n/cancel to abort.",
                 admin_back_kb())
    await state.set_state(AdminStates.pe_import)

@dp.message(AdminStates.pe_import)
async def admin_pe_import_save(m: Message, state: FSMContext):
    if not _is_admin(m.from_user.id): return
    if (m.text or "").strip() == "/cancel":
        return await _cancel_to_admin(m, state)
    if not m.document:
        return await m.answer("❌ JSON file bhejo, ya /cancel.")
    if (m.document.file_size or 0) > 2_000_000:
        return await m.answer("❌ File bahut badi hai (max 2 MB).")
    try:
        f = await bot.get_file(m.document.file_id)
        blob = await bot.download_file(f.file_path)
        items = json.loads(blob.read().decode("utf-8"))
    except Exception:
        return await m.answer("❌ JSON file padh nahi paayi. Export wali file bhejo.")
    if not isinstance(items, list):
        return await m.answer("❌ JSON ek list honi chahiye.")
    saved = updated = skipped = 0
    for it in items[:500]:
        if not isinstance(it, dict):
            continue
        eid = str(it.get("emoji_id", "")).strip()
        if not eid.isdigit() or len(eid) < 6:
            continue
        label = re.sub(r"[^\w \-]", "", str(it.get("label") or "")).strip()[:30] or f"Emoji {eid[-4:]}"
        slot = str(it.get("slot") or "").strip()
        if slot not in DEFAULT_EMOJIS:
            slot = ""
        if db_query("SELECT id FROM premium_emojis WHERE emoji_id=?", (eid,), fetchone=True):
            if slot:
                db_query("UPDATE premium_emojis SET slot=? WHERE emoji_id=?", (slot, eid))
                updated += 1
            else:
                skipped += 1
            continue
        db_query("INSERT INTO premium_emojis (emoji_id, label, slot, created_at) VALUES (?, ?, ?, ?)",
                 (eid, label, slot, _hnow()))
        saved += 1
    pe_apply_all()
    log_activity(m.from_user.id, "PREMIUM_EMOJI_IMPORT", f"new={saved} slot_updated={updated} skipped={skipped}")
    await state.clear()
    await m.answer(f"✅ <b>Import done</b>\n🆕 New: <b>{saved}</b> · 🔁 Slot updated: <b>{updated}</b> · ⏭ Skipped: <b>{skipped}</b>",
                   reply_markup=admin_kb(), parse_mode='HTML')

# ---- Startup backups for the admin (every restart) ----
async def send_startup_backups() -> None:
    await asyncio.sleep(5)
    try:
        path = _pe_backup_file()
        await bot.send_document(ADMIN_ID, FSInputFile(path),
                                caption=f"🌟 <b>Premium emoji DB backup</b> · {len(pe_all())} emojis (restart backup)",
                                parse_mode='HTML')
    except Exception as e:
        logger.error(f"Premium emoji backup send failed: {e}")
    try:
        if os.path.exists(DB_FILE):
            await bot.send_document(ADMIN_ID, FSInputFile(DB_FILE),
                                    caption="📦 <b>User database backup</b> (Cuibcc.db) — restart backup",
                                    parse_mode='HTML')
    except Exception as e:
        logger.error(f"DB backup send failed: {e}")

# ==============================================================================
# 24J. CO-ADMIN LOGIN, RESELLER APPROVAL + BROADCAST, PAYMENT LIST, PER-PANEL DEMO, HOSTING PREMIUM
# ==============================================================================
def ext_init_db() -> None:
    db_query("CREATE TABLE IF NOT EXISTS reseller_requests (id INTEGER PRIMARY KEY AUTOINCREMENT, "
             "user_id INTEGER, fee REAL, status TEXT DEFAULT 'pending', created_at TEXT)")
    db_query("CREATE TABLE IF NOT EXISTS panel_demos (panel_key TEXT PRIMARY KEY, panel_name TEXT, "
             "link TEXT DEFAULT '', video TEXT DEFAULT '')")

# ---- co-admin: /admin password prompt ----
@dp.message(AdminStates.co_login)
async def co_login_check(m: Message, state: FSMContext):
    uid = m.from_user.id
    raw = (m.text or "").strip()
    try:
        await m.delete()                      # keep the password out of the chat
    except Exception:
        pass
    if raw == "/cancel":
        await state.clear()
        return await m.answer("Cancelled.")
    tries = _co_fail.get(uid, 0)
    if tries >= CO_ADMIN_MAX_TRIES:
        await state.clear()
        return await m.answer("🚫 Bahut galat attempts. Owner se contact karo.")
    if verify_password(raw, _co_pw_hash()):
        _co_admins[uid] = time.time() + CO_ADMIN_HOURS * 3600
        _co_fail.pop(uid, None)
        await state.clear()
        sec_log("CO_ADMIN_LOGIN_OK", uid)
        return await m.answer(admin_header(), reply_markup=admin_kb(), parse_mode='HTML')
    _co_fail[uid] = tries + 1
    sec_log("CO_ADMIN_LOGIN_FAIL", uid, f"try={tries + 1}")
    if tries + 1 >= CO_ADMIN_MAX_TRIES:
        await state.clear()
        try:
            await bot.send_message(ADMIN_ID, f"🚨 Admin password: {CO_ADMIN_MAX_TRIES} galat attempts by <code>{uid}</code>", parse_mode='HTML')
        except Exception:
            pass
        return await m.answer("🚫 Locked. Owner ko inform kar diya.")
    await m.answer(f"❌ Galat password. ({CO_ADMIN_MAX_TRIES - tries - 1} attempts baaki)")

@dp.callback_query(F.data == "admin_co_pw")
async def admin_co_pw_start(call: CallbackQuery, state: FSMContext):
    if call.from_user.id != ADMIN_ID:
        return await call.answer("Owner only", show_alert=True)
    await state.clear()
    await _hedit(call, "🔑 <b>Co-Admin password</b> naya bhejo (min 8 characters).\n<i>Purane unlocks khatam ho jayenge.</i>\n\n/cancel to abort.",
                 admin_back_kb())
    await state.set_state(AdminStates.co_setpw)

@dp.message(AdminStates.co_setpw)
async def admin_co_pw_save(m: Message, state: FSMContext):
    if m.from_user.id != ADMIN_ID:
        return
    raw = (m.text or "").strip()
    try:
        await m.delete()
    except Exception:
        pass
    if raw == "/cancel":
        return await _cancel_to_admin(m, state)
    if len(raw) < 8:
        return await m.answer("❌ Kam se kam 8 characters.")
    set_setting("co_admin_pw_hash", hash_password(raw))
    _co_admins.clear()
    sec_log("CO_ADMIN_PW_CHANGED", m.from_user.id)
    await state.clear()
    await m.answer("✅ Co-admin password change ho gaya.", reply_markup=admin_kb(), parse_mode='HTML')

# ---- broadcast: all users (skips banned) + reseller-only broadcast, with failure reasons ----
async def _broadcast_to(message: Message, state: FSMContext, ids: List[int], label: str) -> None:
    await state.clear()
    status = await message.answer(f"⏳ {label} broadcast chal raha hai... ({len(ids)} users)", parse_mode='HTML')
    sent, failed, errors = 0, 0, {}
    for uid in ids:
        try:
            await message.send_copy(chat_id=uid)
            sent += 1
        except Exception as e:
            failed += 1
            key = f"{type(e).__name__}: {str(e)[:70]}"
            errors[key] = errors.get(key, 0) + 1
        await asyncio.sleep(0.05)
    top = "\n".join(f"• {c}× {html_escape(k)}" for k, c in sorted(errors.items(), key=lambda x: -x[1])[:3])
    body = f"✅ <b>{label} Broadcast complete</b>\n🟢 Sent: {sent}\n🔴 Failed/blocked: {failed}"
    if top:
        body += f"\n\n<i>Failure reasons:</i>\n{top}"
    try:
        await status.edit_text(body, reply_markup=admin_kb(), parse_mode='HTML')
    except Exception:
        await message.answer(body, reply_markup=admin_kb(), parse_mode='HTML')

@dp.message(AdminStates.broadcast_msg)
async def admin_broadcast_send(message: Message, state: FSMContext):
    if not _is_admin(message.from_user.id):
        return
    if (message.text or "").strip() == "/cancel":
        return await _cancel_to_admin(message, state)
    ids = [r[0] for r in (db_query("SELECT user_id FROM users WHERE COALESCE(is_banned,0)=0", fetchall=True) or [])]
    await _broadcast_to(message, state, ids, "All users")

@dp.callback_query(F.data == "admin_rbc_start")
async def admin_rbc_start(call: CallbackQuery, state: FSMContext):
    if not _is_admin(call.from_user.id):
        return
    await state.clear()
    await _hedit(call, "📢 <b>Reseller Broadcast</b>\nJo message bhejoge wo sirf <b>Reseller</b> users ko jayega.\n\n/cancel to abort.",
                 admin_back_kb())
    await state.set_state(AdminStates.rbc_msg)

@dp.message(AdminStates.rbc_msg)
async def admin_rbc_send(m: Message, state: FSMContext):
    if not _is_admin(m.from_user.id):
        return
    if (m.text or "").strip() == "/cancel":
        return await _cancel_to_admin(m, state)
    ids = [r[0] for r in (db_query("SELECT user_id FROM users WHERE is_reseller=1 AND COALESCE(is_banned,0)=0", fetchall=True) or [])]
    await _broadcast_to(m, state, ids, "Reseller")

# ---- reseller approval (admin approves, fee is held until then) ----
@dp.callback_query(F.data == "admin_rr_list")
async def admin_rr_list(call: CallbackQuery, state: FSMContext):
    if not _is_admin(call.from_user.id):
        return
    await state.clear()
    rows = db_query("SELECT r.id, r.user_id, u.first_name, r.fee, r.created_at FROM reseller_requests r "
                    "LEFT JOIN users u ON u.user_id = r.user_id WHERE r.status='pending' ORDER BY r.id LIMIT 20", fetchall=True) or []
    text = "📥 <b>RESELLER REQUESTS (pending)</b>\n━━━━━━━━━━━━━━━━━━\n"
    kb = []
    if not rows:
        text += "Koi pending request nahi."
    for rid, uid, fname, fee, at in rows:
        text += f"🆔 #{rid} · {html_escape(fname or '')} (<code>{uid}</code>) · fee {fmt_curr(safe_float(fee))} · {at}\n"
        kb.append([InlineKeyboardButton(text=f"✅ Approve #{rid}", callback_data=f"rr_ok_{rid}", style="success"),
                   InlineKeyboardButton(text=f"❌ Reject #{rid}", callback_data=f"rr_no_{rid}", style="danger")])
    kb.append([InlineKeyboardButton(text="Back", callback_data="admin_reseller_menu", icon_custom_emoji_id=get_emoji_icon("back"), style="danger")])
    await _hedit(call, text, InlineKeyboardMarkup(inline_keyboard=kb))

@dp.callback_query(F.data.startswith("rr_"))
async def admin_rr_decide(call: CallbackQuery):
    if not _is_admin(call.from_user.id):
        return await call.answer("⛔ Not allowed", show_alert=True)
    action, _, rid_s = call.data[3:].partition("_")
    if action not in ("ok", "no") or not rid_s.isdigit():
        return await call.answer("Invalid", show_alert=True)
    rid = int(rid_s)
    row = db_query("SELECT user_id, fee, status FROM reseller_requests WHERE id=?", (rid,), fetchone=True)
    if not row:
        return await call.answer("Request nahi mili.", show_alert=True)
    uid, fee, status = row
    if status != "pending":
        return await call.answer(f"Ye request pehle se {status} hai.", show_alert=True)
    if action == "ok":
        db_query("UPDATE reseller_requests SET status='approved' WHERE id=? AND status='pending'", (rid,))
        db_query("UPDATE users SET is_reseller=1, reseller_since=?, account_type='Reseller' WHERE user_id=?",
                 (datetime.now().strftime("%Y-%m-%d"), uid))
        verdict = "✅ APPROVED"
        user_msg = f"🎉 <b>Reseller request approved!</b>\n#{rid} · Ab aap Reseller tier mein ho."
    else:
        db_query("UPDATE reseller_requests SET status='rejected' WHERE id=? AND status='pending'", (rid,))
        db_query("UPDATE users SET balance = balance + ? WHERE user_id=?", (safe_float(fee), uid))
        verdict = "❌ REJECTED (fee refunded)"
        user_msg = f"❌ <b>Reseller request rejected</b>\n#{rid} · Fee {fmt_curr(safe_float(fee))} wallet mein wapas kar di gayi."
    log_activity(uid, "RESELLER_" + ("APPROVED" if action == "ok" else "REJECTED"), f"#{rid}")
    sec_log("RESELLER_DECISION", call.from_user.id, f"#{rid} {action} user={uid}")
    try:
        await bot.send_message(uid, user_msg, parse_mode='HTML')
    except Exception:
        pass
    await call.answer("Done")
    try:
        await call.message.edit_reply_markup(reply_markup=None)
    except Exception:
        pass
    await call.message.answer(f"Reseller #{rid} → <b>{verdict}</b>", parse_mode='HTML')

# ---- payment requests list (every deposit, approve/reject from here) ----
@dp.callback_query(F.data == "admin_deposits")
async def admin_deposits_list(call: CallbackQuery, state: FSMContext):
    if not _is_admin(call.from_user.id):
        return
    await state.clear()
    rows = db_query("SELECT id, user_id, method, amount, utr, status FROM deposit_requests ORDER BY id DESC LIMIT 20", fetchall=True) or []
    icon = {"pending": "⏳", "approved": "✅", "rejected": "❌", "awaiting_payment": "🕒"}
    text = "🧾 <b>PAYMENT REQUESTS</b> (last 20)\n━━━━━━━━━━━━━━━━━━\n"
    kb = []
    if not rows:
        text += "Abhi koi request nahi."
    for rid, uid, method, amt, utr, st in rows:
        text += (f"{icon.get(st, '•')} #{rid} · {PAY_LABEL.get(method, method)} · {fmt_curr(safe_float(amt))} · "
                 f"<code>{uid}</code> · UTR {html_escape(str(utr or '-'))}\n")
        if st == "pending" and len(kb) < 8:
            kb.append([InlineKeyboardButton(text=f"✅ Approve #{rid}", callback_data=f"dr_ok_{rid}", style="success"),
                       InlineKeyboardButton(text=f"❌ Reject #{rid}", callback_data=f"dr_no_{rid}", style="danger")])
    kb.append([InlineKeyboardButton(text="Back to Admin", callback_data="admin_panel_back",
                                    icon_custom_emoji_id=get_emoji_icon("back"), style="danger")])
    await _hedit(call, text[:4000], InlineKeyboardMarkup(inline_keyboard=kb))

# ---- per-panel demo ----
def _pkey(panel: str) -> str:
    return hashlib.sha1(panel.encode("utf-8")).hexdigest()[:12]

def _pdemo_get(panel: str):
    return db_query("SELECT link, video FROM panel_demos WHERE panel_key=?", (_pkey(panel),), fetchone=True)

def _pdemo_save(panel: str, link: str, video: str) -> None:
    db_query("INSERT OR REPLACE INTO panel_demos (panel_key, panel_name, link, video) VALUES (?, ?, ?, ?)",
             (_pkey(panel), panel, link, video))

def _panel_names() -> List[str]:
    rows = db_query("SELECT DISTINCT panel_name FROM products WHERE panel_name != ''", fetchall=True) or []
    return [r[0] for r in rows if r[0]]

def _panel_by_key(key: str) -> Optional[str]:
    return {_pkey(n): n for n in _panel_names()}.get(key)

@dp.callback_query(F.data.startswith("pdm_"))
async def panel_demo_view(call: CallbackQuery):
    panel = _panel_by_key(call.data[len("pdm_"):])
    row = _pdemo_get(panel) if panel else None
    if not row or not (row[0] or row[1]):
        return await call.answer("Is panel ka demo abhi set nahi hai.", show_alert=True)
    link, video = row
    await call.answer()
    try:
        if video:
            await call.message.answer_video(video, caption=f"🎬 <b>{html_escape(panel)} — Demo</b>", parse_mode='HTML')
        else:
            await call.message.answer(f"🎬 <b>{html_escape(panel)} — Demo</b>\nNeeche button se dekho.",
                                      reply_markup=InlineKeyboardMarkup(inline_keyboard=[[
                                          InlineKeyboardButton(text="▶ Open Demo", url=link, style="success")]]),
                                      parse_mode='HTML')
    except Exception as e:
        logger.error(f"panel demo send failed: {e}")
        await call.message.answer("❌ Demo abhi nahi chal raha. Admin se contact karo.")

@dp.callback_query(F.data == "admin_pdemo_menu")
async def admin_pdemo_menu(call: CallbackQuery, state: FSMContext):
    if not _is_admin(call.from_user.id):
        return
    await state.clear()
    kb = []
    for n in _panel_names()[:40]:
        row = _pdemo_get(n)
        tag = "🟢" if row and (row[0] or row[1]) else "⚪"
        kb.append([InlineKeyboardButton(text=f"{tag} {n}"[:58], callback_data=f"admin_pd_{_pkey(n)}", style="primary")])
    kb.append([InlineKeyboardButton(text="Back to Admin", callback_data="admin_panel_back",
                                    icon_custom_emoji_id=get_emoji_icon("back"), style="danger")])
    text = ("🎬 <b>PANEL DEMOS</b>\n━━━━━━━━━━━━━━━━━━\n"
            "Panel par tap karke uska demo set karo. 🟢 = demo set hai, ⚪ = nahi.\n"
            "<i>Panel name wahi hai jo product mein set hai.</i>")
    if not kb[:-1]:
        text += "\n\nAbhi koi panel nahi — pehle product mein panel name set karo."
    await _hedit(call, text, InlineKeyboardMarkup(inline_keyboard=kb))

@dp.callback_query(F.data.startswith("admin_pd_"))
async def admin_pd_view(call: CallbackQuery):
    if not _is_admin(call.from_user.id):
        return
    key = call.data[len("admin_pd_"):]
    panel = _panel_by_key(key)
    if not panel:
        return await call.answer("Panel nahi mila.", show_alert=True)
    row = _pdemo_get(panel) or ("", "")
    cur = "🎬 video" if row[1] else (f"🔗 {row[0]}" if row[0] else "OFF")
    text = f"🎬 <b>{html_escape(panel)}</b>\n━━━━━━━━━━━━━━━━━━\nDemo: <b>{html_escape(cur)}</b>"
    kb = InlineKeyboardMarkup(inline_keyboard=[
        [InlineKeyboardButton(text="🔗 Set Link", callback_data=f"admin_pdl_{key}", style="success")],
        [InlineKeyboardButton(text="🎬 Upload Video", callback_data=f"admin_pdu_{key}", style="primary")],
        [InlineKeyboardButton(text="🗑 Clear", callback_data=f"admin_pdc_{key}", style="danger")],
        [InlineKeyboardButton(text="Back", callback_data="admin_pdemo_menu", icon_custom_emoji_id=get_emoji_icon("back"), style="danger")],
    ])
    await _hedit(call, text, kb)

@dp.callback_query(F.data.startswith("admin_pdl_"))
async def admin_pdl_start(call: CallbackQuery, state: FSMContext):
    if not _is_admin(call.from_user.id):
        return
    panel = _panel_by_key(call.data[len("admin_pdl_"):])
    if not panel:
        return await call.answer("Panel nahi mila.", show_alert=True)
    await state.clear()
    await state.update_data(pdname=panel)
    await _hedit(call, f"🔗 <b>{html_escape(panel)}</b> ka demo link bhejo (https://...).\n<i>'none' = demo band.</i>\n\n/cancel to abort.",
                 admin_back_kb())
    await state.set_state(AdminStates.pdemo_value)

@dp.callback_query(F.data.startswith("admin_pdu_"))
async def admin_pdu_start(call: CallbackQuery, state: FSMContext):
    if not _is_admin(call.from_user.id):
        return
    panel = _panel_by_key(call.data[len("admin_pdu_"):])
    if not panel:
        return await call.answer("Panel nahi mila.", show_alert=True)
    await state.clear()
    await state.update_data(pdname=panel)
    await _hedit(call, f"🎬 <b>{html_escape(panel)}</b> ka demo <b>video</b> bhejo.\n\n/cancel to abort.", admin_back_kb())
    await state.set_state(AdminStates.pdemo_video)

@dp.callback_query(F.data.startswith("admin_pdc_"))
async def admin_pdc(call: CallbackQuery, state: FSMContext):
    if not _is_admin(call.from_user.id):
        return
    panel = _panel_by_key(call.data[len("admin_pdc_"):])
    if not panel:
        return await call.answer("Panel nahi mila.", show_alert=True)
    _pdemo_save(panel, "", "")
    await call.answer("Cleared")
    await admin_pd_view(call)

@dp.message(AdminStates.pdemo_value)
async def admin_pdemo_link_save(m: Message, state: FSMContext):
    if not _is_admin(m.from_user.id):
        return
    if (m.text or "").strip() == "/cancel":
        return await _cancel_to_admin(m, state)
    panel = (await state.get_data()).get("pdname")
    if not panel:
        await state.clear()
        return await m.answer("❌ Session expire. Panel Demos se dobara kholo.", reply_markup=admin_kb())
    raw = (m.text or "").strip()
    if raw.lower() == "none":
        link = ""
    elif re.fullmatch(r"https?://\S+", raw):
        link = raw
    else:
        return await m.answer("❌ https:// link bhejo, 'none', ya /cancel.")
    _pdemo_save(panel, link, "")
    sec_log("PANEL_DEMO_SET", m.from_user.id, panel)
    await state.clear()
    await m.answer(f"✅ <b>{html_escape(panel)}</b> ka demo: {'band' if not link else 'link set'}.", reply_markup=admin_kb(), parse_mode='HTML')

@dp.message(AdminStates.pdemo_video)
async def admin_pdemo_video_save(m: Message, state: FSMContext):
    if not _is_admin(m.from_user.id):
        return
    if (m.text or "").strip() == "/cancel":
        return await _cancel_to_admin(m, state)
    panel = (await state.get_data()).get("pdname")
    fid = m.video.file_id if m.video else (m.document.file_id if m.document and (m.document.mime_type or "").startswith("video/") else None)
    if not panel:
        await state.clear()
        return await m.answer("❌ Session expire. Panel Demos se dobara kholo.", reply_markup=admin_kb())
    if not fid:
        return await m.answer("❌ Video bhejo, ya /cancel.")
    _pdemo_save(panel, "", fid)
    sec_log("PANEL_DEMO_VIDEO", m.from_user.id, panel)
    await state.clear()
    await m.answer(f"✅ <b>{html_escape(panel)}</b> ka demo video save ho gaya.", reply_markup=admin_kb(), parse_mode='HTML')

# ---- hosting premium: admin sets price + days, user buys with wallet ----
def _prem_price() -> Tuple[float, int]:
    return safe_float(get_setting("host_prem_price", "0")), max(1, int(safe_float(get_setting("host_prem_days", "30"))))

@dp.callback_query(F.data == "admin_hprem")
async def admin_hprem_start(call: CallbackQuery, state: FSMContext):
    if not _is_admin(call.from_user.id):
        return
    await state.clear()
    price, days = _prem_price()
    await _hedit(call, f"💎 <b>Hosting premium</b>\nAbhi: <b>{fmt_curr(price)}</b> · <b>{days} din</b>\n\n"
                       "Naya bhejo: <code>PRICE DAYS</code>\nExample: <code>199 30</code>\n<i>Price 0 = premium band.</i>\n\n/cancel to abort.",
                 admin_back_kb())
    await state.set_state(AdminStates.hprem_value)

@dp.message(AdminStates.hprem_value)
async def admin_hprem_save(m: Message, state: FSMContext):
    if not _is_admin(m.from_user.id):
        return
    if (m.text or "").strip() == "/cancel":
        return await _cancel_to_admin(m, state)
    parts = (m.text or "").split()
    if len(parts) != 2:
        return await m.answer("❌ Format: <code>PRICE DAYS</code> (e.g. <code>199 30</code>)", parse_mode='HTML')
    try:
        price, days = round(float(parts[0]), 2), int(parts[1])
    except ValueError:
        return await m.answer("❌ Numbers bhejo (e.g. 199 30).")
    if not (0 <= price <= 100000) or not (1 <= days <= 3650):
        return await m.answer("❌ Price 0 se 1,00,000 aur days 1 se 3650 ke beech hon.")
    set_setting("host_prem_price", str(price))
    set_setting("host_prem_days", str(days))
    sec_log("HOST_PREMIUM_PRICE", m.from_user.id, f"{price} {days}")
    await state.clear()
    await m.answer(f"✅ Hosting premium: <b>{fmt_curr(price)}</b> for <b>{days} din</b>", reply_markup=admin_kb(), parse_mode='HTML')

@dp.callback_query(F.data == "hst_buyprem")
async def host_buy_prem(call: CallbackQuery, state: FSMContext):
    await state.clear()
    u = host_user(call.from_user.id)
    if not await _host_gate(call, u):
        return
    price, days = _prem_price()
    if price <= 0:
        return await call.answer("💎 Premium abhi available nahi hai.", show_alert=True)
    row = db_query("SELECT balance FROM users WHERE user_id=?", (call.from_user.id,), fetchone=True)
    bal = safe_float(row[0]) if row else 0.0
    text = (f"💎 <b>HOSTING PREMIUM</b>\n━━━━━━━━━━━━━━━━━━\n"
            f"💰 Price: <b>{fmt_curr(price)}</b>\n📅 Validity: <b>{days} din</b>\n"
            f"🎰 Premium slots: <b>{host_limit({'premium': True})}</b>\n\n"
            f"💼 Wallet: <b>{fmt_curr(bal)}</b>\n<i>Confirm karne par wallet se amount katega.</i>")
    kb = InlineKeyboardMarkup(inline_keyboard=[
        [InlineKeyboardButton(text=f"✅ Buy · {fmt_curr(price)}", callback_data="hst_buyprem_yes", style="success")],
        [_btn("Back", "hst_menu", "back", "danger")],
    ])
    await _hedit(call, text, kb)

@dp.callback_query(F.data == "hst_buyprem_yes")
async def host_buy_prem_yes(call: CallbackQuery):
    uid = call.from_user.id
    u = host_user(uid)
    if not await _host_gate(call, u):
        return
    price, days = _prem_price()
    if price <= 0:
        return await call.answer("💎 Premium abhi available nahi hai.", show_alert=True)
    conn = sqlite3.connect(DB_FILE, timeout=15)
    try:
        cur = conn.execute("UPDATE users SET balance = balance - ? WHERE user_id=? AND balance >= ?", (price, uid, price))
        conn.commit()
        ok = cur.rowcount == 1
    finally:
        conn.close()
    if not ok:
        return await call.answer("❌ Balance kam hai. Pehle Add Balance karo.", show_alert=True)
    now = datetime.now()
    base = now
    if u.get("premium") and u.get("premium_until"):
        try:
            base = max(now, datetime.fromisoformat(u["premium_until"]))
        except ValueError:
            pass
    until = base + timedelta(days=days)
    db_query("UPDATE host_users SET is_premium=1, premium_until=? WHERE user_id=?", (until.isoformat(timespec="seconds"), uid))
    log_activity(uid, "HOST_PREMIUM_BUY", f"{price} {days}d")
    sec_log("HOST_PREMIUM_BUY", uid, f"{price} {days}")
    try:
        await bot.send_message(ADMIN_ID, f"💎 <b>Hosting premium bought</b>\n👤 <code>{uid}</code> · {fmt_curr(price)} · {days} din", parse_mode='HTML')
    except Exception:
        pass
    await call.answer("✅ Premium active!", show_alert=True)
    await _hedit(call, f"💎 <b>Premium active!</b>\nValid till: <b>{until:%Y-%m-%d %H:%M}</b>", _host_back_kb())


def _reseller_diag() -> str:
    cfg = get_reseller_config()
    row = db_query("SELECT COUNT(*) FROM products WHERE product_pid != '' AND duration_string != ''", fetchone=True)
    pids = (row or (0,))[0]
    last = get_setting("reseller_last_error", "") or "—"
    key_bad = (not cfg["api_key"]) and ("reseller_api_key" in _bad_secrets)

    def mark(b: bool) -> str:
        return "✅" if b else "❌"
    lines = [
        f"{mark(bool(cfg['url']))} Endpoint set",
        f"{mark(bool(cfg['api_key']))} API key" + (" — ⚠️ decrypt FAILED, dobara bharo" if key_bad else ""),
        f"{mark(bool(cfg['master_key']))} Master key",
        f"{mark(cfg['status'].upper() == 'ON')} API status ON",
        f"{mark(pids > 0)} Products with PID + duration: <b>{pids}</b>",
    ]
    return "\n\n🩺 <b>Diagnostics</b>\n" + "\n".join(lines) + f"\n🕒 Last API error: <code>{html_escape(last[:150])}</code>"

# ==============================================================================
# 25. BOOTSTRAPPING & MAIN
# ==============================================================================
async def main() -> None:
    init_db()
    ext_init_db()
    logger.info("Initializing DB structure...")
    migrate_categories()
    pe_apply_all()                     # saved premium emojis come back after every restart
    encrypt_sensitive_settings()
    host_init_db()
    _harden_process()
    await host_detect_sandbox()
    if _HOST_SANDBOX["mode"] != "bwrap" and not _host_run_as():
        logger.warning("HOSTING: no sandbox (install bubblewrap: apt install bubblewrap, or set HOST_RUN_AS_USER). "
                       "Hosted code runs with a clean environment + limits only.")
    for _p in (DB_FILE, os.path.join(BASE_DIR, ".env"), VAULT_FILE, DATA_KEY_FILE, "bot_activity.log", "security.log"):
        try: os.chmod(_p, 0o600)
        except OSError: pass
    if RESET_USERS_ON_NEXT_START and get_setting(RESET_FLAG_KEY, "0") != "1":
        bk = backup_database()
        cnt = reset_all_user_data()
        set_setting(RESET_FLAG_KEY, "1")
        logger.info(f"FRESH START: user data wiped {cnt} | backup: {bk}")
        try:
            await bot.send_message(ADMIN_ID, f"✅ <b>Fresh start done.</b> All user data & balance history deleted.\nBackup file: <code>{bk}</code>", parse_mode='HTML')
            if bk: await bot.send_document(ADMIN_ID, FSInputFile(bk), caption="📦 Backup of the old data")
        except Exception as e:
            logger.warning(f"Admin notice failed: {e}")
    asyncio.create_task(auto_verify_task())
    asyncio.create_task(host_restore_bots())
    asyncio.create_task(send_startup_backups())
    logger.info("SGVIP Auto-Verifier Daemon Running in Background.")
    logger.info("🚀 CORE SYSTEM IS FULLY OPERATIONAL...")
    try:
        await dp.start_polling(bot)
    except Exception as err:
        logger.error(f"Critical System Failure in Polling: {err}")
    finally:
        host_shutdown()
        await bot.session.close()

if __name__ == "__main__":
    try:
        asyncio.run(main())
    except (KeyboardInterrupt, SystemExit):
        logger.info("System shutting down gracefully. Goodbye.")