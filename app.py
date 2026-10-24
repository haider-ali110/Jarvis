import os
import sys
import re
import json
import wave
import hashlib
import hmac
import ast
import math
import time
import shutil
import queue
import difflib
import random
import socket
import threading
import urllib.parse
import webbrowser
import subprocess
import datetime
import ctypes
import xml.etree.ElementTree as ET
from collections import deque

import psutil
import requests
import speech_recognition as sr
from flask import Flask, jsonify, request
from flask_cors import CORS

# Fixes the blank/black window on some Fedora + WebKitGTK (esp. NVIDIA) setups
os.environ.setdefault("WEBKIT_DISABLE_DMABUF_RENDERER", "1")
try:
    import webview
except Exception as _e:
    print(f"pywebview unavailable ({_e}); will open in your normal browser instead.")
    webview = None

# =====================================================================
# CONFIG (edit these)
# =====================================================================
WAKE_WORD_ENABLED = os.environ.get("JARVIS_WAKE") == "1"   # OFF by default: Jarvis answers any command. Set JARVIS_WAKE=1 to require "Hey Jarvis"
MIC_DEBUG = True                # print what the mic pipeline is doing in the terminal
WAKE_WINDOW_SECONDS = 10        # how long Jarvis stays awake after waking
FOLLOWUP_SECONDS = 8            # extra awake time after each reply
AUTO_ALERTS = True              # speak on low battery / high CPU
DEFAULT_CITY = os.environ.get("JARVIS_CITY", "Peshawar")  # used for weather

VOICE = "evil"                  # "evil", "robot" or "normal" (say "robot voice" to switch live)
WAKE_REPLY = "chime"            # "chime" = instant beep (fast), "speech" = says "Yes?"
SPEAK_MAX_CHARS = 220           # long replies are shown in full but only the start is spoken

# FIX: replies to TYPED commands are spoken too (set to False to keep typed replies silent)
SPEAK_TYPED_REPLIES = os.environ.get("JARVIS_SPEAK_TYPED", "1") == "1"

# FIX: when the normal engine does not understand a command, ask the AI brain to repair the
# mis-heard sentence (this is the "understands me like Claude does" step). Set to 0 to disable.
AI_FIX_ENABLED = os.environ.get("JARVIS_AI_FIX", "1") == "1"

# Reopen the mic exactly as you left it (on/off). Mode, voice, theme and lock are always restored.
RESTORE_MIC = os.environ.get("JARVIS_RESTORE_MIC", "1") == "1"

# Password lock (set it by typing:  set password <your password>)
LOCK_JARVIS_WITH_SCREEN = True   # "lock screen" also locks Jarvis (only if a password is set)
UNLOCK_OS_ON_PASSWORD = True     # the right password also unlocks the system screen (Linux, via loginctl)
MAX_PASSWORD_TRIES = 5           # wrong tries before a short lockout
LOCKOUT_SECONDS = 30
# Password is controlled from CODE. To change it: edit this line and restart Jarvis.
JARVIS_PASSWORD = "2808"
ALLOW_PASSWORD_CHANGE_BY_COMMAND = False

# AI brain: tries local Ollama first, then Claude API if a key is set
OLLAMA_URL = os.environ.get("OLLAMA_URL", "http://localhost:11434")
OLLAMA_MODEL = os.environ.get("OLLAMA_MODEL", "llama3.2")
ANTHROPIC_KEY = os.environ.get("ANTHROPIC_API_KEY", "")
ANTHROPIC_MODEL = "claude-haiku-5-5"

# Speech recognition (English only)
SPEECH_LANG = os.environ.get("JARVIS_LANG", "en-IN")        # English only. Non-English text is rejected. Try en-US or en-GB if it mishears you.
STT_MODE = os.environ.get("JARVIS_STT", "auto").lower()     # auto = Whisper if installed, else Google, else Vosk | whisper | google | vosk

# Whisper (offline speech recognition, much better with accents).   pip install faster-whisper
WHISPER_MODEL = os.environ.get("JARVIS_WHISPER_MODEL", "small.en")   # tiny.en / base.en (faster) / small.en (better) / medium.en
WHISPER_DEVICE = os.environ.get("JARVIS_WHISPER_DEVICE", "cpu")      # "cuda" only if your NVIDIA CUDA libraries are installed
WHISPER_COMPUTE = os.environ.get("JARVIS_WHISPER_COMPUTE") or ("float16" if WHISPER_DEVICE == "cuda" else "int8")
WHISPER_THREADS = int(os.environ.get("JARVIS_WHISPER_THREADS", "4"))

# Which microphone to use (leave empty for the default). Say "list microphones" to see the numbers, e.g. JARVIS_MIC=2
MIC_INDEX = int(os.environ["JARVIS_MIC"]) if os.environ.get("JARVIS_MIC", "").isdigit() else None

# Offline speech recognition (optional): folder of a Vosk model
VOSK_PATH = os.path.expanduser(os.environ.get("VOSK_MODEL", "~/vosk-model"))

IS_LINUX = sys.platform.startswith("linux")
IS_WIN = sys.platform.startswith("win")

JARVIS_DIR = os.path.expanduser("~/.jarvis")
COMMANDS_FILE = os.path.join(JARVIS_DIR, "commands.json")
NOTES_FILE = os.path.join(JARVIS_DIR, "notes.txt")
HISTORY_FILE = os.path.join(JARVIS_DIR, "history.json")
LOCK_FILE = os.path.join(JARVIS_DIR, "lock.json")        # salted password hash (never the password itself)
MODES_FILE = os.path.join(JARVIS_DIR, "modes.json")      # your own "transform" modes
STATE_FILE = os.path.join(JARVIS_DIR, "state.json")      # remembers how you left Jarvis (mode, voice, locked)
TRASH_DIR = os.path.join(JARVIS_DIR, "trash")            # used when the system trash (gio) is missing
os.makedirs(JARVIS_DIR, exist_ok=True)

UNKNOWN = "I didn't understand that command."


# Bundled Resource Path Resolver for PyInstaller
def resource_path(relative_path):
    try:
        base_path = sys._MEIPASS
    except Exception:
        base_path = os.path.dirname(os.path.abspath(__file__))
    return os.path.join(base_path, relative_path)


if getattr(sys, 'frozen', False):
    sys.stdout = open(os.devnull, 'w')
    sys.stderr = open(os.devnull, 'w')

app = Flask(__name__)
CORS(app, origins=["http://127.0.0.1:5000", "http://localhost:5000"])   # only Jarvis' own page, not random websites

# =====================================================================
# GLOBAL STATE
# =====================================================================
state_lock = threading.Lock()
system_status = "PROCESSING"
mic_active = False
messages = []
message_id_counter = 0

speak_queue = queue.Queue()
tts_pending = threading.Event()
speaking_event = threading.Event()
recent_replies = []

# wake word state
awake_until = 0.0
session_active = False
wake_id = 0

# confirmation / memory state
pending_confirm = None
last_command = None
ai_history = deque(maxlen=8)
active_timers = []

# password lock + transform mode state
jarvis_locked = False
lock_fails = 0
lock_until = 0.0
current_mode = "jarvis"
current_persona = ""

# extra state
awaiting_password = False      # True after "unlock the screen": the next input is the password
awaiting_until = 0.0
ui_prefs = {}                  # what the frontend wants remembered (theme, ...)
speak_enabled = True           # False = text-only replies
last_reply = ""
play_proc = None               # the audio player currently speaking
last_speech_end = 0.0           # when Jarvis last finished talking (so the mic ignores his own echo)
stopwatch_start = None


# =====================================================================
# WAKE WORD HELPERS
# =====================================================================
WAKE_RE = re.compile(
    r'\b(?:(?:hey|hay|hi|ok|okay|a)\s+(?:jarvis|jarvas|jarviz|jervis|garvis|harvis|travis|service|'
    r'jar\s?vis|jar\s+this|java\s+is|jarvish)|jarvis|jarvas|jarviz|jervis|garvis|harvis|jarvish)\b'
)


def activate_wake():
    global awake_until, session_active, wake_id
    session_active = True
    wake_id += 1
    awake_until = time.time() + WAKE_WINDOW_SECONDS


def extend_awake(seconds):
    global awake_until
    awake_until = max(awake_until, time.time() + seconds)


def is_awake():
    global session_active
    if not WAKE_WORD_ENABLED:
        return True
    pc = pending_confirm
    if pc and time.time() < pc["expires"]:
        return True
    if awaiting_password and time.time() < awaiting_until:
        return True
    if session_active and time.time() < awake_until:
        return True
    session_active = False
    return False


# =====================================================================
# CHAT HISTORY (survives restarts)
# =====================================================================
def load_history():
    global messages, message_id_counter
    try:
        with open(HISTORY_FILE, "r", encoding="utf-8") as f:
            data = json.load(f)
        if isinstance(data, list):
            messages = data[-200:]
            message_id_counter = max((m.get("id", 0) for m in messages), default=0)
            for m in messages:                     # remove the old name / signature from messages saved earlier
                for key in ("user", "jarvis"):
                    if isinstance(m.get(key), str):
                        t = re.sub(r"\s*Signature:\s*AR-Jatala\.?", "", m[key])
                        t = re.sub(r",\s*Ali\b", "", t)
                        m[key] = re.sub(r"\bAli\b[,!]?\s*", "", t) if re.search(r"\bAli\b", t) else t
    except Exception:
        pass


def save_history():
    try:
        with open(HISTORY_FILE, "w", encoding="utf-8") as f:
            json.dump(messages[-200:], f)
    except Exception:
        pass


load_history()

if not os.path.exists(COMMANDS_FILE):
    try:
        with open(COMMANDS_FILE, "w", encoding="utf-8") as f:
            json.dump({
                "open my project": "code ~/projects",
                "say hello notification": "notify-send 'Hello from Jarvis'"
            }, f, indent=2)
    except Exception:
        pass


# =====================================================================
# VOICE SYNTHESIZER WORKER
# =====================================================================
VOICE_PROFILES = {
    # deep, slowed, distorted, with a dark echo
    "evil": ["pitch", "-450", "tempo", "0.93", "bass", "10", "overdrive", "6",
             "echo", "0.8", "0.6", "45", "0.35", "reverb", "20", "norm", "-1"],
    "robot": ["pitch", "-100", "phaser", "0.6", "0.66", "3", "0.6", "2", "-t"],
    "normal": [],
    "friday": ["pitch", "200", "tempo", "1.03", "norm", "-1"],
    "hacker": ["pitch", "-250", "tempo", "1.12", "overdrive", "4", "norm", "-1"],
}
current_voice = VOICE if VOICE in VOICE_PROFILES else "evil"
CACHE_DIR = os.path.join(JARVIS_DIR, "voice-cache")


def set_voice(name):
    global current_voice
    if name in VOICE_PROFILES:
        current_voice = name
        save_state()
        return True
    return False


def short_for_speech(text):
    text = re.sub(r'\s+', ' ', str(text)).strip()
    if len(text) <= SPEAK_MAX_CHARS:
        return text
    cut = text[:SPEAK_MAX_CHARS]
    end = max(cut.rfind(". "), cut.rfind("! "), cut.rfind("? "))
    return (cut[:end + 1] if end > 60 else cut).strip()


def tts_worker():
    global play_proc
    global system_status
    global last_speech_end

    piper_model = os.path.expanduser("~/piper-voices/en_US-ryan-high.onnx")
    raw_file = "/tmp/jarvis-raw.wav"
    os.makedirs(CACHE_DIR, exist_ok=True)

    # Load the voice ONCE (much faster than starting piper for every reply)
    voice = None
    if os.environ.get("JARVIS_PIPER_FAST", "1") == "1":
        try:
            probe = subprocess.run(
                [sys.executable, "-c",
                 "import sys; from piper import PiperVoice; PiperVoice.load(sys.argv[1])", piper_model],
                capture_output=True, text=True, timeout=60)
            if probe.returncode == 0 and "Exception" not in (probe.stderr or ""):
                from piper import PiperVoice
                voice = PiperVoice.load(piper_model)
            else:
                print("Piper fast mode not supported on this setup; using the safe (slower) mode.")
        except Exception as e:
            print(f"Piper fast mode skipped: {e}")

    player = None
    for cand in (["pw-play"], ["paplay"], ["aplay", "-q"]):
        if shutil.which(cand[0]):
            player = cand
            break

    def synth(text, path):
        if voice is not None:
            try:
                with wave.open(path, "wb") as wf:
                    if hasattr(voice, "synthesize_wav"):
                        voice.synthesize_wav(text, wf)
                    else:
                        voice.synthesize(text, wf)
                return
            except Exception as e:
                print(f"Piper fast mode failed, falling back: {e}")
        try:
            subprocess.run(
                [sys.executable, "-m", "piper", "-m", piper_model, "-f", path, "--", text],
                check=True, stdout=subprocess.DEVNULL, stderr=subprocess.PIPE, text=True
            )
            return
        except subprocess.CalledProcessError as e:
            # FIX: show the real reason piper failed (it was hidden before)
            print(f"Piper failed: {(e.stderr or '').strip()[-300:]}")
        except Exception as e:
            print(f"Piper failed: {e}")

        # FIX: backup voice so Jarvis never goes silent if piper is broken or the model is missing
        for exe, args in (("espeak-ng", ["-w", path, "--", text]), ("espeak", ["-w", path, "--", text])):
            if shutil.which(exe):
                subprocess.run([exe] + args, check=True,
                               stdout=subprocess.DEVNULL, stderr=subprocess.PIPE, text=True)
                print(f"(spoke with backup voice {exe}; install piper for the real voice)")
                return
        raise RuntimeError("No speech engine worked. Fix piper (pip install piper-tts + voice model) "
                           "or install espeak-ng: sudo dnf install espeak-ng")

    while True:
        text = speak_queue.get()

        if text is None:
            speak_queue.task_done()
            break

        with state_lock:
            system_status = "SPEAKING"

        try:
            spoken = short_for_speech(text)
            key = hashlib.md5(f"{current_voice}|{spoken}".encode()).hexdigest()
            final = os.path.join(CACHE_DIR, key + ".wav")  # repeated phrases play instantly

            if not os.path.exists(final):
                synth(spoken, raw_file)
                effects = VOICE_PROFILES.get(current_voice, [])
                if effects:
                    try:
                        subprocess.run(["sox", raw_file, final] + effects, check=True,
                                       stdout=subprocess.DEVNULL, stderr=subprocess.PIPE, text=True)
                    except Exception as effect_error:
                        print(f"Voice effect unavailable (install sox): {effect_error}")
                        final = raw_file
                else:
                    final = raw_file

            if player is None:
                print("No audio player found (need pw-play, paplay or aplay).")
            else:
                play_proc = subprocess.Popen(player + [final])
                play_proc.wait()

        except Exception as e:
            print(f"JARVIS speech error: {e}")
        finally:
            time.sleep(0.3)  # short pause so the mic does not hear the tail of the voice
            last_speech_end = time.time()
            with state_lock:
                system_status = "PROCESSING"
            if speak_queue.qsize() == 0:
                speaking_event.clear()
            if session_active:
                extend_awake(FOLLOWUP_SECONDS)
            speak_queue.task_done()


threading.Thread(target=tts_worker, daemon=True).start()


def add_message(user_msg=None, jarvis_msg=None, speak=True):
    global last_reply
    global message_id_counter

    with state_lock:
        message_id_counter += 1
        item = {"id": message_id_counter}

        if user_msg:
            item["user"] = user_msg

        if jarvis_msg:
            item["jarvis"] = jarvis_msg
            last_reply = jarvis_msg
            if speak and speak_enabled:
                speaking_event.set()
                recent_replies.append((time.time(), jarvis_msg.lower().strip(" .!?,")))
                del recent_replies[:-5]
                tts_pending.set()
                speak_queue.put(jarvis_msg)

        messages.append(item)
        del messages[:-200]
        save_history()


# =====================================================================
# SMALL HELPERS
# =====================================================================
def press_key(vk_code, count=1):  # Windows only
    for _ in range(count):
        ctypes.windll.user32.keybd_event(vk_code, 0, 0, 0)
        time.sleep(0.05)
        ctypes.windll.user32.keybd_event(vk_code, 0, 2, 0)
        time.sleep(0.05)


def has_word(pattern, text):
    return re.search(r'\b(?:' + pattern + r')\b', text) is not None


def run_ok(cmd, timeout=15):
    try:
        return subprocess.run(cmd, capture_output=True, text=True, timeout=timeout).returncode == 0
    except Exception:
        return False


def run_out(cmd, timeout=5):
    try:
        r = subprocess.run(cmd, capture_output=True, text=True, timeout=timeout)
        return r.stdout.strip() if r.returncode == 0 else ""
    except Exception:
        return ""


def onoff(t):
    if has_word("off|disable|disconnect", t):
        return False
    if has_word("on|enable|connect", t):
        return True
    return None


def ask_confirm(prompt, action):
    """Store a dangerous action; it only runs if the next reply is 'yes'."""
    global pending_confirm
    pending_confirm = {"action": action, "expires": time.time() + 20}
    return prompt + " Say yes or no."


def load_custom_commands():
    try:
        with open(COMMANDS_FILE, "r", encoding="utf-8") as f:
            data = json.load(f)
        return data if isinstance(data, dict) else {}
    except Exception:
        return {}


NUM_WORDS = {
    "forty five": 45, "one": 1, "two": 2, "three": 3, "four": 4, "five": 5,
    "six": 6, "seven": 7, "eight": 8, "nine": 9, "ten": 10, "fifteen": 15,
    "twenty": 20, "thirty": 30, "sixty": 60,
}


def normalize_numbers(t):
    t = re.sub(r'\bhalf an hour\b', '30 minutes', t)
    t = re.sub(r'\b(?:an|a)\s+(hour|minute|second)\b', r'1 \1', t)
    for word, num in NUM_WORDS.items():
        t = re.sub(rf'\b{word}\b', str(num), t)
    return t


UNIT_SECONDS = {"s": 1, "m": 60, "h": 3600}


def set_timer(amount, unit, label=None):
    seconds = amount * UNIT_SECONDS[unit[0]]
    unit_name = {"s": "second", "m": "minute", "h": "hour"}[unit[0]]
    if label:
        message = f"Reminder: {label}."
    else:
        message = f"Your {amount} {unit_name} timer is finished."
    t = threading.Timer(seconds, lambda: add_message(jarvis_msg=message))
    t.daemon = True
    t.start()
    active_timers.append(t)
    plural = "s" if amount != 1 else ""
    return f"Okay. {'Reminder' if label else 'Timer'} set for {amount} {unit_name}{plural}."


# =====================================================================
# WEATHER / NEWS / NETWORK
# =====================================================================
def weather_text(code):
    if code == 0:
        return "clear sky"
    if code in (1, 2, 3):
        return "partly cloudy"
    if code in (45, 48):
        return "foggy"
    if 51 <= code <= 57:
        return "drizzle"
    if 61 <= code <= 67 or 80 <= code <= 82:
        return "rainy"
    if 71 <= code <= 77 or code in (85, 86):
        return "snowy"
    if code >= 95:
        return "thunderstorms"
    return "mixed conditions"


def get_weather(city):
    try:
        g = requests.get(
            "https://geocoding-api.open-meteo.com/v1/search",
            params={"name": city, "count": 1}, timeout=8
        ).json()
        if not g.get("results"):
            return f"I could not find a city called {city}."
        place = g["results"][0]
        w = requests.get(
            "https://api.open-meteo.com/v1/forecast",
            params={
                "latitude": place["latitude"],
                "longitude": place["longitude"],
                "current": "temperature_2m,apparent_temperature,weather_code,wind_speed_10m",
            },
            timeout=8
        ).json()["current"]
        return (f"In {place['name']} it is {round(w['temperature_2m'])} degrees Celsius, "
                f"feels like {round(w['apparent_temperature'])}, "
                f"{weather_text(w['weather_code'])}, wind {round(w['wind_speed_10m'])} kilometers per hour.")
    except Exception:
        return "I could not get the weather. Check your internet connection."


def get_news():
    try:
        r = requests.get("https://feeds.bbci.co.uk/news/rss.xml", timeout=8)
        root = ET.fromstring(r.content)
        titles = [i.findtext("title") for i in root.iter("item")][:5]
        titles = [t for t in titles if t]
        if not titles:
            return "I could not find any headlines."
        return "Top headlines. " + ". ".join(titles) + "."
    except Exception:
        return "I could not get the news. Check your internet connection."


def local_ip():
    s = socket.socket(socket.AF_INET, socket.SOCK_DGRAM)
    try:
        s.connect(("8.8.8.8", 80))
        return s.getsockname()[0]
    except Exception:
        return None
    finally:
        s.close()


def ip_info():
    local = local_ip()
    try:
        public = requests.get("https://api.ipify.org", timeout=5).text.strip()
    except Exception:
        public = None
    parts = []
    if local:
        parts.append(f"Your local address is {local}")
    if public:
        parts.append(f"your public address is {public}")
    return (". ".join(parts) + ".") if parts else "I could not find your network address."


def is_online():
    try:
        requests.get("https://www.google.com/generate_204", timeout=4)
        return True
    except Exception:
        return False


def battery_info():
    bat = psutil.sensors_battery() if hasattr(psutil, "sensors_battery") else None
    if bat is None:
        return "I could not find a battery on this machine."
    state = "charging" if bat.power_plugged else "not charging"
    return f"Battery is at {round(bat.percent)} percent and {state}."


def disk_info():
    d = shutil.disk_usage("/")
    free_gb = d.free / (1024 ** 3)
    pct = d.used / d.total * 100
    return f"Main disk is {round(pct)} percent full with {free_gb:.0f} gigabytes free."


# =====================================================================
# LINUX TOOLS: screenshot, clipboard, typing, windows, phone
# =====================================================================
def take_screenshot():
    pics = os.path.expanduser("~/Pictures")
    os.makedirs(pics, exist_ok=True)
    path = os.path.join(pics, "jarvis-" + datetime.datetime.now().strftime("%Y%m%d-%H%M%S") + ".png")
    for cmd in (["gnome-screenshot", "-f", path], ["grim", path],
                ["spectacle", "-b", "-n", "-o", path]):
        if shutil.which(cmd[0]) and run_ok(cmd) and os.path.exists(path):
            return "Screenshot saved to your Pictures folder."
    return "I could not take a screenshot. Install gnome-screenshot first."


def read_clipboard():
    if shutil.which("wl-paste"):
        content = run_out(["wl-paste", "--no-newline"])
    elif shutil.which("xclip"):
        content = run_out(["xclip", "-o", "-selection", "clipboard"])
    else:
        return "Clipboard reading needs wl-clipboard. Install it first."
    content = " ".join(content.split())
    if not content:
        return "Your clipboard is empty."
    if len(content) > 300:
        content = content[:300] + "..."
    return f"Your clipboard says: {content}"


def type_text(content):
    if shutil.which("ydotool"):
        ok = run_ok(["ydotool", "type", "--", content])
    elif shutil.which("wtype"):
        ok = run_ok(["wtype", content])
    elif shutil.which("xdotool"):
        ok = run_ok(["xdotool", "type", "--delay", "20", content])
    else:
        return "Voice typing needs ydotool, wtype or xdotool. Install one first."
    return "Typing." if ok else "I could not type that."


def send_combo(xname, codes):
    if shutil.which("ydotool"):
        seq = [f"{c}:1" for c in codes] + [f"{c}:0" for c in reversed(codes)]
        return run_ok(["ydotool", "key"] + seq)
    if shutil.which("xdotool"):
        return run_ok(["xdotool", "key", xname])
    return False


WINDOW_ACTIONS = {
    "minimize": ("super+h", [125, 35], "Minimizing the window."),
    "maximize": ("super+Up", [125, 103], "Maximizing the window."),
    "switch": ("alt+Tab", [56, 15], "Switching windows."),
    "fullscreen": ("F11", [87], "Toggling fullscreen."),
}


def kde_device():
    if not shutil.which("kdeconnect-cli"):
        return None
    ids = run_out(["kdeconnect-cli", "-a", "--id-only"]).split()
    return ids[0] if ids else None


# =====================================================================
# AI BRAIN (Ollama first, then Claude API)
# =====================================================================
CHIME_FILE = "/usr/share/sounds/freedesktop/stereo/message.oga"


def wake_ack():
    """Instant feedback when 'Hey Jarvis' is heard."""
    if WAKE_REPLY == "chime" and os.path.exists(CHIME_FILE) and shutil.which("pw-play"):
        subprocess.Popen(["pw-play", CHIME_FILE],
                         stdout=subprocess.DEVNULL, stderr=subprocess.DEVNULL)
    else:
        add_message(jarvis_msg="Yes?")


TOOLS_NEEDED = [
    ("wpctl", "wireplumber", "volume"),
    ("brightnessctl", "brightnessctl", "brightness"),
    ("playerctl", "playerctl", "media keys and now playing"),
    ("nmcli", "NetworkManager", "Wi-Fi"),
    ("bluetoothctl", "bluez", "Bluetooth"),
    ("gnome-screenshot", "gnome-screenshot", "screenshots"),
    ("wl-paste", "wl-clipboard", "clipboard reading"),
    ("ydotool", "ydotool", "voice typing and window control"),
    ("kdeconnect-cli", "kdeconnectd", "phone link"),
    ("sox", "sox", "the evil voice effect"),
    ("pw-play", "pipewire-utils", "audio playback"),
    ("xdg-open", "xdg-utils", "opening folders"),
    ("gio", "glib2", "moving files to the trash"),
]


def run_diagnostics():
    """Checks every dependency. Prints a full report to the terminal."""
    import importlib.util
    report, missing_feats, missing_pkgs = [], [], []

    for tool, pkg, feat in TOOLS_NEEDED:
        if shutil.which(tool):
            report.append(f"  OK       {tool}")
        else:
            report.append(f"  MISSING  {tool}  ({feat})  ->  sudo dnf install {pkg}")
            missing_feats.append(feat)
            missing_pkgs.append(pkg)

    for mod, hint in (("piper", "pip install piper-tts"), ("faster_whisper", "pip install faster-whisper (best offline mic)"),
                      ("numpy", "pip install numpy"), ("vosk", "pip install vosk (optional, offline mic)")):
        if importlib.util.find_spec(mod):
            report.append(f"  OK       python module {mod}")
        else:
            report.append(f"  MISSING  python module {mod}  ->  {hint}")

    if importlib.util.find_spec("pyaudio"):
        report.append("  OK       python module pyaudio (mic is tested when you turn it on)")
    else:
        report.append("  MISSING  python module pyaudio  ->  pip install pyaudio (needs portaudio-devel)")

    # FIX: also check the piper voice model and the backup voice
    piper_model = os.path.expanduser("~/piper-voices/en_US-ryan-high.onnx")
    if os.path.exists(piper_model):
        report.append("  OK       piper voice model")
    else:
        report.append(f"  MISSING  piper voice model  ->  {piper_model}")
    if shutil.which("espeak-ng") or shutil.which("espeak"):
        report.append("  OK       backup voice (espeak)")
    else:
        report.append("  MISSING  backup voice espeak-ng  ->  sudo dnf install espeak-ng")

    try:
        requests.get(OLLAMA_URL, timeout=1)
        report.append("  OK       Ollama AI is running")
    except Exception:
        if ANTHROPIC_KEY:
            report.append("  OK       Claude API key is set")
        else:
            report.append("  MISSING  AI brain: start Ollama or set ANTHROPIC_API_KEY")

    print("JARVIS DIAGNOSTICS\n" + "\n".join(report))
    if missing_pkgs:
        print("\nInstall all missing system tools:\n  sudo dnf install " + " ".join(sorted(set(missing_pkgs))))

    if not missing_feats:
        return "Diagnostics complete. All system tools are installed."
    return ("Diagnostics complete. Missing tools for: " + ", ".join(missing_feats)
            + ". Full install command is printed in the terminal.")


AI_SYSTEM = ("You are JARVIS, a concise voice assistant. Answer in one to three short "
             "spoken sentences. No markdown, no lists, no emojis.")


def ai_system():
    """Base prompt plus the personality of the current transform mode."""
    return AI_SYSTEM + ((" " + current_persona) if current_persona else "")


def _llm_once(system, user, max_tokens=60, timeout=8):
    """One quick stateless call to the AI brain (Ollama first, then Claude API). Returns text or None."""
    try:
        r = requests.post(
            OLLAMA_URL + "/api/chat",
            json={
                "model": OLLAMA_MODEL,
                "stream": False,
                "options": {"num_predict": max_tokens, "temperature": 0},
                "messages": [{"role": "system", "content": system},
                             {"role": "user", "content": user}],
            },
            timeout=timeout
        )
        if r.ok:
            out = r.json()["message"]["content"].strip()
            if out:
                return out
    except Exception:
        pass

    if ANTHROPIC_KEY:
        try:
            r = requests.post(
                "https://api.anthropic.com/v1/messages",
                headers={
                    "x-api-key": ANTHROPIC_KEY,
                    "anthropic-version": "2023-06-01",
                    "content-type": "application/json",
                },
                json={
                    "model": ANTHROPIC_MODEL,
                    "max_tokens": max_tokens,
                    "system": system,
                    "messages": [{"role": "user", "content": user}],
                },
                timeout=timeout
            )
            if r.ok:
                out = r.json()["content"][0]["text"].strip()
                if out:
                    return out
        except Exception:
            pass
    return None


def ask_ai(question):
    history = list(ai_history)
    reply = None

    try:
        r = requests.post(
            OLLAMA_URL + "/api/chat",
            json={
                "model": OLLAMA_MODEL,
                "stream": False,
                "options": {"num_predict": 120},
                "messages": [{"role": "system", "content": ai_system()}]
                            + history + [{"role": "user", "content": question}],
            },
            timeout=25
        )
        if r.ok:
            reply = r.json()["message"]["content"].strip()
    except Exception:
        pass

    if not reply and ANTHROPIC_KEY:
        try:
            r = requests.post(
                "https://api.anthropic.com/v1/messages",
                headers={
                    "x-api-key": ANTHROPIC_KEY,
                    "anthropic-version": "2023-06-01",
                    "content-type": "application/json",
                },
                json={
                    "model": ANTHROPIC_MODEL,
                    "max_tokens": 150,
                    "system": ai_system(),
                    "messages": history + [{"role": "user", "content": question}],
                },
                timeout=15
            )
            if r.ok:
                reply = r.json()["content"][0]["text"].strip()
        except Exception:
            pass

    if not reply:
        return None

    reply = re.sub(r'[*#`_]+', '', reply)
    ai_history.append({"role": "user", "content": question})
    ai_history.append({"role": "assistant", "content": reply})
    return reply


# =====================================================================
# COMMAND ENGINE
# =====================================================================
# =====================================================================
# PASSWORD LOCK (say it or type it), TRANSFORM MODES, SAFE FILE COMMANDS, MATH
# =====================================================================
_PW_NUMS = {"zero": "0", "one": "1", "two": "2", "three": "3", "four": "4",
            "five": "5", "six": "6", "seven": "7", "eight": "8", "nine": "9", "ten": "10"}
_PW_NUM_RE = re.compile(r"\b(" + "|".join(_PW_NUMS) + r")\b")
_SETPW_RE = re.compile(
    r"^\W*(?:jarvis\W+)?(?:set|change|new|update)\s+(?:my\s+|the\s+|a\s+)?(?:jarvis\s+)?(?:password|passphrase)\b",
    re.I)
_PW_PREFIX_RE = re.compile(
    r"^\W*(?:(?:hey\s+)?jarvis\W+)?(?:unlock(?:\s+(?:the\s+)?(?:screen|pc|computer|jarvis|it))?\W*"
    r"|(?:the\s+|my\s+)?password\s+(?:is\s+)?|it\s+is\s+|it's\s+|its\s+)", re.I)
_UNLOCK_WORDS = {"", "unlock", "open", "unlock screen", "unlock the screen", "unlock jarvis", "unlock it",
                 "open it", "open the screen", "wake up", "wake", "hello", "hey", "jarvis", "hey jarvis"}


def normalize_pw(s):
    """Same result whether you SAY the password or TYPE it: lowercase, number words -> digits, no spaces."""
    s = _PW_NUM_RE.sub(lambda m: _PW_NUMS[m.group(1)], str(s).lower())
    return re.sub(r"[\s.,!?'\"]+", "", s)


def _pw_hash(pw, salt, iterations=200000):
    return hashlib.pbkdf2_hmac("sha256", normalize_pw(pw).encode("utf-8"), salt, iterations).hex()


def password_is_set():
    return os.path.exists(LOCK_FILE)


def save_password(pw):
    salt = os.urandom(16)
    data = {"salt": salt.hex(), "iterations": 200000, "hash": _pw_hash(pw, salt)}
    fd = os.open(LOCK_FILE, os.O_WRONLY | os.O_CREAT | os.O_TRUNC, 0o600)   # only you can read it
    with os.fdopen(fd, "w", encoding="utf-8") as f:
        json.dump(data, f)


def check_password(pw):
    try:
        with open(LOCK_FILE, "r", encoding="utf-8") as f:
            d = json.load(f)
        salt = bytes.fromhex(d["salt"])
        return hmac.compare_digest(_pw_hash(pw, salt, int(d.get("iterations", 200000))), d["hash"])
    except Exception:
        return False

def sync_code_password():
    """Make the saved password always match JARVIS_PASSWORD from the code."""
    if not JARVIS_PASSWORD:
        return
    try:
        if not password_is_set() or not check_password(JARVIS_PASSWORD):
            save_password(JARVIS_PASSWORD)
            print("[lock] password saved from code")
    except Exception as e:
        print(f"[lock] could not save password: {e}")


sync_code_password()


def redact_for_log(text):
    """Never write a password into the chat history or the terminal."""
    if jarvis_locked or awaiting_password or _SETPW_RE.match(text or ""):
        return "******"
    return text


def do_lock_screen():
    """Locks the system screen. If a password is set, Jarvis locks too and only the password opens it."""
    global jarvis_locked, lock_fails
    try:
        if IS_LINUX:
            subprocess.Popen(["loginctl", "lock-session"])
        elif IS_WIN:
            os.system("rundll32.exe user32.dll,LockWorkStation")
    except Exception as e:
        print(f"Screen lock failed: {e}")
        return "I could not lock the screen."
    if LOCK_JARVIS_WITH_SCREEN and password_is_set():
        jarvis_locked = True
        lock_fails = 0
        save_state()
        return "Screen locked. Say or type the password to unlock."
    return "Locking the screen. Set a password first if you want me to unlock it for you."


def lock_jarvis():
    global jarvis_locked, lock_fails
    if not password_is_set():
        return "Set a password first. Type: set password, then your password."
    jarvis_locked = True
    lock_fails = 0
    save_state()
    return "Jarvis is locked. Say or type the password to unlock."


def handle_locked_input(raw_text):
    """While locked, EVERY input (voice or typed) is treated as a password attempt."""
    global jarvis_locked, lock_fails, lock_until
    now = time.time()
    if now < lock_until:
        return f"Too many wrong tries. Wait {int(lock_until - now) + 1} seconds."

    cand = str(raw_text).strip()
    stripped = cand
    for _ in range(2):                                  # drop filler like "unlock" or "the password is"
        stripped = _PW_PREFIX_RE.sub("", stripped, count=1).strip()

    if check_password(cand) or (stripped and check_password(stripped)):
        jarvis_locked = False
        lock_fails = 0
        save_state()
        if UNLOCK_OS_ON_PASSWORD and IS_LINUX:
            sid = os.environ.get("XDG_SESSION_ID")
            if run_ok(["loginctl", "unlock-session"] + ([sid] if sid else [])):
                return "Password accepted. Welcome back. Screen unlocked."
            return ("Password accepted and Jarvis is unlocked, but I could not unlock the system screen. "
                    "Use your normal login password.")
        return "Password accepted. Welcome back."

    plain = re.sub(r"\W+", " ", cand.lower()).strip()
    if not stripped or plain in _UNLOCK_WORDS:         # they only asked to unlock: ask for the password
        return "Jarvis is locked. Say or type the password to unlock."

    lock_fails += 1
    if lock_fails >= MAX_PASSWORD_TRIES:
        lock_fails = 0
        lock_until = now + LOCKOUT_SECONDS
        return f"Wrong password. Locked out for {LOCKOUT_SECONDS} seconds."
    return "Wrong password."


# ---------------- transform modes (~/.jarvis/modes.json) ----------------
DEFAULT_MODES = {
    "jarvis": {"voice": VOICE, "persona": "", "message": "Back to my original self."},
    "normal": {"voice": "normal", "persona": "", "message": "Normal mode."},
    "evil": {"voice": "evil",
             "persona": "Speak like a dark, sarcastic villain AI, but still answer correctly and briefly.",
             "message": "Evil mode engaged. Fear me."},
    "friday": {"voice": "friday",
               "persona": "Speak warmly and playfully, like a friendly helpful assistant.",
               "message": "Friday online. How can I help?"},
    "hacker": {"voice": "hacker",
               "persona": "Speak in very short, cold, technical hacker style.",
               "message": "Hacker mode active. Terminal ready."},
    "robot": {"voice": "robot",
              "persona": "Speak like a literal robot: short, formal, no emotion.",
              "message": "Robot mode. Beep boop. Ready."},
}
_MODE_BACK_WORDS = {"back", "original", "default", "yourself back", "back to normal", "back to yourself"}

if not os.path.exists(MODES_FILE):
    try:
        with open(MODES_FILE, "w", encoding="utf-8") as f:
            json.dump(DEFAULT_MODES, f, indent=2)
    except Exception:
        pass


def load_modes():
    try:
        with open(MODES_FILE, "r", encoding="utf-8") as f:
            data = json.load(f)
        if isinstance(data, dict) and data:
            return {str(k).lower(): v for k, v in data.items() if isinstance(v, dict)}
    except Exception:
        pass
    return DEFAULT_MODES


def transform_to(name):
    global current_mode, current_persona
    mode = load_modes().get(name)
    if not isinstance(mode, dict):
        return None
    voice_name = str(mode.get("voice", "normal"))
    set_voice(voice_name if voice_name in VOICE_PROFILES else "normal")
    current_mode = name
    current_persona = str(mode.get("persona", ""))
    ai_history.clear()
    save_state()
    return str(mode.get("message") or f"{name.title()} mode activated.")


def save_state():
    """Remember how you left Jarvis, so it opens the same way next time."""
    try:
        with open(STATE_FILE, "w", encoding="utf-8") as f:
            json.dump({"mode": current_mode, "voice": current_voice, "locked": bool(jarvis_locked),
                       "ui": ui_prefs, "speak_enabled": speak_enabled, "mic": bool(mic_active)}, f)
    except Exception:
        pass


def load_state():
    global current_mode, current_persona, current_voice, jarvis_locked, speak_enabled, mic_active
    try:
        with open(STATE_FILE, "r", encoding="utf-8") as f:
            d = json.load(f)
    except Exception:
        return
    if not isinstance(d, dict):
        return
    if d.get("voice") in VOICE_PROFILES:
        current_voice = d["voice"]
    name = str(d.get("mode", "")).lower()
    mode = load_modes().get(name)
    if isinstance(mode, dict):
        current_mode = name
        current_persona = str(mode.get("persona", ""))
    ui = d.get("ui")
    if isinstance(ui, dict):
        ui_prefs.update({str(k): v for k, v in list(ui.items())[:60]})
    if d.get("speak_enabled") is False:
        speak_enabled = False
    if d.get("mic") and RESTORE_MIC:
        mic_active = True
    # A restart must NOT unlock Jarvis: if it was locked, it stays locked (needs a password to exist).
    if d.get("locked") and password_is_set():
        jarvis_locked = True


load_state()


# ---------------- safe file commands ----------------
HOME = os.path.expanduser("~")
SAFE_FOLDERS = {
    "desktop": os.path.join(HOME, "Desktop"),
    "documents": os.path.join(HOME, "Documents"),
    "downloads": os.path.join(HOME, "Downloads"),
}
_FOLDER_END_RE = re.compile(
    r"\s+(?:in|on|inside|from|to)\s+(?:my\s+|the\s+)?(desktop|documents|downloads)(?:\s+folder)?\s*$", re.I)


def _folder_from_text(s):
    """'notes.txt in documents' -> ('notes.txt', 'documents')"""
    m = _FOLDER_END_RE.search(s)
    if m:
        return s[:m.start()].strip(), m.group(1).lower()
    return s.strip(), None


def _clean_filename(raw, default_ext=None):
    s = str(raw).strip().lower().strip(" .,!?\"'")
    s = re.sub(r"\s+(?:dot|point)\s+", ".", s)
    s = re.sub(r"\s+", "_", s)
    s = re.sub(r"[^a-z0-9._-]", "", s)
    if not s or s.startswith(".") or ".." in s:
        return None
    if default_ext and "." not in s:
        s += default_ext
    return s


def _norm_key(s):
    s = re.sub(r"\s+(?:dot|point)\s+", ".", str(s).lower())
    return re.sub(r"[^a-z0-9.]", "", s)


def _label(path):
    return os.path.basename(os.path.dirname(path)) or "that folder"


def _inside_safe(path):
    real = os.path.realpath(path)
    for root in SAFE_FOLDERS.values():
        r = os.path.realpath(root)
        if real == r or real.startswith(r + os.sep):
            return True
    return False


def _matches(query, folder_key=None):
    """(score, path) for files in the safe folders, best first. Score 1.0 = exact name (extension optional)."""
    roots = [SAFE_FOLDERS[folder_key]] if folder_key else list(SAFE_FOLDERS.values())
    qk = _norm_key(query)
    out = []
    if not qk:
        return out
    for root in roots:
        try:
            names = os.listdir(root)
        except OSError:
            continue
        for n in names:
            if n.startswith("."):
                continue
            nk = _norm_key(n)
            sk = _norm_key(os.path.splitext(n)[0])
            if qk in (nk, sk):
                score = 1.0
            else:
                score = max(difflib.SequenceMatcher(None, qk, nk).ratio(),
                            difflib.SequenceMatcher(None, qk, sk).ratio())
            out.append((score, os.path.join(root, n)))
    out.sort(key=lambda c: -c[0])
    return out


def _find_one(query, folder_key=None, fuzzy=False):
    """-> (path, problem). Destructive commands use exact names only (fuzzy=False)."""
    ms = _matches(query, folder_key)
    exact = [p for s, p in ms if s >= 0.999]
    if len(exact) == 1:
        return exact[0], None
    if len(exact) > 1:
        return None, "More than one file has that name. Say the full name with the extension, or the folder."
    if fuzzy and ms and ms[0][0] >= 0.8:
        return ms[0][1], None
    return None, f"I could not find {str(query).strip()}."


def fs_create_file(name_raw, content, folder_key):
    name = _clean_filename(name_raw, ".txt")
    if not name:
        return "I did not catch a valid file name."
    folder = SAFE_FOLDERS[folder_key or "desktop"]
    os.makedirs(folder, exist_ok=True)
    path = os.path.join(folder, name)
    if os.path.exists(path):
        return f"{name} already exists in {_label(path)}."
    with open(path, "w", encoding="utf-8") as f:
        f.write((content.strip() + "\n") if content and content.strip() else "")
    return f"Created {name} in {_label(path)}."


def fs_create_folder(name_raw, folder_key):
    name = _clean_filename(name_raw)
    if not name:
        return "I did not catch a valid folder name."
    folder = SAFE_FOLDERS[folder_key or "desktop"]
    path = os.path.join(folder, name)
    if os.path.exists(path):
        return f"{name} already exists in {_label(path)}."
    os.makedirs(path)
    return f"Created folder {name} in {_label(path)}."


def fs_read(name_raw, folder_key):
    path, problem = _find_one(name_raw, folder_key, fuzzy=True)
    if not path:
        return problem
    if not os.path.isfile(path) or not _inside_safe(path):
        return "I can only read normal files inside Desktop, Documents and Downloads."
    if os.path.getsize(path) > 1_000_000:
        return "That file is too big to read out."
    with open(path, "rb") as f:
        raw = f.read(4000)
    if b"\x00" in raw:
        return "That does not look like a text file."
    content = " ".join(raw.decode("utf-8", errors="replace").split())
    if not content:
        return f"{os.path.basename(path)} is empty."
    if len(content) > 600:
        content = content[:600] + "..."
    return f"{os.path.basename(path)} says: {content}"


def fs_list(folder_key):
    folder = SAFE_FOLDERS[folder_key or "desktop"]
    try:
        names = [n for n in os.listdir(folder) if not n.startswith(".")]
    except OSError:
        return f"I could not open {os.path.basename(folder)}."
    if not names:
        return f"{os.path.basename(folder)} is empty."
    names.sort(key=lambda n: os.path.getmtime(os.path.join(folder, n)), reverse=True)
    return (f"{os.path.basename(folder)} has {len(names)} items. Newest: "
            + ", ".join(names[:8]) + ("." if len(names) <= 8 else ", and more."))


def fs_find(query):
    qk = _norm_key(query)
    if not qk:
        return "What file should I look for?"
    hits = []
    for root in SAFE_FOLDERS.values():
        base_depth = root.rstrip(os.sep).count(os.sep)
        for dirpath, dirnames, filenames in os.walk(root):
            dirnames[:] = [d for d in dirnames if not d.startswith(".")]
            if dirpath.count(os.sep) - base_depth >= 3:
                dirnames[:] = []
            for n in filenames:
                if not n.startswith(".") and qk in _norm_key(n):
                    hits.append(os.path.join(dirpath, n))
            if len(hits) >= 5:
                break
        if len(hits) >= 5:
            break
    if not hits:
        return f"I could not find a file called {str(query).strip()}."
    parts = [f"{os.path.basename(p)} in {_label(p)}" for p in hits[:5]]
    return f"I found {'one file' if len(hits) == 1 else str(len(hits)) + ' files'}. " + ". ".join(parts) + "."


def move_to_trash(path):
    """System trash if possible (you can restore it), otherwise ~/.jarvis/trash. Never a permanent delete."""
    if shutil.which("gio") and run_ok(["gio", "trash", path]):
        return
    os.makedirs(TRASH_DIR, exist_ok=True)
    stamp = datetime.datetime.now().strftime("%Y%m%d-%H%M%S-")
    shutil.move(path, os.path.join(TRASH_DIR, stamp + os.path.basename(path)))


def fs_delete(name_raw, folder_key):
    path, problem = _find_one(name_raw, folder_key, fuzzy=False)
    if not path:
        return problem
    shown, where = os.path.basename(path), _label(path)

    def do_trash(p=path, n=shown):
        try:
            move_to_trash(p)
            return f"Moved {n} to the trash."
        except Exception as e:
            print(f"Trash error: {e}")
            return "I could not move that to the trash."

    return ask_confirm(f"Do you want to move {shown} from {where} to the trash?", do_trash)


def fs_rename(src_raw, dst_raw):
    dst_raw, folder_key = _folder_from_text(dst_raw)
    path, problem = _find_one(src_raw, folder_key, fuzzy=False)
    if not path:
        return problem
    new = _clean_filename(dst_raw)
    if not new:
        return "I did not catch the new name."
    if "." not in new and os.path.isfile(path) and os.path.splitext(path)[1]:
        new += os.path.splitext(path)[1]
    dest = os.path.join(os.path.dirname(path), new)
    if os.path.exists(dest):
        return f"{new} already exists in {_label(dest)}."
    os.rename(path, dest)
    return f"Renamed {os.path.basename(path)} to {new}."


def fs_move_copy(verb, src_raw, src_folder, dst_folder):
    path, problem = _find_one(src_raw, src_folder, fuzzy=False)
    if not path:
        return problem
    dest_dir = SAFE_FOLDERS[dst_folder]
    if os.path.realpath(os.path.dirname(path)) == os.path.realpath(dest_dir):
        return f"{os.path.basename(path)} is already in {os.path.basename(dest_dir)}."
    dest = os.path.join(dest_dir, os.path.basename(path))
    if os.path.exists(dest):
        return f"{os.path.basename(path)} already exists in {os.path.basename(dest_dir)}."
    os.makedirs(dest_dir, exist_ok=True)
    if verb == "move":
        shutil.move(path, dest)
        return f"Moved {os.path.basename(path)} to {os.path.basename(dest_dir)}."
    if os.path.isdir(path):
        shutil.copytree(path, dest)
    else:
        shutil.copy2(path, dest)
    return f"Copied {os.path.basename(path)} to {os.path.basename(dest_dir)}."


def fs_open(name_raw, folder_key):
    path, problem = _find_one(name_raw, folder_key, fuzzy=True)
    if not path:
        return problem
    if not _inside_safe(path):
        return "I can only open files inside Desktop, Documents and Downloads."
    if IS_WIN:
        os.startfile(path)
    else:
        subprocess.Popen(["xdg-open", path], stdout=subprocess.DEVNULL, stderr=subprocess.DEVNULL)
    return f"Opening {os.path.basename(path)}."


# ---------------- voice math ----------------
def _fmt_num(x):
    if isinstance(x, float) and not math.isfinite(x):
        raise ValueError("not finite")
    if float(x) == int(x) and abs(x) < 1e15:
        return str(int(x))
    return f"{x:.6f}".rstrip("0").rstrip(".")


_MATH_OPS = {ast.Add: lambda a, b: a + b, ast.Sub: lambda a, b: a - b, ast.Mult: lambda a, b: a * b,
             ast.Div: lambda a, b: a / b, ast.Mod: lambda a, b: a % b, ast.Pow: lambda a, b: a ** b}


def _safe_eval(expr):
    """Numbers and + - * / % ** () only. Nothing else can run."""
    def ev(n):
        if isinstance(n, ast.Expression):
            return ev(n.body)
        if isinstance(n, ast.Constant) and isinstance(n.value, (int, float)) and not isinstance(n.value, bool):
            return n.value
        if isinstance(n, ast.UnaryOp) and isinstance(n.op, (ast.USub, ast.UAdd)):
            v = ev(n.operand)
            return -v if isinstance(n.op, ast.USub) else v
        if isinstance(n, ast.BinOp) and type(n.op) in _MATH_OPS:
            left, right = ev(n.left), ev(n.right)
            if isinstance(n.op, ast.Pow) and (abs(right) > 100 or abs(left) > 1e9):
                raise OverflowError("too big")
            return _MATH_OPS[type(n.op)](left, right)
        raise ValueError("not allowed")
    return ev(ast.parse(expr, mode="eval"))


def try_math(text):
    """'what is 25 times 4' -> 'The answer is 100.'   Returns None when it is not a math sentence."""
    t = normalize_numbers(str(text).lower())
    t = re.sub(r"[?,]", "", t).strip()
    t = re.sub(r"^(?:what(?:'s| is)|whats|calculate|compute|solve|work out|how much is)\s+", "", t).strip()
    if not t or len(t) > 80:
        return None
    try:
        m = re.fullmatch(r"(?:the\s+)?square root of (\d+(?:\.\d+)?)", t)
        if m:
            n = float(m.group(1))
            return f"The square root of {_fmt_num(n)} is {_fmt_num(math.sqrt(n))}."
        m = re.fullmatch(r"(\d+(?:\.\d+)?)\s*(?:percent|%)\s+of\s+(\d+(?:\.\d+)?)", t)
        if m:
            return f"{m.group(1)} percent of {m.group(2)} is {_fmt_num(float(m.group(1)) * float(m.group(2)) / 100)}."
        m = re.fullmatch(r"(\d+(?:\.\d+)?) squared", t)
        if m:
            n = float(m.group(1))
            return f"{_fmt_num(n)} squared is {_fmt_num(n * n)}."

        for pat, op in ((r"\bto the power of\b|\braised to\b|\bpower of\b", "**"),
                        (r"\bmultiplied by\b|\btimes\b", "*"),
                        (r"\bdivided by\b|\bover\b", "/"),
                        (r"\bplus\b", "+"), (r"\bminus\b", "-"),
                        (r"\bmodulo\b|\bmod\b", "%")):
            t = re.sub(pat, f" {op} ", t)
        t = re.sub(r"(?<=\d)\s*x\s*(?=\d)", " * ", t)
        t = t.replace("^", "**").replace("×", "*").replace("÷", "/")
        if not re.fullmatch(r"[\d\s+\-*/().%]+", t) or not re.search(r"\d", t) or not re.search(r"[+\-*/%]", t):
            return None
        return f"The answer is {_fmt_num(_safe_eval(t.strip()))}."
    except ZeroDivisionError:
        return "You cannot divide by zero."
    except OverflowError:
        return "That number is too big for me."
    except Exception:
        return None


# =====================================================================
# EXTRA FEATURES: unlock by voice or text, stop talking, tasks, jokes, stopwatch,
# focus timer, Wikipedia, dictionary, unit converter, system info, daily briefing
# =====================================================================
TASKS_FILE = os.path.join(JARVIS_DIR, "tasks.json")
UI_THEMES = ["red", "blue", "green", "amber", "violet", "white"]   # same as the colour dots in index.html
THEME_ALIASES = {"cyan": "blue", "purple": "violet", "gold": "amber", "yellow": "amber", "orange": "amber",
                 "ice": "white", "silver": "white", "danger": "red"}

JOKES = [
    "Why do programmers prefer dark mode? Because light attracts bugs.",
    "I would tell you a UDP joke, but you might not get it.",
    "There are ten kinds of people. Those who understand binary, and those who do not.",
    "Why did the computer go to the doctor? It had a virus.",
    "A SQL query walks into a bar, walks up to two tables and asks, can I join you?",
    "Why was the laptop cold? It left its Windows open.",
    "How many programmers does it take to change a light bulb? None. That is a hardware problem.",
    "I would tell you a joke about the cloud, but it is over my head.",
]


def stop_speaking():
    """Cuts the voice off immediately and clears everything waiting to be spoken."""
    while True:
        try:
            speak_queue.get_nowait()
            speak_queue.task_done()
        except queue.Empty:
            break
    p = play_proc
    if p is not None and p.poll() is None:
        try:
            p.terminate()
        except Exception:
            pass
    speaking_event.clear()


def handle_unlock_attempt(raw_text):
    """After 'unlock the screen' the NEXT thing you say or type is the password."""
    global awaiting_password, awaiting_until
    plain = re.sub(r"\W+", " ", str(raw_text).lower()).strip()
    if plain in ("cancel", "never mind", "nevermind", "forget it", "stop"):
        awaiting_password = False
        return "Okay, cancelled."
    reply = handle_locked_input(raw_text)
    if reply.startswith("Password accepted"):
        awaiting_password = False
    else:
        awaiting_until = time.time() + 30
    return reply


# ---------------- to do list ----------------
def load_tasks():
    try:
        with open(TASKS_FILE, "r", encoding="utf-8") as f:
            data = json.load(f)
        return [str(t) for t in data] if isinstance(data, list) else []
    except Exception:
        return []


def save_tasks(tasks):
    try:
        with open(TASKS_FILE, "w", encoding="utf-8") as f:
            json.dump(tasks, f, indent=2)
    except Exception as e:
        print(f"Could not save tasks: {e}")


def add_task(text):
    text = text.strip(" .!?,")
    if not text:
        return "What should I add?"
    tasks = load_tasks()
    tasks.append(text)
    save_tasks(tasks)
    return f"Added. You have {len(tasks)} task{'s' if len(tasks) != 1 else ''}."


def read_tasks():
    tasks = load_tasks()
    if not tasks:
        return "Your to do list is empty."
    items = ". ".join(f"{i}, {t}" for i, t in enumerate(tasks, 1))
    return f"You have {len(tasks)} task{'s' if len(tasks) != 1 else ''}. {items}."


# ---------------- unit converter ----------------
_LEN = {"m": 1, "meter": 1, "meters": 1, "metre": 1, "metres": 1,
        "km": 1000, "kilometer": 1000, "kilometers": 1000, "kilometre": 1000, "kilometres": 1000,
        "cm": 0.01, "centimeter": 0.01, "centimeters": 0.01,
        "mile": 1609.344, "miles": 1609.344,
        "foot": 0.3048, "feet": 0.3048, "ft": 0.3048,
        "inch": 0.0254, "inches": 0.0254}
_MASS = {"kg": 1, "kilo": 1, "kilos": 1, "kilogram": 1, "kilograms": 1,
         "g": 0.001, "gram": 0.001, "grams": 0.001,
         "pound": 0.45359237, "pounds": 0.45359237, "lb": 0.45359237, "lbs": 0.45359237,
         "ounce": 0.028349523, "ounces": 0.028349523, "oz": 0.028349523}
_TEMP = {"c": "c", "celsius": "c", "centigrade": "c", "f": "f", "fahrenheit": "f", "k": "k", "kelvin": "k"}


def convert_units(amount, src, dst):
    src, dst = src.lower(), dst.lower()
    for table in (_LEN, _MASS):
        if src in table and dst in table:
            val = amount * table[src] / table[dst]
            return f"{_fmt_num(amount)} {src} is {_fmt_num(round(val, 4))} {dst}."
    if src in _TEMP and dst in _TEMP:
        s, d = _TEMP[src], _TEMP[dst]
        c = amount if s == "c" else ((amount - 32) * 5 / 9 if s == "f" else amount - 273.15)
        out = c if d == "c" else (c * 9 / 5 + 32 if d == "f" else c + 273.15)
        return f"{_fmt_num(amount)} degrees {src} is {_fmt_num(round(out, 2))} degrees {dst}."
    return None


# ---------------- system questions ----------------
def top_processes(by="cpu"):
    ncpu = psutil.cpu_count() or 1
    procs = []
    for p in psutil.process_iter(["name"]):
        try:
            if by == "cpu":
                p.cpu_percent(None)
            procs.append(p)
        except (psutil.NoSuchProcess, psutil.AccessDenied, psutil.ZombieProcess):
            pass
    if by == "cpu":
        time.sleep(0.5)
    totals = {}
    for p in procs:
        try:
            val = (p.cpu_percent(None) / ncpu) if by == "cpu" else p.memory_percent()
            name = p.info.get("name") or p.name()
            totals[name] = totals.get(name, 0.0) + val
        except (psutil.NoSuchProcess, psutil.AccessDenied, psutil.ZombieProcess):
            pass
    ranked = sorted(totals.items(), key=lambda kv: -kv[1])[:3]
    if not ranked:
        return "I could not read the process list."
    what = "CPU" if by == "cpu" else "memory"
    return f"Top {what} users: " + ", ".join(f"{n} at {round(v)} percent" for n, v in ranked) + "."


def cpu_temperature():
    if not hasattr(psutil, "sensors_temperatures"):
        return "Temperature sensors are not supported here."
    try:
        temps = psutil.sensors_temperatures()
    except Exception:
        temps = {}
    for key in ("coretemp", "k10temp", "zenpower", "cpu_thermal", "acpitz"):
        entries = temps.get(key)
        if entries:
            return f"CPU temperature is {round(max(e.current for e in entries))} degrees Celsius."
    return "I could not read a temperature sensor on this machine."


def uptime_text():
    secs = int(time.time() - psutil.boot_time())
    d, rem = divmod(secs, 86400)
    h, rem = divmod(rem, 3600)
    m = rem // 60
    parts = []
    if d:
        parts.append(f"{d} day{'s' if d != 1 else ''}")
    if h:
        parts.append(f"{h} hour{'s' if h != 1 else ''}")
    parts.append(f"{m} minute{'s' if m != 1 else ''}")
    return "Your computer has been on for " + ", ".join(parts) + "."


def wifi_name():
    if not shutil.which("nmcli"):
        return "Wi-Fi info needs NetworkManager."
    out = run_out(["nmcli", "-t", "-f", "active,ssid", "dev", "wifi"])
    for line in out.splitlines():
        if line.startswith("yes:") and line[4:].strip():
            return f"You are connected to {line[4:].strip()}."
    return "You are not connected to a Wi-Fi network."


def volume_level():
    if not shutil.which("wpctl"):
        return "Volume control utility wpctl is missing."
    out = run_out(["wpctl", "get-volume", "@DEFAULT_AUDIO_SINK@"])
    m = re.search(r"([\d.]+)", out)
    if not m:
        return "I could not read the volume."
    pct = round(float(m.group(1)) * 100)
    return f"Volume is at {pct} percent" + (" and muted." if "MUTED" in out else ".")


# ---------------- lookups ----------------
def wiki_summary(topic):
    try:
        r = requests.get(
            "https://en.wikipedia.org/w/api.php",
            params={"action": "query", "generator": "search", "gsrsearch": topic, "gsrlimit": 1,
                    "prop": "extracts", "exintro": 1, "explaintext": 1, "exsentences": 2, "format": "json"},
            headers={"User-Agent": "JarvisAssistant/1.0"}, timeout=8)
        pages = r.json().get("query", {}).get("pages", {})
        for p in pages.values():
            extract = " ".join((p.get("extract") or "").split())
            if extract:
                return f"{p.get('title', topic)}. {extract}"
        return f"I could not find anything on Wikipedia about {topic}."
    except Exception:
        return "I could not reach Wikipedia. Check your internet connection."


def define_word(word):
    """Returns None on any problem, so the AI brain can answer instead."""
    try:
        r = requests.get("https://api.dictionaryapi.dev/api/v2/entries/en/" + urllib.parse.quote(word), timeout=8)
        if not r.ok:
            return None
        meaning = r.json()[0]["meanings"][0]
        return f"{word}, {meaning.get('partOfSpeech', '')}: {meaning['definitions'][0]['definition']}"
    except Exception:
        return None


def daily_briefing():
    now = datetime.datetime.now()
    parts = [f"It is {now.strftime('%I:%M %p')} on {now.strftime('%A, %B %d')}.", get_weather(DEFAULT_CITY)]
    bat = battery_info()
    if "could not find" not in bat:
        parts.append(bat)
    tasks = load_tasks()
    parts.append(f"You have {len(tasks)} task{'s' if len(tasks) != 1 else ''} on your list." if tasks
                 else "Your to do list is empty.")
    return " ".join(parts)


def copy_to_clipboard(content):
    try:
        if shutil.which("wl-copy"):
            subprocess.run(["wl-copy"], input=content, text=True, timeout=5)
            return True
        if shutil.which("xclip"):
            subprocess.run(["xclip", "-selection", "clipboard"], input=content, text=True, timeout=5)
            return True
    except Exception:
        pass
    return False


def handle_extra_features(text, cmd):
    """Returns a reply, or None if the sentence is not one of these commands."""
    global speak_enabled, awaiting_password, awaiting_until, stopwatch_start
    c = cmd.strip(" .!?,")
    cl = normalize_numbers(re.sub(r"wi[\s-]?fi", "wifi", c.lower()))
    cl = re.sub(r"\s+", " ", cl)

    # ---- unlock the screen: say it or type it, the NEXT thing you say/type is the password ----
    if re.fullmatch(r"unlock(?:\s+(?:the|my))?(?:\s+(?:screen|pc|computer|laptop|system|jarvis|it))?", cl):
        if not password_is_set():
            return "No password is set yet. Type: set password, then your password."
        awaiting_password = True
        awaiting_until = time.time() + 30
        return "Tell me the password, or type it."

    # ---- stop talking / voice on and off / say that again / copy that ----
    if re.fullmatch(r"(?:stop (?:talking|speaking)|be quiet|be silent|shut up)", cl):
        stop_speaking()
        return "Okay."
    if re.fullmatch(r"(?:(?:turn|switch) off (?:your )?(?:voice|speech|speaking)|(?:voice|speech|speaking) off"
                    r"|silent mode(?: on)?|mute (?:your )?voice|text only mode)", cl):
        speak_enabled = False
        stop_speaking()
        save_state()
        return "Voice off. I will reply in text only. Say voice on to hear me again."
    if re.fullmatch(r"(?:(?:turn|switch) on (?:your )?(?:voice|speech|speaking)|(?:voice|speech|speaking) on"
                    r"|silent mode off|unmute (?:your )?voice|start talking|speak again)", cl):
        speak_enabled = True
        save_state()
        return "Voice on."
    if re.fullmatch(r"(?:say that again|say it again|what did you say|repeat what you said|come again|pardon(?: me)?)", cl):
        return last_reply or "I have not said anything yet."
    if re.fullmatch(r"(?:copy|clipboard) (?:that|your (?:last )?(?:reply|answer))(?: to (?:the )?clipboard)?", cl):
        if not last_reply:
            return "I have nothing to copy yet."
        return "Copied to the clipboard." if copy_to_clipboard(last_reply) else "Copying needs wl-clipboard or xclip. Install one first."

    # ---- theme (saved, so it is still the same next time) ----
    if re.fullmatch(r"(?:(?:next|another|new|different) theme|(?:change|switch) (?:the |my )?theme)", cl):
        cur = ui_prefs.get("theme")
        nxt = UI_THEMES[(UI_THEMES.index(cur) + 1) % len(UI_THEMES)] if cur in UI_THEMES else UI_THEMES[0]
        ui_prefs["theme"] = nxt
        save_state()
        return f"Theme changed to {nxt}."
    m = (re.fullmatch(r"(?:change|set|switch|make) (?:the |my )?(?:theme|colou?rs?) ?(?:to )?([a-z]+)(?: theme)?", cl)
         or re.fullmatch(r"theme ([a-z]+)", cl)
         or re.fullmatch(r"([a-z]+) theme", cl))
    if m:
        name = THEME_ALIASES.get(m.group(1), m.group(1))
        if name in UI_THEMES:
            ui_prefs["theme"] = name
            save_state()
            return f"Theme changed to {name}."
        return "I know these themes: " + ", ".join(UI_THEMES) + "."

    # ---- to do list ----
    m = re.match(r"^(?:add|new|create)\s+(?:a\s+|an\s+)?(?:task|todo|to-do|to do)\s*(?:to\s+|called\s+|named\s+|that\s+)?(.+)$", c, re.I)
    if not m:
        m = re.match(r"^add\s+(.+?)\s+to\s+(?:my\s+|the\s+)?(?:tasks?|to-?do|to do)(?:\s+list)?$", c, re.I)
    if m:
        return add_task(m.group(1))
    if re.match(r"^(?:read|show|list|check|what are|what is on|what's on|tell me)\b.*\b(?:tasks|task list|to-?do list|to do list)$", cl):
        return read_tasks()
    m = (re.match(r"^(?:done|complete|completed|finish|finished|remove|delete|tick)\s+(?:with\s+)?task\s+(?:number\s+)?(\d+)$", cl)
         or re.match(r"^mark\s+task\s+(?:number\s+)?(\d+)\s+(?:as\s+)?(?:done|complete|completed|finished)$", cl))
    if m:
        tasks = load_tasks()
        i = int(m.group(1)) - 1
        if 0 <= i < len(tasks):
            gone = tasks.pop(i)
            save_tasks(tasks)
            return f"Done. Removed {gone}."
        return f"I do not have a task number {i + 1}."
    if re.match(r"^(?:clear|delete|remove|empty)\s+(?:all\s+|my\s+)?(?:the\s+)?(?:tasks|to-?do list|to do list)$", cl):
        def clear_tasks():
            save_tasks([])
            return "All tasks cleared."
        return ask_confirm("Do you want to clear your whole to do list?", clear_tasks)

    # ---- fun ----
    if len(cl.split()) <= 6 and re.search(r"\b(?:joke|make me laugh)\b", cl):
        return random.choice(JOKES)
    if re.search(r"\b(?:flip|toss)\s+(?:a\s+)?coin\b|\bheads or tails\b", cl):
        return "It is " + random.choice(["heads", "tails"]) + "."
    if re.search(r"\b(?:roll|throw)\s+(?:a\s+|the\s+)?(?:dice|die)\b", cl):
        return f"You rolled a {random.randint(1, 6)}."
    m = re.search(r"\b(?:random number|pick a number)(?:\s+between\s+(\d+)\s+(?:and|to)\s+(\d+))?", cl)
    if m:
        lo, hi = (int(m.group(1)), int(m.group(2))) if m.group(1) else (1, 100)
        if lo > hi:
            lo, hi = hi, lo
        return f"Your number is {random.randint(lo, hi)}."

    # ---- stopwatch and focus timer ----
    if re.search(r"\bstop ?watch\b", cl):
        now = time.time()
        if re.search(r"\b(?:start|begin|reset)\b", cl):
            stopwatch_start = now
            return "Stopwatch started."
        if stopwatch_start is None:
            return "The stopwatch is not running. Say start stopwatch."
        el = int(now - stopwatch_start)
        shown = f"{el // 60} minutes and {el % 60} seconds" if el >= 60 else f"{el} seconds"
        if re.search(r"\b(?:stop(?! ?watch)|end|pause|finish)\b", cl):
            stopwatch_start = None
            return f"Stopwatch stopped at {shown}."
        return f"The stopwatch is at {shown}."
    if re.search(r"\b(?:pomodoro|focus (?:session|mode|timer)|start focus)\b", cl):
        set_timer(25, "minutes", "focus time is over. Take a five minute break")
        return "Focus session started. I will tell you in 25 minutes."
    if re.search(r"\b(?:start|take)\s+(?:a\s+)?(?:short\s+)?break\b", cl):
        set_timer(5, "minutes", "break is over. Back to work")
        return "Break started. Five minutes."

    # ---- system questions ----
    if re.search(r"\buptime\b|\bhow long\b.*\b(?:pc|computer|laptop|system)\b.*\b(?:on|running|up)\b", cl):
        return uptime_text()
    if re.search(r"\b(?:using|eating|hogging|taking up)\b.*\b(?:cpu|processor|ram|memory)\b|\btop (?:apps|processes|programs)\b", cl):
        return top_processes("mem" if re.search(r"\b(?:ram|memory)\b", cl) else "cpu")
    if re.search(r"\b(?:cpu|processor) temp(?:erature)?\b|\b(?:laptop|pc|computer|system) temperature\b|\bhow hot is my (?:cpu|pc|laptop|computer)\b", cl):
        return cpu_temperature()
    if re.search(r"\b(?:which|what) wifi\b|\bwifi name\b|\bconnected to (?:which )?wifi\b|\bwhat network\b", cl):
        return wifi_name()
    if re.fullmatch(r"what(?:'s| is)? (?:the |my )?(?:current )?volume(?: level)?", cl):
        return volume_level()

    # ---- speech engine / microphones ----
    if re.search(r"\b(?:speech|voice|listening|recognition) engine\b|\bwhich (?:speech|voice) (?:engine|recognition)\b", cl):
        return speech_engine_text()
    if re.search(r"\b(?:list|show|which|what)\b.*\b(?:mics|microphones?)\b", cl):
        out = list_mics()
        print("MICROPHONES (set JARVIS_MIC=<number> to choose one):\n" + out)
        if not out[:1].isdigit():
            return out
        names = [ln.split(": ", 1)[-1] for ln in out.splitlines()][:4]
        return "Microphones: " + "; ".join(names) + ". The full list with numbers is in the terminal."

    # ---- lookups ----
    m = re.match(r"^(?:(?:search|look up|find)\s+(?:on\s+|in\s+)?)?(?:wikipedia|wiki)\s+(?:for\s+|about\s+)?(.+)$", c, re.I)
    if m:
        return wiki_summary(m.group(1).strip())
    m = (re.match(r"^define\s+([a-z]+)$", cl)
         or re.match(r"^(?:what(?:'s| is) the meaning of|meaning of)\s+([a-z]+)$", cl)
         or re.match(r"^what does ([a-z]+) mean$", cl))
    if m:
        return define_word(m.group(1))        # None -> falls through to the AI brain
    if re.search(r"\b(?:daily briefing|morning briefing|evening briefing|brief me|give me a briefing|my briefing)\b", cl):
        return daily_briefing()

    # ---- unit converter ----
    m = re.fullmatch(r"(?:convert )?(-?\d+(?:\.\d+)?) ?([a-z]+) (?:to|into|in) ([a-z]+)", cl)
    if m:
        return convert_units(float(m.group(1)), m.group(2), m.group(3))

    return None


# ---------------- one entry point for all the new commands ----------------
def handle_new_features(text, raw_text):
    """Returns a reply, or None if the sentence is not one of the new commands."""
    cmd = re.sub(r"\s+", " ", str(raw_text)).strip()
    for _ in range(3):
        cmd = re.sub(r"^(?:(?:hey|ok|okay)\s+)?(?:jarvis[\s,]+)?(?:(?:please|can you|could you|would you|kindly)\s+)*",
                     "", cmd, flags=re.I).strip()
    cmd = cmd.strip(" .!?,")

     # ---- save password: re-saves the password that is written in the code ----
    if re.fullmatch(r"(?:save|resave|re-save|restore|reset)\s+(?:my\s+|the\s+)?(?:jarvis\s+)?(?:password|passphrase)",
                    cmd, re.I):
        save_password(JARVIS_PASSWORD)
        return "Password saved."

    # ---- set password (blocked unless you allow it in the config) ----
    m = re.match(r"^(?:set|change|new|update)\s+(?:my\s+|the\s+|a\s+)?(?:jarvis\s+)?(?:password|passphrase)\s*(?:to|is|as)?\s*(.*)$",
                 cmd, re.I)
    if m:
        if not ALLOW_PASSWORD_CHANGE_BY_COMMAND:
            return "The password is fixed in the code. Say save password to restore it."
        pw = m.group(1).strip()
        if not pw:
            return "Put the password after the command, like: set password open sesame."
        if len(normalize_pw(pw)) < 4:
            return "That password is too short. Use at least four characters."
        save_password(pw)
        return "Password saved. Say lock screen, or lock Jarvis, to try it."

    # ---- lock ----
    if re.fullmatch(r"(?:lock|secure)\s+(?:jarvis|yourself|the assistant|assistant|you)", cmd, re.I):
        return lock_jarvis()
    if re.fullmatch(r"(?:lock|secure)\s+(?:the\s+|my\s+)?(?:screen|pc|computer|laptop|system|workstation)", cmd, re.I):
        return do_lock_screen()

    # ---- transform modes ----
    tl = re.sub(r"\s+", " ", re.sub(r"\b(please|now)\b", "", text)).strip(" .!?,")
    modes = load_modes()
    mm = re.search(r"\b(transform|morph|become|change|switch|turn)\b(?:\s+yourself)?(?:\s+(?:in)?to)?\s+(?:the\s+|a\s+)?([a-z ]+?)(?:\s+mode)?\s*$", tl)
    mm2 = re.fullmatch(r"(?:(?:enter|activate|start|go into)\s+)?([a-z]+) mode", tl)
    if mm or mm2:
        verb = mm.group(1) if mm else "mode"
        name = (mm.group(2) if mm else mm2.group(1)).strip()
        if name in _MODE_BACK_WORDS:
            name = "jarvis"
        if name in modes:
            return transform_to(name)
        if verb in ("transform", "morph", "become"):
            if name in ("yourself", ""):
                return "Transform into what? I know: " + ", ".join(modes) + "."
            return f"I don't have a mode called {name}. I know: " + ", ".join(modes) + "."
        # other verbs (switch window, turn off wifi, ...): not a mode, let the normal engine handle it

    # ---- exact volume / brightness ----
    m = re.search(r"\b(?:set\s+|make\s+|put\s+)?(?:the\s+)?(volume|brightness)\s+(?:to|at)\s+(\d{1,3})\s*(?:percent|%)?",
                  normalize_numbers(text))
    if m:
        if not IS_LINUX:
            return "Setting an exact level only works on Linux for now."
        what, level = m.group(1), max(0, min(100, int(m.group(2))))
        if what == "volume":
            if not shutil.which("wpctl"):
                return "Volume control utility wpctl is missing."
            ok = run_ok(["wpctl", "set-volume", "@DEFAULT_AUDIO_SINK@", f"{level}%"])
            return f"Volume set to {level} percent." if ok else "Could not change the volume."
        if not shutil.which("brightnessctl"):
            return "Brightness control is unavailable. Install brightnessctl first."
        level = max(level, 5)                      # never let the screen go fully black
        ok = run_ok(["brightnessctl", "set", f"{level}%"])
        return f"Brightness set to {level} percent." if ok else "I could not change brightness."

    # ---- files ----
    m = re.match(r"^(?:create|make|new|add)\s+(?:a\s+|an\s+|new\s+)*(?:folder|directory)\s+(?:called\s+|named\s+)?(.+)$", cmd, re.I)
    if m:
        name, folder = _folder_from_text(m.group(1))
        return fs_create_folder(name, folder)

    m = re.match(r"^(?:create|make|new|add)\s+(?:a\s+|an\s+|new\s+)*(?:text\s+)?file\s+(?:called\s+|named\s+)?(.+)$", cmd, re.I)
    if m:
        parts = re.split(r"\s+(?:with|containing|saying|that says)\s+(?:the\s+)?(?:text\s+|content\s+|contents\s+)?",
                         m.group(1), maxsplit=1, flags=re.I)
        name, folder = _folder_from_text(parts[0])
        content = parts[1].strip() if len(parts) > 1 else ""
        if not folder and content:
            content, folder = _folder_from_text(content)
        return fs_create_file(name, content, folder)

    m = re.match(r"^(?:read|show|display)\s+(?:me\s+)?(?:the\s+)?file\s+(.+)$", cmd, re.I)
    if m:
        name, folder = _folder_from_text(m.group(1))
        return fs_read(name, folder)

    m = re.match(r"^(?:list|show)\s+(?:me\s+)?(?:my\s+|the\s+)?files(?:\s+(?:in|on)\s+(?:my\s+|the\s+)?(desktop|documents|downloads)(?:\s+folder)?)?$",
                 cmd, re.I)
    if m:
        return fs_list((m.group(1) or "").lower() or None)

    m = re.match(r"^(?:delete|remove|trash)\s+(?:the\s+)?(?:file|folder|directory)\s+(.+)$", cmd, re.I)
    if m:
        name, folder = _folder_from_text(m.group(1))
        return fs_delete(name, folder)

    m = re.match(r"^rename\s+(?:the\s+)?(?:file\s+|folder\s+)?(.+?)\s+to\s+(.+)$", cmd, re.I)
    if m:
        return fs_rename(m.group(1), m.group(2))

    m = re.match(r"^(move|copy)\s+(?:the\s+)?(?:file\s+|folder\s+)?(.+?)(?:\s+from\s+(?:my\s+|the\s+)?(desktop|documents|downloads)(?:\s+folder)?)?"
                 r"\s+to\s+(?:my\s+|the\s+)?(desktop|documents|downloads)(?:\s+folder)?$", cmd, re.I)
    if m:
        return fs_move_copy(m.group(1).lower(), m.group(2), (m.group(3) or "").lower() or None, m.group(4).lower())

    m = re.match(r"^(?:find|locate)\s+(?:my\s+|the\s+)?file\s+(.+)$", cmd, re.I)
    if m:
        return fs_find(m.group(1))

    m = re.match(r"^open\s+(?:the\s+)?file\s+(.+)$", cmd, re.I)
    if m:
        name, folder = _folder_from_text(m.group(1))
        return fs_open(name, folder)

    # ---- math ----
    extra = handle_extra_features(text, cmd)
    if extra is not None:
        return extra
    return try_math(text)


LINUX_APPS = {
    "text editor": ["gnome-text-editor", "gedit", "kate"],
    "visual studio code": ["code"],
    "visual studio": ["code"],
    "vs code": ["code"],
    "vscode": ["code"],
    "settings": ["gnome-control-center"],
    "file manager": ["nautilus"],
    "files": ["nautilus"],
    "calculator": ["gnome-calculator", "kcalc"],
    "terminal": ["ptyxis", "kgx", "gnome-terminal", "konsole"],
    "spotify": ["spotify"],
    "firefox": ["firefox"],
    "browser": ["firefox"],
    "chrome": ["google-chrome-stable", "google-chrome"],
}

PROTECTED_PROCS = {
    "systemd", "gnome-shell", "gdm", "xorg", "xwayland", "pipewire",
    "wireplumber", "dbus-daemon", "dbus-broker", "python", "python3",
    "init", "login", "sshd", "bash", "zsh", "fish",
}

REPEAT_RE = re.compile(r'\b(do (?:it|that) again|repeat (?:that|it)|open it again|same again|once more)\b')
QUESTION_RE = re.compile(r"^(?:ask |tell me|explain|define|describe|calculate|translate|give me|what|who|why|how|when|where|which|is |are |can |does |do |should )")
YESNO_RE = re.compile(r'^\s*(yes|yeah|yep|sure|no|nope|cancel|confirm)\b')


def handle_command(raw_text):
    global pending_confirm

    text = raw_text.lower().strip()
    text = re.sub(r'wi[\s-]?fi', 'wifi', text)
    clean_text = re.sub(
        r'\b(jarvis|please|can you|could you|would you|kindly|for me|navigate|go to|take me to|open up|show me|run|start)\b',
        '', text
    ).strip()
    clean_text = re.sub(r'\s+', ' ', clean_text)

    # ---- 0. Pending confirmation (yes / no) ----
    if pending_confirm:
        pc = pending_confirm
        pending_confirm = None
        if time.time() < pc["expires"]:
            if has_word("yes|yeah|yep|sure|confirm|proceed|do it", text):
                return pc["action"]()
            if has_word("no|nope|cancel|stop|abort|negative", text):
                return "Cancelled."
            # anything else: treat as a brand new command

    # ---- 1. Your custom commands (~/.jarvis/commands.json) ----
    for phrase, cmd in load_custom_commands().items():
        if phrase.lower() in text:
            subprocess.Popen(str(cmd), shell=True, start_new_session=True)
            return f"Running {phrase}."

    # ---- 1a. Password lock, transform modes, file commands, math ----
    try:
        new_reply = handle_new_features(text, raw_text)
    except Exception as e:
        print(f"[feature] error: {e}")
        new_reply = "That command failed. Check the terminal for details."
    if new_reply is not None:
        return new_reply

    # ---- 1b. Diagnostics and voice switching ----
    if re.search(r'\b(diagnostics?|self ?test|system check|check yourself)\b', text):
        return run_diagnostics()
    vm = re.search(r'\b(evil|robot|normal)\s+voice\b|\bvoice\s+(?:to\s+)?(evil|robot|normal)\b', text)
    if vm:
        name = vm.group(1) or vm.group(2)
        set_voice(name)
        return {"evil": "Evil voice activated.",
                "robot": "Robot voice activated.",
                "normal": "Normal voice activated."}[name]

    # ---- 2. Search ----
    search_match = re.search(
        r'\b(?:search|look up|browse)\b\s+(?:(?:on|in|the|for|internet|web|online|about)\s+)*(.+)$',
        text
    )
    if search_match:
        query = search_match.group(1).strip(" ,.!?")
        if query:
            webbrowser.open("https://www.google.com/search?q=" + urllib.parse.quote(query))
            return f"Searching the internet for {query}."

    # ---- 3. Timers and reminders ----
    if re.search(r'\b(remind me|timer|alarm)\b', text):
        if re.search(r'\bcancel\b.*\btimers?\b', text):
            for t in active_timers:
                t.cancel()
            active_timers.clear()
            return "All timers cancelled."
        t2 = normalize_numbers(text)
        m = re.search(
            r'remind me (?:to |about |that )?(.+?)\s+in\s+(\d+)\s*(second|sec|minute|min|hour|hr)s?\b', t2)
        if m:
            return set_timer(int(m.group(2)), m.group(3), m.group(1).strip())
        m = re.search(
            r'\b(?:remind me|timer|alarm)\b.*?(\d+)\s*(second|sec|minute|min|hour|hr)s?\b'
            r'(?:\s*(?:to|that|about)\s+(.+))?', t2)
        if m:
            label = m.group(3).strip() if m.group(3) else None
            return set_timer(int(m.group(1)), m.group(2), label)

    # ---- 4. Notes ----
    note_match = re.search(
        r'\b(?:take a note|take note|make a note|add a note|write a note|note down|note that)\b\s*(.*)', text)
    if note_match:
        note = note_match.group(1).strip(" ,.!?")
        if not note:
            return "What should I note?"
        with open(NOTES_FILE, "a", encoding="utf-8") as f:
            f.write(f"[{datetime.datetime.now():%Y-%m-%d %H:%M}] {note}\n")
        return "Note saved."
    if re.search(r'\bread (?:my |the )?notes\b', text):
        try:
            with open(NOTES_FILE, "r", encoding="utf-8") as f:
                lines = [re.sub(r'^\[[^\]]*\]\s*', '', ln.strip()) for ln in f if ln.strip()]
        except FileNotFoundError:
            lines = []
        if not lines:
            return "You have no notes yet."
        return "Your latest notes. " + ". ".join(lines[-5:]) + "."
    if re.search(r'\b(?:clear|delete) (?:my |all )?notes\b', text):
        def clear_notes():
            open(NOTES_FILE, "w").close()
            return "All notes cleared."
        return ask_confirm("Do you want to delete all your notes?", clear_notes)

    # ---- 5. Voice typing ----
    type_match = re.match(r'(?:type|dictate)\s+(.+)', text)
    if type_match:
        return type_text(type_match.group(1))

    # ---- 6. Weather / news ----
    if "weather" in text:
        city_match = re.search(r'\bin\s+([a-z\s]+?)(?:\s+(?:today|now|tomorrow))?$', text)
        city = city_match.group(1).strip() if city_match else DEFAULT_CITY
        return get_weather(city)
    if has_word("news|headlines", text):
        return get_news()

    # ---- 7. Info: battery, disk, ip, internet ----
    if "battery" in text:
        return battery_info()
    if "disk space" in text or "free space" in text or has_word("storage", text):
        return disk_info()
    if re.search(r'\b(my ip|ip address)\b', text):
        return ip_info()
    if re.search(r'\b(am i online|internet connection|am i connected)\b', text):
        return "You are online." if is_online() else "You appear to be offline."

    # ---- 8. Phone link (KDE Connect) ----
    if re.search(r'\b(find|ring|locate) my phone\b', text):
        dev = kde_device()
        if not dev:
            return "No phone found. Install KDE Connect and pair your phone."
        run_ok(["kdeconnect-cli", "--ring", "-d", dev])
        return "Ringing your phone."
    ping_match = re.search(r'\b(?:send|ping)\b.*?\b(?:message|notification)\s+(.+?)\s+to (?:my )?phone', text)
    if ping_match:
        dev = kde_device()
        if not dev:
            return "No phone found. Install KDE Connect and pair your phone."
        run_ok(["kdeconnect-cli", "--ping-msg", ping_match.group(1), "-d", dev])
        return "Message sent to your phone."

    # ---- 9. Power (always asks first) ----
    if re.search(r'\b(shut ?down|power off|turn off)\b.*\b(pc|computer|system|laptop)\b', text):
        def do_shutdown():
            if IS_WIN:
                os.system("shutdown /s /t 10")
            else:
                subprocess.Popen(["systemctl", "poweroff"])
            return "Shutting down."
        return ask_confirm("Do you want me to shut down the computer?", do_shutdown)
    if re.search(r'\b(restart|reboot)\b.*\b(pc|computer|system|laptop)\b', text):
        def do_reboot():
            if IS_WIN:
                os.system("shutdown /r /t 10")
            else:
                subprocess.Popen(["systemctl", "reboot"])
            return "Restarting."
        return ask_confirm("Do you want me to restart the computer?", do_reboot)
    if IS_WIN and ("cancel shutdown" in text or "abort shutdown" in text):
        os.system("shutdown /a")
        return "Shutdown aborted."

    # ---- 10. LINUX system control ----
    if IS_LINUX:
        if any(k in text for k in [
            "increase volume", "increase the volume", "increasing volume",
            "increasing the volume", "volume up", "turn volume up",
            "turn up the volume", "raise volume", "make the volume louder", "louder"
        ]):
            if not shutil.which("wpctl"):
                return "Volume control utility wpctl is missing."
            ok = run_ok(["wpctl", "set-volume", "@DEFAULT_AUDIO_SINK@", "5%+"])
            return "Increasing volume." if ok else "Could not increase volume."

        if any(k in text for k in [
            "decrease volume", "decrease the volume", "decreasing volume",
            "decreasing the volume", "volume down", "turn volume down",
            "turn down the volume", "lower volume", "make the volume quieter", "quieter"
        ]):
            if not shutil.which("wpctl"):
                return "Volume control utility wpctl is missing."
            ok = run_ok(["wpctl", "set-volume", "@DEFAULT_AUDIO_SINK@", "5%-"])
            return "Decreasing volume." if ok else "Could not decrease volume."

        if has_word("mute|unmute", text):
            if not shutil.which("wpctl"):
                return "Volume control utility wpctl is missing."
            run_ok(["wpctl", "set-mute", "@DEFAULT_AUDIO_SINK@", "toggle"])
            return "Toggling mute."

        if any(k in text for k in [
            "increase brightness", "increasing brightness",
            "increase the brightness", "brightness up"
        ]):
            if not shutil.which("brightnessctl"):
                return "Brightness control is unavailable. Install brightnessctl first."
            ok = run_ok(["brightnessctl", "set", "+10%"])
            return "Increasing brightness." if ok else "I could not change brightness."

        if any(k in text for k in [
            "decrease brightness", "decreasing brightness",
            "decrease the brightness", "brightness down"
        ]):
            if not shutil.which("brightnessctl"):
                return "Brightness control is unavailable. Install brightnessctl first."
            ok = run_ok(["brightnessctl", "set", "10%-"])
            return "Decreasing brightness." if ok else "I could not change brightness."

        if any(k in text for k in [
            "lock screen", "turn off screen", "switch off screen", "screen off"
        ]):
            return do_lock_screen()

        # Wi-Fi / Bluetooth
        if "wifi" in text:
            state = onoff(text)
            if state is None:
                return "Do you want Wi-Fi on or off?"
            if not shutil.which("nmcli"):
                return "Wi-Fi control needs NetworkManager."
            run_ok(["nmcli", "radio", "wifi", "on" if state else "off"])
            return f"Wi-Fi turned {'on' if state else 'off'}."
        if "bluetooth" in text:
            state = onoff(text)
            if state is None:
                return "Do you want Bluetooth on or off?"
            if not shutil.which("bluetoothctl"):
                return "Bluetooth control needs bluetoothctl."
            run_ok(["bluetoothctl", "power", "on" if state else "off"])
            return f"Bluetooth turned {'on' if state else 'off'}."

        # Screenshot / clipboard
        if "screenshot" in text or "screen shot" in text:
            return take_screenshot()
        if re.search(r'\bread (?:what i copied|my clipboard|the clipboard|clipboard)\b', text):
            return read_clipboard()

        # What's playing + media keys (needs playerctl)
        if re.search(r"what(?:'s| is)? (?:currently )?playing|what song|now playing|current song", text):
            if not shutil.which("playerctl"):
                return "Media info needs playerctl. Install it first."
            info = run_out(["playerctl", "metadata", "--format", "{{artist}} - {{title}}"])
            return f"Now playing: {info}." if info else "Nothing is playing right now."
        media = [
            (["pause music", "pause video", "pause media", "play music",
              "play video", "resume media"], "play-pause", "Toggling media playback."),
            (["next track", "next song"], "next", "Skipping to next media item."),
            (["previous track", "previous song"], "previous", "Going to previous media item."),
        ]
        for phrases, action, reply in media:
            if any(p in text for p in phrases):
                if not shutil.which("playerctl"):
                    return "Media control needs playerctl. Install it first."
                run_ok(["playerctl", action])
                return reply

        # Window control
        win_key = None
        if re.search(r'\bminimi[sz]e\b', text):
            win_key = "minimize"
        elif re.search(r'\bmaximi[sz]e\b', text):
            win_key = "maximize"
        elif re.search(r'\b(?:switch|next) window\b', text):
            win_key = "switch"
        elif re.search(r'\bfull ?screen\b', text):
            win_key = "fullscreen"
        if win_key:
            xname, codes, reply = WINDOW_ACTIONS[win_key]
            if send_combo(xname, codes):
                return reply
            return "Window control needs ydotool or xdotool. Install one first."

        # Folders and apps
        if "open downloads" in text or "open download folder" in text:
            subprocess.Popen(["xdg-open", os.path.expanduser("~/Downloads")])
            return "Opening Downloads."
        if any(k in text for k in ["open home folder", "open files", "open file manager"]):
            subprocess.Popen(["xdg-open", os.path.expanduser("~")])
            return "Opening your Home folder."
        if "whatsapp" in clean_text:
            subprocess.Popen(["xdg-open", "https://web.whatsapp.com"])
            return "Opening WhatsApp Web."

        if has_word("open|launch", text):
            for name, candidates in LINUX_APPS.items():
                if name in clean_text:
                    exe = next((c for c in candidates if shutil.which(c)), None)
                    if exe:
                        subprocess.Popen([exe])
                        return f"Opening {name}."
                    return f"I couldn't find {name} on this system."
            # generic: any installed program, e.g. "open gimp"
            app_name = re.sub(r'\b(open|launch)\b', '', clean_text).strip().replace(" ", "-")
            if app_name and shutil.which(app_name):
                subprocess.Popen([app_name])
                return f"Opening {app_name}."

    # ---- 11. WINDOWS system control ----
    if IS_WIN:
        if "volume up" in text or "increase volume" in text or "volume higher" in text:
            press_key(0xAF, 5)
            return "Increasing audio output level."
        if "volume down" in text or "decrease volume" in text or "volume lower" in text:
            press_key(0xAE, 5)
            return "Decreasing audio output level."
        if has_word("mute|unmute", text):
            press_key(0xAD, 1)
            return "Toggling master audio mute."
        if any(k in text for k in ["pause music", "pause video", "play music", "play video", "pause media", "resume media"]):
            press_key(0xB3, 1)
            return "Toggling media playback."
        if "next track" in text or "next song" in text:
            press_key(0xB0, 1)
            return "Skipping to next media item."
        if "previous track" in text or "previous song" in text:
            press_key(0xB1, 1)
            return "Returning to previous media item."
        if any(k in text for k in ["lock pc", "lock computer", "lock screen", "lock workstation"]):
            return do_lock_screen()

        local_nav_map = {
            ("this pc", "my pc", "my computer"): "explorer.exe shell:::{20D04FE0-3AEA-1069-A2D8-08002B30309D}",
            ("recycle bin",): "explorer.exe shell:::{645FF040-5081-101B-9F08-00AA002F954E}",
            ("control panel",): "control.exe",
            ("settings", "pc settings", "windows settings"): "start ms-settings:",
            ("task manager", "taskmgr"): "start taskmgr",
        }
        for key_tuple, cmd in local_nav_map.items():
            if any(k in text for k in key_tuple):
                os.system(cmd)
                return f"Opening {key_tuple[0].title()}."

        drive_match = re.search(r'\b([a-z])\s*(drive|disk)\b', text)
        if drive_match:
            drive_letter = drive_match.group(1).upper()
            drive_path = f"{drive_letter}:\\"
            if os.path.exists(drive_path):
                os.startfile(drive_path)
                return f"Accessing drive {drive_letter}."
            return f"Drive {drive_letter} was not detected."

        if has_word("open|launch", text):
            win_apps = {
                "edge": "msedge", "chrome": "chrome", "notepad": "notepad",
                "calculator": "calc", "paint": "mspaint", "word": "winword",
                "excel": "excel", "powerpoint": "powerpnt", "spotify": "spotify",
                "vscode": "code", "visual studio code": "code",
            }
            for key, cmd in win_apps.items():
                if key in clean_text:
                    os.system(f"start {cmd}")
                    return f"Launching {key.title()}."

    # ---- 12. Date and time ----
    if has_word("time|clock", text):
        return f"Current local time is {datetime.datetime.now().strftime('%I:%M %p')}."
    if has_word("date|today", text) or "what day" in text:
        return f"Today is {datetime.datetime.now().strftime('%A, %B %d, %Y')}."

    # ---- 13. System stats ----
    if any(k in text for k in ["cpu usage", "processor load", "ram usage", "memory status", "system stats"]):
        cpu = psutil.cpu_percent(interval=0.1)
        ram = psutil.virtual_memory().percent
        return f"CPU utilization is at {cpu} percent. Memory is at {ram} percent."

    # ---- 14. Process termination (asks first) ----
    if has_word("close|kill|terminate|exit", text):
        target = re.sub(
            r'\b(close|kill|terminate|stop|exit|app|application|program|process)\b',
            '', clean_text
        ).strip()
        if len(target) < 3:
            return "Specify the target application to terminate."

        matches = []
        for proc in psutil.process_iter(['pid', 'name']):
            try:
                pname = (proc.info['name'] or "").lower()
                if (target in pname and pname not in PROTECTED_PROCS
                        and proc.pid not in (os.getpid(), os.getppid())):
                    matches.append(proc)
            except (psutil.NoSuchProcess, psutil.AccessDenied, psutil.ZombieProcess):
                pass

        if not matches:
            return f"I could not find a running process named {target}."

        def do_kill(procs=matches, name=target):
            count = 0
            for p in procs:
                try:
                    p.kill()
                    count += 1
                except Exception:
                    pass
            return f"Terminated {count} process(es) matching {name}."

        return ask_confirm(f"I found {len(matches)} process(es) matching {target}. Kill them?", do_kill)

    # ---- 15. Special folders ----
    user_home = os.path.expanduser("~")
    special_folders = {
        ("downloads", "download folder"): os.path.join(user_home, "Downloads"),
        ("documents", "my documents"): os.path.join(user_home, "Documents"),
        ("desktop",): os.path.join(user_home, "Desktop"),
        ("pictures", "photos"): os.path.join(user_home, "Pictures"),
        ("videos", "movies"): os.path.join(user_home, "Videos"),
        ("music",): os.path.join(user_home, "Music"),
    }
    if has_word("open|show", text):
        for key_tuple, folder_path in special_folders.items():
            if any(k in text for k in key_tuple) and os.path.exists(folder_path):
                if IS_LINUX:
                    subprocess.Popen(["xdg-open", folder_path])
                else:
                    os.startfile(folder_path)
                return f"Opening {key_tuple[0].title()}."

    # ---- 16. Create / delete: handled earlier by handle_new_features ----
    # (safe folders only, and delete always goes to the trash after a yes/no)

    # ---- 17. YouTube ----
    if has_word("youtube|play|watch", text):
        query = re.sub(r'\b(play|on|youtube|watch|video|search|for)\b', '', clean_text).strip()
        if query:
            webbrowser.open("https://www.youtube.com/results?search_query=" + urllib.parse.quote(query))
            return f"Searching YouTube for {query}."
        webbrowser.open("https://www.youtube.com")
        return "Opening YouTube."

    # ---- 18. Google / direct URLs ----
    if any(p in text for p in ["open google", "launch google", "google homepage"]):
        webbrowser.open("https://www.google.com")
        return "Opening Google."

    if any(ext in text for ext in [".com", ".org", ".net", ".io", ".gov", ".edu", ".ai"]):
        url = clean_text.replace(" ", "")
        if not url.startswith("http"):
            url = "https://" + url
        webbrowser.open(url)
        return f"Navigating to {url}"

    # ---- 19. Identity / help ----
    if any(k in text for k in ["who are you", "identity", "signature", "creator"]):
        return "I am J.A.R.V.I.S., core operating intelligence for The Silent Exploit Base Project for learning."
    if "what can you do" in text or has_word("help", text):
        return ("I can control volume and brightness, open apps, search the web, set timers and reminders, "
                "take notes, check weather and news, take screenshots, type for you, do math, "
                "create, read, rename, move and trash files, transform into other modes, "
                "lock and unlock with a password, keep a to do list, tell jokes, run a stopwatch or focus timer, "
                "look things up on Wikipedia, convert units, give a daily briefing, change the theme, and answer questions."
                + (" Say Hey Jarvis first." if WAKE_WORD_ENABLED else ""))

    # ---- 19b. Smart match: imperfect English -> closest known command ----
    if not (QUESTION_RE.match(clean_text) and len(text.split()) > 4):   # long questions go to the AI instead
        guess = smart_match(text)
        if guess and guess != text.strip():
            if MIC_DEBUG:
                print(f"[smart] understood '{text}' as '{guess}'")
            if guess in ("lock screen",):
                return ask_confirm(f"Did you mean {guess}?", lambda g=guess: handle_command(g))
            return handle_command(guess)

    # ---- 20. AI brain for everything else ----
    if QUESTION_RE.match(clean_text) and len(text.split()) >= 2:
        reply = ask_ai(raw_text)
        if reply:
            return reply
        hit = smart_resolve(raw_text)          # AI offline: maybe this was a command, e.g. "how much charge is left"
        if hit:
            canonical, unsure = hit
            print(f"[smart] '{raw_text}' -> '{canonical}'{' (asking first)' if unsure else ''}")
            if unsure:
                return ask_confirm(f"Did you mean {canonical}?", lambda c=canonical: handle_command(c))
            return handle_command(canonical)
        return "My AI brain is offline. Start Ollama or set the Anthropic API key."

    return UNKNOWN


def execute_command(raw_text):
    """Wrapper: handles 'do that again' memory around the main engine."""
    global last_command

    global awaiting_password
    if awaiting_password:
        if time.time() < awaiting_until:
            return handle_unlock_attempt(raw_text)
        awaiting_password = False

    # While locked, every input (voice or typed) is only a password attempt.
    if jarvis_locked:
        return handle_locked_input(raw_text)

    if REPEAT_RE.search(raw_text.lower()):
        if not last_command:
            return "I have nothing to repeat yet."
        raw_text = last_command

    used = raw_text
    response = handle_command(raw_text)

    # Smart understanding: only runs when the normal engine did not understand you
    if response == UNKNOWN:
        try:
            fixed = fix_words(raw_text)
            if fixed and fixed != raw_text.lower().strip(" .!?,"):
                r2 = handle_command(fixed)
                if r2 != UNKNOWN:
                    print(f"[smart] '{raw_text}' -> '{fixed}'")
                    response, used = r2, fixed
            if response == UNKNOWN:
                hit = smart_resolve(fixed or raw_text)
                if hit:
                    canonical, unsure = hit
                    print(f"[smart] '{raw_text}' -> '{canonical}'{' (asking first)' if unsure else ''}")
                    if unsure:
                        response = ask_confirm(f"Did you mean {canonical}?",
                                               lambda c=canonical: handle_command(c))
                    else:
                        response = handle_command(canonical)
                        used = canonical
        except Exception as e:
            print(f"[smart] error: {e}")

    # FIX: last resort, let the AI brain repair the sentence (like a human would understand it)
    if response == UNKNOWN and AI_FIX_ENABLED:
        try:
            ai_cmd = llm_fix_command(raw_text)
            if ai_cmd:
                print(f"[ai-fix] '{raw_text}' -> '{ai_cmd}'")
                if ai_cmd == "lock screen":
                    response = ask_confirm(f"Did you mean {ai_cmd}?",
                                           lambda c=ai_cmd: handle_command(c))
                else:
                    r3 = handle_command(ai_cmd)
                    if r3 != UNKNOWN:
                        response, used = r3, ai_cmd
        except Exception as e:
            print(f"[ai-fix] error: {e}")

    if (response != UNKNOWN
            and not response.endswith("Say yes or no.")
            and not YESNO_RE.match(used.lower())
            and not _SETPW_RE.match(used)):
        last_command = used
    return response


# =====================================================================
# SPEECH RECOGNITION
# =====================================================================
VOSK_MODEL = None
try:
    from vosk import Model, KaldiRecognizer, SetLogLevel
    if os.path.isdir(VOSK_PATH) and STT_MODE != "google":
        SetLogLevel(-1)
        VOSK_MODEL = Model(VOSK_PATH)
        print("Offline speech recognition (Vosk) enabled.")
except Exception:
    VOSK_MODEL = None


# =====================================================================
# SMART MATCH: understands imperfect English by finding related words
# =====================================================================
_VOL = {"volume", "sound", "sounds", "audio", "speaker", "speakers", "loudness", "loud", "louder", "quiet", "quieter", "softer"}
_UP = {"up", "increase", "raise", "more", "higher", "high", "louder", "loud", "bigger", "big", "boost", "maximum", "max", "add", "brighter", "increasing"}
_DOWN = {"down", "decrease", "lower", "less", "low", "reduce", "quieter", "quiet", "smaller", "small", "softer", "soft", "minimum", "dimmer", "dim", "darker", "dark", "decreasing"}
_BRI = {"brightness", "bright", "brighter", "dim", "dimmer", "darker", "light", "lights"}
_OPEN = {"open", "start", "launch", "run", "show", "use", "want", "need", "go", "take", "please"}

# (command to run, words that name the thing, words that say what to do or None)
SMART_RULES = [
    ("increase the volume", _VOL, _UP),
    ("decrease the volume", _VOL, _DOWN),
    ("increase the brightness", _BRI, _UP),
    ("decrease the brightness", _BRI, _DOWN),
    ("mute", {"mute", "silent", "silence"}, None),
    ("what time is it", {"time", "clock", "hour", "hours", "oclock"}, None),
    ("what is the date", {"date", "day", "today", "calendar", "month"}, None),
    ("what is the weather", {"weather", "temperature", "rain", "raining", "hot", "cold", "climate", "forecast", "sunny", "cloudy"}, None),
    ("tell me the news", {"news", "headlines", "headline", "newspaper", "happening"}, None),
    ("battery status", {"battery", "charge", "charging", "charger", "percentage"}, None),
    ("take a screenshot", {"screenshot", "snapshot", "screenshoot", "capture"}, None),
    ("lock screen", {"lock", "locked", "secure"}, None),
    ("cpu usage", {"cpu", "processor", "ram", "memory", "performance", "slow", "lag", "laggy", "usage"}, None),
    ("who are you", {"yourself", "introduce", "identity", "yourname"}, None),
    ("next song", {"song", "songs", "track", "tracks", "music"}, {"next", "skip", "forward", "change"}),
    ("previous song", {"song", "songs", "track", "tracks", "music"}, {"previous", "back", "last", "before"}),
    ("pause music", {"song", "songs", "track", "music"}, {"pause", "stop", "hold"}),
    ("open firefox", {"firefox", "browser", "internet", "web", "chrome", "browsing", "fire", "fox"}, _OPEN),
    ("open text editor", {"editor", "notepad", "text", "gedit", "kate", "typing"}, _OPEN),
    ("open visual studio code", {"code", "coding", "vscode", "visual", "studio", "vs", "programming"}, _OPEN),
    ("open settings", {"settings", "setting", "setup", "preferences", "configuration", "config", "control"}, _OPEN),
    ("open calculator", {"calculator", "calc", "calculate", "math", "maths", "calculation"}, _OPEN),
    ("open terminal", {"terminal", "console", "shell", "command", "commands", "cmd", "prompt", "bash"}, _OPEN),
    ("open files", {"files", "file", "folder", "folders", "manager", "explorer"}, _OPEN),
    ("open downloads", {"downloads", "download", "downloaded"}, _OPEN),
    ("open youtube", {"youtube", "videos", "video"}, _OPEN),
    ("open whatsapp", {"whatsapp", "chatting", "chat"}, _OPEN),
]


def _word_match(token, words):
    """Exact match, or a close spelling for words of 4+ letters (handles mishearings)."""
    if token in words:
        return True
    if len(token) >= 4:
        return bool(difflib.get_close_matches(token, list(words), n=1, cutoff=0.84))
    return False


def smart_match(text):
    """Imperfect English in, closest SAFE command out (or None). Never maps to delete, kill or shutdown."""
    tokens = re.findall(r"[a-z']+", text.lower().replace("'", ""))
    if not tokens or len(tokens) > 12:
        return None

    best = None
    for command, objects, actions in SMART_RULES:
        obj_idx = [i for i, t in enumerate(tokens) if _word_match(t, objects)]
        if not obj_idx:
            continue
        score, last_act = 1, -1
        exact_obj = sum(1 for i in obj_idx if tokens[i] in objects)   # exact words beat fuzzy ones
        if actions is not None:
            act_idx = [i for i, t in enumerate(tokens) if _word_match(t, actions)]
            if act_idx:
                score, last_act = 2, max(act_idx)
            elif not command.startswith("open ") or len(tokens) > 2:
                continue              # needs a verb like "open"/"up"/"down" (short phrases like "browser please" are fine)
        cand = (score, exact_obj, last_act, command)
        if best is None or cand[:3] > best[:3]:
            best = cand
    return best[3] if best else None


# Phrases Jarvis understands. Short sentences that are *almost* one of these get snapped to it.
KNOWN_PHRASES = [
    "increase the volume", "decrease the volume", "volume up", "volume down", "mute", "unmute",
    "increase the brightness", "decrease the brightness", "lock screen",
    "open text editor", "open visual studio code", "open vs code", "open settings",
    "open firefox", "open calculator", "open terminal", "open downloads", "open files",
    "open youtube", "open google", "open whatsapp", "take a screenshot",
    "what time is it", "what is the date", "what is the weather", "tell me the news",
    "cpu usage", "next song", "previous song", "pause music", "play music",
    "who are you", "run diagnostics", "read my notes", "minimize window", "maximize window",
    "what can you do", "battery status", "what is my ip address",
]

# Common speech-to-text mistakes -> what you actually meant
MISHEARINGS = [
    (r"\bvolume (?:app|op|of|u p)\b", "volume up"),
    (r"\bvolume (?:done|town|dawn|that)\b", "volume down"),
    (r"\bbrightness (?:app|op|of)\b", "brightness up"),
    (r"\bbrightness (?:done|town|dawn)\b", "brightness down"),
    (r"\bbright ness\b", "brightness"),
    (r"\bin ?crease\b", "increase"),
    (r"\b(?:decrees|the crease|de crease)\b", "decrease"),
    (r"\bfire ?fox\b", "firefox"),
    (r"\b(?:v s code|vs coat|v s coat|visual studio coat)\b", "vs code"),
    (r"\b(?:whats ?app|what's app|what's up web|watsapp)\b", "whatsapp"),
    (r"\byou ?tube\b", "youtube"),
    (r"\bblue ?tooth\b", "bluetooth"),
    (r"\b(?:why fi|wife i|wi fi)\b", "wifi"),
    (r"\b(?:calculate her|calculated)\b", "calculator"),
    (r"\bsetting\b", "settings"),
    (r"\bscreen ?shot\b", "screenshot"),
    (r"\btext at it or\b", "text editor"),
    (r"\bterminal's\b", "terminal"),
]


def fix_mishearings(text):
    t = text.lower().strip(" .!?,")
    t = re.sub(r"\s+", " ", t)
    for pat, repl in MISHEARINGS:
        t = re.sub(pat, repl, t)
    if len(t.split()) <= 5:
        close = difflib.get_close_matches(t, KNOWN_PHRASES, n=1, cutoff=0.82)
        if close:
            t = close[0]
    return t


def command_score(text):
    """0..1: how much this sentence looks like something Jarvis can do."""
    t = fix_mishearings(text)
    best = 0.0
    for ph in KNOWN_PHRASES:
        if ph in t:
            best = max(best, 1.0)
        else:
            best = max(best, difflib.SequenceMatcher(None, t, ph).ratio())
    return best


def llm_fix_command(text):
    """FIX: ask the AI brain to repair a mis-heard sentence into ONE command Jarvis knows.
    Safe by design: the answer must be an item from KNOWN_PHRASES or 'search for <topic>'.
    Anything else (including delete, kill, shutdown) is rejected."""
    text = (text or "").strip()
    if not text or len(text.split()) > 15:
        return None

    system = (
        "You repair speech-recognition mistakes for a PC voice assistant. The speaker uses English with an "
        "accent, so words are often misheard or grammar is rough. Decide what they most likely wanted.\n"
        "Reply with EXACTLY one line and nothing else: either one command copied from the list below, "
        "or 'search for <topic>' if they want to look something up on the internet, or NONE if nothing fits.\n"
        "Commands:\n" + "\n".join(KNOWN_PHRASES)
    )
    out = _llm_once(system, f'Transcript: "{text}"', max_tokens=30, timeout=8)
    if not out:
        return None

    out = out.strip().splitlines()[0].strip().strip('"\'`.!?, ').lower()
    if out in KNOWN_PHRASES:
        return out
    if out.startswith("search for ") and 2 < len(out) < 120:
        return out
    return None


def vosk_text(audio):
    rec = KaldiRecognizer(VOSK_MODEL, 16000)
    rec.AcceptWaveform(audio.get_raw_data(convert_rate=16000, convert_width=2))
    out = json.loads(rec.FinalResult()).get("text", "").strip()
    if not out or not is_english(out):
        raise sr.UnknownValueError()
    return out


def is_english(text):
    """True only for plain Latin text. Urdu, Arabic and Hindi script are rejected."""
    return bool(text) and all(ord(c) < 128 for c in text)


def google_best(recognizer, audio):
    """English only: ask Google for several guesses, drop non-English ones, pick the best command match."""
    langs = [SPEECH_LANG] + (["en-US"] if SPEECH_LANG != "en-US" else [])
    saw_non_english = False

    for lang in langs:
        result = recognizer.recognize_google(audio, language=lang, show_all=True)
        alts = []
        if isinstance(result, dict):
            for a in result.get("alternative", []):
                tr = (a.get("transcript") or "").strip()
                if not tr:
                    continue
                if is_english(tr):
                    alts.append(tr)
                else:
                    saw_non_english = True
        if not alts:
            continue                      # nothing English from this language: try the next one

        best = alts[0]
        if len(alts) > 1 and command_score(best) < 0.85:
            for a in alts[1:]:
                if command_score(a) >= 0.85:
                    best = a
                    break
        if MIC_DEBUG and len(alts) > 1:
            print(f"[alternatives] {alts[:4]}")
        return best

    if MIC_DEBUG and saw_non_english:
        print("[ignored] that was not English (Urdu or another language), skipping it")
    raise sr.UnknownValueError()


_google_down_until = 0.0


# ---------------------------------------------------------------- Whisper (offline, accent friendly)
WHISPER = None                 # ("faster", model) or ("openai", model) once loaded
_whisper_state = "off"         # off | loading | ready | failed
WHISPER_PROMPT = ("Jarvis voice commands. Open Firefox. Increase the volume. Decrease the brightness. "
                  "What time is it? What is the weather? Set a timer for five minutes. Take a screenshot.")
_WHISPER_JUNK = {"", "you", "thank you", "thanks", "thank you for watching", "thanks for watching",
                 "bye", "bye bye", "the end", "okay", "ok", "hmm", "uh", "um", "mm", "oh"}


def load_whisper():
    """Loads Whisper in the background. Until it is ready (or if it fails) Google / Vosk are used."""
    global WHISPER, _whisper_state
    if STT_MODE in ("google", "vosk"):
        return
    _whisper_state = "loading"
    try:
        import numpy  # noqa: F401  (Whisper needs it)
        try:
            from faster_whisper import WhisperModel
            print(f"[whisper] loading faster-whisper '{WHISPER_MODEL}' ({WHISPER_DEVICE}, {WHISPER_COMPUTE}). "
                  "The first run downloads the model, please wait...")
            model = WhisperModel(WHISPER_MODEL, device=WHISPER_DEVICE, compute_type=WHISPER_COMPUTE,
                                 cpu_threads=WHISPER_THREADS)
            kind = "faster"
        except ImportError:
            import whisper as openai_whisper                      # the older "openai-whisper" package
            print(f"[whisper] loading openai-whisper '{WHISPER_MODEL}' (slower than faster-whisper)...")
            model = openai_whisper.load_model(WHISPER_MODEL, device=WHISPER_DEVICE)
            kind = "openai"
        WHISPER = (kind, model)
        _whisper_state = "ready"
        print("[whisper] ready")
        add_message(jarvis_msg=f"Speech engine ready: Whisper {WHISPER_MODEL}.", speak=False)
    except ImportError as e:
        _whisper_state = "failed"
        print(f"[whisper] not installed ({e}). Install it with:  pip install faster-whisper")
        add_message(jarvis_msg="Whisper is not installed, so the microphone uses Google. Install it with: pip install faster-whisper",
                    speak=False)
    except Exception as e:
        _whisper_state = "failed"
        print(f"[whisper] could not start: {e}")
        add_message(jarvis_msg="Whisper could not start, so the microphone uses Google or Vosk. Check the terminal.", speak=False)


def whisper_text(audio):
    """One recorded phrase -> text. Raises UnknownValueError when there is nothing real to hear."""
    import numpy as np
    kind, model = WHISPER
    raw = audio.get_raw_data(convert_rate=16000, convert_width=2)
    pcm = np.frombuffer(raw, dtype=np.int16).astype(np.float32) / 32768.0
    if len(pcm) < 16000 * 0.3:                                    # shorter than 0.3 seconds
        raise sr.UnknownValueError()
    if float(np.sqrt(np.mean(pcm * pcm))) < 0.0015:               # silence / hiss: Whisper would invent words
        raise sr.UnknownValueError()

    # the command-word prompt helps with accents, but is NOT used for passwords
    prompt = None if (jarvis_locked or awaiting_password) else WHISPER_PROMPT
    parts = []
    if kind == "faster":
        segments, _info = model.transcribe(
            pcm, language="en", beam_size=5, temperature=0.0, condition_on_previous_text=False,
            vad_filter=True, vad_parameters={"min_silence_duration_ms": 400, "speech_pad_ms": 200},
            initial_prompt=prompt, without_timestamps=True)
        for seg in segments:
            if seg.no_speech_prob > 0.7 and seg.avg_logprob < -0.8:
                continue
            parts.append(seg.text)
    else:
        res = model.transcribe(pcm, language="en", fp16=False, temperature=0.0,
                               condition_on_previous_text=False, initial_prompt=prompt)
        for seg in res.get("segments", []):
            if seg.get("no_speech_prob", 0) > 0.7 and seg.get("avg_logprob", 0) < -0.8:
                continue
            parts.append(seg.get("text", ""))

    text = " ".join(" ".join(parts).split())
    text = text.replace("\u2019", "'").replace("\u2018", "'").encode("ascii", "ignore").decode().strip()
    plain = re.sub(r"[^a-z0-9' ]", "", text.lower()).strip()
    if (not re.search(r"[a-z0-9]", plain) or plain in _WHISPER_JUNK or "amara.org" in plain
            or "subscribe" in plain or plain.startswith("jarvis voice commands")):
        raise sr.UnknownValueError()
    return text


def speech_engine_text():
    if WHISPER is not None:
        return f"I am listening with Whisper {WHISPER_MODEL}, offline."
    if _whisper_state == "loading":
        return "Whisper is still loading. I am using Google for now."
    if STT_MODE == "vosk" and VOSK_MODEL is not None:
        return "I am listening with Vosk, offline."
    return "I am listening with Google" + (", and Vosk when you are offline." if VOSK_MODEL is not None else ".")


def transcribe(recognizer, audio):
    """Order: Whisper (offline, best with accents) -> Google (online) -> Vosk (offline).
      auto    -> Whisper once it is loaded, Google/Vosk until then or if Whisper is missing
      whisper -> same as auto
      google  -> online only        vosk -> offline only"""
    global _google_down_until

    if STT_MODE in ("auto", "whisper") and WHISPER is not None:
        return whisper_text(audio)

    if STT_MODE == "vosk" and VOSK_MODEL is not None:
        return vosk_text(audio)

    if STT_MODE in ("auto", "google", "vosk", "whisper") and time.time() >= _google_down_until:
        try:
            return google_best(recognizer, audio)
        except sr.RequestError as e:
            _google_down_until = time.time() + 30      # skip Google for 30s so we do not wait on a dead connection
            if VOSK_MODEL is not None:
                print(f"[stt] Google unavailable ({e}); using offline Vosk for a while")
                return vosk_text(audio)
            raise

    if VOSK_MODEL is not None:
        return vosk_text(audio)

    # Google was marked down, but there is no offline model: try Google again anyway
    return google_best(recognizer, audio)


threading.Thread(target=load_whisper, daemon=True).start()


# =====================================================================
# SMART UNDERSTANDING: works even when your English is not perfect
# =====================================================================
ALIASES_FILE = os.path.join(JARVIS_DIR, "aliases.json")
if not os.path.exists(ALIASES_FILE):
    try:
        with open(ALIASES_FILE, "w", encoding="utf-8") as f:
            json.dump({
                "make sound big": "increase the volume",
                "make screen dark": "decrease the brightness",
            }, f, indent=2)
    except Exception:
        pass


def load_aliases():
    """~/.jarvis/aliases.json : your own words -> a command Jarvis already knows."""
    try:
        with open(ALIASES_FILE, "r", encoding="utf-8") as f:
            data = json.load(f)
        return data if isinstance(data, dict) else {}
    except Exception:
        return {}


_I_UP = {"up", "increase", "raise", "higher", "louder", "more", "bigger", "big", "loud",
       "boost", "add", "plus", "high", "maximum", "max", "grow", "increasing"}
_I_DOWN = {"down", "decrease", "lower", "less", "reduce", "quieter", "smaller", "small",
         "soft", "minus", "low", "quiet", "dim", "dimmer", "drop", "decreasing", "reducing"}
_SOUND = {"volume", "sound", "audio", "speaker", "speakers", "loudness", "sounds"}
_BRIGHT = {"brightness", "bright", "light", "screen", "display", "dim", "dimmer", "brighter"}
_I_OPEN = {"open", "launch", "start", "run", "begin", "show", "want", "need", "opening"}
_OFF = {"off", "disable", "stop", "disconnect", "close"}
_ON = {"on", "enable", "connect", "start"}

# (command to run, [word groups that must ALL match], ask first?, confidence factor)
SMART_INTENTS = [
    ("increase the volume", [_I_UP, _SOUND], False, 1.0),
    ("decrease the volume", [_I_DOWN, _SOUND], False, 1.0),
    ("increase the volume", [{"louder", "loud"}], False, 1.0),
    ("decrease the volume", [{"quieter", "softer"}], False, 1.0),
    ("mute", [{"mute", "silence", "unmute"}], False, 1.0),
    ("increase the brightness", [_I_UP, _BRIGHT], False, 1.0),
    ("decrease the brightness", [_I_DOWN, _BRIGHT], False, 1.0),
    ("increase the brightness", [{"brighter", "brightest"}], False, 1.0),

    ("open firefox", [_I_OPEN, {"firefox", "browser", "internet", "mozilla"}], False, 1.0),
    ("open text editor", [_I_OPEN, {"editor", "notepad", "gedit", "text"}], False, 1.0),
    ("open visual studio code", [_I_OPEN, {"code", "coding", "vscode", "studio", "programming", "visual"}], False, 1.0),
    ("open settings", [_I_OPEN, {"settings", "setting", "preferences", "configuration", "options"}], False, 1.0),
    ("open calculator", [_I_OPEN, {"calculator", "calculate", "calculation", "math", "maths"}], False, 1.0),
    ("open terminal", [_I_OPEN, {"terminal", "console", "command", "shell"}], False, 1.0),
    ("open downloads", [_I_OPEN, {"downloads", "download"}], False, 1.0),
    ("open files", [_I_OPEN, {"files", "file", "folder", "folders", "manager", "explorer"}], False, 1.0),
    ("open youtube", [_I_OPEN, {"youtube", "video", "videos"}], False, 1.0),
    ("open whatsapp", [_I_OPEN, {"whatsapp", "whatsup", "messages", "chat"}], False, 1.0),
    # only the app word, no "open": ask first
    ("open firefox", [{"firefox", "mozilla"}], True, 0.7),
    ("open calculator", [{"calculator"}], True, 0.7),
    ("open terminal", [{"terminal"}], True, 0.7),
    ("open settings", [{"settings"}], True, 0.7),
    ("open youtube", [{"youtube"}], True, 0.7),

    ("what time is it", [{"time", "clock", "hour", "oclock"}], False, 1.0),
    ("what is the date", [{"date", "calendar", "month"}], False, 1.0),
    ("what is the weather", [{"weather", "temperature", "rain", "raining", "sunny", "forecast", "climate"}], False, 1.0),
    ("tell me the news", [{"news", "headlines", "newspaper", "updates"}], False, 1.0),
    ("battery status", [{"battery", "charge", "charging", "charger"}], False, 1.0),
    ("take a screenshot", [{"screenshot", "screenshots", "capture", "snapshot"}], False, 1.0),
    ("cpu usage", [{"cpu", "processor", "performance", "memory", "usage"}], False, 1.0),
    ("what is my ip address", [{"ip"}], False, 1.0),
    ("who are you", [{"who", "name", "introduce"}, {"you", "yourself", "your"}], False, 1.0),
    ("what can you do", [{"help", "abilities", "features", "commands", "capable", "skills"}], False, 1.0),
    ("read my notes", [{"read", "show", "tell", "list"}, {"notes", "note"}], False, 1.0),
    ("run diagnostics", [{"diagnostics", "diagnostic", "check", "test"}, {"system", "systems", "yourself", "self"}], False, 1.0),
    ("next song", [{"next", "skip", "forward"}, {"song", "track", "music", "songs"}], False, 1.0),
    ("previous song", [{"previous", "back", "last"}, {"song", "track", "music", "songs"}], False, 1.0),
    ("pause music", [{"pause", "resume"}, {"music", "song", "songs", "media", "video"}], False, 1.0),

    # these change your system, so Jarvis always asks first
    ("lock screen", [{"lock", "secure", "sleep"}, {"screen", "computer", "pc", "laptop"}], True, 1.0),
    ("turn off wifi", [{"wifi", "wireless"}, _OFF], True, 1.0),
    ("turn on wifi", [{"wifi", "wireless"}, _ON], True, 1.0),
    ("turn off bluetooth", [{"bluetooth"}, _OFF], True, 1.0),
    ("turn on bluetooth", [{"bluetooth"}, _ON], True, 1.0),
]

_SEARCH_WORDS = {"search", "find", "google", "lookup", "seach", "serch", "searching", "browse", "look"}
_SEARCH_FILLER = {"me", "for", "about", "on", "the", "internet", "web", "online", "please", "up", "a", "some"}

# words that look like command words but are normal English: never "correct" these
_PROTECT = {"right", "night", "might", "sight", "fight", "write", "white", "quite", "where",
            "there", "these", "those", "which", "while", "would", "could", "should", "about",
            "other", "their", "first", "water", "think", "thing", "things", "today", "please"}


def _build_vocab():
    words = set()
    for _, groups, _, _ in SMART_INTENTS:
        for g in groups:
            words |= g
    for ph in KNOWN_PHRASES:
        words |= set(ph.split())
    return words


_VOCAB = _build_vocab()
_VOCAB_LONG = sorted(w for w in _VOCAB if len(w) >= 5)


def fix_words(text):
    """Fix misspelled or mis-heard command words: 'volum' -> 'volume', 'brightnes' -> 'brightness'."""
    t = fix_mishearings(text)
    out = []
    for w in t.split():
        if len(w) >= 5 and w not in _VOCAB and w not in _PROTECT:
            close = difflib.get_close_matches(w, _VOCAB_LONG, n=1, cutoff=0.84)
            if close:
                w = close[0]
        out.append(w)
    return " ".join(out)


def _word_score(w, group):
    if w in group:
        return 1.0
    if len(w) < 5:
        return 0.0
    best = 0.0
    for g in group:
        if len(g) >= 5:
            r = difflib.SequenceMatcher(None, w, g).ratio()
            if r > best:
                best = r
    return best if best >= 0.82 else 0.0


def _intent_score(words, groups, factor):
    scores = []
    for g in groups:
        sc = max((_word_score(w, g) for w in words), default=0.0)
        if sc == 0.0:
            return 0.0
        scores.append(sc)
    return (sum(scores) / len(scores)) * factor


def smart_resolve(text):
    """Find the command you most likely meant. Returns (command, ask_first) or None."""
    t = re.sub(r"[^a-z0-9' ]", " ", text.lower())
    words = t.split()
    if not words:
        return None
    clean = " ".join(words)

    # 1. your own words (~/.jarvis/aliases.json)
    for phrase, target in load_aliases().items():
        ph = str(phrase).lower().strip()
        if ph and (ph in clean or difflib.SequenceMatcher(None, clean, ph).ratio() >= 0.85):
            return str(target), False

    # 2. "find me cat videos", "serch black holes" -> search
    if len(words) >= 2 and _word_score(words[0], _SEARCH_WORDS) >= 0.82:
        query = " ".join(w for w in words[1:] if w not in _SEARCH_FILLER)
        if query:
            return "search for " + query, False

    # 3. related words: "make sound big" -> increase the volume
    best = None
    for canon, groups, ask, factor in SMART_INTENTS:
        sc = _intent_score(words, groups, factor)
        if sc > 0 and (best is None or sc > best[0]):
            best = (sc, canon, ask)
    if best and best[0] >= 0.6:
        sc, canon, ask = best
        return canon, (ask or sc < 0.9)
    return None


def is_echo(text):
    """True if the text is just Jarvis hearing his own recent reply."""
    t = text.lower().strip(" .!?,")
    tw = len(t.split())
    now = time.time()
    for ts, r in recent_replies:
        if now - ts > 15:
            continue
        rw = len(r.split())
        if rw >= 2 and tw >= 2 and (t == r or t in r or r in t):
            return True
    return False


_mic_ok = False


def mic_preflight():
    """Test PyAudio in a child process. A PortAudio crash there cannot kill the app."""
    global _mic_ok
    if _mic_ok:
        return True, ""
    code = ("import pyaudio\n"
            "p = pyaudio.PyAudio()\n"
            "info = p.get_default_input_device_info()\n"
            "print(info.get('name'))\n"
            "p.terminate()\n")
    try:
        r = subprocess.run([sys.executable, "-c", code],
                           capture_output=True, text=True, timeout=20)
    except Exception as e:
        return False, f"Microphone check failed: {e}"
    if r.returncode == 0:
        _mic_ok = True
        print(f"Microphone OK: {r.stdout.strip()}")
        return True, ""
    return False, ("No usable microphone: PortAudio crashed or found no input device. "
                   "Check 'wpctl status' shows a microphone, then try: "
                   "sudo dnf install pipewire-alsa alsa-plugins-pulseaudio")


def list_mics():
    """Names of the microphones, read in a child process (a PortAudio crash cannot kill Jarvis)."""
    code = ("import speech_recognition as sr\n"
            "for i, n in enumerate(sr.Microphone.list_microphone_names()):\n"
            "    print(f'{i}: {n}')\n")
    try:
        r = subprocess.run([sys.executable, "-c", code], capture_output=True, text=True, timeout=20)
        if r.returncode != 0:
            print((r.stderr or "").strip()[-400:])
            return "Could not list the microphones. Check the terminal."
        return r.stdout.strip() or "No microphones found."
    except Exception as e:
        return f"Could not list microphones: {e}"


def _open_mic():
    return sr.Microphone(device_index=MIC_INDEX) if MIC_INDEX is not None else sr.Microphone()


def handle_audio(recognizer, audio):
    """One recorded phrase -> command. An error here can NEVER turn the microphone off."""
    try:
        text = transcribe(recognizer, audio).strip()

        if not text or speaking_event.is_set() or is_echo(text):
            return
        print(f"[heard] {redact_for_log(text)}")

        if WAKE_WORD_ENABLED:
            lowered = text.lower()
            m = WAKE_RE.search(lowered)
            if m:
                activate_wake()
                command = (lowered[:m.start()] + " " + lowered[m.end():]).strip(" ,.!?")
                command = re.sub(r'\s+', ' ', command)
                if not command:
                    wake_ack()
                    return
                text = command
            elif not is_awake():
                print("[asleep] ignored (say \"Hey Jarvis\" first)")
                return

        add_message(user_msg=redact_for_log(text))
        response = execute_command(text)
        if response != UNKNOWN:
            add_message(jarvis_msg=response)
        if session_active:
            extend_awake(FOLLOWUP_SECONDS)

    except sr.UnknownValueError:
        if MIC_DEBUG:
            print("[mic] sound detected but could not be understood")
    except sr.RequestError as e:
        print(f"Speech service error (check internet, or install Whisper / use Vosk): {e}")
        time.sleep(1)
    except Exception as e:
        print(f"[voice] error while handling that phrase: {e!r}")


def listening_worker():
    global system_status, mic_active
    recognizer = sr.Recognizer()
    recognizer.dynamic_energy_threshold = True
    recognizer.operation_timeout = 8        # do not hang when the internet is slow
    recognizer.pause_threshold = 0.9        # a little longer, so "open ... firefox" is not cut in the middle
    recognizer.non_speaking_duration = 0.5
    echo_guard = 1.2                        # ignore a phrase that ends within this many seconds after Jarvis stopped talking

    calibrated = False
    quiet = 0
    fails = 0

    while True:
        with state_lock:
            current_mic = mic_active

        if not current_mic or speaking_event.is_set():
            time.sleep(0.2)
            continue

        if not calibrated:
            ok, msg = mic_preflight()
            if not ok:
                print(msg)
                with state_lock:
                    mic_active = False
                save_state()
                add_message(jarvis_msg="I cannot use the microphone. Check the terminal for details.")
                continue

        try:
            # FIX: the microphone is opened ONCE and stays open between phrases. Before, it was closed and
            # re-opened every few seconds, and the first words you said while it re-opened were lost.
            with _open_mic() as source:
                if not calibrated:
                    try:
                        recognizer.adjust_for_ambient_noise(source, duration=1.0)     # once only
                        recognizer.energy_threshold = min(recognizer.energy_threshold, 600)  # never deaf to normal speech
                    except Exception as e:
                        print(f"Microphone calibration skipped: {e}")
                    calibrated = True
                    if MIC_DEBUG:
                        print(f"[mic] speech: {STT_MODE} (Whisper {_whisper_state}, "
                              f"{'Vosk ready' if VOSK_MODEL is not None else 'no Vosk'}) language {SPEECH_LANG} | "
                              f"energy threshold {int(recognizer.energy_threshold)} | "
                              f"wake word {'ON: say Hey Jarvis' if WAKE_WORD_ENABLED else 'OFF'}")
                fails = 0

                # keep listening until the mic is switched off or Jarvis starts talking (then close it, so he cannot hear himself)
                while mic_active and not speaking_event.is_set():
                    with state_lock:
                        system_status = "LISTENING"
                    try:
                        audio = recognizer.listen(source, timeout=2, phrase_time_limit=12)
                    except sr.WaitTimeoutError:
                        quiet += 1
                        if MIC_DEBUG and quiet == 8:
                            print(f"[mic] no speech picked up for 16s (threshold {int(recognizer.energy_threshold)}). "
                                  "If you are talking, your mic volume is too low or muted, or pick another mic: say 'list microphones'.")
                        continue
                    quiet = 0

                    # Jarvis' own voice (or its tail) is not a command
                    if speaking_event.is_set() or time.time() - last_speech_end < echo_guard:
                        continue
                    handle_audio(recognizer, audio)

        except Exception as e:
            fails += 1
            print(f"[mic] problem ({fails}/5): {e}")
            if fails >= 5:
                with state_lock:
                    mic_active = False
                save_state()
                fails = 0
                add_message(jarvis_msg="The microphone keeps failing, so I switched it off. Check the terminal, then press MIC.")
            time.sleep(min(2 * fails, 8))


threading.Thread(target=listening_worker, daemon=True).start()


# =====================================================================
# AUTO ALERTS (battery / CPU)
# =====================================================================
def monitor_worker():
    battery_alerted = False
    cpu_high_since = None
    cpu_alerted = False

    while True:
        time.sleep(5)
        try:
            bat = psutil.sensors_battery() if hasattr(psutil, "sensors_battery") else None
            if bat is not None:
                if not bat.power_plugged and bat.percent <= 15 and not battery_alerted:
                    battery_alerted = True
                    add_message(jarvis_msg=f"Warning. Battery is at {round(bat.percent)} percent. Please plug in the charger.")
                elif bat.power_plugged or bat.percent > 20:
                    battery_alerted = False

            cpu = psutil.cpu_percent(interval=None)
            if cpu >= 90:
                if cpu_high_since is None:
                    cpu_high_since = time.time()
                elif time.time() - cpu_high_since > 60 and not cpu_alerted:
                    cpu_alerted = True
                    add_message(jarvis_msg="Warning. CPU usage has been very high for over a minute.")
            else:
                cpu_high_since = None
                cpu_alerted = False
        except Exception:
            pass


if AUTO_ALERTS:
    threading.Thread(target=monitor_worker, daemon=True).start()


# =====================================================================
# REST API FOR THE FRONTEND
# =====================================================================
UI_SETTINGS_FILE = os.path.join(JARVIS_DIR, "ui_settings.json")   # your whole customize panel, saved here


def load_ui_settings():
    try:
        with open(UI_SETTINGS_FILE, "r", encoding="utf-8") as f:
            data = json.load(f)
        return data if isinstance(data, dict) else {}
    except Exception:
        return {}


@app.route('/api/settings', methods=['GET', 'POST'])
def ui_settings():
    """The frontend saves its full settings here, so they survive restarts (the desktop window forgets localStorage)."""
    if request.method == 'POST':
        data = request.get_json(silent=True)
        if not isinstance(data, dict):
            return jsonify({"error": "bad data"}), 400
        out = {}
        if isinstance(data.get("jarvis3d_cfg"), dict):
            out["jarvis3d_cfg"] = data["jarvis3d_cfg"]
        if isinstance(data.get("jarvis_cmds"), list):
            out["jarvis_cmds"] = data["jarvis_cmds"][:50]
        raw = json.dumps(out)
        if len(raw) > 400000:
            return jsonify({"error": "too big"}), 413
        tmp = UI_SETTINGS_FILE + ".tmp"
        with open(tmp, "w", encoding="utf-8") as f:
            f.write(raw)
        os.replace(tmp, UI_SETTINGS_FILE)
        return jsonify({"ok": True})
    return jsonify(load_ui_settings())


@app.route('/')
def serve_frontend():
    html_file = resource_path('index.html')
    if not os.path.exists(html_file):
        return (f"index.html not found. Put it in the same folder as app.py:<br>{html_file}", 404)
    with open(html_file, 'r', encoding='utf-8') as f:
        html = f.read()
    try:
        blob = dict(load_ui_settings())
        blob["_locked"] = bool(jarvis_locked)          # so a locked Jarvis opens locked
        html = html.replace("/*SRV*/null", json.dumps(blob).replace("</", "<\\/"), 1)
    except Exception as e:
        print(f"Could not inject saved settings: {e}")
    return html, 200, {"Content-Type": "text/html; charset=utf-8", "Cache-Control": "no-store"}


@app.route('/three.min.js')
def serve_three():
    """Optional offline copy of three.js (save it next to app.py as three.min.js)."""
    path = resource_path('three.min.js')
    if not os.path.exists(path):
        return ("", 404)
    with open(path, 'rb') as f:
        return f.read(), 200, {"Content-Type": "application/javascript"}


@app.route('/api/poll', methods=['GET'])
def poll():
    since_id = request.args.get('since', 0, type=int)
    with state_lock:
        new_items = [m for m in messages if m["id"] > since_id]
        current_status = system_status
        mic = mic_active
    return jsonify({
        "status": current_status,
        "items": new_items,
        "mic_active": mic,
        "awake": is_awake() if mic else False,   # True after "Hey Jarvis"
        "wake_id": wake_id,                      # increases on every wake-up
        "speaking": speaking_event.is_set(),
        "ui": ui_prefs,                          # saved look of the UI (theme ...)
        "speak_enabled": speak_enabled,
        "awaiting_password": awaiting_password,   # the UI masks the input while True
        "locked": jarvis_locked,                 # lets the UI show a lock screen
        "mode": current_mode,                    # lets the UI change theme per transform mode
    })


@app.route('/api/sysinfo', methods=['GET'])
def sysinfo():
    bat = psutil.sensors_battery() if hasattr(psutil, "sensors_battery") else None
    return jsonify({
        "cpu": psutil.cpu_percent(interval=None),
        "ram": psutil.virtual_memory().percent,
        "disk": shutil.disk_usage("/").used / shutil.disk_usage("/").total * 100,
        "battery": round(bat.percent) if bat else None,
        "plugged": bat.power_plugged if bat else None,
    })


@app.route('/api/toggle_mic', methods=['POST'])
def toggle_mic():
    global mic_active
    with state_lock:
        mic_active = not mic_active
        current_mic = mic_active

    if current_mic:
        if WAKE_WORD_ENABLED:
            add_message(jarvis_msg="Audio input active. Say Hey Jarvis to wake me.")
        else:
            add_message(jarvis_msg="Audio input active.")
    else:
        add_message(jarvis_msg="Audio input deactivated.")

    save_state()
    return jsonify({"mic_active": current_mic})


@app.route('/api/wake', methods=['POST'])
def force_wake():
    """Lets the UI wake Jarvis with a button, same as saying 'Hey Jarvis'."""
    activate_wake()
    return jsonify({"awake": True, "wake_id": wake_id})


@app.route('/api/ui', methods=['GET', 'POST'])
def ui_state():
    """The frontend saves/loads its look here (theme etc.) so Jarvis reopens the way you left it."""
    if request.method == 'POST':
        data = request.get_json(silent=True) or {}
        if isinstance(data, dict):
            for k, v in list(data.items())[:30]:
                if (isinstance(k, str) and 0 < len(k) <= 40
                        and (v is None or isinstance(v, (bool, int, float))
                             or (isinstance(v, str) and len(v) <= 200))):
                    ui_prefs[k] = v
            save_state()
    return jsonify(ui_prefs)


@app.route('/api/stop_speaking', methods=['POST'])
def api_stop_speaking():
    stop_speaking()
    return jsonify({"ok": True})


@app.route('/api/command', methods=['POST'])
def handle_typed_command():
    data = request.get_json(silent=True) or {}
    raw_text = str(data.get('command', '')).strip()

    if not raw_text:
        return jsonify({"error": "Command cannot be empty."}), 400

    add_message(user_msg=redact_for_log(raw_text))

    try:
        response_text = execute_command(raw_text)
        if not isinstance(response_text, str):
            response_text = str(response_text)
    except Exception as exc:
        print(f"Command error: {exc}")
        response_text = "Command execution failed. Check the system log."

    # FIX: typed commands now get a spoken reply too (the frontend can send {"speak": false} to skip it)
    speak = bool(data.get("speak", SPEAK_TYPED_REPLIES))
    add_message(jarvis_msg=response_text, speak=speak)

    return jsonify({"ok": True, "response": response_text, "spoken": speak,
                    "locked": jarvis_locked, "awaiting_password": awaiting_password})


def start_flask():
    app.run(host='127.0.0.1', port=5000, threaded=True, debug=False, use_reloader=False)


STARTUP_MESSAGES = [
    "JARVIS Core initialized. The Silent Exploit Base Project for learning online.",
    "All systems awake. The Silent Exploit Base Project for learning is now live.",
    "JARVIS core is up and running. The Silent Exploit Base learning project is online.",
    "Boot sequence complete. The Silent Exploit Base Project for learning is active.",
    "Core systems online. Welcome to The Silent Exploit Base, a project for learning.",
    "I am awake. The Silent Exploit Base Project for learning is ready.",
]
_last_startup = None


def get_startup_message():
    """Same meaning every time, different words (never the same one twice in a row)."""
    global _last_startup
    choices = [m for m in STARTUP_MESSAGES if m != _last_startup]
    _last_startup = random.choice(choices)
    return _last_startup


def get_greeting():
    hour = datetime.datetime.now().hour

    if 5 <= hour < 12:
        greeting = "Good morning"
        message = "Yo bro, ready to get things done? What's the move?"
    elif 12 <= hour < 17:
        greeting = "Good afternoon"
        message = "What's up, bro? What are we working on today?"
    elif 17 <= hour < 21:
        greeting = "Good evening"
        message = "Yo bro, how's it going? What's the plan?"
    else:
        greeting = "Hey"
        message = "Still grinding, bro? What do you need?"

    name = ""
    return f"{greeting}{name}! {message}"


if __name__ == '__main__':
    threading.Thread(target=run_diagnostics, daemon=True).start()
    add_message(jarvis_msg=get_startup_message())
    add_message(jarvis_msg=get_greeting())

    threading.Thread(target=start_flask, daemon=True).start()

    if webview is None or "--browser" in sys.argv:
        time.sleep(1.5)
        print("Open http://127.0.0.1:5000 (opening your browser now). Press Ctrl+C to quit.")
        webbrowser.open("http://127.0.0.1:5000/")
        try:
            while True:
                time.sleep(1)
        except KeyboardInterrupt:
            sys.exit(0)

    for _ in range(60):                       # wait until the server is really up (avoids a blank window)
        try:
            socket.create_connection(("127.0.0.1", 5000), timeout=0.2).close()
            break
        except OSError:
            time.sleep(0.1)

    webview.create_window(
        'JARVIS Core',
        'http://127.0.0.1:5000/',
        width=1366,
        height=768,
        background_color="#050a10"
    )
    try:
        # keep the window's storage between runs (the default is a throw-away private window)
        webview.start(private_mode=False, storage_path=os.path.join(JARVIS_DIR, "webview"))
    except TypeError:
        webview.start()