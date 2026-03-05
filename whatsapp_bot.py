# -*- coding: utf-8 -*-
"""
WhatsApp Bot (Hebrew) – deterministic ranking + learning over time (no external AI)
- Supports RTL typing in Tkinter Entry fields (stable cursor)
- Chooses easiest available item in "who brings what" lists
- Learns over time via learn_stats.json (items + categories + tokens) with decay
"""

import os
import re
import time
import json
import hashlib
import threading
from dataclasses import dataclass, asdict
from typing import List, Dict, Set, Optional, Tuple
from datetime import datetime

import pyperclip

import selenium  # noqa: F401
import selenium.webdriver  # noqa: F401
import selenium.webdriver.chrome.webdriver  # noqa: F401

from selenium import webdriver
from selenium.webdriver.chrome.options import Options
from selenium.webdriver.chrome.service import Service
from webdriver_manager.chrome import ChromeDriverManager

from selenium.webdriver.common.by import By
from selenium.webdriver.common.keys import Keys
from selenium.webdriver.common.action_chains import ActionChains

from selenium.webdriver.support.ui import WebDriverWait
from selenium.webdriver.support import expected_conditions as EC
from selenium.common.exceptions import TimeoutException

import tkinter as tk
from tkinter import messagebox, scrolledtext


# =========================
# Files / constants
# =========================
CONFIG_FILE = "config.json"
LOG_FILE = "bot.log"
LEARN_FILE = "learn_stats.json"
DEFAULT_PROFILE_DIR = r"C:\temp\whatsapp_bot_profile"

RLM = "\u200F"  # Right-to-left mark
DASH_CHARS = "[-‐-‒–—―־]"  # includes Hebrew maqaf (־)

HEB_RE = re.compile(r"[\u0590-\u05FF]")  # Hebrew (incl. niqqud)
TOKEN_RE = re.compile(r"[א-ת0-9]+", re.UNICODE)


# =========================
# Logging / normalization
# =========================
def _ts() -> str:
    return datetime.now().strftime("%Y-%m-%d %H:%M:%S")


def log_simple(msg: str, ui_log=None) -> None:
    line = f"[{_ts()}] {msg}"
    try:
        with open(LOG_FILE, "a", encoding="utf-8") as f:
            f.write(line + "\n")
    except Exception:
        pass

    if ui_log is not None:
        try:
            ui_log.insert(tk.END, line + "\n", "rtl")
            ui_log.see(tk.END)
            ui_log.update_idletasks()
        except Exception:
            pass


def normalize_text(s: str) -> str:
    if s is None:
        return ""
    s = str(s)
    # strip bidi controls that break matching/scoring
    for ch in ["\u200f", "\u200e", "\u202a", "\u202b", "\u202c", "\u2066", "\u2067", "\u2068", "\u2069"]:
        s = s.replace(ch, "")
    s = s.replace("\u00a0", " ")
    s = re.sub(DASH_CHARS, "-", s)
    s = s.strip().lower()
    s = re.sub(r"\s+", " ", s)
    return s


# =========================
# Config
# =========================
@dataclass
class BotConfig:
    group_keywords: List[str]
    name_to_insert: str
    trigger_phrases: List[str]
    scan_interval_seconds: int = 6
    lookback_messages: int = 30
    profile_dir: str = DEFAULT_PROFILE_DIR


def load_config() -> Optional[BotConfig]:
    if not os.path.exists(CONFIG_FILE):
        return None
    try:
        with open(CONFIG_FILE, "r", encoding="utf-8") as f:
            data = json.load(f)
        return BotConfig(**data)
    except Exception:
        return None


def save_config(cfg: BotConfig) -> None:
    with open(CONFIG_FILE, "w", encoding="utf-8") as f:
        json.dump(asdict(cfg), f, ensure_ascii=False, indent=2)


# =========================
# “Learning” store (no external AI)
# =========================
def _now_ts() -> float:
    return time.time()


def load_learn_stats() -> dict:
    """
    {
      "items": {"מפיות": 3.0, ...},
      "cats":  {"0": 5.0, "4": 1.0, ...},
      "tokens":{"פלטת": 2.0, "ירקות": 2.0, ...},
      "last_ts": 1710000000.0
    }
    """
    if not os.path.exists(LEARN_FILE):
        return {"items": {}, "cats": {}, "tokens": {}, "last_ts": _now_ts()}
    try:
        with open(LEARN_FILE, "r", encoding="utf-8") as f:
            d = json.load(f)
        if not isinstance(d, dict):
            raise ValueError("bad learn stats")
        d.setdefault("items", {})
        d.setdefault("cats", {})
        d.setdefault("tokens", {})
        d.setdefault("last_ts", _now_ts())
        return d
    except Exception:
        return {"items": {}, "cats": {}, "tokens": {}, "last_ts": _now_ts()}


def save_learn_stats(d: dict) -> None:
    try:
        with open(LEARN_FILE, "w", encoding="utf-8") as f:
            json.dump(d, f, ensure_ascii=False, indent=2)
    except Exception:
        pass


def decay_counts(d: dict, half_life_days: float = 30.0) -> dict:
    """
    Exponential decay so old behavior doesn't dominate forever.
    half_life_days=30 means after ~30 days counts halve.
    """
    try:
        last = float(d.get("last_ts", _now_ts()))
    except Exception:
        last = _now_ts()

    now = _now_ts()
    dt_days = max(0.0, (now - last) / 86400.0)
    if dt_days <= 0:
        return d

    factor = 0.5 ** (dt_days / max(1e-6, half_life_days))

    def _decay_map(m):
        out = {}
        for k, v in (m or {}).items():
            try:
                nv = float(v) * factor
            except Exception:
                continue
            if nv >= 0.25:
                out[k] = nv
        return out

    d["items"] = _decay_map(d.get("items", {}))
    d["cats"] = _decay_map(d.get("cats", {}))
    d["tokens"] = _decay_map(d.get("tokens", {}))
    d["last_ts"] = now
    return d


def tokenize_item(name: str) -> List[str]:
    s = normalize_text(name)
    toks = TOKEN_RE.findall(s)
    # Keep it focused; prevent noisy general tokens
    stop = {"של", "עם", "או", "וגם", "ו", "את", "על", "המ", "ה", "זה", "זו", "מגש", "מגשי"}
    out = []
    for t in toks:
        if len(t) < 3:
            continue
        if t in stop:
            continue
        out.append(t)
    return out


# =========================
# Signup list parsing / utilities
# =========================
def already_assigned(text: str, name: str) -> bool:
    return re.search(rf"{DASH_CHARS}\s*{re.escape(name)}\s*$", text, flags=re.MULTILINE) is not None


def fingerprint_text(text: str) -> str:
    norm = text.strip().replace("\r\n", "\n")
    return hashlib.sha1(norm.encode("utf-8")).hexdigest()


def is_item_line(line: str) -> bool:
    ln = normalize_text(line)
    if not ln:
        return False
    if "מי מביא" in ln or "מי מביאה" in ln or "נא להירשם" in ln:
        return False
    if re.search(r"[-:]", ln):
        return True
    if len(ln) <= 35 and not re.search(r"[.?!]$", ln):
        return True
    return False


def is_empty_item_line(line: str) -> bool:
    ln = normalize_text(line)
    if not ln:
        return False
    if re.search(r"[-:]\s*$", ln):
        return True
    if re.search(r"^.+\s*[-:]\s*.+$", ln):
        return False
    if is_item_line(ln) and not re.search(r"[-:]", ln):
        return True
    return False


def extract_item_name(line: str) -> str:
    ln = normalize_text(line)
    m = re.search(r"^(.*?)([-:])\s*(.*)$", ln)
    if not m:
        return ln
    return m.group(1).strip()


def normalize_and_merge_lines(lines: List[str]) -> List[str]:
    """
    Merges small continuation lines starting with 'ו' into previous empty-item line.
    Helps with WhatsApp line breaks that split items.
    """
    out: List[str] = []
    for raw in lines:
        ln = (raw or "").strip()
        if not ln:
            out.append("")
            continue
        if out:
            prev = (out[-1] or "").rstrip()
            if ln.startswith("ו") and len(normalize_text(ln)) <= 25 and is_item_line(prev) and is_empty_item_line(prev):
                prev_name = extract_item_name(prev).strip()
                merged = f"{prev_name} {ln}".replace("  ", " ").strip()
                if re.search(rf"{DASH_CHARS}\s*$", prev):
                    merged = merged.rstrip("-").rstrip() + " -"
                out[-1] = merged
                continue
        out.append(ln)
    return out


def looks_like_signup_list(text: str) -> bool:
    if not text or len(text.strip()) < 10:
        return False
    lines = [ln.strip() for ln in text.splitlines() if ln.strip()]
    if len(lines) < 3:
        return False
    item_lines = [ln for ln in lines if is_item_line(ln)]
    empty_lines = [ln for ln in lines if is_empty_item_line(ln)]
    if len(lines) >= 4 and len(item_lines) >= 3:
        return True
    if len(empty_lines) >= 2:
        return True
    return False


def message_matches_triggers(message_text: str, triggers: List[str]) -> bool:
    return any(t.strip() and (t.strip() in message_text) for t in triggers)


# =========================
# Category logic (your preferences)
# - Platter easier than salad
# - Salad easier than cake/baking
# =========================
def classify_item(item_name: str) -> Tuple[int, int]:
    """
    (category_rank, base_score) -- lower is easier.

    0: חד"פ / אביזרים
    1: קנייה במכולת (לא מצריך קירור)
    2: קנייה במכולת + קירור
    3: כבד (משקאות/מים/קרח)
    4: פלטה / הרכבה בלי אש      (קל מסלט)
    5: סלט / חיתוך              (קל מאפייה)
    6: אפייה
    7: בישול
    8: טיגון
    9: לא ידוע
    """
    s = normalize_text(item_name)

    def has_any(words): return any(w in s for w in words)

    # 8) Frying
    fry_kw = [
        "לטגן", "טיגון", "מטוגן", "מטוגנות", "טיגון עמוק",
        "שניצל", "שניצלים", "צ'יפס", "ציפס", "לביבות", "לביבה",
        "סופגני", "פלאפל", "חציל מטוגן"
    ]
    if has_any(fry_kw):
        return 8, 90

    # 7) Cooking
    cook_kw = [
        "לבשל", "בישול", "מבושל", "תבשיל", "קדרה", "חמין",
        "מרק", "פסטה", "אורז", "תפו\"א", "תפוחי אדמה", "ממולא", "ממולאים",
        "קציצות ברוטב", "קציצות", "רוטב"
    ]
    if has_any(cook_kw):
        return 7, 80

    # 6) Baking
    bake_kw = [
        "לאפות", "אפייה", "אפה", "בתנור",
        "עוגה", "עוגת", "עוגיות", "מאפינס",
        "פשטיד", "קיש", "פאי", "לזניה", "פוקאצ", "בורקס", "מאפים"
    ]
    if has_any(bake_kw):
        # sub-ranking: pie/quiche/lasagna harder than cake
        if "פשטיד" in s or "קיש" in s or "לזניה" in s:
            return 6, 78
        if "עוג" in s:
            return 6, 72
        return 6, 76

    # 0) Disposable / accessories
    disposable_kw = [
        "מפיות", "כוסות", "צלחות",
        "סכום", "סכו\"ם", "סכו״ם", "מזלגות", "כפיות", "סכינים",
        "כלים חד פעמי", "כלים חד פעמיים", "כלים חד-פעמיים",
        "חד פעמי", "חד-פעמי", "חד פעמיים", "חד-פעמיים",
        "חד״פ", "חד'פ", "חדפ",
        "קשים", "מגבונים", "שקיות", "שקיות אשפה",
        "נייר", "נייר סופג", "נייר אפיה", "נייר אפייה",
        "רדיד", "אלומיניום", "ניילון נצמד", "פלסטיק נצמד",
        "מגש אלומיניום", "מגשים"
    ]
    if has_any(disposable_kw):
        return 0, 5

    # 3) Heavy / carry only (avoid triggering on "מי מביא")
    heavy_kw = [
        "מים", "בקבוק", "בקבוקי", "שישייה", "שישיות", "קרטון",
        "שתייה", "שתיה", "קולה", "סודה", "מיץ",
        "בירה", "יין", "קרח", "ארגז"
    ]
    if "מי מביא" not in s and "מי מביאה" not in s and has_any(heavy_kw):
        if "קרח" in s:
            return 3, 20
        return 3, 22

    # 4) Platter / assembly (must be before salad so "פלטת ירקות" doesn't fall to salad)
    platter_kw = [
        "פלטה", "פלטת", "מגש", "מגשי", "מגש אירוח",
        "פלטת ירקות", "פלטת פירות", "פלטת גבינות",
        "כריכונים", "סנדוויצ", "טורטיה", "טורטיות", "מגולגל",
        "קינוח בכוס", "כוסות קינוח", "טרייפל", "פינגר פוד"
    ]
    if has_any(platter_kw):
        return 4, 35

    # 5) Salad / cutting
    salad_kw = [
        "סלט", "לחתוך", "קצוץ", "קצוצים", "חתוך", "חתוכים",
        "חסה", "כרוב", "מלפפון", "עגבני", "גזר",
        "סלט ירקות", "סלט חסה"
    ]
    if has_any(salad_kw):
        return 5, 45

    # 2) Refrigerated grocery
    cold_kw = [
        "חומוס", "טחינה", "גבינה", "גבינות", "יוגורט", "שמנת", "חלב",
        "סלטים מוכנים", "מטבוחה", "חצילים", "כרוב מוכן",
        "נקניק", "נקניקים", "ביצים", "חמאה", "קינוח", "קינוחים"
    ]
    if has_any(cold_kw):
        return 2, 15

    # 1) Regular grocery
    grocery_kw = [
        "פיתות", "לחם", "חלה", "קרקרים", "בייגלה",
        "עוגיות", "שוקולד", "חטיפים", "במבה", "ביסלי",
        "פיצוחים", "שימורים", "טונה", "תירס", "מלפפון חמוץ",
        "דבש", "ריבה", "רטב", "רטבים"
    ]
    if has_any(grocery_kw) or (len(s) <= 25 and not re.search(r"[-:]", s)):
        return 1, 12

    return 9, 60


def learn_on_choice(item_name: str) -> None:
    """
    Update learn_stats.json:
    - item exact
    - category rank
    - tokens
    with decay so old history fades
    """
    item_name = (item_name or "").strip()
    if not item_name:
        return

    d = load_learn_stats()
    d = decay_counts(d, half_life_days=30.0)

    item_key = normalize_text(item_name)
    cat_rank, _ = classify_item(item_name)
    cat_key = str(cat_rank)

    d["items"][item_key] = float(d["items"].get(item_key, 0.0)) + 1.0
    d["cats"][cat_key] = float(d["cats"].get(cat_key, 0.0)) + 1.0

    for tok in tokenize_item(item_name):
        d["tokens"][tok] = float(d["tokens"].get(tok, 0.0)) + 1.0

    save_learn_stats(d)


def difficulty_score(item_name: str) -> int:
    """
    Lower is easier.
    Uses base score + learning adjustment:
    - preferred items/categories/tokens (chosen often) become *even easier*
    - mild diversity penalty to avoid always picking same item forever
    """
    cat_rank, base = classify_item(item_name)

    d = load_learn_stats()
    d = decay_counts(d, half_life_days=30.0)
    save_learn_stats(d)

    s_item = normalize_text(item_name)
    item_hits = float(d["items"].get(s_item, 0.0))
    cat_hits = float(d["cats"].get(str(cat_rank), 0.0))

    token_hits = 0.0
    for tok in tokenize_item(item_name):
        token_hits += float(d["tokens"].get(tok, 0.0))

    # bonuses (tuneable)
    bonus = 0.0
    bonus += min(18.0, item_hits * 3.0)     # exact item strong
    bonus += min(10.0, cat_hits * 0.8)      # category moderate
    bonus += min(12.0, token_hits * 0.4)    # tokens light

    # diversity penalty (optional but useful)
    diversity_penalty = min(8.0, item_hits * 0.8)

    score = base - bonus + diversity_penalty
    score = max(1.0, min(200.0, score))
    return int(round(score))


def compute_candidates_debug(list_text: str, top_n: int = 10) -> List[Tuple[int, int, int, str]]:
    """
    Returns list of (cat_rank, score, line_index, item_name) sorted by preference.
    """
    lines = normalize_and_merge_lines(list_text.splitlines())
    candidates: List[Tuple[int, int, int, str]] = []

    for idx, line in enumerate(lines):
        if is_empty_item_line(line):
            item_name = extract_item_name(line)
            cat_rank, _ = classify_item(item_name)
            score = difficulty_score(item_name)
            candidates.append((cat_rank, score, idx, item_name))

    candidates.sort(key=lambda x: (x[0], x[1], x[2]))
    return candidates[:top_n]


def local_fill_one_empty_item(text: str, name: str) -> Tuple[str, Optional[str]]:
    """
    Fill the best empty line with "- name" / ": name" / " - name"
    Returns (new_text, chosen_item_name)
    """
    if already_assigned(text, name):
        return text, None

    lines = normalize_and_merge_lines(text.splitlines())

    candidates = []
    for idx, line in enumerate(lines):
        if is_empty_item_line(line):
            item_name = extract_item_name(line)
            cat_rank, _ = classify_item(item_name)
            score = difficulty_score(item_name)
            candidates.append((cat_rank, score, idx, line, item_name))

    if not candidates:
        return text, None

    candidates.sort(key=lambda x: (x[0], x[1], x[2]))
    _, _, idx, line, item_name = candidates[0]

    stripped = (line or "").strip()
    ln_norm = normalize_text(stripped)

    if re.search(r"-\s*$", ln_norm):
        lines[idx] = re.sub(DASH_CHARS + r"\s*$", f"- {name}", stripped).strip()
    elif re.search(r":\s*$", ln_norm):
        lines[idx] = re.sub(r":\s*$", f": {name}", stripped).strip()
    else:
        lines[idx] = f"{stripped} - {name}"

    return "\n".join(lines), item_name


# =========================
# Selenium helpers
# =========================
def wait_for_whatsapp_ready(driver, timeout=120):
    wait = WebDriverWait(driver, timeout)
    candidates = [
        (By.XPATH, '//*[@id="side"]'),
        (By.XPATH, '//div[@role="application"]'),
        (By.XPATH, '//div[@role="textbox" and @contenteditable="true"]'),
    ]
    last_err = None
    for by, sel in candidates:
        try:
            wait.until(EC.presence_of_element_located((by, sel)))
            return
        except Exception as e:
            last_err = e
    raise TimeoutException(f"WhatsApp Web לא נטען בזמן. {last_err}")


def find_first(driver, locator_list, timeout=20):
    wait = WebDriverWait(driver, timeout)
    last_err = None
    for by, sel in locator_list:
        try:
            return wait.until(EC.presence_of_element_located((by, sel)))
        except Exception as e:
            last_err = e
    raise TimeoutException(f"לא נמצא אלמנט מתאים. {last_err}")


def get_search_box(driver):
    locators = [
        (By.XPATH, '//*[@id="side"]//div[@role="textbox" and @contenteditable="true"][1]'),
        (By.XPATH, '//div[@role="textbox" and @contenteditable="true" and (contains(@aria-label,"Search") or contains(@aria-label,"חפש"))]'),
    ]
    return find_first(driver, locators, timeout=25)


def clear_box(el):
    el.click()
    el.send_keys(Keys.CONTROL, "a")
    el.send_keys(Keys.BACKSPACE)


def find_chat_titles_by_keyword(driver, keyword: str, max_results: int = 200) -> List[str]:
    search_box = get_search_box(driver)
    clear_box(search_box)
    search_box.send_keys(keyword)
    time.sleep(1.2)

    spans = driver.find_elements(By.XPATH, '//span[@title]')
    titles, seen = [], set()

    for sp in spans:
        try:
            t = sp.get_attribute("title")
            if not t:
                continue
            if keyword not in t:
                continue
            if t in seen:
                continue
            seen.add(t)
            titles.append(t)
            if len(titles) >= max_results:
                break
        except Exception:
            continue

    try:
        clear_box(search_box)
        time.sleep(0.2)
    except Exception:
        pass

    return titles


def open_chat_by_title(driver, title: str) -> bool:
    try:
        el = WebDriverWait(driver, 10).until(
            EC.element_to_be_clickable((By.XPATH, f'//span[@title="{title}"]'))
        )
        el.click()
        time.sleep(0.6)
        return True
    except Exception:
        return False


def get_open_chat_title(driver) -> str:
    bad_titles = {
        "יש ללחוץ להצגת פרטי הקבוצה",
        "Click here for group info",
        "Click here for contact info",
    }
    selectors = [
        (By.XPATH, '//header//span[@dir="auto"][@title]'),
        (By.XPATH, '//header//span[@title]'),
    ]
    for by, sel in selectors:
        try:
            spans = driver.find_elements(by, sel)
            for sp in spans:
                t = (sp.get_attribute("title") or "").strip()
                if not t or t in bad_titles:
                    continue
                return t
        except Exception:
            continue
    return ""


def get_recent_message_texts(driver, lookback: int) -> List[str]:
    msgs = driver.find_elements(By.CSS_SELECTOR, "div.copyable-text")
    if not msgs:
        return []
    subset = msgs[-max(1, int(lookback)):]
    out = []
    for m in subset:
        try:
            t = (m.text or "").strip()
            if t:
                out.append(t)
        except Exception:
            continue
    return out


def pick_relevant_list_message(texts: List[str], triggers: List[str]) -> Optional[str]:
    best_triggered = None
    best_listlike = None
    for t in texts:
        if looks_like_signup_list(t):
            best_listlike = t
            if message_matches_triggers(t, triggers):
                best_triggered = t
    return best_triggered or best_listlike


def get_message_box(driver):
    locators = [
        (By.XPATH, '//footer//div[@role="textbox" and @contenteditable="true"]'),
        (By.XPATH, '//div[@role="textbox" and @contenteditable="true" and @data-lexical-editor="true"]'),
    ]
    return find_first(driver, locators, timeout=25)


def send_message(driver, text: str):
    pyperclip.copy(text)
    msg_box = get_message_box(driver)
    msg_box.click()
    time.sleep(0.2)
    actions = ActionChains(driver)
    actions.key_down(Keys.CONTROL).send_keys('v').key_up(Keys.CONTROL).perform()
    time.sleep(0.4)
    actions.send_keys(Keys.ENTER).perform()


# =========================
# Bot runner
# =========================
class BotRunner:
    def __init__(self, ui_log):
        self.ui_log = ui_log
        self.stop_event = threading.Event()
        self.thread: Optional[threading.Thread] = None
        self.driver = None

    def start(self, cfg: BotConfig):
        if self.thread and self.thread.is_alive():
            log_simple("הבוט עדיין רץ/נסגר... נסה שוב עוד רגע.", self.ui_log)
            return
        self.stop_event.clear()
        self.thread = threading.Thread(target=self._run, args=(cfg,), daemon=True)
        self.thread.start()
        log_simple("----- התחלת ריצה -----", self.ui_log)

    def stop(self):
        log_simple("עוצר... (סוגר כרום)", self.ui_log)
        self.stop_event.set()
        try:
            if self.driver:
                self.driver.quit()
        except Exception:
            pass
        try:
            if self.thread and self.thread.is_alive():
                self.thread.join(timeout=10)
        except Exception:
            pass
        self.driver = None
        self.thread = None
        log_simple("נעצר. אפשר ללחוץ 'הפעל' מחדש.", self.ui_log)

    def _run(self, cfg: BotConfig):
        try:
            log_simple(
                f"פרמטרים: group_keywords={cfg.group_keywords}, name='{cfg.name_to_insert}', "
                f"triggers={cfg.trigger_phrases}, interval={cfg.scan_interval_seconds}, lookback={cfg.lookback_messages}",
                self.ui_log
            )

            chrome_options = Options()
            chrome_options.add_argument(f"--user-data-dir={cfg.profile_dir}")
            log_simple("ממתין לטעינת WhatsApp Web...", self.ui_log)

            self.driver = webdriver.Chrome(service=Service(ChromeDriverManager().install()), options=chrome_options)
            self.driver.get("https://web.whatsapp.com")

            messagebox.showinfo(
                "חיבור ל-WhatsApp",
                "נפתח WhatsApp Web.\nאם מופיע QR – סרקו.\nאחרי שרואים צ'אטים בצד שמאל – OK."
            )

            wait_for_whatsapp_ready(self.driver, timeout=120)
            if self.stop_event.is_set():
                return
            log_simple("WhatsApp Web נטען.", self.ui_log)

            all_titles: List[str] = []
            all_seen: Set[str] = set()
            for kw in cfg.group_keywords:
                kw = kw.strip()
                if not kw:
                    continue
                titles = find_chat_titles_by_keyword(self.driver, kw, max_results=250)
                log_simple(f"חיפוש קבוצות לפי '{kw}' -> נמצאו {len(titles)} תוצאות", self.ui_log)
                for t in titles:
                    if t not in all_seen:
                        all_seen.add(t)
                        all_titles.append(t)

            if not all_titles:
                log_simple("לא נמצאו קבוצות לניטור.", self.ui_log)
                messagebox.showwarning("לא נמצאו קבוצות", "לא נמצאו קבוצות לפי המילים שהגדרת.")
                return

            log_simple(f"סה\"כ קבוצות לניטור: {len(all_titles)}", self.ui_log)

            processed_per_chat: Dict[str, Set[str]] = {}
            cycle = 0

            while not self.stop_event.is_set():
                cycle += 1
                log_simple(f"--- סבב #{cycle} ---", self.ui_log)

                for title in all_titles:
                    if self.stop_event.is_set():
                        break

                    if not open_chat_by_title(self.driver, title):
                        log_simple(f"לא הצלחתי לפתוח צ'אט: {title}", self.ui_log)
                        continue

                    chat_title = get_open_chat_title(self.driver) or title
                    recent_texts = get_recent_message_texts(self.driver, cfg.lookback_messages)
                    if not recent_texts:
                        continue

                    candidate = pick_relevant_list_message(recent_texts, cfg.trigger_phrases)
                    if not candidate:
                        continue

                    # debug top candidates
                    cand_debug = compute_candidates_debug(candidate, top_n=10)
                    if cand_debug:
                        debug_str = " | ".join(
                            [f"{name}=[cat={cat} score={score}]" for cat, score, _, name in cand_debug]
                        )
                        log_simple(f"מועמדים: {debug_str}", self.ui_log)
                    else:
                        log_simple("מועמדים: לא נמצאו שורות פנויות בהודעה הזו", self.ui_log)

                    fp = fingerprint_text(candidate)
                    processed = processed_per_chat.setdefault(chat_title, set())
                    if fp in processed:
                        continue

                    if already_assigned(candidate, cfg.name_to_insert):
                        processed.add(fp)
                        continue

                    new_text, chosen_item = local_fill_one_empty_item(candidate, cfg.name_to_insert)
                    if new_text.strip() == candidate.strip():
                        processed.add(fp)
                        continue

                    send_message(self.driver, new_text)
                    processed.add(fp)

                    if chosen_item:
                        learn_on_choice(chosen_item)
                        log_simple(f"✅ נשלח: {chat_title} | נרשמתי על: {chosen_item}", self.ui_log)

                time.sleep(max(2, int(cfg.scan_interval_seconds)))

        except Exception as e:
            log_simple(f"קריסה: {e}", self.ui_log)
            messagebox.showerror("קריסה", f"הבוט נעצר בגלל שגיאה:\n{e}")


# =========================
# GUI (RTL Entry)
# =========================
class RtlEntry(tk.Entry):
    """
    Stable RTL Entry:
    - justify right
    - add RLM only if Hebrew exists
    - remove RLM if no Hebrew
    - preserve logical cursor position
    """
    def __init__(self, master, textvariable=None, width=40, **kwargs):
        kwargs.setdefault("justify", "right")
        super().__init__(master, textvariable=textvariable, width=width, **kwargs)

        self._in_fix = False
        self.bind("<FocusIn>", self._fix_rtl)
        self.bind("<KeyRelease>", self._fix_rtl)
        self.bind("<<Paste>>", self._fix_rtl)

    def _fix_rtl(self, _evt=None):
        if self._in_fix:
            return
        self._in_fix = True
        try:
            raw = self.get() or ""
            cur = self.index(tk.INSERT)
            had_rlm = raw.startswith(RLM)

            logical = raw.replace(RLM, "")
            need_rtl = bool(HEB_RE.search(logical))

            logical_cur = cur - 1 if had_rlm and cur > 0 else cur
            logical_cur = max(0, min(len(logical), logical_cur))

            new_text = (RLM + logical) if need_rtl else logical

            if new_text != raw:
                self.delete(0, tk.END)
                self.insert(0, new_text)

            if need_rtl:
                self.icursor(min(len(new_text), logical_cur + 1))
            else:
                self.icursor(min(len(new_text), logical_cur))
        except Exception:
            pass
        finally:
            self._in_fix = False


def clean_entry_value(s: str) -> str:
    if not s:
        return ""
    # strip bidi controls
    for ch in ["\u200f", "\u200e", "\u202a", "\u202b", "\u202c", "\u2066", "\u2067", "\u2068", "\u2069"]:
        s = s.replace(ch, "")
    return s.strip()


def parse_csv_line(s: str) -> List[str]:
    s = clean_entry_value(s)
    parts = []
    for chunk in s.replace("\n", ",").split(","):
        chunk = chunk.strip()
        if chunk:
            parts.append(chunk)
    return parts


def start_gui():
    root = tk.Tk()
    root.title("WhatsApp Bot - הגדרות")
    root.grid_columnconfigure(0, weight=1)

    existing = load_config()

    def add_label(text, row):
        lbl = tk.Label(root, text=text, anchor="e")
        lbl.grid(row=row, column=0, sticky="e", padx=10, pady=(10, 2))

    def add_entry(var, row, width=55):
        ent = RtlEntry(root, textvariable=var, width=width)
        ent.grid(row=row, column=0, sticky="e", padx=10, pady=2)
        return ent

    add_label("מילים לשמות קבוצות (מופרד בפסיקים):", 0)
    group_var = tk.StringVar(value="הורי, גן, כיתה" if not existing else ", ".join(existing.group_keywords))
    add_entry(group_var, 1, width=60)

    add_label("השם שיודבק ברשימה:", 2)
    name_var = tk.StringVar(value="דרור" if not existing else existing.name_to_insert)
    add_entry(name_var, 3, width=35)

    add_label("משפטים/ביטויים לחיפוש בהודעה (מופרד בפסיקים):", 4)
    trig_default = "מי מביא, מי מביאה, נא להירשם"
    trig_var = tk.StringVar(value=trig_default if not existing else ", ".join(existing.trigger_phrases))
    add_entry(trig_var, 5, width=60)

    add_label("כמה הודעות אחורה לסרוק (מומלץ 30):", 6)
    lookback_var = tk.StringVar(value="30" if not existing else str(existing.lookback_messages))
    add_entry(lookback_var, 7, width=10)

    add_label("כל כמה שניות לבדוק (מומלץ 6):", 8)
    interval_var = tk.StringVar(value="6" if not existing else str(existing.scan_interval_seconds))
    add_entry(interval_var, 9, width=10)

    add_label(r"תיקיית פרופיל Chrome (ברירת מחדל: C:\temp\whatsapp_bot_profile):", 10)
    prof_var = tk.StringVar(value=DEFAULT_PROFILE_DIR if not existing else existing.profile_dir)
    add_entry(prof_var, 11, width=60)

    add_label("לוג:", 12)
    ui_log = scrolledtext.ScrolledText(root, width=95, height=14, wrap=tk.WORD)
    ui_log.grid(row=13, column=0, sticky="e", padx=10, pady=(2, 10))
    ui_log.configure(font=("Consolas", 10))
    ui_log.tag_configure("rtl", justify="right")

    runner = BotRunner(ui_log)

    def on_start():
        # clear log file and UI log
        try:
            with open(LOG_FILE, "w", encoding="utf-8") as f:
                f.write("")
        except Exception:
            pass
        ui_log.delete("1.0", tk.END)

        log_simple("הפעלה נלחצה.", ui_log)

        group_keywords = parse_csv_line(group_var.get())
        name_to_insert = clean_entry_value(name_var.get())
        trigger_phrases = parse_csv_line(trig_var.get())

        if not group_keywords:
            messagebox.showerror("שגיאה", "חייבים להכניס לפחות מילת חיפוש אחת לשמות הקבוצות.")
            return
        if not name_to_insert:
            messagebox.showerror("שגיאה", "חייבים להכניס שם שיודבק.")
            return
        if not trigger_phrases:
            messagebox.showerror("שגיאה", "חייבים להכניס לפחות ביטוי אחד לחיפוש בהודעה.")
            return

        try:
            interval = int(clean_entry_value(interval_var.get()))
        except Exception:
            interval = 6
        interval = max(2, min(60, interval))

        try:
            lookback = int(clean_entry_value(lookback_var.get()))
        except Exception:
            lookback = 30
        lookback = max(5, min(200, lookback))

        profile_dir = clean_entry_value(prof_var.get()) or DEFAULT_PROFILE_DIR

        cfg = BotConfig(
            group_keywords=group_keywords,
            name_to_insert=name_to_insert,
            trigger_phrases=trigger_phrases,
            scan_interval_seconds=interval,
            lookback_messages=lookback,
            profile_dir=profile_dir,
        )
        save_config(cfg)
        runner.start(cfg)

    def on_stop():
        runner.stop()

    btn_frame = tk.Frame(root)
    btn_frame.grid(row=14, column=0, sticky="e", padx=10, pady=10)

    tk.Button(btn_frame, text="הפעל", command=on_start, width=14).pack(side="right")
    tk.Button(btn_frame, text="עצור", command=on_stop, width=14).pack(side="right", padx=8)
    tk.Button(
        btn_frame,
        text="פתח לוג",
        command=lambda: os.startfile(LOG_FILE) if os.path.exists(LOG_FILE) else None,
        width=14
    ).pack(side="right")

    root.mainloop()


if __name__ == "__main__":
    start_gui()