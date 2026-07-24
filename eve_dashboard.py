# -*- coding: utf-8 -*-
"""
EVE Canary — der Kanarienvogel im Bergwerk. Liest die lokalen EVE-Logs (EULA-konform, reine
Textdateien, jede Client-Sprache) und zeigt Mining, Schaden, ISK, Effizienz,
Spielzeit und Sicherheits-Alarme (Spieler-Angriff, Asteroid leer) live +
historisch im Browser. Alles lokal, SQLite-Historie, Backups.

Start:  python eve_dashboard.py   ->  http://localhost:8765
"""
import base64
import email.utils
import hashlib
import json
import os
import re
import shutil
import sqlite3
import sys
import threading
import time
import urllib.error
import urllib.parse
import urllib.request

VERSION = "1.18.1"
UPDATE_FILES = ["eve_dashboard.py", "ore_types.json",
                "mining_tools.json", "README_INSTALL.md"]
from collections import deque
from datetime import datetime, timezone, timedelta
from http.server import BaseHTTPRequestHandler, ThreadingHTTPServer
from pathlib import Path

APP_DIR = Path(__file__).parent
DB_PATH = APP_DIR / "dashboard.db"
CONFIG_PATH = APP_DIR / "config.json"
BACKUP_DIR = APP_DIR / "backups"


# ---------------------------------------------------------------- Fehlercodes
# Damit Nutzer bei Problemen etwas Konkretes schicken koennen statt "geht nicht".
# Aufbau: CN-<BEREICH>-<NR>. Die Liste ist zugleich die Erklaerung im Support.
ERROR_HELP = {
    "CN-LOG-01": "Kein Log-Ordner eingestellt",
    "CN-LOG-02": "Log-Ordner existiert nicht",
    "CN-LOG-03": "Log-Ordner enthaelt keine Gamelogs",
    "CN-LOG-04": "Logdatei nicht lesbar (Rechte/Sperre)",
    "CN-LOG-05": "Fehler beim Einlesen der Logs",
    "CN-CHAT-01": "Chatlogs nicht lesbar (Systemanzeige faellt aus)",
    "CN-DB-01": "Datenbankfehler",
    "CN-NET-01": "Marktpreise nicht abrufbar",
    "CN-ESI-01": "ESI-Abfrage fehlgeschlagen",
    "CN-INTEL-01": "Bedrohungs-Abfrage fehlgeschlagen",
    "CN-CLIP-01": "Zwischenablage nicht lesbar",
    "CN-UPD-01": "Update fehlgeschlagen",
    "CN-CFG-01": "Einstellungen nicht speicherbar",
    "CN-SRV-01": "Interner Serverfehler",
}
ERRORS = deque(maxlen=60)
ERROR_SEEN = {}


def log_error(code, where, exc=None):
    """Fehler mit Code merken, damit er in der Diagnose auftaucht.
    Gleicher Code an gleicher Stelle wird gezaehlt statt 60x geloggt (sonst
    ueberschreibt ein Dauerfehler im 2s-Takt alles andere)."""
    msg = f"{type(exc).__name__}: {exc}" if isinstance(exc, BaseException) else str(exc or "")
    key = (code, where, msg[:120])
    e = ERROR_SEEN.get(key)
    if e is not None:
        e["n"] += 1
        e["ts"] = time.time()
        return
    e = {"ts": time.time(), "first": time.time(), "code": code,
         "where": where, "msg": msg[:300], "n": 1}
    ERROR_SEEN[key] = e
    ERRORS.append(e)
    if len(ERROR_SEEN) > 200:
        ERROR_SEEN.clear()   # Neustart der Zaehlung, damit der Speicher nicht waechst
    # flush: sonst haengt die Meldung im Puffer, sobald die Ausgabe umgeleitet
    # ist (Autostart, nohup) und der Nutzer sieht im Fenster gar nichts.
    print(f"[{code}] {where}: {msg[:300]}", flush=True)


def load_json(name, default):
    p = APP_DIR / name
    try:
        return json.loads(p.read_text(encoding="utf-8"))
    except Exception:
        return default


ORE_TYPES = load_json("ore_types.json", {})
MINING_TOOLS = sorted(load_json("mining_tools.json", []), key=len, reverse=True)

REGIONS = {"10000002": "Jita", "10000043": "Amarr", "10000030": "Rens",
           "10000032": "Dodixie", "10000042": "Hek"}
PRICE_REFRESH = 900
PORT_DEFAULT = 8765
SESSION_MAX_AGE = 3 * 3600  # Log länger unverändert -> Session gilt als beendet, keine Live-Karte
ACTIVE_WINDOW = 300  # ohne Log-Ereignis in den letzten X s gilt ein Char als inaktiv
# Schweres Wasser pro Sekunde Kernlaufzeit (ESI-Dogma: Medium/Large Industrial Core,
# T1 = 100/min, T2 = 200/min — gilt für Porpoise und Orca gleichermassen)
HW_RATE = {"t1": 100 / 60.0, "t2": 200 / 60.0}
HW_CORE_GAP = 300  # laengere Kompressions-Pause -> Kern gilt als aus (Verbrauch pausiert)

TS_RE = re.compile(r"^\[ (\d{4})\.(\d{2})\.(\d{2}) (\d{2}):(\d{2}):(\d{2}) \] \((\w+)\) (.*)$")
HINT_RE = re.compile(r'hint="([^"]+)"')
STRIP_RE = re.compile(r"<[^>]+>")
NUM_RE = re.compile(r"([\d][\d.,   ]*)")
CHAR_FILE_RE = re.compile(r"^\d{8}_\d{6}_(\d+)\.txt$")
CHAT_LINE_RE = re.compile(r"^\[ [\d. :]+ \] ([^>]+?) > (.*)$")
OUT_COLOR = "0xff00ffff"
IN_COLOR = "0xffcc0000"
# Spieler stehen im Kampflog IMMER als "Name[TICKER](Schiffstyp)", NPCs nie.
# Das gilt in jeder Client-Sprache und ist damit das verlaessliche Kriterium —
# eine Namensliste kann es nicht sein, weil Missionen ihre Rats frei umbenennen
# ("Shadow's Grunt", "Roden Shipyard Interceptor" stehen in keiner ESI-Kategorie).
PLAYER_RE = re.compile(r"\[[^\[\]]{1,10}\]\s*\([^()]+\)")
# Fuehrende Schadenszahl (auch mit Tausender-Trennung) am Zeilenanfang
DMG_HEAD_RE = re.compile(r"^\d[\d.,  ]*")
# Sprachabhängige Signale. ALLES ANDERE (Erz, Schaden, Gegner, Bounties, Module)
# ist sprachunabhängig über hint-Tags, Farbcodes und Zahlen — nur diese vier
# Meldungen stehen als reiner Fließtext im Log und brauchen pro Sprache ein Muster.
# Erweitern ohne neue Version: in config.json unter "log_texts", z.B.
#   "log_texts": {"undock": ["Désamarrage", "Отстыковка"]}
# Die echten Sätze liefert die Diagnose eines Nutzers (Abschnitt "Unerkannte
# Meldungen"), damit hier nichts geraten werden muss.
CARGO_FULL_TEXTS = ["Frachtraum des Schiffs ist voll", "cargo hold is full",
                    "cargohold is full"]
DRONE_UNLOAD_TEXTS = ["Bergbaudrohnen müssen ihre aktuellen Erzladungen verladen",
                      "mining drones must unload"]
UNDOCK_TEXTS = ["Abdocken", "Undocking"]      # (None)-Zeile beim Abdocken
TRADE_TEXTS = ["Handel mit", "Trade with"]    # Handel abgeschlossen -> Laderaum unklar
# EWAR gegen dich (Kampf-Log, keine Schadenszeile). Nur fuer die PvP/Missions-Ansicht.
EWAR_TEXTS = [
    ("scramble", ["warp scramble", "warpstör", "warp-stör"]),
    ("disrupt", ["warp disrupt", "warpunterbrech"]),
    ("web", ["stasis web", "fesselung"]),
    # "You're jammed by X" ist die echte ECM-Meldung — nicht "jam attempt".
    ("jam", ["jammed by", "jam attempt", "ecm", "target jam", "gejammt",
             "stört deine zielerfass", "verlierst die zielerfass"]),
    ("neut", ["energy neutraliz", "nosferatu", "energie neutral"]),
    ("paint", ["target paint", "zielmarkier"]),
    ("damp", ["remote sensor damp", "sensordämpf"]),
    ("td", ["tracking disrupt", "verfolgungsstör"]),
]
SALVAGE_OK = ["successfully salvage from"]
SALVAGE_EMPTY = ["contains nothing of value"]
SALVAGE_FAIL = ["salvaging attempt failed"]
LOG_TEXT_KEYS = {"cargo_full": CARGO_FULL_TEXTS, "drone_unload": DRONE_UNLOAD_TEXTS,
                 "undock": UNDOCK_TEXTS, "trade": TRADE_TEXTS}

# Unerkannte notify-Meldungen sammeln. Bei Clients in anderen Sprachen als DE/EN
# fehlen die Muster oben — mit diesen Beispielen aus der Diagnose lassen sie sich
# exakt nachtragen, statt sie zu raten (geratene Muster greifen still nicht).
UNKNOWN_NOTIFY = deque(maxlen=80)
_UNKNOWN_SEEN = set()
# Wie oft die eingebauten Muster gegriffen haben. Stehen hier ueberall Nullen,
# ist die Client-Sprache noch nicht abgedeckt — das sieht man in der Diagnose
# sofort, ohne die Meldungen darunter lesen zu muessen.
LOG_TEXT_HITS = {"cargo_full": 0, "drone_unload": 0, "undock": 0, "trade": 0}


# Grossgeschriebenes Wort, das NICHT am Satzanfang steht = vermutlich Eigenname
PROPER_RE = re.compile(r"(?<![.!?]\s)(?<!^)\b[A-ZÄÖÜÀ-ÖØ-ÞА-ЯЁ][\w'’-]{2,}", re.UNICODE)


def note_unknown(text):
    if not text or len(_UNKNOWN_SEEN) > 600:
        return
    # Zahlen und Eigennamen (System-, Stations-, Spielernamen) vereinheitlichen,
    # sonst belegt "Jumping from A to B" mit jeder Kombination einen eigenen
    # Platz und verdraengt die Meldungen, um die es hier eigentlich geht.
    t = re.sub(r"\d[\d.,]*", "#", text).strip()
    t = PROPER_RE.sub("@", t)[:150]
    if len(t) < 12 or t in _UNKNOWN_SEEN:
        return
    _UNKNOWN_SEEN.add(t)
    UNKNOWN_NOTIFY.append(t)


def num(s):
    return int(re.sub(r"[.,   ]", "", s) or 0)


def parse_line(raw):
    """Gamelog-Zeile -> Event-Dict oder None. Nur sprachunabhängige Signale."""
    m = TS_RE.match(raw.strip())
    if not m:
        return None
    y, mo, d, h, mi, s, tag, body = m.groups()
    ts = datetime(int(y), int(mo), int(d), int(h), int(mi), int(s),
                  tzinfo=timezone.utc).timestamp()
    day = f"{y}-{mo}-{d}"
    base = {"ts": ts, "day": day}
    if tag == "mining":
        text = STRIP_RE.sub("", body)
        n = NUM_RE.search(text)
        hint = HINT_RE.search(body)
        # Lokalisierte Clients wrappen den Erznamen in <localized hint="EnglName">.
        # Der ENGLISCHE Client lokalisiert nicht -> kein hint, Name als Klartext:
        # "You mined 42 units of Coesite".
        ore = hint.group(1) if hint else None
        if ore is None:
            me = re.search(r"units of\s+(.+?)\s*$", text)
            if me:
                ore = me.group(1).strip().rstrip("*").strip()
        if ore and n:
            return {**base, "kind": "ore", "key": ore, "value": num(n.group(1))}
    elif tag == "combat":
        low = body.lower()
        direction = "dmg_out" if OUT_COLOR in low else ("dmg_in" if IN_COLOR in low else None)
        if direction:
            plain = STRIP_RE.sub("", body).strip()
            n = NUM_RE.search(plain)
            hints = HINT_RE.findall(body)
            if n:
                # Klartext hinter der Schadenszahl: "<Gegner> - <Waffe> - <Qualitaet>".
                # Der ENGLISCHE Client setzt keine hint-Tags, dort ist das die
                # einzige Quelle fuer den Gegnernamen (sonst blieb er "?").
                who = weapon = None
                m = re.match(r"^\d[\d.,  ]*\s+(?:from|to)\s+(.+)$", plain)
                if m:
                    parts = [p.strip() for p in m.group(1).split(" - ")]
                    who = parts[0] or None
                    if len(parts) >= 3:
                        weapon = parts[1]
                # Spieler? Dann steht "[TICKER](Schiff)" drin — Pilotenname ist
                # alles davor, ohne Schadenszahl und Richtungswort.
                mp = PLAYER_RE.search(plain)
                if mp:
                    head = DMG_HEAD_RE.sub("", plain[:mp.start()]).strip()
                    who = (head.split(" ", 1)[1] if " " in head else head).strip() or who
                elif hints:
                    who = hints[0]   # lokalisierter Client: NPC-Name aus dem hint
                ev = {**base, "kind": direction, "key": who or "?",
                      "value": num(n.group(1)), "player": bool(mp)}
                if direction == "dmg_out":
                    if len(hints) > 1:
                        ev["weapon"] = hints[1]
                    elif weapon:
                        ev["weapon"] = weapon
                return ev
        # Nicht-Schaden-Kampfzeilen fuer die PvP/Missions-Ansicht: Fehlschuesse
        # (eigene = Trefferquote, gegnerische = Ausweichen) und EWAR gegen dich.
        pl = STRIP_RE.sub("", body).strip().lower()
        if "misses you" in pl or "verfehlt dich" in pl or "verfehlen dich" in pl:
            return {**base, "kind": "miss_in", "key": "", "value": 1}
        if re.match(r"^(your|deine?|ihr)\b", pl) and ("miss" in pl or "verfehl" in pl):
            return {**base, "kind": "miss_out", "key": "", "value": 1}
        for etype, pats in EWAR_TEXTS:
            if any(p in pl for p in pats):
                return {**base, "kind": "ewar", "key": etype, "value": 1}
        return None
    elif tag == "bounty":
        n = NUM_RE.search(STRIP_RE.sub("", body))
        if n:
            return {**base, "kind": "bounty", "key": "", "value": num(n.group(1))}
    elif tag == "notify":
        text = STRIP_RE.sub("", body).strip()
        hints = HINT_RE.findall(body)
        comp = next((h for h in hints if h.startswith("Compressed")), None)
        if comp:
            n = NUM_RE.search(text)
            if n:
                raw_ore = next((h for h in hints if not h.startswith("Compressed")), None)
                return {**base, "kind": "compressed", "key": comp,
                        "raw": raw_ore, "value": num(n.group(1))}
        # Englischer Client (kein hint): "Successfully compressed Coesite into 41 Compressed Coesite."
        mc = re.search(r"compressed (.+?) into (\d[\d.,]*) (Compressed .+?)\.?\s*$", text)
        if mc:
            return {**base, "kind": "compressed",
                    "key": mc.group(3).strip().rstrip("*").strip(),
                    "raw": mc.group(1).strip().rstrip("*").strip(),
                    "value": num(mc.group(2))}
        if any(t in text for t in TRADE_TEXTS):
            LOG_TEXT_HITS["trade"] += 1
            return {**base, "kind": "hold_reset", "key": "trade", "value": 1}
        for tool in MINING_TOOLS:
            # Modulnamen sind nie lokalisiert: "Strip Miner I* schaltet ab, …"
            if text.startswith(tool):
                return {**base, "kind": "depleted", "key": tool, "value": 1}
        if hints == ["Asteroid"]:
            # Modul versucht Zyklus auf zerstörtem/ungültigem Ziel — Asteroid weg
            return {**base, "kind": "depleted", "key": "Ziel verloren", "value": 1}
        if (len(hints) == 1 and hints[0] in ORE_TYPES
                and not hints[0].startswith("Compressed")
                and not any(ch.isdigit() for ch in text)):
            # "Drohnen greifen <Erz> an" (ohne Zahlen — Distanz-Fehler haben immer km-Angaben):
            # Mining-Drohnen wurden neu angesetzt -> Drohnen-Warnung aufheben
            return {**base, "kind": "drone_engage", "key": hints[0], "value": 1}
        low_t = text.lower()
        if any(t in low_t for t in SALVAGE_OK):
            return {**base, "kind": "salvage", "key": "ok", "value": 1}
        if any(t in low_t for t in SALVAGE_EMPTY):
            return {**base, "kind": "salvage", "key": "empty", "value": 1}
        if any(t in low_t for t in SALVAGE_FAIL):
            return {**base, "kind": "salvage", "key": "fail", "value": 1}
        if any(t in text for t in CARGO_FULL_TEXTS):
            LOG_TEXT_HITS["cargo_full"] += 1
            return {**base, "kind": "cargo", "key": "", "value": 1}
        if any(t in text for t in DRONE_UNLOAD_TEXTS):
            LOG_TEXT_HITS["drone_unload"] += 1
            return {**base, "kind": "drone_idle", "key": "", "value": 1}
        note_unknown(text)
        return None
    elif tag == "None":
        text = STRIP_RE.sub("", body)
        if any(t in text for t in UNDOCK_TEXTS):
            LOG_TEXT_HITS["undock"] += 1
            return {**base, "kind": "hold_reset", "key": "dock", "value": 1}
        note_unknown(text)
        return None
    return None


def read_char_name(file):
    try:
        with open(file, encoding="utf-8-sig", errors="replace") as f:
            for _ in range(6):
                line = f.readline()
                if ":" in line and "---" not in line:
                    return line.split(":", 1)[1].strip()
    except OSError:
        pass
    return file.stem


def _steam_libs():
    """Alle Steam-Bibliotheken auf dem Rechner (auch auf zweiten Platten)."""
    home = Path.home()
    libs = []
    for r in [home / ".steam" / "steam", home / ".steam" / "root",
              home / ".local" / "share" / "Steam",
              home / ".var" / "app" / "com.valvesoftware.Steam" / ".local" / "share" / "Steam",
              home / "snap" / "steam" / "common" / ".local" / "share" / "Steam"]:
        sa = r / "steamapps"
        if sa.is_dir() and sa not in libs:
            libs.append(sa)
    # Zusatz-Bibliotheken stehen in libraryfolders.vdf (eigenes Format, kein JSON)
    for sa in list(libs):
        try:
            txt = (sa / "libraryfolders.vdf").read_text(encoding="utf-8", errors="replace")
        except OSError:
            continue
        for m in re.finditer(r'"path"\s+"([^"]+)"', txt):
            p = Path(m.group(1).replace("\\\\", "/")) / "steamapps"
            if p.is_dir() and p not in libs:
                libs.append(p)
    return libs


def find_log_dir():
    # 1) Windows und macOS: EVE schreibt direkt ins Benutzerverzeichnis
    home = Path.home()
    for d in [home / "Documents", home / "OneDrive" / "Documents",
              home / "OneDrive" / "Dokumente", home / "Dokumente"]:
        p = d / "EVE" / "logs" / "Gamelogs"
        if p.exists():
            return p
    if os.name == "nt":
        return None
    # 2) Linux: EVE laeuft ueber Wine/Proton, die Logs liegen IM Praefix.
    #    Steam/Proton legt pro Spiel eines unter steamapps/compatdata/<appid>/pfx
    #    an — wir suchen ueber alle, statt uns auf eine feste App-ID zu verlassen.
    prefixes = []
    for sa in _steam_libs():
        cd = sa / "compatdata"
        if cd.is_dir():
            prefixes.extend(sorted(cd.glob("*/pfx")))
    if os.environ.get("WINEPREFIX"):
        prefixes.append(Path(os.environ["WINEPREFIX"]))
    prefixes.append(home / ".wine")
    games = home / "Games"          # Lutris legt seine Praefixe hier ab
    if games.is_dir():
        prefixes.extend(sorted(games.glob("*")))
    hits = []
    for pfx in prefixes:
        users = pfx / "drive_c" / "users"
        if not users.is_dir():
            continue
        for docs in ("Documents", "Dokumente", "My Documents"):
            hits.extend(p for p in users.glob(f"*/{docs}/EVE/logs/Gamelogs") if p.is_dir())
    if not hits:
        return None

    def newest(p):
        try:
            return max((f.stat().st_mtime for f in p.glob("*.txt")), default=0)
        except OSError:
            return 0
    # Mehrere Treffer (z.B. altes Wine-Praefix daneben): das mit dem juengsten Log
    return max(hits, key=newest)


def load_config():
    cfg = {"port": PORT_DEFAULT, "region": "10000002", "log_dir": None,
           "mode": "all", "install_ts": time.time(),
           "goal": None, "watchlist": [], "idle_warn": 240, "heavy_water": {},
           "clip_watch": False, "roles": {}, "log_texts": {},
           "update_url": "https://raw.githubusercontent.com/Eve-Online-Askend/eve-canary/main"}
    if CONFIG_PATH.exists():
        try:
            cfg.update(json.loads(CONFIG_PATH.read_text(encoding="utf-8")))
        except Exception:
            pass
    if not cfg.get("log_dir"):
        d = find_log_dir()
        cfg["log_dir"] = str(d) if d else ""
    save_config(cfg)
    return cfg


CONFIG_LOCK = threading.RLock()


def save_config(cfg=None):
    # Atomar und thread-sicher: mehrere Threads (hw_tick, Esi.poll, do_POST …)
    # schreiben sonst gleichzeitig und hinterlassen kaputtes JSON.
    with CONFIG_LOCK:
        try:
            data = json.dumps(cfg or CONFIG, indent=1, ensure_ascii=False)
            tmp = CONFIG_PATH.with_suffix(".tmp")
            tmp.write_text(data, encoding="utf-8")
            os.replace(tmp, CONFIG_PATH)
        except OSError as e:
            # z.B. schreibgeschuetzter Ordner oder volle Platte — sonst gehen
            # Einstellungen und ESI-Tokens still verloren.
            log_error("CN-CFG-01", "save_config", e)


CONFIG = load_config()

# Eigene Sprachmuster aus config.json ergaenzen die eingebauten (DE/EN), damit
# eine neue Client-Sprache ohne neue Programmversion nachgetragen werden kann.
for _key, _builtin in LOG_TEXT_KEYS.items():
    for _t in (CONFIG.get("log_texts") or {}).get(_key) or []:
        if isinstance(_t, str) and _t.strip() and _t.strip() not in _builtin:
            _builtin.append(_t.strip())

# ---------------------------------------------------------------- Datenbank
DB_LOCK = threading.Lock()
DB = sqlite3.connect(DB_PATH, check_same_thread=False)
# WAL + kurzer Busy-Timeout: Leser sehen stets den letzten committeten Stand,
# statt halbe Schreibtransaktionen anderer Threads (Dirty Reads).
try:
    DB.execute("PRAGMA journal_mode=WAL")
    DB.execute("PRAGMA busy_timeout=4000")
except sqlite3.OperationalError:
    pass
DB.executescript("""
CREATE TABLE IF NOT EXISTS meta(key TEXT PRIMARY KEY, value TEXT);
CREATE TABLE IF NOT EXISTS files(name TEXT PRIMARY KEY, char_id TEXT, char_name TEXT,
    offset INTEGER DEFAULT 0, skipped INTEGER DEFAULT 0,
    first_ts REAL, last_ts REAL);
CREATE TABLE IF NOT EXISTS daily(day TEXT, char_id TEXT, char_name TEXT, kind TEXT,
    key TEXT, value REAL, PRIMARY KEY(day, char_id, kind, key));
CREATE TABLE IF NOT EXISTS baseline_offsets(day TEXT, char_id TEXT, kind TEXT,
    key TEXT, value REAL, PRIMARY KEY(day, char_id, kind, key));
CREATE TABLE IF NOT EXISTS threat(name TEXT PRIMARY KEY COLLATE NOCASE,
    data TEXT, ts REAL);
CREATE TABLE IF NOT EXISTS journal(id INTEGER, char TEXT, ts REAL,
    ref_type TEXT, amount REAL, party TEXT, PRIMARY KEY(id, char));
CREATE TABLE IF NOT EXISTS item_ids(name TEXT PRIMARY KEY COLLATE NOCASE, type_id INTEGER);
CREATE TABLE IF NOT EXISTS missions(mid TEXT PRIMARY KEY, char_id TEXT, char TEXT,
    start_ts REAL, end_ts REAL, system TEXT, dmg_out INTEGER, dmg_in INTEGER,
    kills INTEGER, bounty REAL, hits INTEGER, miss_out INTEGER, miss_in INTEGER,
    weapons TEXT, enemies TEXT, loot_isk REAL, loot_text TEXT);
""")
DB.commit()
try:  # v1.5.1: System-Kontext je Journal-Eintrag (filtert Belt-Bounties aus der Missions-Statistik)
    DB.execute("ALTER TABLE journal ADD COLUMN ctx INTEGER")
    DB.commit()
except sqlite3.OperationalError:
    pass


def meta_get(key, default=None):
    r = DB.execute("SELECT value FROM meta WHERE key=?", (key,)).fetchone()
    return r[0] if r else default


# Parser-Version: hochzaehlen, wenn eine Parser-Aenderung ein Neu-Einlesen aller
# Logs noetig macht. "2" = englischer Client (Mining/Kompr. ohne hint) wird erfasst.
# "3" = Gegnernamen im Kampflog des englischen Clients (standen vorher alle als "?")
# "4" = Missions-Historie an Undock-Grenzen rueckwirkend aus allen Logs aufbauen
PARSE_VER = "4"


def rebuild_if_needed():
    """Einmaliges Neu-Aufbereiten nach einem Parser-Update: Tages-Statistik und
    Datei-Offsets loeschen, damit alle Logs frisch mit dem neuen Parser gelesen
    werden. So werden zuvor verpasste Erze (z.B. englischer Client) rueckwirkend
    erfasst, ohne Doppelzaehlung (daily startet leer). Baseline bleibt erhalten."""
    if meta_get("parse_ver") == PARSE_VER:
        return
    with DB_LOCK:
        DB.execute("DELETE FROM daily")
        DB.execute("DELETE FROM files")
        DB.execute("INSERT OR REPLACE INTO meta VALUES('parse_ver', ?)", (PARSE_VER,))
        DB.commit()
    print("Parser aktualisiert: Logs werden einmalig neu eingelesen …")


def db_add(day, char_id, char_name, kind, key, value):
    DB.execute("""INSERT INTO daily VALUES(?,?,?,?,?,?)
                  ON CONFLICT(day,char_id,kind,key)
                  DO UPDATE SET value=value+excluded.value, char_name=excluded.char_name""",
               (day, char_id, char_name, kind, key, value))


def save_mission(m):
    """Abgeschlossene Mission speichern. INSERT OR IGNORE über mid=char:start,
    damit ein erneutes Einlesen (Rebuild) nicht doppelt anlegt und vom Nutzer
    eingefügten Loot nicht überschreibt."""
    mid = f"{m['char_id']}:{int(m['start_ts'])}"
    DB.execute("""INSERT OR IGNORE INTO missions
        (mid,char_id,char,start_ts,end_ts,system,dmg_out,dmg_in,kills,bounty,
         hits,miss_out,miss_in,weapons,enemies,loot_isk,loot_text)
        VALUES(?,?,?,?,?,?,?,?,?,?,?,?,?,?,?,?,?)""",
        (mid, m["char_id"], m["char"], m["start_ts"], m["end_ts"], m["system"],
         m["dmg_out"], m["dmg_in"], m["kills"], m["bounty"], m["hits"],
         m["miss_out"], m["miss_in"], json.dumps(m["weapons"], ensure_ascii=False),
         json.dumps(m["enemies"], ensure_ascii=False), None, None))


def do_backup():
    BACKUP_DIR.mkdir(exist_ok=True)
    name = f"dashboard_{datetime.now().strftime('%Y%m%d_%H%M%S')}.db"
    with DB_LOCK:
        DB.commit()
        shutil.copy2(DB_PATH, BACKUP_DIR / name)
    for f in sorted(BACKUP_DIR.glob("dashboard_*.db"))[:-10]:
        f.unlink(missing_ok=True)
    return name


def do_reset_baseline():
    today = datetime.now(timezone.utc).strftime("%Y-%m-%d")
    with DB_LOCK:
        DB.execute("DELETE FROM baseline_offsets")
        DB.execute("""INSERT INTO baseline_offsets
                      SELECT day, char_id, kind, key, value FROM daily WHERE day=?""", (today,))
        DB.execute("INSERT OR REPLACE INTO meta VALUES('baseline_day',?)", (today,))
        DB.execute("INSERT OR REPLACE INTO meta VALUES('baseline_ts',?)", (str(time.time()),))
        DB.commit()


def clear_baseline():
    with DB_LOCK:
        DB.execute("DELETE FROM baseline_offsets")
        DB.execute("DELETE FROM meta WHERE key IN ('baseline_day','baseline_ts')")
        DB.commit()


# ---------------------------------------------------------------- Update
def fetch_url(url, timeout=15):
    with urllib.request.urlopen(url, timeout=timeout) as r:
        return r.read()


AUTOSTART_OK = os.name == "nt" or sys.platform.startswith("linux")
CLIPBOARD_OK = sys.platform == "win32"


def autostart_path():
    if os.name == "nt":
        return (Path(os.environ.get("APPDATA", "")) / "Microsoft" / "Windows"
                / "Start Menu" / "Programs" / "Startup" / "EVE-Canary-Autostart.vbs")
    base = os.environ.get("XDG_CONFIG_HOME") or (Path.home() / ".config")
    return Path(base) / "autostart" / "eve-canary.desktop"


def set_autostart(on):
    """Startet Canary beim Login still im Hintergrund.
    Windows: VBS im Autostart-Ordner (unterdrueckt das Konsolenfenster).
    Linux: .desktop-Datei nach XDG-Standard, greift in GNOME/KDE/XFCE gleich."""
    if not AUTOSTART_OK:
        return
    p = autostart_path()
    if not on:
        try:
            p.unlink()
        except FileNotFoundError:
            pass
        return
    script = APP_DIR / "eve_dashboard.py"
    p.parent.mkdir(parents=True, exist_ok=True)
    if os.name == "nt":
        exe = Path(sys.executable)
        pyw = exe.with_name("pythonw.exe")
        runner = pyw if pyw.exists() else exe
        # --no-browser: beim Login still starten, ohne Browser-Tab aufzupoppen
        p.write_text('CreateObject("WScript.Shell").Run '
                     f'"""{runner}"" ""{script}"" --no-browser", 0\n', encoding="utf-8")
    else:
        p.write_text("[Desktop Entry]\nType=Application\nName=EVE Canary\n"
                     f'Exec="{sys.executable}" "{script}" --no-browser\n'
                     "Terminal=false\nX-GNOME-Autostart-enabled=true\n", encoding="utf-8")


UPDATE_INFO = {"ts": 0, "available": False, "latest": None}


def refresh_update_info():
    """Alle 6 Stunden still nach einer neuen Version schauen (für den Kopfleisten-Badge)."""
    if time.time() - UPDATE_INFO["ts"] < 6 * 3600:
        return
    UPDATE_INFO["ts"] = time.time()
    chk = check_update()
    if chk.get("ok"):
        UPDATE_INFO["available"] = bool(chk.get("available"))
        UPDATE_INFO["latest"] = chk.get("latest")


def _ver(v):
    """Versionsstring in vergleichbares Tupel, '1.5.2' -> (1, 5, 2).
    Pro Segment nur den fuehrenden Zahlteil (so bleibt '1.6.0-rc1' vergleichbar)."""
    out = []
    for seg in str(v).split("."):
        m = re.match(r"\d+", seg)
        out.append(int(m.group()) if m else 0)
    return tuple(out)


def check_update():
    base = (CONFIG.get("update_url") or "").rstrip("/")
    if not base.startswith("https://"):
        return {"ok": False, "error": "Keine Update-Quelle konfiguriert (Optionen -> update_url)."}
    try:
        info = json.loads(fetch_url(f"{base}/version.json").decode("utf-8"))
        latest = str(info.get("version", "?"))
        return {"ok": True, "current": VERSION, "latest": latest,
                "available": _ver(latest) > _ver(VERSION),
                "files": info.get("files", UPDATE_FILES),
                # Fuer den Download ueber das GitHub-Release (siehe do_update)
                "repo": info.get("repo"), "tag": info.get("tag")}
    except Exception as e:
        return {"ok": False, "error": f"Update-Server nicht erreichbar: {e}"}


def do_update():
    chk = check_update()
    if not chk.get("ok"):
        return chk
    if not chk.get("available"):
        return {"ok": True, "updated": False, "message": "Bereits aktuell."}
    base = CONFIG["update_url"].rstrip("/")
    # Bevorzugt vom GitHub-Release laden: nur dort zaehlt GitHub die Downloads
    # (raw.githubusercontent liefert keine Statistik). Klappt das nicht, geht es
    # ueber raw weiter — das Update darf daran niemals scheitern.
    rel = None
    if chk.get("repo") and chk.get("tag") and re.fullmatch(r"[\w.-]+/[\w.-]+", chk["repo"]) \
            and re.fullmatch(r"[\w.-]+", chk["tag"]):
        rel = f"https://github.com/{chk['repo']}/releases/download/{chk['tag']}"

    def grab(name):
        if rel:
            try:
                return fetch_url(f"{rel}/{name}", timeout=30)
            except Exception:
                pass
        return fetch_url(f"{base}/{name}", timeout=30)

    try:
        blobs = {}
        for name in chk["files"]:
            if name not in UPDATE_FILES:
                continue  # nur bekannte Dateien, keine fremden Pfade
            blobs[name] = grab(name)
        if "eve_dashboard.py" in blobs:
            compile(blobs["eve_dashboard.py"].decode("utf-8"), "eve_dashboard.py", "exec")
    except SyntaxError:
        return {"ok": False, "error": "Die neue Version war fehlerhaft. Update abgebrochen, es wurde nichts geändert."}
    except Exception as e:
        return {"ok": False, "error": f"Download fehlgeschlagen: {e}"}
    # Atomar anwenden: erst alle Dateien komplett als .new schreiben, dann per
    # os.replace einzeln tauschen. Bricht das Tauschen ab (z.B. Virenscanner-Lock),
    # werden bereits getauschte Dateien aus dem .bak zurückgerollt -> keine Mischversion.
    written = []
    try:
        for name, data in blobs.items():
            (APP_DIR / (name + ".new")).write_bytes(data)
        for name in blobs:
            target = APP_DIR / name
            if target.exists():
                shutil.copy2(target, APP_DIR / (name + ".bak"))
            os.replace(APP_DIR / (name + ".new"), target)
            written.append(name)
    except Exception as e:
        for name in written:  # Rollback der schon getauschten Dateien
            bak = APP_DIR / (name + ".bak")
            if bak.exists():
                try:
                    shutil.copy2(bak, APP_DIR / name)
                except OSError:
                    pass
        for name in blobs:  # verwaiste .new aufräumen
            try:
                (APP_DIR / (name + ".new")).unlink()
            except OSError:
                pass
        return {"ok": False, "error": f"Update konnte nicht angewendet werden ({e}). "
                "Vorheriger Stand wurde wiederhergestellt."}
    def _restart():
        import subprocess
        kwargs = {"cwd": str(APP_DIR), "stdout": subprocess.DEVNULL,
                  "stderr": subprocess.DEVNULL}
        if os.name == "nt":
            # DETACHED_PROCESS | CREATE_NEW_PROCESS_GROUP: ueberlebt das
            # Schliessen des alten Konsolenfensters; Popen quotet Pfade
            # mit Leerzeichen korrekt (os.execv tut das unter Windows nicht!)
            kwargs["creationflags"] = 0x00000008 | 0x00000200
        subprocess.Popen([sys.executable, str(APP_DIR / "eve_dashboard.py")], **kwargs)
        os._exit(0)

    threading.Timer(1.0, _restart).start()
    return {"ok": True, "updated": True,
            "message": f"Update auf {chk['latest']} installiert. Neustart läuft, die Seite lädt gleich neu."}


# ---------------------------------------------------------------- Alarme
class Alerts:
    def __init__(self):
        self.items = deque(maxlen=50)
        self.next_id = 1
        self.lock = threading.Lock()

    def push(self, kind, char, text):
        with self.lock:
            self.items.append({"id": self.next_id, "ts": time.time(),
                               "kind": kind, "char": char, "text": text})
            self.next_id += 1

    def resolve(self, kinds, char, min_age=0):
        """Alarme eines Chars entfernen, deren Ursache behoben ist
        (z.B. Erz fliesst wieder -> Frachtraum/Asteroid/Stillstand hinfaellig).
        min_age: Alarme juenger als X Sekunden bleiben stehen, damit die
        Warnung nicht verschwindet, bevor man sie gesehen hat."""
        cutoff = time.time() - min_age
        with self.lock:
            kept = [a for a in self.items
                    if a["char"] != char or a["kind"] not in kinds
                    or a["ts"] > cutoff]
            if len(kept) != len(self.items):
                self.items = deque(kept, maxlen=self.items.maxlen)

    def list(self):
        with self.lock:
            return list(self.items)[-20:]


alerts = Alerts()


# ---------------------------------------------------------------- Live-Session
class CharSession:
    def __init__(self, char_id, name, file):
        self.char_id, self.name, self.file = char_id, name, file
        self.start = time.time()
        self.first_ts = None
        self.trips = 0  # Anzahl Station-Stopps (Abdocken) in dieser Session
        self.mining = {}
        self.compressed = {}
        self.hold_raw = {}    # Laderaum-Schaetzung: unkomprimiertes Erz
        self.hold_comp = {}   # Laderaum-Schaetzung: komprimiertes Erz
        self.weapons = {}
        self.depleted = 0
        self.tool_off = {}    # Werkzeug -> [Anzahl, letzter ts] — verfaellt nach 240s
        self.lasers_off = {}  # Laser -> {"since": ts, "before": m3/min} — bleibt bis Erholung/Dock/Klick
        self.core_timeline = []  # (ts, kumulative Kern-Sekunden) je Kompressions-Event
        self.cargo_full = False
        self.cargo_ts = 0
        self.last_ore_ts = None   # fuer Stillstand-Erkennung
        self.last_event_ts = None # letztes Log-Ereignis (Aktivitaets-/Online-Heuristik)
        self.idle_alerted = False
        self.low_since = None     # Raten-Waechter (Teilausfall-Erkennung)
        self.low_alerted = False
        self.gaps = deque(maxlen=40)  # letzte Abstaende zwischen Erz-Events (lernt Drohnen-Zyklen)
        # Drohnen-Erkennung: Mining-Drohnen liefern mehrere kleine Erz-Portionen
        # dicht beieinander (ein Zyklus = alle Drohnen fast gleichzeitig). Bleiben
        # diese Bursts aus, waehrend der Laser weiterlaeuft, sind die Drohnen idle.
        self.ore_ts = deque(maxlen=12)   # letzte Erz-Lieferzeitpunkte (Burst-Fenster)
        self.drone_last = None           # ts des letzten erkannten Drohnen-Bursts
        self.drone_gaps = deque(maxlen=15)  # Abstaende zwischen Drohnen-Bursts
        self.drone_alerted = False
        self.ore_hist = deque(maxlen=400)  # alle Erz-ts (fuer Laser/Drohnen-Strom-Analyse)
        self.laser_alerted = False
        self.dmg_out = self.dmg_in = self.bounty = 0
        self.kills = 0  # NPC-Abschuesse (eine Bounty-Zeile = ein Kill)
        self.targets = {}
        self.attackers = {}
        self.win_out = deque()
        self.win_in = deque()
        # PvP/Missions-Ansicht: Trefferquote, EWAR, Salvage
        self.hits_out = 0     # Schaden-austeilende Schuesse (Treffer)
        self.miss_out = 0     # eigene Fehlschuesse
        self.miss_in = 0      # Gegner daneben
        self.ewar = {}        # Typ -> Anzahl (scramble/jam/web/…)
        self.salvage = {"ok": 0, "empty": 0, "fail": 0}
        self.dmg_min = deque(maxlen=180)  # [Minute, {"out":x,"in":y}] — Kampfverlauf
        self.rate_min = deque(maxlen=180)  # [Minute, {Erz: m3}] — fuer Sparkline + Raten-Waechter

    def feed(self, ev, live):
        now = time.time()
        if self.first_ts is None or ev["ts"] < self.first_ts:
            self.first_ts = ev["ts"]
        if self.last_event_ts is None or ev["ts"] > self.last_event_ts:
            self.last_event_ts = ev["ts"]
        k = ev["kind"]
        if k == "ore":
            self.cargo_full = False
            if self.last_ore_ts:
                gap = ev["ts"] - self.last_ore_ts
                if 0 < gap < 900:
                    self.gaps.append(gap)
            self.last_ore_ts = ev["ts"]
            self.idle_alerted = False
            # Drohnen-Burst: >=4 Erz-Lieferungen innerhalb von 8s. Ein Schiff hat
            # hoechstens 3 Strip Miner, also sind 4+ dicht aufeinanderfolgende
            # Lieferungen zwangslaeufig Mining-Drohnen (kein Fehlalarm bei Lasern).
            self.ore_ts.append(ev["ts"])
            self.ore_hist.append(ev["ts"])
            recent = [t for t in self.ore_ts if ev["ts"] - t <= 8]
            if len(recent) >= 4:
                # Neuer Zyklus nur, wenn >15s seit letztem Burst (sonst zaehlen die
                # 5 Drohnen EINES Zyklus als 5 Bursts -> falsche Mini-Gaps).
                if self.drone_last is None or ev["ts"] - self.drone_last > 15:
                    if self.drone_last and ev["ts"] - self.drone_last < 900:
                        self.drone_gaps.append(ev["ts"] - self.drone_last)
                self.drone_last = ev["ts"]
                self.drone_alerted = False   # Drohnen liefern wieder
            self.mining[ev["key"]] = self.mining.get(ev["key"], 0) + ev["value"]
            self.hold_raw[ev["key"]] = self.hold_raw.get(ev["key"], 0) + ev["value"]
            vol = ORE_TYPES.get(ev["key"], {}).get("volume", 0.0)
            minute = int(ev["ts"] // 60) * 60
            if not self.rate_min or self.rate_min[-1][0] != minute:
                if self.rate_min and self.lasers_off:
                    # Abgeschlossene Minute auswerten: Rate wieder auf Normal-
                    # niveau -> abgeschalteter Laser wurde offenbar neu gezielt
                    pm, pmix = self.rate_min[-1]
                    ptotal = sum(pmix.values())
                    for tool, info in list(self.lasers_off.items()):
                        if (info["before"] and pm > info["since"]
                                and ptotal >= 0.85 * info["before"]):
                            del self.lasers_off[tool]
                self.rate_min.append([minute, {}])
            mix = self.rate_min[-1][1]
            mix[ev["key"]] = mix.get(ev["key"], 0) + ev["value"] * vol
        elif k == "dmg_out":
            self.dmg_out += ev["value"]
            self.hits_out += 1
            self.targets[ev["key"]] = self.targets.get(ev["key"], 0) + ev["value"]
            w = ev.get("weapon", "Schiff/Direkt")
            self.weapons[w] = self.weapons.get(w, 0) + ev["value"]
            self._dmg_bucket(ev["ts"], "out", ev["value"])
            if live:
                self.win_out.append((now, ev["value"]))
        elif k == "dmg_in":
            self.dmg_in += ev["value"]
            self.attackers[ev["key"]] = self.attackers.get(ev["key"], 0) + ev["value"]
            self._dmg_bucket(ev["ts"], "in", ev["value"])
            if live:
                self.win_in.append((now, ev["value"]))
        elif k == "miss_out":
            self.miss_out += 1
        elif k == "miss_in":
            self.miss_in += 1
        elif k == "ewar":
            self.ewar[ev["key"]] = self.ewar.get(ev["key"], 0) + 1
        elif k == "salvage":
            if ev["key"] in self.salvage:
                self.salvage[ev["key"]] += 1
        elif k == "bounty":
            self.bounty += ev["value"]
            self.kills += 1
        elif k == "compressed":
            self.cargo_full = False  # Kompression schafft Platz
            # Kern-Laufzeit aus Kompressions-Kadenz: Luecken > HW_CORE_GAP
            # zaehlen nicht (Kern war vermutlich aus / angedockt)
            tl = self.core_timeline
            cum = tl[-1][1] if tl else 0.0
            if tl:
                gap = ev["ts"] - tl[-1][0]
                if 0 < gap < HW_CORE_GAP:
                    cum += gap
            tl.append((ev["ts"], cum))
            if len(tl) > 6000:
                del tl[:1000]
            self.compressed[ev["key"]] = self.compressed.get(ev["key"], 0) + ev["value"]
            self.hold_comp[ev["key"]] = self.hold_comp.get(ev["key"], 0) + ev["value"]
            raw_ore = ev.get("raw")
            if raw_ore:
                self.hold_raw[raw_ore] = max(0, self.hold_raw.get(raw_ore, 0) - ev["value"])
        elif k == "hold_reset":
            self.hold_raw = {}
            self.hold_comp = {}
            self.cargo_full = False  # angedockt/gehandelt -> Frachtraum-Warnung hinfaellig
            self.lasers_off = {}     # an der Station sind alle Module ohnehin aus
            if ev["key"] == "dock":
                # Station-Stopp: Karte beginnt einen neuen Trip, sonst zeigen
                # ISK/Erz-Werte laengst abgeladene Ladung an. Historie (DB)
                # bleibt davon unberuehrt.
                self.trips += 1
                self.mining = {}
                self.compressed = {}
                self.weapons = {}
                self.targets = {}
                self.attackers = {}
                self.bounty = 0
                self.kills = 0
                self.dmg_out = self.dmg_in = 0
                self.hits_out = self.miss_out = self.miss_in = 0
                self.ewar = {}
                self.salvage = {"ok": 0, "empty": 0, "fail": 0}
                self.dmg_min = deque(maxlen=180)
                self.depleted = 0
                self.start = time.time()
                self.first_ts = ev["ts"]
        elif k == "depleted":
            self.depleted += 1
            if "Drone" not in ev["key"]:
                # Dauerstatus "Laser aus": Normalrate vor dem Ausfall merken
                # (Median der letzten vollen Minuten), damit die Erholung
                # erkannt werden kann, sobald die Rate wieder stimmt.
                completed = [t for t in (sum(mix.values())
                                         for _, mix in list(self.rate_min)[:-1]) if t > 0]
                tail = sorted(completed[-6:])
                before = tail[len(tail) // 2] if len(tail) >= 3 else None
                self.lasers_off[ev["key"]] = {"since": ev["ts"], "before": before}
            e = self.tool_off.setdefault(ev["key"], [0, 0])
            if ev["ts"] - e[1] > 60:
                e[0] = 0  # alter Vorfall abgelaufen -> neu zaehlen
            e[0] += 1
            e[1] = ev["ts"]
        elif k == "cargo":
            self.cargo_full = True
            self.cargo_ts = ev["ts"]
        elif k == "drone_idle":
            e = self.tool_off.setdefault("Mining Drone", [0, 0])
            e[0] += 1
            e[1] = ev["ts"]
        elif k == "drone_engage":
            # Drohnen arbeiten wieder — Drohnen-Warnungen sofort aufheben
            for tool in list(self.tool_off):
                if "Drone" in tool:
                    del self.tool_off[tool]

    def tool_warns(self):
        """Aktive Modul-Warnungen (letzte 60s), mit Werkzeugname."""
        cutoff = time.time() - 60
        out = []
        for tool, (cnt, ts) in list(self.tool_off.items()):
            if ts < cutoff:
                del self.tool_off[tool]
            else:
                out.append({"tool": tool, "count": cnt, "drone": "Drone" in tool})
        return out

    def rate_status(self):
        """(Normalrate, aktuelle Rate) in m3/min — verglichen wird nur mit
        Minuten desselben dominanten Erzes (Moissanite ist langsamer als
        Veldspar und darf keinen Fehlalarm ausloesen)."""
        entries = list(self.rate_min)
        if len(entries) < 7:
            return None
        nowm = int(time.time() // 60) * 60
        last3 = {nowm - 60, nowm - 120, nowm - 180}
        totals = {m: sum(mix.values()) for m, mix in entries}
        doms = {m: max(mix, key=mix.get) for m, mix in entries if mix}
        cur = sum(totals.get(m, 0) for m in last3) / 3
        vols = {}
        for m, mix in entries:
            if m in last3:
                for o, v in mix.items():
                    vols[o] = vols.get(o, 0) + v
        if not vols:
            return None
        dom = max(vols, key=vols.get)
        hist = sorted(t for m, t in totals.items()
                      if m not in last3 and m != nowm and t > 0 and doms.get(m) == dom)
        if len(hist) < 5:
            return None
        return hist[len(hist) // 2], cur

    def core_active_since(self, t0):
        """Sekunden mit laufendem Industriekern seit t0 (aus Kompressions-Kadenz)."""
        tl = self.core_timeline
        if not tl or tl[-1][0] <= t0:
            return 0.0
        base = 0.0
        for ts, cum in reversed(tl):
            if ts <= t0:
                base = cum
                break
        return tl[-1][1] - base

    def core_on(self):
        return bool(self.core_timeline) and time.time() - self.core_timeline[-1][0] < HW_CORE_GAP

    def idle_threshold(self, base):
        """Effektive Stillstand-Schwelle: 3x Median der Lieferabstaende,
        mindestens die konfigurierte Basis — passt sich Drohnen-Booten an."""
        if not self.gaps:
            return base
        med = sorted(self.gaps)[len(self.gaps) // 2]
        return max(base, 3 * med)

    def drones_idle(self, now=None):
        """True, wenn Mining-Drohnen liefen, jetzt aber keine Bursts mehr kommen,
        obwohl weiter Erz eintrifft (Laser laeuft, Drohnen stehen). Braucht ein
        gelerntes Zyklus-Muster (>=4 Bursts), sonst kein Urteil."""
        if self.drone_last is None or len(self.drone_gaps) < 4:
            return False
        now = now or time.time()
        if self.last_ore_ts is None or now - self.last_ore_ts > 180:
            return False   # gar kein Erz mehr -> Stillstand-Warnung greift, nicht drohnenspezifisch
        # Schwelle an die SCHWANKUNG der Abstaende anpassen: Drohnen fliegen je
        # nach Asteroiden-Distanz unterschiedlich lange (Rueckweg!), der Abstand
        # schwankt stark. 90%-Perzentil + 30s Puffer sitzt knapp ueber dem
        # normalen Maximal-Abstand -> kein Fehlalarm beim langen Rueckflug,
        # trotzdem schnelle Meldung bei gleichmaessigen Drohnen.
        g = sorted(self.drone_gaps)
        p90 = g[min(len(g) - 1, int(len(g) * 0.9))]
        return max(90, p90 + 30) < now - self.drone_last < 1800

    def laser_stalled(self, now=None):
        """True, wenn der Strip-Miner-/Laser-Strom abreisst, waehrend Drohnen
        weiterliefern (Laser manuell aus oder haengt). Dichte-Analyse: isolierte
        Lieferungen = Laser, dichte 4er-Cluster = Drohnen. Braucht ein gelerntes
        Laser-Muster; Erschoepfungs-Faelle deckt bereits lasers_off ab."""
        if self.lasers_off:
            return False   # Erschoepfung ist bereits erkannt -> keine Doppelmeldung
        now = now or time.time()
        ts = list(self.ore_hist)
        if len(ts) < 12:
            return False
        laser, drone = [], []
        for i, t in enumerate(ts):
            near = sum(1 for u in ts if abs(u - t) <= 6)
            (drone if near >= 4 else laser).append(t)
        if len(laser) < 5 or not drone:
            return False   # kein klares Laser-Muster oder gar keine Drohnen als Referenz
        # Drohnen muessen noch aktiv sein (sonst ist es Gesamt-Stillstand -> mine_idle)
        if now - drone[-1] > 180:
            return False
        gaps = sorted(b - a for a, b in zip(laser, laser[1:]) if 0 < b - a < 400)
        if len(gaps) < 4:
            return False
        # 25%-Perzentil als Takt: Laser-Lieferungen, die zufaellig mit einem
        # Drohnen-Burst zusammenfallen, werden als Drohne fehlklassifiziert und
        # blaehen den Median auf — das Perzentil bleibt beim echten Takt.
        p25 = gaps[len(gaps) // 4]
        return max(75, p25 * 3) < now - laser[-1] < 1800

    def dps(self, win):
        cut = time.time() - 60
        while win and win[0][0] < cut:
            win.popleft()
        return round(sum(d for _, d in win) / 60, 1)

    def _dmg_bucket(self, ts, side, val):
        """Schaden pro Minute sammeln (Kampfverlauf-Sparkline)."""
        minute = int(ts // 60) * 60
        if not self.dmg_min or self.dmg_min[-1][0] != minute:
            self.dmg_min.append([minute, {"out": 0, "in": 0}])
        self.dmg_min[-1][1][side] += val

    def mission_dict(self, end_ts, system):
        """Die gerade abgeschlossene Mission als Datensatz — oder None, wenn
        seit dem letzten Undock kein Kampf stattfand (z.B. reiner Mining-Trip)."""
        if not (self.bounty or self.kills or self.dmg_out):
            return None
        return {"char_id": self.char_id, "char": self.name,
                "start_ts": self.first_ts or end_ts, "end_ts": end_ts, "system": system,
                "dmg_out": self.dmg_out, "dmg_in": self.dmg_in, "kills": self.kills,
                "bounty": self.bounty, "hits": self.hits_out,
                "miss_out": self.miss_out, "miss_in": self.miss_in,
                "weapons": sorted(self.weapons.items(), key=lambda x: -x[1])[:6],
                "enemies": sorted(self.targets.items(), key=lambda x: -x[1])[:8]}


# ---------------------------------------------------------------- Ingest
class Ingest(threading.Thread):
    daemon = True

    def __init__(self):
        super().__init__()
        self.sessions = {}
        self.lock = threading.Lock()
        self.progress = {"done": 0, "total": 0}
        self.started_full = False
        self.filecache = {}  # name -> (size, mtime) fertig verarbeiteter Dateien
        self.live_files = []  # [(Pfad, cid)] der neuesten Datei je Char
        self.last_scan = 0.0  # Zeitpunkt des letzten Voll-Scans des Log-Ordners

    def log_dir(self):
        return Path(CONFIG["log_dir"]) if CONFIG["log_dir"] else None

    def run(self):
        while True:
            try:
                self.tick()
                self.check_idle()
                self.hw_tick()
                refresh_update_info()
            except Exception as e:
                log_error("CN-LOG-05", "Ingest.run", e)
            time.sleep(2)

    def hw_tick(self):
        """Schweres-Wasser-Buchhaltung: Verbrauch seit letztem Checkpoint abziehen,
        Stand in der Config sichern (uebersteht Neustarts), bei <30 min warnen."""
        with CONFIG_LOCK:
            hw = dict(CONFIG.get("heavy_water") or {})  # Kopie: do_POST/sync_ship mutieren parallel
        if not hw:
            return
        now = time.time()
        changed = False
        with self.lock:
            by_name = {s.name: s for s in self.sessions.values()}
        for char, e in hw.items():
            if now - e.get("ck", 0) < 60:
                continue
            e["ck"] = now
            s = by_name.get(char)
            if s is None:
                continue
            rate = HW_RATE.get(e.get("core"), HW_RATE["t1"])
            active = s.core_active_since(e.get("ts", now))
            if active > 0:
                e["units"] = max(0.0, e["units"] - active * rate)
                e["ts"] = now
                changed = True
            if (s.core_on() and not e.get("warned")
                    and e["units"] < rate * 1800):
                e["warned"] = True
                changed = True
                mins = int(e["units"] / rate / 60)
                alerts.push("hw", char,
                            f"{char}: Heavy Water fast leer, reicht noch etwa {mins} Minuten!")
        if changed:
            save_config()

    def check_idle(self):
        """Warnt, wenn ein aktiver Miner laenger als idle_warn kein Erz mehr liefert."""
        if not self.started_full:
            return
        thr = int(CONFIG.get("idle_warn", 240) or 0)
        now = time.time()
        # Drohnen- und Strip-Miner-Stillstand erscheinen NUR als Info in der
        # Charakter-Karte (Felder drones_idle/laser_stalled), nicht im Alarm-Banner.
        with self.lock:
            for s in self.sessions.values():
                if thr <= 0:
                    continue
                if s.last_ore_ts is None or s.idle_alerted:
                    continue
                idle = now - s.last_ore_ts
                eff = s.idle_threshold(thr)
                if eff < idle < 1800:
                    s.idle_alerted = True
                    alerts.push("idle", s.name,
                                f"{s.name}: Seit {round(idle / 60)} Minuten kein Erz. Laser und Drohnen prüfen!")
                # Raten-Waechter: Teilausfall (z.B. 1 von 2 Strip Minern aus)
                rs = s.rate_status()
                if rs:
                    base, cur = rs
                    if cur > 0 and cur < 0.55 * base:
                        if s.low_since is None:
                            s.low_since = now
                        elif now - s.low_since > 120 and not s.low_alerted:
                            s.low_alerted = True
                            alerts.push("rate", s.name,
                                        f"{s.name}: Abbaurate nur noch {round(100 * cur / base)}%. "
                                        f"Vermutlich ist ein Modul oder eine Drohne aus!")
                    else:
                        s.low_since = None
                        if cur >= 0.75 * base:
                            s.low_alerted = False

    def tick(self):
        d = self.log_dir()
        if not d or not d.exists():
            return
        # Voll-Scan des Ordners nur alle 15s (neue Dateien entstehen nur beim
        # EVE-Login). Dazwischen werden nur die Live-Dateien der Chars geprüft:
        # bei Jahren an Logs spart das den Grossteil der Dauerlast.
        full = time.time() - self.last_scan >= 15 or not self.live_files
        if full:
            self.last_scan = time.time()
            files = []
            for f in d.glob("*.txt"):
                m = CHAR_FILE_RE.match(f.name)
                if m:
                    try:
                        files.append((f, m.group(1), f.stat()))
                    except OSError:
                        continue
            newest = {}
            for f, cid, st in files:
                if cid not in newest or st.st_mtime > newest[cid][1]:
                    newest[cid] = (f, st.st_mtime)
            newest = {cid: f for cid, (f, _) in newest.items()}
            self.live_files = [(f, cid) for cid, f in newest.items()]
            self.progress["total"] = len(files)
        else:
            files = []
            for f, cid in self.live_files:
                try:
                    files.append((f, cid, f.stat()))
                except OSError:
                    self.last_scan = 0  # Datei weg? Beim nächsten Tick voll scannen
                    return
            newest = {cid: f for f, cid in self.live_files}
        done = 0
        for f, cid, st in sorted(files, key=lambda x: x[2].st_mtime):
            # Fertig gelesene Alt-Dateien ohne Datenbank-Zugriff überspringen.
            # Bei Jahren an Logs (zigtausend Dateien) macht das den Takt erst bezahlbar.
            if (self.filecache.get(f.name) == (st.st_size, st.st_mtime)
                    and newest.get(cid) != f):
                done += 1
                if full:
                    self.progress["done"] = done
                continue
            row = DB.execute("SELECT offset, skipped, char_name, first_ts, last_ts "
                             "FROM files WHERE name=?", (f.name,)).fetchone()
            if row is None:
                skip = (CONFIG["mode"] == "fresh"
                        and st.st_mtime < float(CONFIG["install_ts"])
                        and newest.get(cid) != f)
                name = read_char_name(f)
                with DB_LOCK:
                    DB.execute("INSERT OR REPLACE INTO files VALUES(?,?,?,?,?,NULL,NULL)",
                               (f.name, cid, name, st.st_size if skip else 0, int(skip)))
                    DB.commit()
                row = (st.st_size if skip else 0, int(skip), name, None, None)
            offset, skipped, cname, first_ts, last_ts = row
            if CONFIG["mode"] == "all" and skipped:
                with DB_LOCK:
                    DB.execute("UPDATE files SET offset=0, skipped=0 WHERE name=?", (f.name,))
                    DB.commit()
                offset, skipped = 0, 0
            live_file = newest.get(cid) == f
            sess = None
            if live_file and not skipped:
                fresh = time.time() - st.st_mtime <= SESSION_MAX_AGE
                with self.lock:
                    sess = self.sessions.get(cid)
                    if not fresh:
                        # Log seit Stunden unverändert (z.B. Session von gestern):
                        # keine Live-Karte aufbauen bzw. verwaiste entfernen.
                        # Kommen wieder Einträge, wird die Session beim nächsten
                        # Tick vollständig aus dem Dateikopf rekonstruiert.
                        self.sessions.pop(cid, None)
                        sess = None
                    elif sess is None or sess.file != f:
                        sess = CharSession(cid, cname, f)
                        self.sessions[cid] = sess
                        if offset > 0:
                            # Session-Statistik für bereits eingelesenen Teil rekonstruieren
                            try:
                                with open(f, "rb") as fh0:
                                    head = fh0.read(offset)
                                for bline in head.split(b"\n"):
                                    ev = parse_line(bline.decode("utf-8", "replace").lstrip("﻿"))
                                    if ev:
                                        sess.feed(ev, live=False)
                            except OSError:
                                pass
            if skipped or st.st_size <= offset:
                if newest.get(cid) != f:
                    self.filecache[f.name] = (st.st_size, st.st_mtime)
                done += 1
                if full:
                    self.progress["done"] = done
                continue
            try:
                catch_up = not self.started_full
                batch = []
                missions_done = []   # beim Undock abgeschlossene Missionen
                with open(f, "rb") as fh:
                    fh.seek(offset)
                    data = fh.read()
                cut = data.rfind(b"\n")
                if cut < 0:
                    done += 1
                    continue
                new_offset = offset + cut + 1
                now = time.time()
                # Session-Mutation unter self.lock, damit snapshot_live (HTTP-Thread)
                # nicht mitten in der Iteration von mining/rate_min/win_out crasht.
                with self.lock:
                    for bline in data[:cut + 1].split(b"\n"):
                        ev = parse_line(bline.decode("utf-8", "replace").lstrip("﻿"))
                        if ev:
                            batch.append(ev)
                            if sess:
                                # Undock schliesst die vorige Mission ab -> erfassen,
                                # BEVOR feed() die Kampfwerte der Session zuruecksetzt.
                                if ev["kind"] == "hold_reset" and ev["key"] == "dock":
                                    md = sess.mission_dict(ev["ts"],
                                                           chatwatch.systems.get(cid, "?"))
                                    if md:
                                        missions_done.append(md)
                                sess.feed(ev, live=not catch_up)
                            # Live-Alarme nur für wirklich frische Ereignisse (< 10 min).
                            # Schaltet man später auf "alle Logs", werden sonst Jahre an
                            # historischen PvP-Treffern als Alarm + zKill-Abfrage ausgelöst.
                            if not catch_up and now - ev["ts"] < 600:
                                self.live_alerts(ev, cname)
                                if ev["kind"] == "ore":
                                    self.learn_mine_system(cid)
                with DB_LOCK:
                    for ev in batch:
                        if ev["kind"] in ("drone_engage", "hold_reset"):
                            continue  # reine Live-Signale, nicht historisieren
                        db_add(ev["day"], cid, cname, ev["kind"], ev["key"], ev["value"])
                        if ev["kind"] == "dmg_out" and "weapon" in ev:
                            db_add(ev["day"], cid, cname, "weapon", ev["weapon"], ev["value"])
                        if ev["kind"] == "dmg_in" and ev.get("player"):
                            db_add(ev["day"], cid, cname, "pvp_in", ev["key"], ev["value"])
                    for md in missions_done:
                        save_mission(md)
                    if batch:
                        ts = [ev["ts"] for ev in batch]
                        first_ts = min(first_ts or ts[0], *ts)
                        last_ts = max(last_ts or ts[0], *ts)
                        DB.execute("UPDATE files SET first_ts=?, last_ts=? WHERE name=?",
                                   (first_ts, last_ts, f.name))
                    DB.execute("UPDATE files SET offset=? WHERE name=?", (new_offset, f.name))
                    DB.commit()
            except OSError:
                pass
            done += 1
            # Fortschritt live mitschreiben: beim Erst-Einlesen grosser Bestaende
            # (Jahre an Logs) soll die Anzeige nicht minutenlang auf 0 stehen
            if full:
                self.progress["done"] = done
        if full:
            self.progress["done"] = done
            self.started_full = True

    def learn_mine_system(self, cid):
        """Merkt sich Systeme, in denen aktiv gemint wird. Bounties aus diesen
        Systemen zählen nicht als Missions-Einkommen (Belt-Ratten-Filter)."""
        sysname = chatwatch.systems.get(cid)
        if not sysname or sysname == "?":
            return
        ms = CONFIG.setdefault("mine_systems", {})
        if sysname not in ms:
            ms[sysname] = 0  # System-ID löst der ESI-Thread nach
            save_config()

    def live_alerts(self, ev, cname):
        # Entwarnung: Gegensignal im Log macht alte Alarme sofort hinfaellig
        if ev["kind"] == "ore":
            alerts.resolve(("cargo", "idle", "rate"), cname)
            # Asteroid-leer erst nach 60s Anzeige loeschen: der zweite Laser
            # liefert evtl. weiter Erz, obwohl der erste noch neu gezielt
            # werden muss — die Warnung soll sichtbar bleiben.
            alerts.resolve(("depleted",), cname, min_age=60)
        elif ev["kind"] == "compressed":
            alerts.resolve(("cargo",), cname)
        elif ev["kind"] == "hold_reset":
            alerts.resolve(("cargo", "depleted", "idle"), cname)
        elif ev["kind"] == "drone_engage":
            alerts.resolve(("drones",), cname)
        # Drohnen-/Modul-Status (depleted, drone_idle) landet NICHT im oberen
        # Alarm-Banner — nur als Info in der jeweiligen Charakter-Karte (tool_warns).
        # Grund: 5 Drohnen erzeugten 5 fast identische Banner-Eintraege, und beim
        # Zurückfliegen der Drohnen ist ein kurzer Lieferstopp kein echtes Problem.
        if ev["kind"] == "cargo":
            alerts.push("cargo", cname, f"{cname}: Frachtraum voll, Mining gestoppt!")
        elif ev["kind"] == "dmg_in" and ev.get("player"):
            alerts.push("pvp", cname, f"SPIELER-ANGRIFF: {ev['key']} schießt auf {cname}!")
            # Täterprofil sofort nachladen — Ergebnis kommt als eigener Intel-Alarm
            threat.request([ev["key"]], prio=True, alert="yellow")


# ---------------------------------------------------------------- Local-Chat (System + Watchlist)
class ChatWatch(threading.Thread):
    daemon = True

    def __init__(self):
        super().__init__()
        self.systems = {}      # char_id -> System
        self.offsets = {}      # file -> offset
        self.started_full = False

    def chat_dir(self):
        if not CONFIG["log_dir"]:
            return None
        return Path(CONFIG["log_dir"]).parent / "Chatlogs"

    def run(self):
        while True:
            try:
                self.tick()
            except Exception as e:
                log_error("CN-CHAT-01", "ChatWatch.run", e)
            self.started_full = True
            time.sleep(3)

    def tick(self):
        d = self.chat_dir()
        if not d or not d.exists():
            return
        newest = {}
        for f in list(d.glob("Local_*.txt")) + list(d.glob("Lokal_*.txt")):
            m = re.search(r"_(\d+)\.txt$", f.name)
            if m:
                cid = m.group(1)
                if cid not in newest or f.stat().st_mtime > newest[cid].stat().st_mtime:
                    newest[cid] = f
        watch = {w.lower() for w in CONFIG.get("watchlist", [])}
        for cid, f in newest.items():
            off = self.offsets.get(f, 0)
            try:
                with open(f, "rb") as fh:
                    fh.seek(off)
                    data = fh.read()
                # UTF-16 = 2 Byte je Zeichen. Erwischt read() einen noch nicht
                # fertig geschriebenen Block mit ungerader Länge, nur die geraden
                # Bytes konsumieren; das letzte Byte bleibt für den nächsten Tick.
                usable = len(data) & ~1
                self.offsets[f] = off + usable
                for line in data[:usable].decode("utf-16-le", "replace").splitlines():
                    line = line.strip().lstrip("﻿").strip()
                    cm = CHAT_LINE_RE.match(line)
                    if not cm:
                        continue
                    sender, msg = cm.group(1).strip(), cm.group(2).strip()
                    if "EVE" in sender and ":" in msg:
                        self.systems[cid] = msg.rsplit(":", 1)[1].strip().rstrip("*")
                    elif self.started_full:
                        if watch and sender.lower() in watch:
                            alerts.push("watch", sender,
                                        f"Watchlist: {sender} ist im Local aktiv!")
                        # Jeden Local-Sprecher still einstufen; Alarm nur bei Rot
                        threat.request([sender], alert="red")
            except OSError:
                pass


# ---------------------------------------------------------------- Preise
class Prices(threading.Thread):
    daemon = True

    def __init__(self):
        super().__init__()
        self.cache = {}
        self.fetched = {}
        self.requested = {}   # region -> Set bereits angefragter typeIDs

    def wanted_ids(self):
        ids = set()
        for (ore,) in DB.execute("SELECT DISTINCT key FROM daily WHERE kind IN ('ore','compressed')"):
            t = ORE_TYPES.get(ore)
            if t:
                ids.add(t["typeID"])
                comp = ORE_TYPES.get("Compressed " + ore)
                if comp:  # Bewertung läuft über den Preis der komprimierten Variante
                    ids.add(comp["typeID"])
        return ids

    def get(self, region):
        return self.cache.setdefault(region, {})

    def run(self):
        while True:
            region = CONFIG["region"]
            ids = self.wanted_ids()
            # Sofort nachladen, wenn eine neue Erzsorte auftaucht (noch nie angefragt)
            # — sonst bliebe frisch abgebautes Erz bis zu 15 min ohne Preis. Wir merken
            # uns ANGEFRAGTE IDs (nicht nur zurückgelieferte), damit Erze ohne Markt
            # nicht alle 3s neu abgefragt werden.
            new_ids = ids - self.requested.get(region, set())
            due = time.time() - self.fetched.get(region, 0) > PRICE_REFRESH
            if ids and (due or new_ids):
                try:
                    url = (f"https://market.fuzzwork.co.uk/aggregates/"
                           f"?region={region}&types={','.join(map(str, sorted(ids)))}")
                    with urllib.request.urlopen(url, timeout=15) as r:
                        data = json.load(r)
                    self.cache[region] = {int(k): float(v["buy"]["max"]) for k, v in data.items()}
                    self.fetched[region] = time.time()
                    self.requested[region] = set(ids)
                except Exception as e:
                    log_error("CN-NET-01", f"Prices.run(region={region})", e)
                    self.fetched[region] = time.time() - PRICE_REFRESH + 60
            time.sleep(3)


# ---------------------------------------------------------------- ESI (offizielles EVE-SSO, PKCE)
SSO_AUTH = "https://login.eveonline.com/v2/oauth/authorize"
SSO_TOKEN = "https://login.eveonline.com/v2/oauth/token"
ESI_BASE = "https://esi.evetech.net/latest"
ESI_SCOPES = ("esi-assets.read_assets.v1 esi-location.read_ship_type.v1 "
              "esi-wallet.read_character_wallet.v1 esi-location.read_online.v1")
ESI_UA = f"EVE-Canary/{VERSION} (https://github.com/Eve-Online-Askend/eve-canary)"
# Eingebaute Canary-ESI-App: so muss kein Nutzer eine eigene App registrieren,
# er klickt nur "Mit EVE-Account verbinden". Die ID ist bei PKCE bauartbedingt
# KEIN Geheimnis (steht beim Login ohnehin in der URL) — hier nur verschleiert
# abgelegt, damit sie nicht im Klartext im Code oder in der Oberflaeche steht.
def _canary_cid():
    key = b"canary"
    raw = base64.b64decode("WwIKUkoaUlRcUEZNV1hcVUpPVlBbA0McVQQNUkVMU1Y=")
    return bytes(b ^ key[i % len(key)] for i, b in enumerate(raw)).decode()


CANARY_CID = _canary_cid()
HW_TYPE_ID = 16272  # Heavy Water
# Wallet-Journal-Typen fuer die Missions-Statistik
JOURNAL_TYPES = {"agent_mission_reward", "agent_mission_time_bonus_reward",
                 "bounty_prizes", "bounty_prize"}
CORE_TYPES = {62590: "t1", 62591: "t2",   # Medium Industrial Core I/II (Porpoise)
              58945: "t1", 58950: "t2"}   # Large Industrial Core I/II (Orca)
# Reine Drohnen-/Boost-Schiffe: haben KEINE Strip Miner, minern nur mit Drohnen.
# Für sie darf die "Strip Miner aus"-Warnung nie kommen.
DRONE_ONLY_SHIP_IDS = {42244,  # Porpoise
                       28606,  # Orca
                       28352}  # Rorqual
DRONE_ONLY_SHIP_NAMES = ("Porpoise", "Orca", "Rorqual")


class Esi(threading.Thread):
    """EVE-SSO-Login (PKCE, ohne Client-Secret) + periodischer Abgleich:
    Schweres Wasser im aktuellen Schiff, Kern-Typ aus der Fitting, Wallet."""
    daemon = True

    def __init__(self):
        super().__init__()
        self.pending = {}     # state -> code_verifier laufender Logins
        self.status = {}      # char -> Klartext-Status fuer die Optionen-Seite
        self.type_cache = {}  # type_id -> Name (Schiffstypen, öffentlicher Endpunkt)
        self.party_names = {} # id -> Name (Agenten aus dem Wallet-Journal)

    def cfg(self):
        return CONFIG.setdefault("esi", {"client_id": "", "chars": {}})

    def client_id(self):
        # Eigene Client-ID (Override fuer Fortgeschrittene) hat Vorrang, sonst
        # die eingebaute Canary-App -> Nutzer muss nichts registrieren/eintragen.
        return self.cfg().get("client_id") or CANARY_CID

    def redirect_uri(self):
        return f"http://localhost:{CONFIG.get('port', PORT_DEFAULT)}/sso/callback"

    def login_url(self):
        if not self.client_id():
            return None
        verifier = base64.urlsafe_b64encode(os.urandom(32)).rstrip(b"=").decode()
        challenge = base64.urlsafe_b64encode(
            hashlib.sha256(verifier.encode()).digest()).rstrip(b"=").decode()
        state = base64.urlsafe_b64encode(os.urandom(12)).rstrip(b"=").decode()
        self.pending[state] = verifier
        return SSO_AUTH + "?" + urllib.parse.urlencode({
            "response_type": "code", "redirect_uri": self.redirect_uri(),
            "client_id": self.client_id(), "scope": ESI_SCOPES,
            "code_challenge": challenge, "code_challenge_method": "S256",
            "state": state})

    def _token_request(self, data):
        req = urllib.request.Request(
            SSO_TOKEN, data=urllib.parse.urlencode(data).encode(),
            headers={"Content-Type": "application/x-www-form-urlencoded",
                     "User-Agent": ESI_UA})
        with urllib.request.urlopen(req, timeout=20) as r:
            return json.loads(r.read())

    def callback(self, code, state):
        """Auth-Code gegen Tokens tauschen. Liefert None bei Erfolg, sonst Fehlertext."""
        verifier = self.pending.pop(state, None)
        if not verifier:
            return "Die Login-Anfrage ist abgelaufen. Bitte starte den Login noch einmal."
        try:
            tok = self._token_request({
                "grant_type": "authorization_code", "code": code,
                "client_id": self.client_id(), "code_verifier": verifier})
            pay = tok["access_token"].split(".")[1]
            pay = json.loads(base64.urlsafe_b64decode(pay + "==="))
            name = pay["name"]
            self.cfg()["chars"][name] = {
                "char_id": int(pay["sub"].split(":")[-1]),
                "refresh": tok["refresh_token"], "access": tok["access_token"],
                "exp": time.time() + tok.get("expires_in", 1199) - 60,
                "assets_next": 0}
            save_config()
            self.status[name] = "verbunden"
            return None
        except Exception as e:
            return f"Token-Tausch fehlgeschlagen: {e}"

    def _access(self, c):
        if time.time() >= c.get("exp", 0) or not c.get("access"):
            tok = self._token_request({
                "grant_type": "refresh_token", "refresh_token": c["refresh"],
                "client_id": self.client_id()})
            c["refresh"] = tok.get("refresh_token", c["refresh"])
            c["access"] = tok["access_token"]
            c["exp"] = time.time() + tok.get("expires_in", 1199) - 60
            # Rotiertes Refresh-Token SOFORT sichern: CCP invalidiert das alte,
            # ein späterer Fehler im selben poll dürfte es sonst nie speichern.
            save_config()
        return c["access"]

    def _get(self, c, path, params=None):
        url = ESI_BASE + path + ("?" + urllib.parse.urlencode(params) if params else "")
        req = urllib.request.Request(url, headers={
            "Authorization": "Bearer " + self._access(c), "User-Agent": ESI_UA})
        with urllib.request.urlopen(req, timeout=30) as r:
            return json.loads(r.read()), r.headers

    def type_name(self, tid):
        n = self.type_cache.get(tid)
        if n:
            return n
        try:
            req = urllib.request.Request(f"{ESI_BASE}/universe/types/{tid}/",
                                         headers={"User-Agent": ESI_UA})
            with urllib.request.urlopen(req, timeout=15) as r:
                n = json.loads(r.read()).get("name")
        except Exception:
            return None
        if n:
            self.type_cache[tid] = n
        return n

    def sync_ship(self, name, c):
        """Heavy Water + Kern-Typ aus dem aktuellen Schiff uebernehmen."""
        ship, _ = self._get(c, f"/characters/{c['char_id']}/ship/")
        items, page = [], 1
        while True:
            data, hdr = self._get(c, f"/characters/{c['char_id']}/assets/",
                                  {"page": page})
            items += data
            if page >= int(hdr.get("X-Pages") or 1):
                break
            page += 1
        # Asset-Cache: erst nach Ablauf erneut fragen (ESI cached bis zu 1h)
        try:
            exp = email.utils.parsedate_to_datetime(hdr["Expires"]).timestamp()
        except Exception:
            exp = time.time() + 3600
        try:
            asof = email.utils.parsedate_to_datetime(hdr["Last-Modified"]).timestamp()
        except Exception:
            asof = time.time()
        c["assets_next"] = exp + 10
        # Cargo-Wert (Loot + mitgefuehrte Munition) fuer das PvP/Missions-Dashboard.
        # Kommt aus ESI, kein Kopieren noetig. "as_of"/"next" = wie alt / wann frisch,
        # weil ESI die Assets nur ~1x/Stunde aktualisiert.
        try:
            self.value_cargo(name, c, items, ship["ship_item_id"], asof, exp)
        except Exception as e:
            log_error("CN-ESI-01", "value_cargo", e)
        try:
            self.read_fitting(name, c, items, ship["ship_item_id"],
                              ship["ship_type_id"], asof, exp)
        except Exception as e:
            log_error("CN-ESI-01", "read_fitting", e)
        in_ship = [i for i in items if i.get("location_id") == ship["ship_item_id"]]
        units = sum(i["quantity"] for i in in_ship if i["type_id"] == HW_TYPE_ID)
        core = next((CORE_TYPES[i["type_id"]] for i in in_ship
                     if i["type_id"] in CORE_TYPES), None)
        with CONFIG_LOCK:
            hw = CONFIG.setdefault("heavy_water", {})
            prev = hw.get(name) or {}
            if core is None and units == 0:
                # Schiff ohne Industriekern (Barge, Hauler, ...) -> keine Anzeige
                if prev.get("esi"):
                    hw.pop(name, None)
            else:
                hw[name] = {"units": float(units), "fill": max(float(units), prev.get("fill") or 0),
                            "core": core or prev.get("core", "t1"),
                            "ts": time.time(), "ck": 0, "esi": True,
                            "warned": bool(prev.get("warned")) and units <= prev.get("units", 0)}

    def value_cargo(self, name, c, items, ship_item_id, asof, nxt):
        """Frachtraum des aktiven Schiffs bewerten (Jita), fuer die Loot-Anzeige."""
        cargo = [i for i in items if i.get("location_flag") == "Cargo"
                 and i.get("location_id") == ship_item_id]
        qty = {}
        for i in cargo:
            qty[i["type_id"]] = qty.get(i["type_id"], 0) + i["quantity"]
        pm = hub_prices("10000002", set(qty)) if qty else {}
        rows = []
        for tid, q in qty.items():
            buy, sell = pm.get(tid, (0, 0))
            rows.append({"name": self.type_name(tid) or str(tid), "qty": q,
                         "isk": round(q * buy)})
        rows.sort(key=lambda r: -r["isk"])
        with CONFIG_LOCK:
            c["cargo"] = {
                "buy": round(sum(q * pm.get(t, (0, 0))[0] for t, q in qty.items())),
                "sell": round(sum(q * pm.get(t, (0, 0))[1] for t, q in qty.items())),
                "as_of": int(asof), "next": int(nxt),
                "n": len(cargo), "items": rows[:12]}

    # Slot-Gruppe je location_flag (High/Mid/Low/Rig/Subsystem) fuer die grafische Anzeige
    SLOT_GROUP = [("hi", "HiSlot"), ("med", "MedSlot"), ("low", "LoSlot"),
                  ("rig", "RigSlot"), ("sub", "SubSystemSlot")]

    def read_fitting(self, name, c, items, ship_item_id, ship_tid, asof, nxt):
        """Gefittete Module des aktiven Schiffs aus den Assets lesen, nach Slot
        gruppiert. Fuer die grafische Fitting-Anzeige (Icons vom EVE-Bilderdienst)."""
        mods = []
        for i in items:
            if i.get("location_id") != ship_item_id:
                continue
            flag = i.get("location_flag", "")
            grp = next((g for g, pre in self.SLOT_GROUP if flag.startswith(pre)), None)
            if not grp:
                continue
            slot = int(re.search(r"\d+", flag).group())
            mods.append({"grp": grp, "slot": slot, "tid": i["type_id"],
                         "name": self.type_name(i["type_id"]) or str(i["type_id"])})
        order = {g: n for n, (g, _) in enumerate(self.SLOT_GROUP)}
        mods.sort(key=lambda x: (order.get(x["grp"], 9), x["slot"]))
        with CONFIG_LOCK:
            c["fitting"] = {"ship_tid": ship_tid, "as_of": int(asof), "next": int(nxt),
                            "mods": mods}

    def sync_journal(self, name, c):
        """Wallet-Journal einlesen: Missions-Belohnungen, Boni, Bounty-Ticks.
        Lokale Historie waechst unbegrenzt (ESI liefert nur ~30 Tage rueckwirkend)."""
        data, hdr = self._get(c, f"/characters/{c['char_id']}/wallet/journal/")
        pages = int(hdr.get("X-Pages") or 1)
        page = 2
        while page <= pages:  # aktive Tage/lange Offline-Zeit füllen mehrere Seiten
            more, _ = self._get(c, f"/characters/{c['char_id']}/wallet/journal/",
                                {"page": page})
            data += more
            page += 1
        try:
            exp = email.utils.parsedate_to_datetime(hdr["Expires"]).timestamp()
        except Exception:
            exp = time.time() + 3600
        c["journal_next"] = exp + 10
        try:  # Stand der ESI-Daten (Wallet aktualisiert ESI nur ~1x/Stunde)
            c["journal_asof"] = email.utils.parsedate_to_datetime(hdr["Last-Modified"]).timestamp()
        except Exception:
            c["journal_asof"] = time.time()
        keep = [e for e in data if e.get("ref_type") in JOURNAL_TYPES
                and (e.get("amount") or 0) > 0]
        ids = {e.get("first_party_id") for e in keep
               if str(e.get("ref_type", "")).startswith("agent_")}
        ids -= set(self.party_names)
        try:
            self.party_names.update(self._names(list(ids)))
        except Exception:
            pass
        with DB_LOCK:
            for e in keep:
                ts = datetime.fromisoformat(
                    e["date"].replace("Z", "+00:00")).timestamp()
                ctx = (e.get("context_id")
                       if e.get("context_id_type") == "system_id" else None)
                DB.execute("INSERT OR IGNORE INTO journal VALUES(?,?,?,?,?,?,?)",
                           (e["id"], name, ts, e["ref_type"], e["amount"],
                            self.party_names.get(e.get("first_party_id"), ""), ctx))
            DB.commit()

    def resolve_mine_systems(self):
        """System-Namen aus dem Belt-Bounty-Filter zu IDs auflösen (öffentlich)."""
        ms = CONFIG.get("mine_systems") or {}
        names = [n for n, i in ms.items() if not i]
        if not names:
            return False
        req = urllib.request.Request(
            ESI_BASE + "/universe/ids/", data=json.dumps(names).encode(),
            headers={"Content-Type": "application/json", "User-Agent": ESI_UA})
        with urllib.request.urlopen(req, timeout=20) as r:
            data = json.loads(r.read())
        for s in data.get("systems", []):
            ms[s["name"]] = s["id"]
        return bool(data.get("systems"))

    def poll(self):
        changed = False
        try:
            changed = self.resolve_mine_systems() or changed
        except Exception:
            pass
        for name, c in list(self.cfg().get("chars", {}).items()):
            try:
                bal, _ = self._get(c, f"/characters/{c['char_id']}/wallet/")
                c["wallet"] = bal
                if time.time() >= c.get("journal_next", 0):
                    self.sync_journal(name, c)
                ship, _ = self._get(c, f"/characters/{c['char_id']}/ship/")
                new_ship = ship["ship_type_id"] != c.get("ship_type_id")
                c["ship_type_id"] = ship["ship_type_id"]
                c["ship"] = self.type_name(ship["ship_type_id"]) or c.get("ship") or "?"
                if new_ship:
                    c["assets_next"] = 0  # Schiffswechsel -> Laderaum sofort neu abgleichen
                if time.time() >= c.get("assets_next", 0):
                    self.sync_ship(name, c)
                # Online-Status (Scope esi-location.read_online.v1). Fehlt der Scope
                # (Char noch nicht neu verbunden), liefert ESI 403 -> still ignorieren,
                # dann greift der Log-Aktivitäts-Fallback.
                try:
                    onl, _ = self._get(c, f"/characters/{c['char_id']}/online/")
                    c["online"] = bool(onl.get("online"))
                except Exception:
                    c.pop("online", None)  # Scope fehlt/Fehler -> Log-Aktivität greift
                self.status[name] = "verbunden"
                changed = True
            except urllib.error.HTTPError as e:
                self.status[name] = f"HTTP-Fehler {e.code}" + (
                    ". Login abgelaufen? Bitte neu verbinden." if e.code in (400, 401) else "")
            except Exception as e:
                self.status[name] = f"Fehler: {str(e)[:80]}"
        if changed:
            save_config()

    def run(self):
        time.sleep(6)
        while True:
            try:
                self.poll()
            except Exception as e:
                log_error("CN-ESI-01", "Esi.poll", e)
            time.sleep(120)


# ---------------------------------------------------------------- Bedrohungs-Ampel (öffentliche APIs)
# Opfer-Schiffsgruppen, die auf Miner-/Hauler-Ganks hindeuten
MINER_GROUPS = {463, 543,        # Mining Barge, Exhumer
                941, 883,        # Industrial Command Ship (Orca/Porpoise), Capital Industrial (Rorqual)
                28, 380, 1202,   # Hauler, Deep Space Transport, Blockade Runner
                513, 902}        # Freighter, Jump Freighter
THREAT_TTL = 12 * 3600           # Cache-Lebensdauer eines Profils


class ThreatIntel(threading.Thread):
    """Bedrohungs-Einstufung von Piloten über öffentliche APIs (ESI + zKillboard).
    Kein Login nötig. Ergebnisse landen im SQLite-Cache (Tabelle threat)."""
    daemon = True

    def __init__(self):
        super().__init__()
        self.queue = []          # [Name, ...] FIFO
        self.queued = set()      # lower(Name) zum Dedupen
        self.alert_on = {}       # lower(Name) -> Mindest-Stufe fuer Alarm ("red"/"yellow")
        self.lock = threading.Lock()
        self.wake = threading.Event()

    # ---------- oeffentliche Schnittstelle
    def request(self, names, prio=False, alert=None):
        """Namen zur Pruefung einreihen (nur unbekannte/abgelaufene). Liefert Cache-Treffer.
        alert: "yellow" = ab Gelb alarmieren (Angreifer), "red" = nur bei Rot (Sprecher)."""
        results, missing = {}, []
        for n in names:
            n = n.strip()
            if not n or len(n) > 37:
                continue
            hit = self.cached(n)
            if hit is not None:
                results[n] = hit
            else:
                missing.append(n)
        with self.lock:
            for n in missing:
                k = n.lower()
                if alert:
                    self.alert_on[k] = alert
                if k not in self.queued:
                    self.queued.add(k)
                    if prio:
                        self.queue.insert(0, n)
                    else:
                        self.queue.append(n)
        if missing:
            self.wake.set()
        return results

    def cached(self, name):
        row = DB.execute("SELECT data, ts FROM threat WHERE name=?", (name,)).fetchone()
        if row and time.time() - row[1] < THREAT_TTL:
            return json.loads(row[0])
        return None

    def pending(self):
        with self.lock:
            return len(self.queue)

    # ---------- Verarbeitung
    def _http(self, url, timeout=20):
        req = urllib.request.Request(url, headers={
            "User-Agent": ESI_UA, "Accept-Encoding": "gzip"})
        with urllib.request.urlopen(req, timeout=timeout) as r:
            raw = r.read()
            if r.headers.get("Content-Encoding") == "gzip":
                import gzip
                raw = gzip.decompress(raw)
            return json.loads(raw)

    def _post_ids(self, names):
        """ESI: Namen -> Charakter-IDs (exakte Treffer, oeffentlich)."""
        req = urllib.request.Request(
            ESI_BASE + "/universe/ids/", data=json.dumps(names).encode(),
            headers={"Content-Type": "application/json", "User-Agent": ESI_UA})
        with urllib.request.urlopen(req, timeout=20) as r:
            data = json.loads(r.read())
        return {c["name"]: c["id"] for c in data.get("characters", [])}

    def _names(self, ids):
        """ESI: IDs -> Namen (Corp/Allianz, oeffentlich)."""
        ids = [i for i in ids if i]
        if not ids:
            return {}
        req = urllib.request.Request(
            ESI_BASE + "/universe/names/", data=json.dumps(ids).encode(),
            headers={"Content-Type": "application/json", "User-Agent": ESI_UA})
        with urllib.request.urlopen(req, timeout=20) as r:
            return {e["id"]: e["name"] for e in json.loads(r.read())}

    @staticmethod
    def _classify(age_days, sec, recent_kills, miner_kills, total_kills, danger):
        if (miner_kills >= 3 and recent_kills >= 1) or sec <= -2.0 \
                or (age_days is not None and age_days < 60 and recent_kills >= 1):
            return "red"
        if recent_kills >= 3 or danger >= 60 or miner_kills >= 3:
            return "yellow"
        if recent_kills >= 1 or total_kills >= 10:
            return "yellow" if danger >= 30 else "green"
        return "green"

    def _store(self, name, data):
        with DB_LOCK:
            DB.execute("INSERT OR REPLACE INTO threat VALUES(?,?,?)",
                       (name, json.dumps(data), time.time()))
            DB.commit()
        k = name.lower()
        with self.lock:
            min_lvl = self.alert_on.pop(k, None)
        lvl = data.get("level")
        if min_lvl and (lvl == "red" or (lvl == "yellow" and min_lvl == "yellow")):
            lbl = "GANKER-VERDACHT" if lvl == "red" else "PvP-aktiv"
            alerts.push("intel", name,
                        f"⚠ {lbl}: {name} ({data.get('corp') or '?'}), "
                        f"{data.get('recent_kills', 0)} Kills in 60 Tagen, "
                        f"{data.get('miner_kills', 0)} Miner-Kills gesamt")

    def _profile(self, name, cid):
        pub = self._http(f"{ESI_BASE}/characters/{cid}/")
        age = None
        try:
            born = datetime.fromisoformat(pub["birthday"].replace("Z", "+00:00"))
            age = int((datetime.now(timezone.utc) - born).days)
        except Exception:
            pass
        z = self._http(f"https://zkillboard.com/api/stats/characterID/{cid}/") or {}
        months = z.get("months") or {}
        now = datetime.now(timezone.utc)
        keys = {(now.year, now.month)}
        for back in (1, 2):
            y, m = now.year, now.month - back
            while m < 1:
                m += 12
                y -= 1
            keys.add((y, m))
        recent = sum((v or {}).get("shipsDestroyed", 0) for k, v in months.items()
                     if (int(str(k)[:4]), int(str(k)[4:])) in keys)
        miner = sum((g or {}).get("shipsDestroyed", 0)
                    for gid, g in (z.get("groups") or {}).items()
                    if int(gid) in MINER_GROUPS)
        info = z.get("info") or {}
        nm = self._names([pub.get("corporation_id"), pub.get("alliance_id")])
        sec = float(info.get("secStatus") or 0.0)
        total = int(z.get("shipsDestroyed") or 0)
        danger = int(z.get("dangerRatio") or 0)
        return {
            "id": cid, "age_days": age, "sec": round(sec, 1),
            "corp": nm.get(pub.get("corporation_id")),
            "alliance": nm.get(pub.get("alliance_id")),
            "kills": total, "losses": int(z.get("shipsLost") or 0),
            "recent_kills": recent, "miner_kills": miner,
            "danger": danger, "gang": int(z.get("gangRatio") or 0),
            "level": self._classify(age, sec, recent, miner, total, danger)}

    def run(self):
        while True:
            self.wake.wait()
            with self.lock:
                batch = self.queue[:20]
                del self.queue[:20]
                if not self.queue:
                    self.wake.clear()
            if not batch:
                continue
            try:
                ids = self._post_ids(batch)
            except Exception as e:
                log_error("CN-INTEL-01", "ThreatIntel._post_ids", e)
                ids = {}
            idmap = {n.lower(): (n, i) for n, i in ids.items()}
            for raw in batch:
                real, cid = idmap.get(raw.lower(), (raw, None))
                try:
                    if cid is None:
                        data = {"level": "unknown", "note": "kein Charakter mit diesem Namen"}
                    else:
                        data = self._profile(real, cid)
                except Exception as e:
                    data = {"level": "unknown", "note": f"Abfrage fehlgeschlagen: {str(e)[:60]}"}
                self._store(raw, data)
                with self.lock:
                    self.queued.discard(raw.lower())
                time.sleep(1.1)  # zKillboard-Etikette: nicht schneller als ~1 Request/s


NAME_RE = re.compile(r"^[A-Za-z0-9][A-Za-z0-9' .-]{1,36}$")


class ClipWatch(threading.Thread):
    """Beobachtet die Windows-Zwischenablage (opt-in): Kopiert man im EVE-Local
    die Mitgliederliste (Strg+A, Strg+C), erkennt Canary die Namensliste und
    startet automatisch den Bedrohungs-Scan — ohne Alt-Tab. Der Inhalt bleibt
    lokal; nur als Pilotennamen erkannte Zeilen gehen zur Auflösung an ESI."""
    daemon = True

    def __init__(self):
        super().__init__()
        self.last = None
        self.names = []   # letzter automatisch erkannter Satz
        self.ts = 0

    @staticmethod
    def read_clipboard():
        import ctypes
        from ctypes import wintypes
        u32, k32 = ctypes.windll.user32, ctypes.windll.kernel32
        # 64-Bit-Handles: ohne explizite restypes stutzt ctypes auf 32 Bit!
        u32.GetClipboardData.restype = wintypes.HANDLE
        k32.GlobalLock.restype = ctypes.c_void_p
        k32.GlobalLock.argtypes = [wintypes.HANDLE]
        k32.GlobalUnlock.argtypes = [wintypes.HANDLE]
        if not u32.OpenClipboard(0):
            return None
        try:
            h = u32.GetClipboardData(13)  # CF_UNICODETEXT
            if not h:
                return None
            ptr = k32.GlobalLock(h)
            if not ptr:
                return None
            try:
                return ctypes.wstring_at(ptr)
            finally:
                k32.GlobalUnlock(h)
        finally:
            u32.CloseClipboard()

    def check(self):
        text = self.read_clipboard()
        if text is None or text == self.last or len(text) > 20000:
            self.last = text if text is not None and len(text) <= 20000 else self.last
            return
        self.last = text
        lines = [l.strip() for l in text.splitlines() if l.strip()]
        if not 2 <= len(lines) <= 300:
            return
        good = [l for l in lines if NAME_RE.match(l)]
        # nur reagieren, wenn der Inhalt klar wie eine Mitgliederliste aussieht
        if len(good) < 2 or len(good) / len(lines) < 0.8:
            return
        self.names = list(dict.fromkeys(good))[:200]
        self.ts = time.time()
        threat.request(self.names, alert="red")

    def run(self):
        while sys.platform == "win32":
            time.sleep(2)
            try:
                if CONFIG.get("clip_watch"):
                    self.check()
            except Exception as e:
                log_error("CN-CLIP-01", "ClipWatch.run", e)


ingest = Ingest()
chatwatch = ChatWatch()
prices = Prices()
esi = Esi()
threat = ThreatIntel()
clipwatch = ClipWatch()


# ---------------------------------------------------------------- Abfragen
def ore_value(ore, units, pm):
    """ISK und Volumen eines Erz-Postens. Bewertet wird zum Preis der
    komprimierten Variante (Komprimieren ist 1:1 in Stück), denn das ist der
    Wert, der beim Verkauf wirklich ankommt. Gibt es keine komprimierte
    Variante oder keinen Preis dafür, gilt der Rohpreis. Volumen immer vom Rohtyp."""
    t = ORE_TYPES.get(ore, {})
    comp = ORE_TYPES.get("Compressed " + ore)
    price = pm.get(comp["typeID"]) if comp else None
    if price is None:
        price = pm.get(t.get("typeID"), 0.0)
    return units * price, units * t.get("volume", 0.0)


def baseline_filter(rows):
    b_day = meta_get("baseline_day")
    if not b_day:
        return list(rows)
    offsets = {(d, c, k, key): v for d, c, k, key, v in DB.execute(
        "SELECT day,char_id,kind,key,value FROM baseline_offsets")}
    out = []
    for day, cid, cname, kind, key, value in rows:
        if day < b_day:
            continue
        if day == b_day:
            value -= offsets.get((day, cid, kind, key), 0)
            if value <= 0:
                continue
        out.append((day, cid, cname, kind, key, value))
    return out


def all_rows(days=None, kinds=None):
    q = "SELECT day,char_id,char_name,kind,key,value FROM daily WHERE 1=1"
    args = []
    if days:
        cutoff = datetime.now(timezone.utc).strftime("%Y-%m-%d")
        q += f" AND day > date('{cutoff}', '-{int(days)} day')"
    if kinds:
        q += f" AND kind IN ({','.join('?' * len(kinds))})"
        args += list(kinds)
    return baseline_filter(DB.execute(q, args).fetchall())


_LOGDIR_CHECK = {"ts": 0, "path": None, "ok": False, "n": 0}


def log_dir_status():
    """(gefunden?, Anzahl Gamelogs) im eingestellten Ordner. Kurz gecacht, weil
    state_info im Sekundentakt abgefragt wird und das sonst jedes Mal listet."""
    d = CONFIG.get("log_dir") or ""
    c = _LOGDIR_CHECK
    if c["path"] == d and time.time() - c["ts"] < 10:
        return c["ok"], c["n"]
    n = 0
    if not d:
        log_error("CN-LOG-01", "log_dir_status", "kein Pfad eingestellt")
    else:
        p = Path(d)
        if not p.is_dir():
            log_error("CN-LOG-02", "log_dir_status", d)
        else:
            try:
                n = sum(1 for f in p.iterdir() if CHAR_FILE_RE.match(f.name))
            except OSError as e:
                log_error("CN-LOG-04", "log_dir_status", e)
            if n == 0:
                log_error("CN-LOG-03", "log_dir_status", d)
    c.update(ts=time.time(), path=d, ok=n > 0, n=n)
    return c["ok"], n


def diagnose_text():
    """Kompakter Bericht zum Kopieren und Verschicken. Bewusst OHNE
    Charakternamen, Tokens oder Pfade mit Klarnamen-Anteil ausserhalb des
    Log-Ordners — nur was zur Fehlersuche noetig ist."""
    ok, n = log_dir_status()
    L = [f"EVE Canary Diagnose v{VERSION}",
         f"System   : {sys.platform} / {os.name} / Python {sys.version.split()[0]}",
         f"Log-Ordner: {CONFIG.get('log_dir') or '(nicht gesetzt)'}",
         f"           gefunden={ok}, Gamelogs={n}",
         f"Modus    : {CONFIG.get('mode')}   Autostart={AUTOSTART_OK} Clipboard={CLIPBOARD_OK}"]
    try:
        with DB_LOCK:
            files = DB.execute("SELECT COUNT(*) FROM files").fetchone()[0]
            daily = DB.execute("SELECT COUNT(*) FROM daily").fetchone()[0]
        L.append(f"Datenbank: {files} Logdateien erfasst, {daily} Tageswerte")
    except Exception as e:
        L.append(f"Datenbank: NICHT LESBAR ({type(e).__name__}: {e})")
    try:
        with ingest.lock:
            L.append(f"Sessions : {len(ingest.sessions)} aktiv")
    except Exception:
        pass
    L.append(f"ESI      : {len((CONFIG.get('esi') or {}).get('chars', {}))} Charaktere verbunden")
    # Meldungen, fuer die es kein Textmuster gibt. Bei DE/EN ist das harmloses
    # Rauschen, bei anderen Client-Sprachen stehen hier die Saetze, die noch
    # fehlen (Frachtraum voll, Abdocken, Handel, Drohnen abladen).
    hits = " ".join(f"{k}={v}" for k, v in LOG_TEXT_HITS.items())
    L.append(f"Sprachmuster: {hits}")
    if not any(LOG_TEXT_HITS.values()):
        L.append("  ACHTUNG: kein einziges Muster hat gegriffen — Client-Sprache")
        L.append("  vermutlich noch nicht abgedeckt. Die Zeilen unten helfen dabei.")
    if UNKNOWN_NOTIFY:
        L.append(f"\nUnerkannte Meldungen ({len(UNKNOWN_NOTIFY)}, fuer Sprachunterstuetzung):")
        for t in list(UNKNOWN_NOTIFY)[-30:]:
            L.append(f"  · {t}")
    if not ERRORS:
        L.append("\nFehler   : keine")
    else:
        L.append(f"\nFehler   : {len(ERRORS)} verschiedene (neueste zuletzt)")
        for e in list(ERRORS)[-25:]:
            when = datetime.fromtimestamp(e["ts"]).strftime("%d.%m. %H:%M:%S")
            times = f" x{e['n']}" if e["n"] > 1 else ""
            L.append(f"  [{e['code']}]{times} {when} {e['where']}")
            L.append(f"      {ERROR_HELP.get(e['code'], '?')}: {e['msg']}")
    return "\n".join(L)


def portrait_url(name):
    """Charakter-Portrait über den öffentlichen EVE-Bilderdienst. Die ID kommt
    vom ESI-Login oder aus dem Bedrohungs-Cache, sonst gibt es kein Bild."""
    c = (CONFIG.get("esi") or {}).get("chars", {}).get(name)
    cid = c.get("char_id") if c else None
    if not cid:
        hit = threat.cached(name)
        cid = hit.get("id") if hit else None
    return f"https://images.evetech.net/characters/{cid}/portrait?size=64" if cid else None


def snapshot_live():
    pm = prices.get(CONFIG["region"])
    chars = []
    with ingest.lock:
      sessions = list(ingest.sessions.values())
      for s in sessions:
        ores, ore_isk, m3 = [], 0.0, 0.0
        for ore, units in sorted(s.mining.items(), key=lambda x: -x[1]):
            isk, vol = ore_value(ore, units, pm)
            ore_isk += isk
            m3 += vol
            # known=False: Erz-Typ nicht in ORE_TYPES -> kein m3/ISK berechenbar.
            # Trotzdem sichtbar machen (mit Namen), statt still mit 0 zu verschlucken.
            ores.append({"ore": ore, "units": units, "m3": round(vol), "isk": round(isk),
                         "known": ore in ORE_TYPES})
        # Unbekannte Erze nach oben (zum Melden), sonst nach ISK-Wert
        ores.sort(key=lambda o: (0 if not o["known"] else 1, -o["isk"]))
        comp = []
        for ctype, units in sorted(s.compressed.items(), key=lambda x: -x[1]):
            t = ORE_TYPES.get(ctype, {})
            comp.append({"type": ctype, "units": units,
                         "m3": round(units * t.get("volume", 0.0)),
                         "isk": round(units * pm.get(t.get("typeID"), 0.0))})
        comp.sort(key=lambda k: -k["isk"])
        hold_isk = hold_m3 = 0.0
        hold_types = hold_missing = 0
        for tname, units in list(s.hold_raw.items()) + list(s.hold_comp.items()):
            if units <= 0:
                continue
            hold_types += 1
            t = ORE_TYPES.get(tname, {})
            price = pm.get(t.get("typeID"))
            if price is None:
                hold_missing += 1
                price = 0.0
            hold_isk += units * price
            hold_m3 += units * t.get("volume", 0.0)
        if hold_types == 0 or hold_missing == 0:
            hold_prices = "ok"
        elif hold_missing == hold_types:
            hold_prices = "none"
        else:
            hold_prices = "partial"
        mins = max((time.time() - (s.first_ts or s.start)) / 60, 1)
        hw_cfg = (CONFIG.get("heavy_water") or {}).get(s.name)
        hw = None
        if hw_cfg:
            rate = HW_RATE.get(hw_cfg.get("core"), HW_RATE["t1"])
            rem = max(0.0, hw_cfg["units"]
                      - s.core_active_since(hw_cfg.get("ts", 0)) * rate)
            on = s.core_on()
            hw = {"units": round(rem), "core": hw_cfg.get("core", "t1"), "on": on,
                  "fill": round(hw_cfg.get("fill") or 0), "esi": bool(hw_cfg.get("esi")),
                  "min_left": round(rem / rate / 60),
                  "eta": round(time.time() + rem / rate) if on else None}
        esi_char = (CONFIG.get("esi") or {}).get("chars", {}).get(s.name)
        # Aktiv/Online: ESI-Online-Status falls vorhanden (Scope granted), sonst
        # Log-Aktivität (letztes Ereignis < ACTIVE_WINDOW). Fallback deckt alle Chars ab.
        esi_online = (esi_char or {}).get("online")
        log_active = s.last_event_ts is not None and (time.time() - s.last_event_ts) < ACTIVE_WINDOW
        active = esi_online if isinstance(esi_online, bool) else log_active
        # Porpoise/Orca/Rorqual minern nur mit Drohnen (kein Strip Miner) -> keine
        # Laser-Warnungen. Läuft ein Industriekern, ist es ebenfalls so ein Boost-Schiff.
        _shipname = (esi_char or {}).get("ship") or ""
        drone_only = ((esi_char or {}).get("ship_type_id") in DRONE_ONLY_SHIP_IDS
                      or any(n in _shipname for n in DRONE_ONLY_SHIP_NAMES)
                      or s.core_on())
        chars.append({
            "heavy_water": hw,
            "active": active,
            "role": (CONFIG.get("roles") or {}).get(s.name, ""),
            "portrait": portrait_url(s.name),
            "esi_linked": esi_char is not None,
            "ship": (esi_char or {}).get("ship"),
            "wallet": (esi_char or {}).get("wallet"),
            "cargo": (esi_char or {}).get("cargo"),
            # Fitting nur zeigen, wenn es zum AKTUELLEN Schiff passt. Der ship/-
            # Endpunkt ist sekundenaktuell, die Assets (das Fitting) bis 1h alt —
            # nach einem Schiffswechsel wäre das gespeicherte Fitting sonst falsch.
            "fitting": (lambda ft, cur: ft if (ft and ft.get("ship_tid") == cur) else None)(
                (esi_char or {}).get("fitting"), (esi_char or {}).get("ship_type_id")),
            "trips": s.trips,
            "compressed": comp, "tool_warns": s.tool_warns(),
            "lasers_off": [] if drone_only else [{"tool": t, "since": int(i["since"])}
                           for t, i in sorted(s.lasers_off.items())],
            "rate_low": (lambda rs: round(100 * rs[1] / rs[0])
                         if rs and 0 < rs[1] < 0.55 * rs[0] else None)(s.rate_status()),
            "cargo_full": s.cargo_full and (time.time() - s.cargo_ts) < 300,
            "drones_idle": s.drones_idle(),
            "laser_stalled": False if drone_only else s.laser_stalled(),
            "hold_isk": round(hold_isk), "hold_m3": round(hold_m3),
            "hold_prices": hold_prices,
            "mine_idle": round(time.time() - s.last_ore_ts) if s.last_ore_ts else None,
            "idle_thr": round(s.idle_threshold(int(CONFIG.get("idle_warn", 240) or 0))),
            "name": s.name, "session_min": round(mins),
            "system": chatwatch.systems.get(s.char_id, "?"),
            "ores": ores, "m3": round(m3), "ore_isk": round(ore_isk),
            "m3h": round(m3 / mins * 60), "bounty": s.bounty, "kills": s.kills,
            "total_isk": round(ore_isk + s.bounty),
            "dmg_out": s.dmg_out, "dmg_in": s.dmg_in,
            "dps_out": s.dps(s.win_out), "dps_in": s.dps(s.win_in),
            "depleted": s.depleted,
            "weapons": sorted(s.weapons.items(), key=lambda x: -x[1])[:6],
            "top_targets": sorted(s.targets.items(), key=lambda x: -x[1])[:6],
            "top_attackers": sorted(s.attackers.items(), key=lambda x: -x[1])[:6],
            "hits_out": s.hits_out, "miss_out": s.miss_out, "miss_in": s.miss_in,
            "ewar": sorted(s.ewar.items(), key=lambda x: -x[1]),
            "salvage": s.salvage,
            "spark_out": [b[1]["out"] for b in list(s.dmg_min)[-60:]],
            "spark_in": [b[1]["in"] for b in list(s.dmg_min)[-60:]],
            "spark": [round(sum(mix.values())) for _, mix in list(s.rate_min)[-60:]],
        })
    chars.sort(key=lambda c: c["name"])
    return chars


CALC_CACHE = {}  # region -> {"ts": Zeit, "prices": {typeID: (buy, sell)}}
CALC_LOCK = threading.Lock()


def hub_prices(region, ids):
    """Buy/Sell-Preise für die angefragten Typen in einer Region, 15 min Cache."""
    with CALC_LOCK:
        e = CALC_CACHE.get(region)
        if e and time.time() - e["ts"] < PRICE_REFRESH and ids <= set(e["prices"]):
            return dict(e["prices"])
    url = (f"https://market.fuzzwork.co.uk/aggregates/?region={region}"
           f"&types={','.join(map(str, sorted(ids)))}")
    with urllib.request.urlopen(url, timeout=15) as r:
        data = json.load(r)
    fetched = {int(k): (float(v["buy"]["max"]), float(v["sell"]["min"]))
               for k, v in data.items()}
    with CALC_LOCK:
        merged = CALC_CACHE.get(region, {}).get("prices", {})
        merged.update(fetched)
        CALC_CACHE[region] = {"ts": time.time(), "prices": merged}
        return dict(merged)


def parse_calc_text(text):
    """Zeilen wie 'Compressed Veldspar<TAB>49.105' (Frachtraum-Kopie) oder
    'Compressed Scordite 42000' in (Typname, Menge) übersetzen."""
    names = sorted(ORE_TYPES, key=len, reverse=True)
    items, unknown = {}, []
    for raw in (text or "").splitlines():
        line = raw.strip()
        if not line:
            continue
        low = line.lower()
        match = next((n for n in names if low.startswith(n.lower())), None)
        if not match:
            unknown.append(line.split("\t")[0][:40])
            continue
        rest = line[len(match):].lstrip("*").split("\t")
        qty = 1
        for part in rest:
            m = NUM_RE.search(STRIP_RE.sub("", part))
            if m and num(m.group(1)) > 0:
                qty = num(m.group(1))
                break
        items[match] = items.get(match, 0) + qty
    return items, unknown


def calc_hubs(text):
    items, unknown = parse_calc_text(text)
    if not items:
        return {"ok": True, "items": [], "unknown": unknown}
    ids = {ORE_TYPES[n]["typeID"] for n in items}
    hubs, jita = {}, {}
    for rid, rname in REGIONS.items():
        try:
            pm = hub_prices(rid, ids)
        except Exception:
            hubs[rid] = {"name": rname, "error": True}
            continue
        if rid == "10000002":
            jita = pm
        hubs[rid] = {"name": rname,
                     "buy": round(sum(q * pm.get(ORE_TYPES[n]["typeID"], (0, 0))[0]
                                      for n, q in items.items())),
                     "sell": round(sum(q * pm.get(ORE_TYPES[n]["typeID"], (0, 0))[1]
                                       for n, q in items.items()))}
    rows = [{"name": n, "qty": q,
             "m3": round(q * ORE_TYPES[n].get("volume", 0)),
             "isk": round(q * jita.get(ORE_TYPES[n]["typeID"], (0, 0))[0])}
            for n, q in items.items()]
    rows.sort(key=lambda r: -r["isk"])
    return {"ok": True, "items": rows, "hubs": hubs, "unknown": unknown,
            "m3": round(sum(r["m3"] for r in rows))}


def resolve_item_ids(names):
    """Item-Namen -> typeID, mit lokalem Cache in der DB. Unbekannte werden
    einmal bei ESI (/universe/ids/) nachgeschlagen und dann gemerkt, damit die
    Loot-Bewertung nicht bei jedem Mal ESI anfragt."""
    out, missing = {}, []
    with DB_LOCK:
        for n in names:
            row = DB.execute("SELECT type_id FROM item_ids WHERE name=?", (n,)).fetchone()
            if row:
                if row[0]:
                    out[n] = row[0]
            else:
                missing.append(n)
    for i in range(0, len(missing), 500):   # ESI nimmt bis 1000, wir bleiben moderat
        batch = missing[i:i + 500]
        found = {}
        try:
            req = urllib.request.Request(
                ESI_BASE + "/universe/ids/", data=json.dumps(batch).encode(),
                headers={"Content-Type": "application/json", "User-Agent": ESI_UA})
            with urllib.request.urlopen(req, timeout=20) as r:
                data = json.loads(r.read())
            found = {t["name"]: t["id"] for t in data.get("inventory_types", [])}
        except Exception as e:
            log_error("CN-NET-01", "resolve_item_ids", e)
        with DB_LOCK:
            for n in batch:
                tid = found.get(n)
                # auch 0/NULL merken, damit ein unbekannter Name nicht bei jedem
                # Einfügen erneut ESI belastet
                DB.execute("INSERT OR REPLACE INTO item_ids VALUES(?,?)", (n, tid or 0))
                if tid:
                    out[n] = tid
            DB.commit()
    return out


def calc_loot(text):
    """Beliebige Frachtraum-Kopie (Loot, nicht nur Erz) über alle Handelsplätze
    bewerten. Namen kommen aus dem ersten Tab-Feld, Menge aus dem Rest."""
    qty = {}
    for raw in (text or "").splitlines():
        line = raw.strip()
        if not line:
            continue
        cols = line.split("\t")
        name = cols[0].strip()
        if not name:
            continue
        n = 1
        for part in cols[1:] + [""]:
            m = NUM_RE.search(STRIP_RE.sub("", part))
            if m and num(m.group(1)) > 0:
                n = num(m.group(1))
                break
        qty[name] = qty.get(name, 0) + n
    ids_map = resolve_item_ids(list(qty))
    unknown = [n for n in qty if n not in ids_map]
    ids = set(ids_map.values())
    hubs, jita = {}, {}
    for rid, rname in REGIONS.items():
        try:
            pm = hub_prices(rid, ids) if ids else {}
        except Exception:
            hubs[rid] = {"name": rname, "error": True}
            continue
        if rid == "10000002":
            jita = pm
        hubs[rid] = {"name": rname,
                     "buy": round(sum(q * pm.get(ids_map[n], (0, 0))[0]
                                      for n, q in qty.items() if n in ids_map)),
                     "sell": round(sum(q * pm.get(ids_map[n], (0, 0))[1]
                                       for n, q in qty.items() if n in ids_map))}
    rows = [{"name": n, "qty": q,
             "isk": round(q * jita.get(ids_map[n], (0, 0))[0])}
            for n, q in qty.items() if n in ids_map]
    rows.sort(key=lambda r: -r["isk"])
    return {"ok": True, "items": rows, "hubs": hubs, "unknown": unknown}


def query_summary():
    """Geminert-Wert heute, gestern und letzte 7 Tage (ISK und m3) für die Ertrags-Leiste."""
    pm = prices.get(CONFIG["region"])
    today = datetime.now(timezone.utc).date()
    isk, m3 = {}, {}
    # Nur Roherz zählen: das Komprimat ist dasselbe Material, sonst zählt es doppelt
    for day, cid, cname, kind, key, value in all_rows(days=8, kinds=("ore",)):
        i, v = ore_value(key, value, pm)
        isk[day] = isk.get(day, 0) + i
        m3[day] = m3.get(day, 0) + v
    t = today.strftime("%Y-%m-%d")
    y = (today - timedelta(days=1)).strftime("%Y-%m-%d")
    week = {(today - timedelta(days=n)).strftime("%Y-%m-%d") for n in range(7)}
    return {"today": round(isk.get(t, 0)), "yesterday": round(isk.get(y, 0)),
            "week": round(sum(v for d, v in isk.items() if d in week)),
            "m3_today": round(m3.get(t, 0)),
            "m3_week": round(sum(v for d, v in m3.items() if d in week))}


def query_month():
    pm = prices.get(CONFIG["region"])
    days = {}
    for day, cid, cname, kind, key, value in all_rows(days=30):
        d = days.setdefault(day, {"day": day, "chars": {}, "ore_isk": 0, "bounty": 0,
                                  "m3": 0, "dmg_out": 0, "dmg_in": 0, "depleted": 0})
        c = d["chars"].setdefault(cname, {"ore_isk": 0, "bounty": 0})
        if kind == "ore":
            isk, vol = ore_value(key, value, pm)
            d["ore_isk"] += isk
            d["m3"] += vol
            c["ore_isk"] += isk
        elif kind == "bounty":
            d["bounty"] += value
            c["bounty"] += value
        elif kind in ("dmg_out", "dmg_in", "depleted"):
            d[kind] += value
    out = sorted(days.values(), key=lambda d: d["day"])
    for d in out:
        d["ore_isk"] = round(d["ore_isk"])
        d["m3"] = round(d["m3"])
        d["depleted"] = round(d["depleted"])
        d["total"] = round(d["ore_isk"] + d["bounty"])
        d["chars"] = {k: {"ore_isk": round(v["ore_isk"]), "bounty": round(v["bounty"])}
                      for k, v in d["chars"].items()}
    return out


def query_total():
    pm = prices.get(CONFIG["region"])
    t = {"ore_isk": 0.0, "m3": 0.0, "bounty": 0, "dmg_out": 0, "dmg_in": 0,
         "units": 0, "days": set(), "ores": {}, "chars": {}, "depleted": 0}
    comp = {}
    day_isk = {}
    for day, cid, cname, kind, key, value in all_rows():
        t["days"].add(day)
        c = t["chars"].setdefault(cname, {"ore_isk": 0, "bounty": 0, "m3": 0})
        if kind == "ore":
            isk, vol = ore_value(key, value, pm)
            t["ore_isk"] += isk
            t["m3"] += vol
            t["units"] += value
            t["ores"][key] = t["ores"].get(key, 0) + value
            c["ore_isk"] += isk
            c["m3"] += vol
            day_isk[day] = day_isk.get(day, 0) + isk
        elif kind == "bounty":
            t["bounty"] += value
            c["bounty"] += value
            day_isk[day] = day_isk.get(day, 0) + value
        elif kind == "compressed":
            e = comp.setdefault(cname, {})
            e[key] = e.get(key, 0) + value
        elif kind in ("dmg_out", "dmg_in", "depleted"):
            t[kind] += value
    comp_list = []
    for cname, types in sorted(comp.items()):
        for ctype, units in sorted(types.items(), key=lambda x: -x[1]):
            tt = ORE_TYPES.get(ctype, {})
            comp_list.append({"char": cname, "type": ctype, "units": round(units),
                              "m3": round(units * tt.get("volume", 0.0)),
                              "isk": round(units * pm.get(tt.get("typeID"), 0.0))})
    best = max(day_isk.items(), key=lambda x: x[1]) if day_isk else ("—", 0)
    ores = []
    for ore, units in t["ores"].items():
        isk, vol = ore_value(ore, units, pm)
        ores.append({"ore": ore, "units": units, "m3": round(vol), "isk": round(isk)})
    ores.sort(key=lambda o: -o["isk"])
    ores = ores[:15]
    return {"ore_isk": round(t["ore_isk"]), "m3": round(t["m3"]), "bounty": t["bounty"],
            "total_isk": round(t["ore_isk"] + t["bounty"]), "units": t["units"],
            "days_active": len(t["days"]), "dmg_out": t["dmg_out"], "dmg_in": t["dmg_in"],
            "depleted": round(t["depleted"]),
            "best_day": {"day": best[0], "isk": round(best[1])}, "ores": ores,
            "compressed": comp_list,
            "chars": {k: {kk: round(vv) for kk, vv in v.items()} for k, v in t["chars"].items()}}


def compression_periods():
    """Kompressions-Bilanz je Zeitraum: gesamt + pro Charakter, nach Typ."""
    pm = prices.get(CONFIG["region"])
    today = datetime.now(timezone.utc).date()
    cuts = {"today": 0, "week": 6, "month": 29, "year": 364}
    rows = all_rows(kinds=["compressed"])

    def pack(d):
        types, U, M, I = [], 0, 0.0, 0.0
        for ctype, units in d.items():
            t = ORE_TYPES.get(ctype, {})
            isk = units * pm.get(t.get("typeID"), 0.0)
            m3 = units * t.get("volume", 0.0)
            U += units
            M += m3
            I += isk
            types.append({"type": ctype, "units": round(units), "m3": round(m3),
                          "isk": round(isk)})
        types.sort(key=lambda x: -x["isk"])
        return {"units": round(U), "m3": round(M), "isk": round(I), "types": types}

    out = {}
    for pkey, back in cuts.items():
        cutoff = (today - timedelta(days=back)).strftime("%Y-%m-%d")
        agg_t, agg_c = {}, {}
        for day, cid, cname, kind, key, value in rows:
            if day < cutoff:
                continue
            agg_t[key] = agg_t.get(key, 0) + value
            d = agg_c.setdefault(cname, {})
            d[key] = d.get(key, 0) + value
        out[pkey] = {"total": pack(agg_t),
                     "chars": {c: pack(d) for c, d in sorted(agg_c.items())}}
    return out


def query_analyse():
    pm = prices.get(CONFIG["region"])
    # Waffen
    weapons = {}
    for day, cid, cname, kind, key, value in all_rows(kinds=["weapon"]):
        weapons[key] = weapons.get(key, 0) + value
    # PvP-Vorfälle
    pvp = {}
    for day, cid, cname, kind, key, value in all_rows(kinds=["pvp_in"]):
        e = pvp.setdefault(key, {"dmg": 0, "days": set(), "char": cname})
        e["dmg"] += value
        e["days"].add(day)
    pvp_list = [{"attacker": k, "dmg": round(v["dmg"]), "char": v["char"],
                 "days": sorted(v["days"])} for k, v in
                sorted(pvp.items(), key=lambda x: -x[1]["dmg"])][:15]
    # Effizienz: ISK/m3 je geschürfter Erzart
    eff = []
    for day, cid, cname, kind, key, value in all_rows(kinds=["ore"]):
        eff.append((key, value))
    agg = {}
    for ore, units in eff:
        agg[ore] = agg.get(ore, 0) + units
    eff_list = []
    for ore, units in agg.items():
        t = ORE_TYPES.get(ore, {})
        price = pm.get(t.get("typeID"), 0.0)
        vol = t.get("volume", 0.0) or 1
        eff_list.append({"ore": ore, "units": units, "isk_per_m3": round(price / vol, 1),
                         "isk": round(units * price), "m3": round(units * vol)})
    eff_list.sort(key=lambda x: -x["isk_per_m3"])
    # Spielzeit pro Tag (aus Session-Dateien)
    b_ts = float(meta_get("baseline_ts") or 0)
    play = {}
    for name, cname, first_ts, last_ts in DB.execute(
            "SELECT name, char_name, first_ts, last_ts FROM files "
            "WHERE first_ts IS NOT NULL AND skipped=0"):
        if last_ts and last_ts > b_ts:
            day = datetime.fromtimestamp(max(first_ts, b_ts),
                                         timezone.utc).strftime("%Y-%m-%d")
            d = play.setdefault(day, {"day": day, "minutes": 0, "chars": {}})
            mins = (last_ts - max(first_ts, b_ts)) / 60
            d["minutes"] += mins
            d["chars"][cname] = d["chars"].get(cname, 0) + mins
    play_list = sorted(play.values(), key=lambda x: x["day"])
    for p in play_list:
        p["minutes"] = round(p["minutes"])
        p["chars"] = {k: round(v) for k, v in p["chars"].items()}
    # Ziel & Prognose
    goal = CONFIG.get("goal")
    goal_info = None
    total = query_total()
    month = query_month()
    if goal and goal.get("isk"):
        last7 = [d["total"] for d in month[-7:]]
        avg = sum(last7) / max(len(last7), 1)
        remaining = max(0, goal["isk"] - total["total_isk"])
        eta_days = round(remaining / avg, 1) if avg > 0 else None
        eta_date = ((datetime.now() + timedelta(days=eta_days)).strftime("%Y-%m-%d")
                    if eta_days is not None else None)
        goal_info = {"isk": goal["isk"], "deadline": goal.get("deadline"),
                     "current": total["total_isk"],
                     "pct": round(100 * total["total_isk"] / goal["isk"], 1),
                     "avg7": round(avg), "eta_days": eta_days, "eta_date": eta_date}
    return {"weapons": sorted(weapons.items(), key=lambda x: -x[1])[:10],
            "pvp": pvp_list, "efficiency": eff_list, "playtime": play_list,
            "goal": goal_info, "depleted_total": total["depleted"],
            "compression": compression_periods()}


def state_info():
    return {"region": CONFIG["region"], "regions": REGIONS, "mode": CONFIG["mode"],
            "baseline_day": meta_get("baseline_day"), "log_dir": CONFIG["log_dir"],
            "idle_warn": int(CONFIG.get("idle_warn", 240) or 0),
            "clip_watch": bool(CONFIG.get("clip_watch")),
            "autostart": AUTOSTART_OK and autostart_path().exists(),
            # Was diese Plattform kann — die Oberflaeche blendet den Rest aus,
            # damit auf Linux keine toten Schalter stehen.
            "autostart_ok": AUTOSTART_OK, "clip_ok": CLIPBOARD_OK,
            # Ohne gueltigen Log-Ordner zeigt die Oberflaeche erst die
            # Einrichtung statt eines leeren Dashboards.
            "log_ok": log_dir_status()[0], "log_count": log_dir_status()[1],
            # Fehlercodes fuer den Support: der Nutzer schickt die Diagnose
            "errors": [{"code": e["code"], "n": e["n"], "ts": int(e["ts"]),
                        "help": ERROR_HELP.get(e["code"], "")} for e in list(ERRORS)[-10:]],
            "update": {"available": UPDATE_INFO["available"],
                       "latest": UPDATE_INFO["latest"]},
            "version": VERSION,
            "ingesting": not ingest.started_full,
            "progress": ingest.progress, "prices_loaded": bool(prices.get(CONFIG["region"])),
            "watchlist": CONFIG.get("watchlist", []), "goal": CONFIG.get("goal"),
            "esi": {"client_id": (CONFIG.get("esi") or {}).get("client_id", ""),
                    "cb": esi.redirect_uri(),
                    "chars": [{"name": n, "status": esi.status.get(n, "warte auf Abgleich …"),
                               "ship": c.get("ship"), "wallet": c.get("wallet")}
                              for n, c in (CONFIG.get("esi") or {}).get("chars", {}).items()]},
            "alerts": alerts.list()}


def query_mission_history(limit=40):
    """Einzelne Missionen (aus den Gamelogs, an Undock-Grenzen getrennt), neueste
    zuerst, inkl. vom Nutzer eingefügtem Loot."""
    with DB_LOCK:
        rows = DB.execute(
            """SELECT mid,char,start_ts,end_ts,system,dmg_out,dmg_in,kills,bounty,
                      hits,miss_out,miss_in,weapons,enemies,loot_isk,loot_text
               FROM missions ORDER BY start_ts DESC LIMIT ?""", (limit,)).fetchall()
    out = []
    for r in rows:
        (mid, char, st, et, sysn, do, di, kills, bounty, hits, mo, mi,
         wj, ej, loot, loot_text) = r
        shots = (hits or 0) + (mo or 0)
        out.append({
            "mid": mid, "char": char, "start": int(st or 0), "end": int(et or 0),
            "min": round(((et or 0) - (st or 0)) / 60), "system": sysn or "?",
            "dmg_out": do or 0, "dmg_in": di or 0, "kills": kills or 0,
            "bounty": round(bounty or 0), "hit": round(100 * hits / shots) if shots else None,
            "weapons": json.loads(wj or "[]"), "enemies": json.loads(ej or "[]"),
            "loot_isk": round(loot) if loot else None, "loot_text": loot_text or "",
            "total": round((bounty or 0) + (loot or 0))})
    return out


def query_missions():
    """Missions-Statistik aus dem Wallet-Journal: Tage, Quellen, Agenten, Chars.
    Bounties aus bekannten Mining-Systemen bleiben draussen (Belt-Ratten)."""
    mine_sys = CONFIG.get("mine_systems") or {}
    mine_ids = {i for i in mine_sys.values() if i}
    rows = DB.execute(
        "SELECT char, ts, ref_type, amount, party, ctx FROM journal").fetchall()
    days, agents, chars = {}, {}, {}
    for char, ts, ref, amount, party, ctx in rows:
        if ref in ("bounty_prizes", "bounty_prize") and ctx in mine_ids:
            continue
        day = datetime.fromtimestamp(ts, timezone.utc).strftime("%Y-%m-%d")
        d = days.setdefault(day, {"day": day, "missions": 0, "reward": 0,
                                  "bonus": 0, "bounty": 0, "total": 0})
        c = chars.setdefault(char, {"char": char, "missions": 0, "total": 0})
        d["total"] += amount
        c["total"] += amount
        if ref == "agent_mission_reward":
            d["missions"] += 1
            d["reward"] += amount
            c["missions"] += 1
            if party:
                a = agents.setdefault(party, {"agent": party, "missions": 0, "isk": 0})
                a["missions"] += 1
                a["isk"] += amount
        elif ref == "agent_mission_time_bonus_reward":
            d["bonus"] += amount
            if party:
                agents.setdefault(party, {"agent": party, "missions": 0, "isk": 0})["isk"] += amount
        else:
            d["bounty"] += amount
    day_list = sorted(days.values(), key=lambda d: d["day"], reverse=True)
    today = datetime.now(timezone.utc).strftime("%Y-%m-%d")
    # Gegner der letzten 30 Tage aus den Gamelogs (nicht aus dem Journal):
    # wen hast du bekaempft, wer hat zurueckgeschossen.
    foes = {}
    for _day, _cid, _cname, kind, key, value in all_rows(30, ("dmg_out", "dmg_in")):
        if not key or key == "?":
            continue
        f = foes.setdefault(key, {"name": key, "dealt": 0, "taken": 0})
        f["dealt" if kind == "dmg_out" else "taken"] += value
    # ESI-Frische des Wallet-Journals (aktualisiert nur ~1x/Stunde) — für den
    # "Stand"-Hinweis, damit die verzögerten Zahlen nicht als Fehler wirken.
    jchars = list((CONFIG.get("esi") or {}).get("chars", {}).values())
    asofs = [c["journal_asof"] for c in jchars if c.get("journal_asof")]
    nexts = [c["journal_next"] for c in jchars if c.get("journal_next")]
    return {
        "mine_systems": sorted(n for n, i in mine_sys.items() if i),
        "linked": bool((CONFIG.get("esi") or {}).get("chars")),
        "asof": int(min(asofs)) if asofs else None,
        "next": int(min(nexts)) if nexts else None,
        "today": days.get(today) or {"day": today, "missions": 0, "reward": 0,
                                     "bonus": 0, "bounty": 0, "total": 0},
        "days": [{k: (round(v) if isinstance(v, float) else v) for k, v in d.items()}
                 for d in day_list[:30]],
        "foes": sorted(({"name": f["name"], "dealt": round(f["dealt"]),
                         "taken": round(f["taken"])} for f in foes.values()),
                       key=lambda f: -(f["dealt"] + f["taken"]))[:20],
        "agents": sorted(({**a, "isk": round(a["isk"])} for a in agents.values()),
                         key=lambda a: -a["isk"])[:10],
        "chars": sorted(({**c, "total": round(c["total"])} for c in chars.values()),
                        key=lambda c: -c["total"])}


def _csv_cell(s):
    """Formel-Injection neutralisieren: Excel/Calc fuehren Zellen aus, die mit
    = + - @ beginnen. Solche Namen (aus Logs) mit ' entschaerfen, ; quoten."""
    s = str(s)
    if s[:1] in ("=", "+", "-", "@"):
        s = "'" + s
    if ";" in s or '"' in s or "\n" in s:
        s = '"' + s.replace('"', '""') + '"'
    return s


def export_csv():
    lines = ["day;char;kind;key;value"]
    for day, cid, cname, kind, key, value in all_rows():
        lines.append(";".join(_csv_cell(x) for x in (day, cname, kind, key, value)))
    return "\n".join(lines)


# ---------------------------------------------------------------- HTTP
def _host_ok(headers):
    """Schuetzt vor DNS-Rebinding: nur localhost-Hosts duerfen zugreifen.
    Eine fremde Website, die per Rebinding auf 127.0.0.1 zeigt, sendet ihren
    eigenen (fremden) Host-Header und wird hier abgewiesen."""
    host = (headers.get("Host") or "").rsplit(":", 1)[0].strip("[]").lower()
    return host in ("localhost", "127.0.0.1", "::1", "")


def _origin_ok(headers):
    """Schuetzt vor CSRF: Ein Origin (bei fetch/CORS gesetzt) muss localhost sein.
    Gleiche-Ursprung-Requests der eigenen Seite senden localhost oder gar keinen."""
    origin = headers.get("Origin")
    if not origin:
        return True  # klassische Navigation/Formular ohne Origin -> ok, Host-Check greift
    try:
        h = urllib.parse.urlparse(origin).hostname or ""
    except ValueError:
        return False
    return h.lower() in ("localhost", "127.0.0.1", "::1")


class Handler(BaseHTTPRequestHandler):
    def _send(self, body, ctype="application/json", download=None):
        if isinstance(body, str):
            body = body.encode()
        self.send_response(200)
        self.send_header("Content-Type", ctype)
        if download:
            self.send_header("Content-Disposition", f'attachment; filename="{download}"')
        self.send_header("Content-Length", str(len(body)))
        self.end_headers()
        self.wfile.write(body)

    def _deny(self, code=403):
        self.send_response(code)
        self.send_header("Content-Length", "0")
        self.end_headers()

    def do_GET(self):
        # Unerwartete Fehler mit Code festhalten, statt sie nur als Traceback
        # ins Konsolenfenster zu schreiben (das sieht kein Nutzer).
        try:
            self._do_GET()
        except Exception as e:
            log_error("CN-SRV-01", f"GET {self.path.split('?')[0]}", e)
            try:
                self._deny(500)
            except Exception:
                pass

    def do_POST(self):
        try:
            self._do_POST()
        except Exception as e:
            log_error("CN-SRV-01", "POST", e)
            try:
                self._deny(500)
            except Exception:
                pass

    def _do_GET(self):
        if not _host_ok(self.headers):
            return self._deny()
        p = self.path.split("?")[0]
        if p == "/data":
            view = (self.path.split("view=")[1].split("&")[0]
                    if "view=" in self.path else "live")
            data = {"state": state_info()}
            if view == "live":
                data["chars"] = snapshot_live()
                data["summary"] = query_summary()
            elif view == "month":
                data["days"] = query_month()
            elif view == "analyse":
                data["analyse"] = query_analyse()
            elif view == "intel":
                data["intel_auto"] = {"ts": clipwatch.ts, "names": clipwatch.names}
            elif view == "missionen":
                data["missions"] = query_missions()
                data["mission_log"] = query_mission_history()
                data["chars"] = snapshot_live()
            elif view == "rechner":
                pass  # der Rechner holt seine Daten per calc-POST
            else:
                data["total"] = query_total()
            self._send(json.dumps(data))
        elif p == "/sso/callback":
            qs = urllib.parse.parse_qs(self.path.split("?", 1)[1] if "?" in self.path else "")
            err = esi.callback(qs.get("code", [""])[0], qs.get("state", [""])[0])
            ok = err is None
            self._send("<html><head><meta charset='utf-8'><title>EVE Canary</title></head>"
                       "<body style='font-family:sans-serif;background:#101418;color:#dfe7ef;"
                       "text-align:center;padding-top:90px'><div style='font-size:42px'>"
                       + ("🐤" if ok else "⚠️") + "</div><h2>"
                       + ("Charakter verbunden!" if ok else "Login fehlgeschlagen")
                       + "</h2><p>" + (err or "Du kannst dieses Fenster schließen. "
                       "Canary gleicht Laderaum und Wallet ab jetzt automatisch ab.")
                       + "</p></body></html>", "text/html; charset=utf-8")
        elif p == "/diagnose.txt":
            self._send(diagnose_text(), "text/plain; charset=utf-8")
        elif p == "/export.csv":
            self._send(export_csv(), "text/csv; charset=utf-8", "eve_dashboard_export.csv")
        elif p == "/export.json":
            self._send(json.dumps({"month": query_month(), "total": query_total(),
                                   "analyse": query_analyse()}, indent=1),
                       "application/json", "eve_dashboard_export.json")
        else:
            self._send(PAGE, "text/html; charset=utf-8")

    def _do_POST(self):
        if not _host_ok(self.headers) or not _origin_ok(self.headers):
            return self._deny()
        length = int(self.headers.get("Content-Length", 0))
        try:
            body = json.loads(self.rfile.read(length) or b"{}")
        except Exception:
            body = {}
        action = body.get("action")
        if action == "region" and str(body.get("region")) in REGIONS:
            CONFIG["region"] = str(body["region"])
        elif action == "mode" and body.get("mode") in ("all", "fresh"):
            with ingest.lock:
                # filecache leeren, damit ein Wechsel fresh->all die geskippten
                # Alt-Logs wirklich nachimportiert (Cache-Check greift sonst davor).
                ingest.filecache.clear()
                ingest.last_scan = 0
            CONFIG["mode"] = body["mode"]
        elif action == "reset":
            do_reset_baseline()
        elif action == "clear_baseline":
            clear_baseline()
        elif action == "idle_warn":
            CONFIG["idle_warn"] = max(0, int(body.get("seconds") or 0))
        elif action == "set_role":
            char = str(body.get("char") or "")
            role = body.get("role") if body.get("role") in ("mining", "mission", "pvp") else ""
            if char:
                with CONFIG_LOCK:
                    roles = CONFIG.setdefault("roles", {})
                    if role:
                        roles[char] = role
                    else:
                        roles.pop(char, None)
        elif action == "log_dir":
            # Pfad von Hand setzen, falls die automatische Suche nichts findet
            # (v.a. Linux/Wine mit ungewoehnlichem Praefix). Erst pruefen, dann
            # uebernehmen, sonst laeuft Canary still ins Leere.
            raw = (body.get("path") or "").strip().strip('"')
            p = Path(os.path.expanduser(raw)) if raw else None
            if not raw:
                self._send(json.dumps({"ok": False, "msg": "Bitte einen Pfad eintragen."}))
                return
            if not p.is_dir():
                self._send(json.dumps({"ok": False,
                                       "msg": f"Ordner nicht gefunden: {p}"}))
                return
            def gamelogs_in(d):
                try:
                    return [f for f in d.iterdir() if CHAR_FILE_RE.match(f.name)]
                except OSError:
                    return []
            # Haeufiger Tippfehler: Pfad endet auf .../EVE/logs oder .../EVE statt
            # auf Gamelogs. Statt zu meckern nehmen wir den richtigen Unterordner.
            hits, chosen = gamelogs_in(p), p
            for sub in (p / "Gamelogs", p / "logs" / "Gamelogs",
                        p / "EVE" / "logs" / "Gamelogs"):
                if hits:
                    break
                if sub.is_dir():
                    hits, chosen = gamelogs_in(sub), sub
            if not hits:
                self._send(json.dumps({"ok": False,
                                       "msg": f"Keine Gamelogs in {p} gefunden. Gemeint ist der "
                                              "Ordner 'Gamelogs' (dort liegen Dateien wie "
                                              "20260723_120000_1234567.txt)."}))
                return
            p = chosen
            CONFIG["log_dir"] = str(p)
            with ingest.lock:
                ingest.filecache.clear()
                ingest.last_scan = 0     # sofort neu einlesen statt aufs Intervall warten
            save_config()
            self._send(json.dumps({"ok": True,
                                   "msg": f"{len(hits)} Gamelogs gefunden. Wird eingelesen …",
                                   "state": state_info()}))
            return
        elif action == "autostart":
            set_autostart(bool(body.get("on")))
        elif action == "clip_watch":
            CONFIG["clip_watch"] = bool(body.get("on"))
        elif action == "calc":
            self._send(json.dumps(calc_hubs(body.get("text") or "")))
            return
        elif action == "loot":
            self._send(json.dumps(calc_loot(body.get("text") or "")))
            return
        elif action == "mission_loot":
            # Loot einer einzelnen Mission bewerten und dauerhaft an ihr speichern.
            mid = str(body.get("mid") or "")
            text = body.get("text") or ""
            res = calc_loot(text)
            isk = res["hubs"].get("10000002", {}).get("buy", 0) if res.get("ok") else 0
            with DB_LOCK:
                DB.execute("UPDATE missions SET loot_isk=?, loot_text=? WHERE mid=?",
                           (isk, text, mid))
                DB.commit()
            self._send(json.dumps({"ok": True, "isk": isk, "unknown": res.get("unknown", [])}))
            return
        elif action == "threat_scan":
            names = [str(n).strip() for n in body.get("names", [])][:200]
            names = [n for n in names if n]
            results = threat.request(names, prio=True)
            self._send(json.dumps({"ok": True, "results": results,
                                   "pending": threat.pending()}))
            return
        elif action == "esi_login":
            url = esi.login_url()
            self._send(json.dumps({"ok": bool(url), "url": url,
                                   "error": None if url else "Login konnte nicht gestartet werden."}))
            return
        elif action == "esi_forget":
            char = str(body.get("char") or "")
            with CONFIG_LOCK:
                esi.cfg().get("chars", {}).pop(char, None)
                esi.status.pop(char, None)
                hw_entry = (CONFIG.get("heavy_water") or {}).get(char)
                if hw_entry and hw_entry.get("esi"):
                    CONFIG["heavy_water"].pop(char, None)
        elif action == "heavy_water":
            char = str(body.get("char") or "")
            units = body.get("units")
            with CONFIG_LOCK:
                hw = CONFIG.setdefault("heavy_water", {})
                if char and units is None:
                    hw.pop(char, None)
                elif char:
                    hw[char] = {"units": max(0.0, float(units)),
                                "fill": max(0.0, float(units)),
                                "core": "t2" if body.get("core") == "t2" else "t1",
                                "ts": time.time(), "warned": False, "ck": 0}
        elif action == "laser_ok":
            with ingest.lock:
                for s in ingest.sessions.values():
                    if s.name == body.get("char"):
                        s.lasers_off.pop(body.get("tool"), None)
        elif action == "watchlist":
            CONFIG["watchlist"] = [str(n).strip() for n in body.get("names", []) if str(n).strip()][:50]
        elif action == "goal":
            isk = body.get("isk")
            CONFIG["goal"] = ({"isk": int(isk), "deadline": str(body.get("deadline") or "")}
                              if isk else None)
        elif action == "backup":
            name = do_backup()
            self._send(json.dumps({"ok": True, "file": name}))
            return
        elif action == "check_update":
            self._send(json.dumps(check_update()))
            return
        elif action == "do_update":
            self._send(json.dumps(do_update()))
            return
        save_config()
        self._send(json.dumps({"ok": True, "state": state_info()}))

    def log_message(self, *a):
        pass


# ---------------------------------------------------------------- Frontend
PAGE = """<!DOCTYPE html><html lang="de"><head><meta charset="utf-8">
<meta name="viewport" content="width=device-width,initial-scale=1">
<title>EVE Canary</title>
<link rel="icon" href="data:image/svg+xml,<svg xmlns=%22http://www.w3.org/2000/svg%22 viewBox=%220 0 100 100%22><text y=%22.9em%22 font-size=%2290%22>🐤</text></svg>">
<style>
:root{--bg:#0b0e14;--card:#121722;--inset:#0e1320;--line:#1e2636;--txt:#c9d4e3;
--dim:#5d6b80;--cyan:#35c8e8;--red:#e8564f;--green:#4fd47f;--gold:#e8c645;--white:#fff}
[data-theme=light]{--bg:#f2f4f8;--card:#ffffff;--inset:#eef1f6;--line:#d8dee9;
--txt:#2a3242;--dim:#7a8699;--cyan:#0e7ea3;--red:#c2372f;--green:#1e8f4d;--gold:#9a7a00;--white:#101828}
/* ---------- Photon-Skin: EVE-Fensterstil — Nebel, Transparenz+Blur, Titelleisten, Eck-Klammern */
html[data-skin=photon]{--bg:#0a0d0f;--card:rgba(13,17,19,.80);--inset:rgba(255,255,255,.04);
--line:rgba(130,150,158,.16);--txt:#c9d1d4;--dim:#7d888e;--cyan:#5fc1d4;--red:#c8443d;--green:#7db35c;
--gold:#d9a33c;--white:#eef1f2}
html[data-skin=photon] body,html[data-skin=photon] dialog,html[data-skin=photon] .btn,
html[data-skin=photon] input,html[data-skin=photon] textarea{font-family:'Bahnschrift','Segoe UI',system-ui,sans-serif}
/* Nebel + Sternenfeld (rein CSS, drei Stern-Ebenen als gekachelte Punkte) */
html[data-skin=photon] body{background:
 radial-gradient(1px 1px at 21% 33%,rgba(255,255,255,.5) 0,transparent 100%),
 radial-gradient(1px 1px at 67% 12%,rgba(255,255,255,.35) 0,transparent 100%),
 radial-gradient(1.5px 1.5px at 44% 76%,rgba(200,230,255,.4) 0,transparent 100%),
 radial-gradient(1px 1px at 86% 58%,rgba(255,255,255,.3) 0,transparent 100%),
 radial-gradient(1400px 900px at 78% -12%,rgba(52,102,84,.28),transparent 62%),
 radial-gradient(1100px 800px at 6% 108%,rgba(30,58,78,.30),transparent 58%),
 radial-gradient(700px 500px at 34% 42%,rgba(74,94,60,.10),transparent 60%),#0a0d0f;
 background-size:290px 290px,210px 210px,340px 340px,260px 260px,auto,auto,auto,auto;
 background-attachment:fixed}
/* Holo-Scanlines, extrem dezent */
html[data-skin=photon] body::after{content:"";position:fixed;inset:0;z-index:9999;pointer-events:none;
 background:repeating-linear-gradient(0deg,rgba(255,255,255,.012) 0 1px,transparent 1px 3px)}
/* Alles kantig */
html[data-skin=photon] .card,html[data-skin=photon] .stat,html[data-skin=photon] .alert,
html[data-skin=photon] .cardwarn,html[data-skin=photon] dialog,html[data-skin=photon] .btn,
html[data-skin=photon] input,html[data-skin=photon] textarea,html[data-skin=photon] select.pill,
html[data-skin=photon] .pill,html[data-skin=photon] .laserok,html[data-skin=photon] header{border-radius:0}
/* Karten = EVE-Fenster: transluzent, Blur, Eck-Klammern wie am Zielobjekt */
html[data-skin=photon] .card,html[data-skin=photon] header,html[data-skin=photon] dialog{
 background:var(--card);backdrop-filter:blur(9px);-webkit-backdrop-filter:blur(9px);
 border:1px solid var(--line);box-shadow:0 12px 30px rgba(0,0,0,.45)}
html[data-skin=photon] .card{position:relative;overflow:hidden}
html[data-skin=photon] .card::before,html[data-skin=photon] .card::after{
 content:"";position:absolute;width:11px;height:11px;pointer-events:none;opacity:.5}
html[data-skin=photon] .card::before{top:0;left:0;border-top:1px solid #dfe7ea;border-left:1px solid #dfe7ea}
html[data-skin=photon] .card::after{bottom:0;right:0;border-bottom:1px solid #dfe7ea;border-right:1px solid #dfe7ea}
/* Kartenkopf = Fenster-Titelleiste */
html[data-skin=photon] .chead{background:linear-gradient(180deg,rgba(255,255,255,.07),rgba(255,255,255,.02));
 margin:-14px -16px 10px -16px;padding:9px 14px;border-bottom:1px solid rgba(0,0,0,.55)}
html[data-skin=photon] .card.min .chead{margin:-10px -16px -10px -16px;border-bottom:none}
html[data-skin=photon] .char{color:var(--gold);font-weight:400;letter-spacing:.4px}
html[data-skin=photon] .sys{color:var(--txt);opacity:.7}
/* Kopfzeile als Leiste */
html[data-skin=photon] header{padding:8px 14px;margin-bottom:12px}
html[data-skin=photon] h1{letter-spacing:4px;font-weight:300}
html[data-skin=photon] h1 b{color:var(--gold);font-weight:400}
/* Navigation wie EVE-Tab-Leiste */
html[data-skin=photon] nav{border-bottom:1px solid var(--line);gap:0}
html[data-skin=photon] nav span{text-transform:uppercase;letter-spacing:1.4px;font-size:11px;
 border-right:1px solid rgba(130,150,158,.10);padding:8px 18px}
html[data-skin=photon] nav span:hover{background:rgba(95,193,212,.06);color:var(--txt)}
html[data-skin=photon] nav span.on{color:var(--white);background:rgba(255,255,255,.05);
 border-bottom:2px solid var(--gold)}
/* Typo-Details */
html[data-skin=photon] .sect{text-transform:uppercase;letter-spacing:1.4px;font-size:10px}
html[data-skin=photon] th{text-transform:uppercase;font-size:10px;letter-spacing:1px;font-weight:400}
html[data-skin=photon] .stat .l{text-transform:uppercase;letter-spacing:.6px;font-size:9.5px}
html[data-skin=photon] .stat .v{font-weight:300;letter-spacing:.3px}
/* Zeilen-Hover wie Overview-Selektion */
html[data-skin=photon] .pf{border-radius:1px;border:1px solid var(--line)}
html[data-skin=photon] tr:hover td{background:rgba(95,193,212,.07)}
html[data-skin=photon] td{border-top-color:rgba(130,150,158,.10)}
/* Bedienelemente */
html[data-skin=photon] .btn{text-transform:uppercase;letter-spacing:.8px;font-size:11px;
 background:rgba(255,255,255,.04)}
html[data-skin=photon] .btn:hover{border-color:var(--cyan);color:var(--white);
 box-shadow:inset 0 0 10px rgba(95,193,212,.12),0 0 8px rgba(95,193,212,.18)}
html[data-skin=photon] .pill{background:rgba(255,255,255,.03)}
html[data-skin=photon] .pill.on{background:rgba(95,193,212,.12);color:var(--cyan);border-color:var(--cyan)}
html[data-skin=photon] .stat{border:1px solid rgba(130,150,158,.10);background:rgba(255,255,255,.03);
 transition:border-color .12s,box-shadow .12s}
/* Hover wie ein EVE-Inventar-Slot: Teal-Rahmen mit Eck-Klammern und Glimmen */
html[data-skin=photon] .stat:hover{border-color:rgba(95,193,212,.55);
 box-shadow:0 0 10px rgba(95,193,212,.25),inset 0 0 14px rgba(95,193,212,.06);
 background-image:
  linear-gradient(var(--cyan),var(--cyan)),linear-gradient(var(--cyan),var(--cyan)),
  linear-gradient(var(--cyan),var(--cyan)),linear-gradient(var(--cyan),var(--cyan)),
  linear-gradient(var(--cyan),var(--cyan)),linear-gradient(var(--cyan),var(--cyan)),
  linear-gradient(var(--cyan),var(--cyan)),linear-gradient(var(--cyan),var(--cyan));
 background-repeat:no-repeat;
 background-size:9px 2px,2px 9px,9px 2px,2px 9px,9px 2px,2px 9px,9px 2px,2px 9px;
 background-position:top left,top left,top right,top right,bottom left,bottom left,bottom right,bottom right}
html[data-skin=photon] .alert{border-left-width:3px;backdrop-filter:blur(9px)}
html[data-skin=photon] dialog::backdrop{background:rgba(2,4,5,.75);backdrop-filter:blur(3px)}
html[data-skin=photon] ::-webkit-scrollbar{width:9px;height:9px}
html[data-skin=photon] ::-webkit-scrollbar-thumb{background:#2b3236;border:2px solid #0b0e10}
html[data-skin=photon] ::-webkit-scrollbar-track{background:transparent}
*{margin:0;box-sizing:border-box;font-family:'Segoe UI',system-ui,sans-serif}
body{background:var(--bg);color:var(--txt);padding:18px;transition:background .2s}
html[data-fs="2"] body{zoom:1.15}
html[data-fs="3"] body{zoom:1.3}
header{display:flex;align-items:center;gap:10px;flex-wrap:wrap;margin-bottom:10px}
h1{font-size:14px;font-weight:600;letter-spacing:2px;color:var(--dim)}
h1 b{color:var(--cyan)}
.byline{font-size:10px;color:var(--dim);letter-spacing:1.6px;font-weight:400;text-transform:uppercase;opacity:.8}
/* ---------- Boot-Screen beim Erst-Einlesen */
#boot{position:fixed;inset:0;z-index:2000;background:var(--bg);display:flex;
 align-items:center;justify-content:center;opacity:1;transition:opacity .8s}
/* hidden-Attribut MUSS gewinnen: sonst überdeckt der Boot-Screen beim
   Schnellstart (DB schon gefüllt) dauerhaft das fertige Dashboard. */
#boot[hidden]{display:none}
#boot.fade{opacity:0;pointer-events:none}
.bootbox{text-align:center;width:min(440px,84vw)}
.bootbird{font-size:64px;animation:bootpulse 1.6s ease-in-out infinite}
@keyframes bootpulse{0%,100%{transform:scale(1)}50%{transform:scale(1.14)}}
.bootbox h2{letter-spacing:7px;font-weight:300;color:var(--txt);margin:12px 0 2px;font-size:22px}
.bootbox h2 b{color:var(--cyan);font-weight:600}
.bootby{color:var(--gold);font-size:11px;letter-spacing:2.5px;text-transform:uppercase;margin-bottom:26px}
.boottext{color:var(--dim);font-size:13px;margin-bottom:12px}
.bootbar{height:10px;border:1px solid var(--line);border-radius:6px;overflow:hidden;background:var(--card)}
#bootfill{height:100%;width:0%;background:linear-gradient(90deg,var(--cyan),var(--gold));
 transition:width .5s;box-shadow:0 0 12px rgba(53,200,232,.4)}
.bootnum{color:var(--txt);font-size:13px;margin-top:10px}
.boothint{color:var(--dim);font-size:11px;margin-top:18px;line-height:1.5}
html[data-skin=photon] .bootbar,html[data-skin=photon] #bootfill{border-radius:1px}
/* ---------- Optionen-Gruppen */
.optgroup{background:var(--inset);border:1px solid var(--line);border-radius:8px;
 padding:12px 14px;margin-bottom:10px}
.optgroup .sect{margin-top:0}
.btnrow{display:flex;gap:6px;flex-wrap:wrap;margin-top:8px}
html[data-skin=photon] .optgroup{border-radius:1px}
.pills{display:flex;gap:4px;margin-left:auto}
.pill{background:var(--card);border:1px solid var(--line);color:var(--dim);font-size:11px;
padding:4px 11px;border-radius:20px;cursor:pointer;user-select:none}
.pill.on{background:var(--cyan);color:var(--bg);border-color:var(--cyan)}
.pill.rolef{padding:4px 9px}
.rolesel{appearance:none;-webkit-appearance:none;background:var(--inset);border:1px solid var(--line);
 color:var(--dim);font-size:10px;padding:2px 6px;border-radius:20px;cursor:pointer;flex:none}
.rolesel:hover{color:var(--txt);border-color:var(--cyan)}
html[data-skin=photon] .rolesel{border-radius:1px}
nav{display:flex;gap:2px;border-bottom:1px solid var(--line);margin-bottom:14px}
nav span{color:var(--dim);font-size:12px;padding:7px 16px;cursor:pointer;user-select:none}
nav span.on{color:var(--cyan);border-bottom:2px solid var(--cyan)}
#alerts{display:flex;flex-direction:column;gap:6px;margin-bottom:12px}
.alert{border-radius:8px;padding:8px 12px;font-size:12px;border:1px solid var(--line);background:var(--card)}
.alert.pvp{border-color:var(--red);color:var(--red);font-weight:600}
.alert.watch{border-color:var(--gold);color:var(--gold)}
.alert.depleted{border-color:var(--gold);color:var(--gold)}
.alert.idle{border-color:var(--gold);color:var(--gold);font-weight:600}
.alert.rate{border-color:var(--gold);color:var(--gold);font-weight:600}
.alert.drones{border-color:var(--red);color:var(--red);font-weight:600}
.alert.cargo{border-color:var(--red);color:var(--red);font-weight:600}
.cardwarn{border:1px solid var(--gold);color:var(--gold);border-radius:7px;
padding:7px 10px;font-size:12px;font-weight:600;margin-bottom:8px;overflow:hidden}
.cardwarn.drone{border-color:var(--red);color:var(--red)}
.warnbadge{color:var(--gold);font-weight:600}
.warnbadge.drone{color:var(--red)}
.pill.upd{border-color:var(--gold);color:var(--gold);animation:updpulse 2.4s ease-in-out infinite}
@keyframes updpulse{0%,100%{box-shadow:0 0 0 rgba(232,198,69,0)}50%{box-shadow:0 0 9px rgba(232,198,69,.45)}}
.laserok{float:right;border:1px solid var(--line);border-radius:20px;padding:1px 9px;
color:var(--dim);cursor:pointer;font-weight:400;margin-left:8px}
.laserok:hover{color:var(--fg);border-color:var(--fg)}
.hwset{cursor:pointer;opacity:.55}
.hwset:hover{opacity:1}
tr.lvl-red td{background:rgba(232,86,79,.10)}
tr.lvl-yellow td{background:rgba(228,179,76,.07)}
#intelTbl a{color:inherit}
#grid{display:grid;grid-template-columns:repeat(auto-fit,minmax(420px,1fr));gap:14px;align-items:start}
@media (max-width:900px){#grid{grid-template-columns:1fr}}
#hero:not(:empty){margin-bottom:14px}
select.pill{appearance:none;-webkit-appearance:none;outline:none;background:var(--card);
border:1px solid var(--line);color:var(--dim);font-size:11px;padding:4px 11px;border-radius:20px;cursor:pointer}
.card{background:var(--card);border:1px solid var(--line);border-radius:10px;padding:14px 16px}
.char{font-size:15px;font-weight:600;color:var(--white)}
.chead{display:flex;align-items:center;gap:8px;cursor:pointer;user-select:none;flex-wrap:wrap}
.chead .mini{margin-left:auto;font-size:12px;color:var(--dim);text-align:right;min-width:0}
.pf{width:26px;height:26px;border-radius:5px;flex:none;background:var(--inset)}
.pf-none{display:flex;align-items:center;justify-content:center;font-size:14px;
 border:1px dashed var(--dim);color:var(--dim);cursor:pointer;opacity:.7}
.pf-none:hover{opacity:1;border-color:var(--cyan);color:var(--cyan)}
.esinudge{border:1px solid var(--cyan);border-radius:7px;padding:8px 11px;margin:2px 0 10px 0;
 font-size:12px;color:var(--txt);background:rgba(53,200,232,.08)}
html[data-skin=photon] .esinudge{border-radius:1px}
#esiChars{font-size:13px;line-height:1.7;margin-bottom:8px}
.chead .arr{color:var(--dim);font-size:11px;transition:transform .15s}
.card.min .arr{transform:rotate(-90deg)}
.card.min .cbody{display:none}
.card.min{padding:10px 16px}
.sys{color:var(--cyan);font-weight:400;font-size:12px}
.sub{font-size:11px;color:var(--dim);margin-bottom:10px}
.stats{display:grid;grid-template-columns:repeat(3,1fr);gap:8px;margin-bottom:10px}
.stat{background:var(--inset);border-radius:7px;padding:8px 10px}
.stat .l{font-size:10px;text-transform:uppercase;letter-spacing:1px;color:var(--dim)}
.stat .v{font-size:16px;font-weight:600;margin-top:2px}
.isk{color:var(--gold)}.out{color:var(--cyan)}.in{color:var(--red)}.grn{color:var(--green)}
table{width:100%;border-collapse:collapse;font-size:12px;margin-top:6px}
/* Horizontaler Abstand, sonst kleben Spalten bei langen Zahlen aneinander
   ("33.415 m³681.0 M"). Aussen buendig bleiben, damit nichts einrueckt. */
td,th{padding:3px 10px;border-top:1px solid var(--line)}
td:first-child,th:first-child{padding-left:0}
td:last-child,th:last-child{padding-right:0}
th{border-top:none}
td.r{text-align:right;color:var(--dim);white-space:nowrap}
.sect{font-size:10px;text-transform:uppercase;letter-spacing:1px;color:var(--dim);margin-top:10px}
.bar{height:4px;border-radius:2px;background:var(--cyan);opacity:.7}
.spark{display:flex;align-items:flex-end;gap:1px;height:30px;margin-top:8px}
.spark div{flex:1;background:var(--cyan);opacity:.75;border-radius:1px 1px 0 0;min-height:1px}
.spark.dmgin div{background:var(--red)}
.fitsec{margin-top:10px}
.fittoggle{cursor:pointer;color:var(--cyan);font-size:12px}
.fitbox{margin-top:8px}
.fitwrap{display:flex;gap:14px;align-items:flex-start;flex-wrap:wrap}
.fitship{width:132px;height:132px;border-radius:8px;border:1px solid var(--line);object-fit:cover;background:var(--inset)}
.fitslots{flex:1;min-width:200px;display:flex;flex-direction:column;gap:6px}
.fitrow{display:flex;align-items:center;gap:8px}
.fitlbl{width:34px;flex:none;font-size:10px;text-transform:uppercase;letter-spacing:1px;color:var(--dim)}
.fiticons{display:flex;flex-wrap:wrap;gap:4px}
.fiticon{width:34px;height:34px;border-radius:5px;border:1px solid var(--line);background:var(--inset)}
.chart{display:flex;align-items:flex-end;gap:3px;height:120px;margin-top:12px}
.chart .col{flex:1;display:flex;flex-direction:column;justify-content:flex-end}
.chart .seg1{background:var(--cyan);border-radius:2px 2px 0 0}
.chart .seg2{background:var(--green)}
.legend{display:flex;gap:14px;font-size:11px;color:var(--dim);margin-top:6px}
.dot{display:inline-block;width:8px;height:8px;border-radius:2px;margin-right:4px;vertical-align:-1px}
.progress{background:var(--inset);border-radius:8px;height:16px;overflow:hidden;margin:8px 0}
.progress div{background:var(--gold);height:100%;transition:width .5s}
#empty{color:var(--dim);font-size:13px;margin-top:30px}
dialog{background:var(--card);color:var(--txt);border:1px solid var(--line);border-radius:12px;
padding:20px 22px;max-width:620px;width:94%}
dialog::backdrop{background:rgba(0,0,0,.55)}
dialog h2{font-size:14px;margin-bottom:12px;color:var(--white)}
dialog label{display:block;font-size:13px;margin:8px 0;cursor:pointer}
dialog .hint{font-size:11px;color:var(--dim);margin:2px 0 10px 0}
dialog input[type=text],dialog input[type=number],dialog input[type=date],dialog textarea{
background:var(--inset);border:1px solid var(--line);color:var(--txt);border-radius:6px;
padding:6px 8px;font-size:12px;width:100%}
.btn{background:var(--inset);border:1px solid var(--line);color:var(--txt);font-size:12px;
padding:7px 14px;border-radius:8px;cursor:pointer;margin:4px 6px 0 0}
.btn.warn{color:var(--red);border-color:var(--red)}
.note{font-size:11px;color:var(--dim);margin-top:10px}
</style></head><body>
<div id="boot" hidden>
 <div class="bootbox">
  <div class="bootbird">🐤</div>
  <h2>EVE <b>CANARY</b></h2>
  <div class="bootby">by Askend</div>
  <div class="boottext">Logdateien werden gelesen und analysiert …</div>
  <div class="bootbar"><div id="bootfill"></div></div>
  <div class="bootnum" id="bootnum"></div>
  <div class="boothint">Das passiert nur beim ersten Start. Je nach Log-Bestand kann es ein paar Minuten dauern,
  danach öffnet sich das Dashboard von selbst.</div>
 </div>
</div>
<header>
 <h1>🐤 EVE <b>CANARY</b> <span class="byline">by Askend</span></h1>
 <span class="pill modesel" data-mode="mining" title="Mining-Ansicht">⛏ Mining</span><span class="pill modesel" data-mode="combat" title="PvP- und Missions-Ansicht">⚔ PvP &amp; Missionen</span>
 <span class="pill rolef on" data-role="" title="Alle Charaktere">Alle</span>
 <span class="pill rolef" data-role="mining" title="Nur Mining-Charaktere">⛏</span>
 <span class="pill rolef" data-role="mission" title="Nur Mission-Runner">🎯</span>
 <span class="pill rolef" data-role="pvp" title="Nur PvP-Charaktere">⚔</span>
 <span class="pill" id="showOffline" title="Standardmäßig zeigt Live nur eingeloggte Charaktere. Hier einschalten, um auch Offline-Charaktere zu sehen.">💤 Offline zeigen</span>
 <select class="pill" id="charFilter" title="Charakter-Filter"><option value="">Alle Charaktere</option></select>
 <span class="pill" id="collapseAll">Alle einklappen</span>
 <span class="pill langsel" data-l="de" title="Deutsch">DE</span><span class="pill langsel" data-l="en" title="English">EN</span>
 <div class="pills" id="regions"></div>
 <span class="pill upd" id="updBadge" hidden title="Neue Version verfügbar, Klick installiert sie"></span>
 <span class="pill" id="ovToggle" title="Always-on-top Mini-Overlay (Chrome/Edge)">◱ Overlay</span>
 <span class="pill" id="fontsize" title="Schriftgröße (3 Stufen)">A</span>
 <span class="pill" id="theme" title="Dark/Light">◐</span>
 <span class="pill" id="gear">⚙ Optionen</span>
</header>
<nav>
 <span data-v="live" class="on">Live</span>
 <span data-v="month">30 Tage</span>
 <span data-v="total">Gesamt</span>
 <span data-v="analyse">Analyse</span>
 <span data-v="intel">🚦 Intel</span>
 <span data-v="missionen">🎯 Missionen</span>
 <span data-v="rechner">🧮 Ore Calculator</span>
</nav>
<div id="alerts"></div>
<div id="hero"></div>
<div id="setup" hidden></div>
<div id="grid"></div>
<div id="empty" hidden></div>

<dialog id="opts">
 <h2>⚙ Optionen <span class="byline">EVE Canary by Askend</span></h2>

 <div class="optgroup">
  <div class="sect">🎨 Darstellung</div>
  <label><input type="radio" name="skin" value=""> Klassisch (das gewohnte Canary-Design)</label>
  <label><input type="radio" name="skin" value="photon"> Photon (angelehnt ans EVE-Interface: dunkel, kantig, Gold-Akzente)</label>
  <div class="btnrow"><button class="btn" id="ovBtn">◱ Mini-Overlay öffnen/schließen</button></div>
  <div class="hint">Das Overlay ist ein schwebendes Always-on-top-Fenster mit Status und Alarmen,
  bleibt über dem EVE-Client (Fenstermodus/randlos). Benötigt Chrome oder Edge, Start nur per Klick.</div>
 </div>

 <div class="optgroup">
  <div class="sect">🔔 Alarme &amp; Wachen</div>
  <label><input type="checkbox" id="sndPvp" checked> Sound bei Spieler-Angriff</label>
  <label><input type="checkbox" id="sndDep" checked> Sound bei leerem Asteroiden</label>
  <label><input type="checkbox" id="sndWatch" checked> Sound bei Watchlist-Treffer</label>
  <div style="display:flex;gap:6px;align-items:center;margin-top:8px">
   <input type="number" id="idleWarn" min="0" step="30" style="width:110px">
   <span class="hint" style="margin:0">Sekunden ohne Erz bis zur Stillstand-Warnung (0 = aus)</span>
   <button class="btn" id="saveIdle">Speichern</button>
  </div>
  <div class="sect" style="margin-top:12px">Watchlist (Local-Chat, ein Name pro Zeile)</div>
  <textarea id="watchlist" rows="3" placeholder="Bekannte Ganker..."></textarea>
  <div class="btnrow">
   <button class="btn" id="saveWatch">Watchlist speichern</button>
   <button class="btn" id="notifPerm">Desktop-Benachrichtigungen erlauben</button>
  </div>
 </div>

 <div class="optgroup">
  <div class="sect">🎯 Ziel &amp; Zähler</div>
  <div style="display:flex;gap:6px">
   <input type="number" id="goalIsk" placeholder="ISK-Ziel, z.B. 1000000000">
   <input type="date" id="goalDate">
  </div>
  <div class="btnrow">
   <button class="btn" id="saveGoal">Ziel speichern</button>
   <button class="btn" id="clearGoal">Ziel löschen</button>
   <button class="btn warn" id="reset">Auswertung ab jetzt neu lesen</button>
   <button class="btn" id="unreset">Baseline aufheben</button>
  </div>
  <div class="hint" id="baseinfo"></div>
 </div>

 <div class="optgroup">
  <div class="sect esi">🔑 EVE-Account verbinden</div>
  <div class="esinudge" id="esiNudge" hidden>✨ Verbinde deinen EVE-Account, dann zeigt Canary automatisch Portrait,
   aktuelles Schiff, Wallet-Stand, Heavy Water und Missions-Einnahmen. Kein Setup nötig, einfach einloggen.</div>
  <div id="esiChars"></div>
  <div class="btnrow"><button class="btn" id="esiLogin">🔑 Mit EVE-Account verbinden</button></div>
 </div>

 <div class="optgroup">
  <div class="sect">🖥 System &amp; Daten</div>
  <label id="autostartRow"><input type="checkbox" id="autostart"> Canary beim Systemstart automatisch mitstarten (still im Hintergrund, ohne Konsolenfenster)</label>
  <div style="margin-top:10px"><b>Log-Ordner</b>
   <div class="hint">Findet Canary die Logs nicht von selbst, hier den Ordner <b>Gamelogs</b> eintragen.
    Unter Linux liegt der im Wine-Präfix, bei Steam etwa
    <code>~/.steam/steam/steamapps/compatdata/8500/pfx/drive_c/users/steamuser/Documents/EVE/logs/Gamelogs</code></div>
   <div class="btnrow" style="margin-top:6px">
    <input id="logDir" style="flex:1;min-width:260px" placeholder="Pfad zum Gamelogs-Ordner">
    <button class="btn" id="saveLogDir">Übernehmen</button>
   </div>
   <div class="hint" id="logDirStat"></div>
  </div>
  <label style="margin-top:8px"><input type="radio" name="mode" value="all"> Alle vorhandenen Logs auswerten</label>
  <label><input type="radio" name="mode" value="fresh"> Nur ab Installation zählen</label>
  <div class="btnrow">
   <button class="btn" id="checkUpd">Nach Update suchen</button>
   <button class="btn" id="doUpd" hidden>Update installieren</button>
   <button class="btn" id="backup">Backup erstellen</button>
   <button class="btn" id="diagBtn">🩺 Diagnose kopieren</button>
   <a class="btn" href="/export.csv" style="text-decoration:none">Export CSV</a>
   <a class="btn" href="/export.json" style="text-decoration:none">Export JSON</a>
  </div>
  <div class="hint" id="diagStat"></div>
  <textarea id="diagOut" rows="10" hidden readonly style="width:100%;margin-top:6px;font-family:monospace;font-size:11px"></textarea>
  <div class="hint" id="errBox"></div>
  <div class="hint" id="verinfo"></div>
  <div class="hint" id="updstatus"></div>
  <div class="note" id="loginfo"></div>
 </div>

 <div style="text-align:right"><button class="btn" id="close">Schließen</button></div>
</dialog>

<script>
const $=s=>document.querySelector(s);
const fmt=n=>Math.round(n).toLocaleString();
const fmtM=n=>n>=1e9?(n/1e9).toFixed(2)+' Mrd':n>=1e6?(n/1e6).toFixed(1)+' M':fmt(n);
// HTML-Escape: Spieler-/Corp-/Schiffsnamen aus Logs, ESI und zKillboard sind
// fremdbestimmt und dürfen nie ungefiltert in innerHTML landen (XSS).
const esc=s=>String(s==null?'':s).replace(/[&<>"']/g,c=>({'&':'&amp;','<':'&lt;','>':'&gt;','"':'&quot;',"'":'&#39;'}[c]));
function lsGet(key,fallback){try{const v=localStorage.getItem(key);return v==null?fallback:JSON.parse(v);}catch(e){return fallback;}}
const VIEWS=['live','month','total','analyse','intel','missionen','rechner'];
let view=location.pathname.replace(/^\\//,'')||'live', state=null, lastAlertId=Number(localStorage.getItem('lastAlertId')||0);
if(!VIEWS.includes(view))view='live';
window.addEventListener('popstate',()=>{
 view=location.pathname.replace(/^\\//,'')||'live';
 if(!VIEWS.includes(view))view='live';
 document.querySelectorAll('nav span').forEach(x=>x.classList.toggle('on',x.dataset.v===view));
 tick();
});

const savedTheme=localStorage.getItem('theme');
if(savedTheme)document.documentElement.dataset.theme=savedTheme;
else if(matchMedia('(prefers-color-scheme: light)').matches)document.documentElement.dataset.theme='light';
const savedSkin=localStorage.getItem('skin');
if(savedSkin)document.documentElement.dataset.skin=savedSkin;
$('#autostart').onchange=async()=>{const r=await post({action:'autostart',on:$('#autostart').checked});if(r.state)state=r.state;syncOpts();};
$('#saveLogDir').onclick=async()=>{
 const st=$('#logDirStat');st.textContent='Prüfe …';st.style.color='';
 const r=await post({action:'log_dir',path:$('#logDir').value});
 st.textContent=r.msg||'';st.style.color=r.ok?'var(--green)':'var(--red)';
 if(r.ok){if(r.state)state=r.state;tick();}};
$('#logDir').onkeydown=e=>{if(e.key==='Enter')$('#saveLogDir').click();};
document.querySelectorAll('#opts input[name=skin]').forEach(r=>r.onchange=()=>{
 if(r.value)document.documentElement.dataset.skin=r.value;
 else delete document.documentElement.dataset.skin;
 localStorage.setItem('skin',r.value);
});
$('#theme').onclick=()=>{const t=document.documentElement.dataset.theme==='light'?'dark':'light';
 document.documentElement.dataset.theme=t;localStorage.setItem('theme',t);};

const FS_LABEL={1:'A',2:'A+',3:'A++'};
let fontsize=Number(localStorage.getItem('fontsize')||1);
function applyFs(){
 document.documentElement.dataset.fs=fontsize;
 $('#fontsize').textContent=FS_LABEL[fontsize];
}
applyFs();
$('#fontsize').onclick=()=>{fontsize=fontsize%3+1;localStorage.setItem('fontsize',fontsize);applyFs();};

document.querySelectorAll('nav span').forEach(el=>el.onclick=()=>{
 document.querySelectorAll('nav span').forEach(x=>x.classList.remove('on'));
 el.classList.add('on');view=el.dataset.v;
 history.pushState(null,'','/'+(view==='live'?'':view));tick();});
document.querySelectorAll('nav span').forEach(x=>x.classList.toggle('on',x.dataset.v===view));

['sndPvp','sndDep','sndWatch'].forEach(id=>{
 const el=$('#'+id);
 el.checked=localStorage.getItem(id)!=='0';
 el.onchange=()=>localStorage.setItem(id,el.checked?'1':'0');});

$('#gear').onclick=()=>{syncOpts();$('#opts').showModal();};
$('#close').onclick=()=>$('#opts').close();
$('#reset').onclick=async()=>{if(confirm('Auswertung ab jetzt neu starten? Alte Daten bleiben gespeichert, werden aber ausgeblendet.')){await post({action:'reset'});tick();syncOpts();}};
$('#unreset').onclick=async()=>{await post({action:'clear_baseline'});tick();syncOpts();};
$('#backup').onclick=async()=>{const r=await post({action:'backup'});alert('Backup: '+r.file);};
// Diagnose: Bericht holen, in die Zwischenablage legen und zum Nachlesen anzeigen
$('#diagBtn').onclick=async()=>{
 const st=$('#diagStat');
 try{
  const txt=await (await fetch('/diagnose.txt')).text();
  let copied=false;
  try{await navigator.clipboard.writeText(txt);copied=true;}catch(e){}
  $('#diagOut').value=txt;$('#diagOut').hidden=false;
  if(!copied)$('#diagOut').select();
  st.textContent=copied?'In die Zwischenablage kopiert. Einfach an Askend schicken.'
                       :'Kopieren ging nicht, Text ist markiert: Strg+C drücken.';
  st.style.color='var(--green)';
 }catch(e){st.textContent='Diagnose konnte nicht erstellt werden: '+e;st.style.color='var(--red)';}
};
$('#saveGoal').onclick=async()=>{await post({action:'goal',isk:Number($('#goalIsk').value)||null,deadline:$('#goalDate').value});syncOpts();};
$('#clearGoal').onclick=async()=>{await post({action:'goal',isk:null});$('#goalIsk').value='';syncOpts();};
$('#saveWatch').onclick=async()=>{await post({action:'watchlist',names:$('#watchlist').value.split('\\n')});};
$('#notifPerm').onclick=()=>Notification.requestPermission();
$('#saveIdle').onclick=async()=>{await post({action:'idle_warn',seconds:Number($('#idleWarn').value)||0});syncOpts();};
$('#esiLogin').onclick=async()=>{
 const r=await post({action:'esi_login'});
 if(r.url)window.open(r.url,'_blank');
 else alert(r.error||'Login konnte nicht gestartet werden.');
};
$('#checkUpd').onclick=async()=>{
 $('#updstatus').textContent='Prüfe …';$('#doUpd').hidden=true;
 const r=await post({action:'check_update'});
 if(!r.ok){$('#updstatus').textContent=r.error;return;}
 if(r.available){$('#updstatus').textContent='Neue Version verfügbar: '+r.latest+' (installiert: '+r.current+')';$('#doUpd').hidden=false;}
 else $('#updstatus').textContent='Du hast die aktuellste Version ('+r.current+').';
};
$('#doUpd').onclick=async()=>{
 $('#updstatus').textContent='Lade Update …';
 const r=await post({action:'do_update'});
 $('#updstatus').textContent=r.ok?(r.message||''):r.error;
 if(r.ok&&r.updated)setTimeout(()=>location.reload(),4000);
};
document.querySelectorAll('#opts input[name=mode]').forEach(r=>r.onchange=()=>post({action:'mode',mode:r.value}));

async function post(b){return (await fetch('/',{method:'POST',body:JSON.stringify(b)})).json();}

function syncOpts(){
 if(!state)return;
 document.querySelectorAll('#opts input[name=mode]').forEach(r=>r.checked=r.value===state.mode);
 document.querySelectorAll('#opts input[name=skin]').forEach(r=>r.checked=r.value===(document.documentElement.dataset.skin||''));
 $('#autostart').checked=!!state.autostart;
 // Autostart gibt es nur auf Windows und Linux — sonst Zeile ausblenden
 $('#autostartRow').hidden=state.autostart_ok===false;
 // Log-Ordner nur befüllen, solange niemand darin tippt
 if(document.activeElement!==$('#logDir'))$('#logDir').value=state.log_dir||'';
 // Aufgetretene Fehlercodes auflisten, damit man sie schicken kann
 const errs=state.errors||[];
 $('#errBox').innerHTML=errs.length
  ? '<b style="color:var(--red)">Aufgetretene Fehler:</b><br>'+errs.map(e=>
     esc(e.code)+(e.n>1?' ×'+e.n:'')+' &middot; '+esc(e.help)).join('<br>')
    +'<br>Mit „🩺 Diagnose kopieren" den vollen Bericht holen und schicken.'
  : '';
 $('#baseinfo').textContent=state.baseline_day?('Aktive Baseline: zählt seit '+state.baseline_day+' (UTC).'):'Keine Baseline aktiv.';
 $('#loginfo').textContent='Log-Ordner: '+(state.log_dir||'nicht gefunden!')+' · Dateien: '+state.progress.done+'/'+state.progress.total;
 $('#watchlist').value=(state.watchlist||[]).join('\\n');
 $('#idleWarn').value=state.idle_warn??240;
 $('#verinfo').textContent='Installiert: EVE Canary v'+(state.version||'?')+' · by Askend';
 if(state.goal){$('#goalIsk').value=state.goal.isk;$('#goalDate').value=state.goal.deadline||'';}
 if(state.esi){
  $('#esiNudge').hidden=(state.esi.chars||[]).length>0;
  $('#esiChars').innerHTML=(state.esi.chars||[]).map(c=>
   '👤 <b>'+esc(c.name)+'</b>: '+esc(c.status)+(c.ship?' · '+esc(c.ship):'')+(c.wallet!=null?' · Wallet: '+fmtM(c.wallet)+' ISK':'')+
   ' <span class="esiForget" data-char="'+esc(c.name)+'" style="cursor:pointer;text-decoration:underline">trennen</span>'
  ).join('<br>')||'';
  document.querySelectorAll('.esiForget').forEach(b=>b.onclick=async()=>{
   const r=await post({action:'esi_forget',char:b.dataset.char});if(r.state)state=r.state;syncOpts();});
 }
 // syncOpts baut Teile des Dialogs NEU auf, oft nach dem letzten tick() —
 // ohne diesen Aufruf blieben die frischen Knoten bis zum naechsten Takt deutsch.
 if(lang!=='de')tr(document.body);
}

function beep(freq,times,dur){
 try{
  const ctx=beep.ctx||(beep.ctx=new (window.AudioContext||window.webkitAudioContext)());
  if(ctx.state==='suspended')ctx.resume();  // Autoplay-Sperre: erst nach User-Geste hörbar
  for(let i=0;i<times;i++){
   const o=ctx.createOscillator(),g=ctx.createGain();
   o.frequency.value=freq;o.connect(g);g.connect(ctx.destination);
   const t=ctx.currentTime+i*(dur+0.08);
   g.gain.setValueAtTime(0.15,t);g.gain.exponentialRampToValueAtTime(0.001,t+dur);
   o.start(t);o.stop(t+dur);}
 }catch(e){}}
// AudioContext bei der ersten Nutzer-Geste anlegen/aufwecken, damit spätere
// Alarme im Hintergrund-Tab wirklich tönen (Browser blockiert Autoplay sonst).
window.addEventListener('pointerdown',()=>{
 try{const ctx=beep.ctx||(beep.ctx=new (window.AudioContext||window.webkitAudioContext)());
  if(ctx.state==='suspended')ctx.resume();}catch(e){}
},{once:true});

function handleAlerts(){
 const list=state.alerts||[];
 const now=Date.now()/1000;
 $('#alerts').innerHTML=list.filter(a=>now-a.ts<300).slice(-4).reverse().map(a=>{
  const t=new Date(a.ts*1000).toLocaleTimeString();
  return `<div class="alert ${a.kind}">[${t}] ${esc(a.text)}</div>`}).join('');
 for(const a of list){
  if(a.id<=lastAlertId)continue;
  if(a.kind==='pvp'){
   if($('#sndPvp').checked)beep(880,3,0.18);
   if(Notification.permission==='granted')new Notification('EVE: SPIELER-ANGRIFF!',{body:a.text});
  }else if(a.kind==='depleted'&&$('#sndDep').checked)beep(520,1,0.12);
  else if(a.kind==='drones'){
   if($('#sndDep').checked)beep(590,2,0.15);
   if(Notification.permission==='granted')new Notification('EVE: Drohnen prüfen!',{body:a.text});
  }
  else if(a.kind==='cargo'){
   if($('#sndDep').checked)beep(700,3,0.18);
   if(Notification.permission==='granted')new Notification('EVE: Frachtraum voll!',{body:a.text});
  }
  else if(a.kind==='idle'){
   if($('#sndDep').checked)beep(470,2,0.2);
   if(Notification.permission==='granted')new Notification('EVE: Mining steht!',{body:a.text});
  }
  else if(a.kind==='rate'){
   if($('#sndDep').checked)beep(505,2,0.18);
   if(Notification.permission==='granted')new Notification('EVE: Abbaurate gefallen!',{body:a.text});
  }
  else if(a.kind==='watch'){
   if($('#sndWatch').checked)beep(660,2,0.15);
   if(Notification.permission==='granted')new Notification('EVE: Watchlist',{body:a.text});
  }
  else if(a.kind==='intel'){
   if($('#sndWatch').checked)beep(770,3,0.16);
   if(Notification.permission==='granted')new Notification('EVE: Bedrohung erkannt!',{body:a.text});
  }
  else if(a.kind==='hw'){
   if($('#sndDep').checked)beep(430,2,0.2);
   if(Notification.permission==='granted')new Notification('EVE: Heavy Water fast leer!',{body:a.text});
  }
  lastAlertId=a.id;
 }
 localStorage.setItem('lastAlertId',lastAlertId);
}

let bootDone=false;
function bootScreen(){
 if(bootDone)return;
 const b=$('#boot'),p=(state&&state.progress)||{};
 if(state&&state.ingesting&&p.total>0&&p.done<p.total){
  b.hidden=false;
  const pct=Math.round(100*p.done/p.total);
  $('#bootfill').style.width=pct+'%';
  $('#bootnum').textContent=fmt(p.done)+' / '+fmt(p.total)+' Logdateien · '+pct+'%';
 }else if(!b.hidden){
  $('#bootfill').style.width='100%';
  $('#bootnum').textContent=fmt(p.total||0)+' Logdateien analysiert. Willkommen!';
  setTimeout(()=>b.classList.add('fade'),450);
  setTimeout(()=>{b.hidden=true;},1400);
  bootDone=true;
 }else bootDone=true;
}
function updateBadge(){
 const u=(state&&state.update)||{};
 const b=$('#updBadge');
 if(u.available&&u.latest){b.hidden=false;b.textContent='⬆ Update v'+u.latest;}
 else b.hidden=true;
}
$('#updBadge').onclick=async()=>{
 const v=(state&&state.update&&state.update.latest)||'?';
 if(!confirm('Update auf v'+v+' installieren? Canary startet danach automatisch neu.'))return;
 $('#updBadge').textContent='Update läuft …';
 const r=await post({action:'do_update'});
 if(r.ok&&r.updated)setTimeout(()=>location.reload(),4000);
 else{alert(r.error||r.message||'Update fehlgeschlagen.');updateBadge();}
};
function regionPills(){
 $('#regions').innerHTML=Object.entries(state.regions).map(([id,n])=>
  `<span class="pill ${id===state.region?'on':''}" data-r="${id}">${n}</span>`).join('');
 document.querySelectorAll('#regions .pill').forEach(p=>p.onclick=async()=>{
  await post({action:'region',region:p.dataset.r});tick();});
}

let collapsed=new Set(lsGet('collapsed',[]));
// Master-Umschalter der Live-Ansicht: Miner vs. PvP/Missionen. Strikt getrennt.
let liveMode=localStorage.getItem('liveMode')||'mining';
function renderLiveView(){
 if(lastChars)(liveMode==='combat'?renderCombat:renderLive)(lastChars,lastSummary);
}
function toggleChar(name){
 if(collapsed.has(name))collapsed.delete(name);else collapsed.add(name);
 localStorage.setItem('collapsed',JSON.stringify([...collapsed]));
 renderLiveView();
}
let lastChars=null,lastSummary=null;
$('#charFilter').value=localStorage.getItem('charFilter')||'';
$('#charFilter').onchange=()=>{
 localStorage.setItem('charFilter',$('#charFilter').value);
 if(lastChars)renderLive(lastChars,lastSummary);};
$('#collapseAll').onclick=()=>{
 const names=(lastChars||[]).map(c=>c.name);
 if(names.length&&names.every(n=>collapsed.has(n)))names.forEach(n=>collapsed.delete(n));
 else names.forEach(n=>collapsed.add(n));
 localStorage.setItem('collapsed',JSON.stringify([...collapsed]));
 if(lastChars)renderLive(lastChars,lastSummary);};
// Rollen-Filter-Pills (Alle / Mining / Missionen / PvP)
(function(){const rf=localStorage.getItem('roleFilter')||'';
 document.querySelectorAll('.rolef').forEach(p=>{
  p.classList.toggle('on',p.dataset.role===rf);
  p.onclick=()=>{localStorage.setItem('roleFilter',p.dataset.role);
   document.querySelectorAll('.rolef').forEach(x=>x.classList.toggle('on',x===p));
   renderLiveView();};});})();
// "Offline zeigen" umschalten (Live blendet Offline-Chars standardmäßig aus)
$('#showOffline').classList.toggle('on',localStorage.getItem('showOffline')==='1');
$('#showOffline').onclick=()=>{const on=localStorage.getItem('showOffline')!=='1';
 localStorage.setItem('showOffline',on?'1':'0');
 $('#showOffline').classList.toggle('on',on);
 renderLiveView();};
// Mining- vs. PvP/Missionen-Ansicht umschalten (nur in der Live-Ansicht sichtbar)
function syncModeSel(){document.querySelectorAll('.modesel').forEach(b=>b.classList.toggle('on',b.dataset.mode===liveMode));}
document.querySelectorAll('.modesel').forEach(b=>b.onclick=()=>{
 liveMode=b.dataset.mode;localStorage.setItem('liveMode',liveMode);syncModeSel();renderLiveView();});
syncModeSel();
function syncCharFilter(chars){
 const sel=$('#charFilter');
 const names=chars.map(c=>c.name);
 const want='Alle Charaktere|'+names.join('|');
 if(sel.dataset.opts!==want){
  // Auswahl aus localStorage wiederherstellen (beim ersten Render war value=''
  // gesetzt, bevor die Optionen existierten -> sonst Dropdown und Filter uneins).
  const cur=localStorage.getItem('charFilter')||'';
  sel.innerHTML='<option value="">Alle Charaktere</option>'+
   names.map(n=>`<option value="${esc(n)}">${esc(n)}</option>`).join('');
  sel.value=names.includes(cur)?cur:'';
  sel.dataset.opts=want;
 }
 const all=names.length&&names.every(n=>collapsed.has(n));
 $('#collapseAll').textContent=all?'Alle aufklappen':'Alle einklappen';
}
function heroTiles(label,today,yesterday,week,subToday,subWeek){
 const delta=yesterday>0?Math.round((today/yesterday-1)*100):null;
 const trend=delta==null?'':' · <span style="color:var(--'+(delta>=0?'green':'red')+')">'+(delta>=0?'▲':'▼')+' '+Math.abs(delta)+'% vs. gestern</span>';
 return `<div class="card" style="grid-column:1/-1">
  <div class="stats" style="grid-template-columns:repeat(3,1fr);margin:0">
   <div class="stat"><div class="l">${label}</div><div class="v isk" style="font-size:24px">${fmtM(today)}</div><div class="l">${subToday||''}${trend}</div></div>
   <div class="stat"><div class="l">Gestern</div><div class="v isk" style="font-size:24px">${fmtM(yesterday)}</div></div>
   <div class="stat"><div class="l">Letzte 7 Tage</div><div class="v isk" style="font-size:24px">${fmtM(week)}</div><div class="l">${subWeek||''}</div></div>
  </div></div>`;
}
function heroBar(s){
 if(!s)return '';
 return heroTiles('⛏ Geminert heute',s.today,s.yesterday,s.week,
  fmt(s.m3_today)+' m³',fmt(s.m3_week)+' m³ · Ø '+fmtM(s.week/7)+'/Tag');
}
function renderLive(chars,summary){
 lastChars=chars;
 if(summary!==undefined)lastSummary=summary;
 syncCharFilter(chars);
 const f=localStorage.getItem('charFilter')||'';
 if(f&&chars.some(c=>c.name===f))chars=chars.filter(c=>c.name===f);
 // Rollen-Filter: nur Chars der gewählten Rolle zeigen (Alle = kein Filter)
 const rf=localStorage.getItem('roleFilter')||'';
 if(rf)chars=chars.filter(c=>c.role===rf);
 // Live zeigt nur eingeloggte Chars. Offline nur, wenn ausdrücklich gewünscht.
 const showOff=localStorage.getItem('showOffline')==='1';
 if(!showOff)chars=chars.filter(c=>c.active);
 $('#hero').innerHTML=heroBar(summary);
 if(!chars.length){$('#empty').hidden=false;
  $('#empty').textContent=!showOff?'Gerade ist kein Charakter eingeloggt. Mit „💤 Offline zeigen" siehst du auch die abgemeldeten.':(rf?'Kein Charakter mit dieser Rolle. Tippe auf einer Karte auf das Rollen-Symbol, um sie zuzuweisen.':'Warte auf Gamelog-Daten … (EVE-Client an? Im Client „Spielprotokoll speichern" aktivieren.)');
  $('#grid').innerHTML='';return;}
 $('#empty').hidden=true;
 $('#grid').innerHTML=chars.map(c=>{
  const maxOre=Math.max(1,...c.ores.map(o=>o.isk));
  const maxS=Math.max(1,...c.spark);
  const min=collapsed.has(c.name);
  return `<div class="card ${min?'min':''}">
   <div class="chead" data-c="${esc(c.name)}">
    <span class="arr">▼</span>
    ${c.portrait?`<img class="pf" src="${c.portrait}" alt="">`
      :(!c.esi_linked?`<span class="pf pf-none" data-esihint="1" title="Noch nicht mit EVE-Login verbunden. Klick für Portrait, Schiff, Wallet und automatisches Heavy Water.">👤</span>`:'')}
    <span class="char">${esc(c.name)} <span class="sys">· ${esc(c.system)}${c.ship?' · '+esc(c.ship):''}</span></span>
    <select class="rolesel" data-c="${esc(c.name)}" title="Rolle zuweisen (für die Filter oben)">
     <option value=""${c.role?'':' selected'}>Rolle …</option>
     <option value="mining"${c.role==='mining'?' selected':''}>⛏ Mining</option>
     <option value="mission"${c.role==='mission'?' selected':''}>🎯 Missionen</option>
     <option value="pvp"${c.role==='pvp'?' selected':''}>⚔ PvP</option>
    </select>
    <span class="mini">${c.cargo_full?'<span class="warnbadge drone">⚠ Frachtraum voll!</span> · ':''}${(c.tool_warns||[]).map(w=>'<span class="warnbadge'+(w.drone?' drone':'')+'">⚠ '+w.tool+(w.count>1?' ×'+w.count:'')+'</span> · ').join('')}${(c.lasers_off||[]).map(w=>'<span class="warnbadge">⛔ '+w.tool+' aus</span> · ').join('')}${c.heavy_water&&c.heavy_water.on&&c.heavy_water.min_left<30?'<span class="warnbadge drone">⛽ HW ~'+c.heavy_water.min_left+' min</span> · ':''}${c.drones_idle?'<span class="warnbadge">🤖 Drohnen ohne Erz</span> · ':''}${c.laser_stalled?'<span class="warnbadge">⛏ Laser ohne Erz</span> · ':''}${c.rate_low?'<span class="warnbadge">⚠ Rate '+c.rate_low+'%</span> · ':''}${mineIdle(c,state)?'<span class="warnbadge">⚠ Kein Erz seit '+Math.round(c.mine_idle/60)+' min</span> · ':''}${fmtM(c.total_isk)} ISK · ${fmt(c.m3h)} m³/h${c.dps_in>0?' · <span class=\"in\">⚠ '+c.dps_in+' DPS rein</span>':''}</span>
   </div>
   <div class="cbody">
   ${c.cargo_full?`<div class="cardwarn drone">⚠ Frachtraum voll! Erz verladen oder komprimieren.</div>`:''}
   ${(c.tool_warns||[]).map(w=>w.drone
     ?`<div class="cardwarn drone">⚠ ${esc(w.tool)}${w.count>1?' ×'+w.count:''} abgeschaltet, Drohnen prüfen!</div>`
     :`<div class="cardwarn">⚠ ${esc(w.tool)}${w.count>1?' ×'+w.count:''} abgeschaltet, Ziel prüfen</div>`).join('')}
   ${(c.lasers_off||[]).map(w=>`<div class="cardwarn">⛔ ${esc(w.tool)} aus seit ${new Date(w.since*1000).toLocaleTimeString().slice(0,5)}. Neues Ziel erfassen! <span class="laserok" data-char="${esc(c.name)}" data-tool="${esc(w.tool)}">✓ erledigt</span></div>`).join('')}
   ${c.drones_idle?`<div class="cardwarn">🤖 Drohnen liefern gerade kein Erz (gestoppt, voll oder auf dem Rückweg).</div>`:''}
   ${c.laser_stalled?`<div class="cardwarn">⛏ Strip Miner liefert gerade kein Erz, während die Drohnen weiterlaufen.</div>`:''}
   ${c.rate_low?`<div class="cardwarn">⚠ Abbaurate nur noch ${c.rate_low}%. Vermutlich ist ein Modul oder eine Drohne aus.</div>`:''}
   ${mineIdle(c,state)?`<div class="cardwarn">⚠ Seit ${Math.round(c.mine_idle/60)} min kein Erz. Laser und Drohnen prüfen!</div>`:''}
   <div class="sub">${c.trips>0?'Trip '+(c.trips+1)+' · seit Abdocken':'Session'} ${c.session_min} min · ${c.depleted} Asteroiden leergebaggert · Preise: ${state.regions[state.region]}</div>
   <div class="stats">
    <div class="stat"><div class="l">${c.trips>0?'ISK Trip':'ISK Session'}</div><div class="v isk">${fmtM(c.total_isk)}</div></div>
    <div class="stat"><div class="l">Erz (${fmt(c.m3)} m³)</div><div class="v isk">${fmtM(c.ore_isk)}</div></div>
    <div class="stat"><div class="l">m³/h</div><div class="v out">${fmt(c.m3h)}</div></div>
    <div class="stat"><div class="l">Laderaum ≈ ${fmt(c.hold_m3)} m³ · ${state.regions[state.region]}</div><div class="v isk">${
      c.hold_prices==='none'
       ?'<span style="color:var(--dim);font-size:12px;font-weight:400">keine Preisdaten</span>'
       :'~'+fmtM(c.hold_isk)+(c.hold_prices==='partial'?' <span style="color:var(--dim)" title="Für einzelne Erztypen fehlen Preisdaten">±</span>':'')
    }</div></div>
    ${c.heavy_water||!c.esi_linked?`<div class="stat"><div class="l">Heavy Water${c.heavy_water?' · '+c.heavy_water.core.toUpperCase():''}${c.heavy_water&&c.heavy_water.esi?' · ESI':''} ${c.heavy_water&&c.heavy_water.esi?'':`<span class="hwset" data-char="${esc(c.name)}" data-core="${c.heavy_water?c.heavy_water.core:''}" data-fill="${c.heavy_water&&c.heavy_water.fill?c.heavy_water.fill:''}" title="Bestand im Laderaum setzen">⛽</span>`}</div><div class="v ${c.heavy_water&&c.heavy_water.on&&c.heavy_water.min_left<30?'in':''}">${c.heavy_water?fmt(c.heavy_water.units):'—'}</div><div class="l">${c.heavy_water?(c.heavy_water.on&&c.heavy_water.eta?'reicht bis ~'+new Date(c.heavy_water.eta*1000).toLocaleTimeString().slice(0,5)+' Uhr':'Kern inaktiv, Verbrauch pausiert'):'per ⛽ setzen'}</div></div>`:''}
    <div class="stat"><div class="l">Bounties</div><div class="v grn">${fmtM(c.bounty)}</div></div>
    ${c.wallet!=null?`<div class="stat"><div class="l">Wallet (ESI)</div><div class="v grn">${fmtM(c.wallet)}</div></div>`:''}
    <div class="stat"><div class="l">Schaden raus/rein</div><div class="v"><span class="out">${fmtM(c.dmg_out)}</span> / <span class="in">${fmtM(c.dmg_in)}</span></div></div>
    <div class="stat"><div class="l">DPS raus/rein</div><div class="v"><span class="out">${c.dps_out}</span> / <span class="in">${c.dps_in}</span></div></div>
   </div>
   ${c.spark.length>1?`<div class="spark">${c.spark.map(v=>`<div style="height:${Math.max(3,100*v/maxS)}%"></div>`).join('')}</div><div class="sub">Mining m³/min</div>`:''}
   ${c.ores.length?`<div class="sect">Mining</div><table>`+c.ores.map(o=>o.known
     ?`<tr><td>${esc(o.ore)}<div class="bar" style="width:${100*o.isk/maxOre}%"></div></td>
      <td class="r">${fmt(o.units)} Stk</td><td class="r isk">${fmtM(o.isk)}</td></tr>`
     :`<tr title="Dieses Erz kennt Canary noch nicht, daher kein Wert. Bitte den Namen im Discord melden."><td>⚠ ${esc(o.ore)}</td>
      <td class="r">${fmt(o.units)} Stk</td><td class="r" style="color:var(--gold)">unbekannt</td></tr>`).join('')+`</table>`
     +(c.ores.some(o=>!o.known)?`<div class="sub" style="color:var(--gold)">⚠ Ein Erz ist Canary unbekannt (oben markiert). Bitte den Namen im Discord melden, dann nehme ich es auf.</div>`:''):''}
   ${c.compressed.length?`<div class="sect">Komprimiert (Session)</div><table>`+c.compressed.map(k=>
     `<tr><td>${k.type}</td><td class="r">${fmt(k.units)} Stk</td><td class="r">${fmt(k.m3)} m³</td><td class="r isk">${fmtM(k.isk)}</td></tr>`).join('')+`</table>`:''}
   ${c.weapons.length?`<div class="sect">Waffen</div><table>`+c.weapons.map(w=>
     `<tr><td>${esc(w[0])}</td><td class="r">${fmt(w[1])} dmg</td></tr>`).join('')+`</table>`:''}
   ${c.top_targets.length?`<div class="sect">Top-Ziele</div><table>`+c.top_targets.map(t=>
     `<tr><td>${esc(t[0])}</td><td class="r">${fmt(t[1])}</td></tr>`).join('')+`</table>`:''}
   ${c.top_attackers.length?`<div class="sect">Top-Angreifer</div><table>`+c.top_attackers.map(t=>
     `<tr><td>${esc(t[0])}</td><td class="r">${fmt(t[1])}</td></tr>`).join('')+`</table>`:''}
   ${fittingSection(c)}
   </div>
  </div>`}).join('');
 bindFit();
 document.querySelectorAll('.chead').forEach(h=>h.onclick=()=>toggleChar(h.dataset.c));
 document.querySelectorAll('.rolesel').forEach(s=>{
  s.onclick=e=>e.stopPropagation();  // Klick soll die Karte nicht ein-/ausklappen
  s.onchange=async()=>{await post({action:'set_role',char:s.dataset.c,role:s.value});
   if(lastChars){lastChars.forEach(c=>{if(c.name===s.dataset.c)c.role=s.value;});renderLive(lastChars,lastSummary);}};
 });
 document.querySelectorAll('[data-esihint]').forEach(el=>el.onclick=e=>{
  e.stopPropagation();syncOpts();$('#opts').showModal();
  const s=$('#opts .sect.esi');if(s)s.scrollIntoView({block:'center'});
 });
 document.querySelectorAll('.laserok').forEach(b=>b.onclick=async e=>{
  e.stopPropagation();
  await post({action:'laser_ok',char:b.dataset.char,tool:b.dataset.tool});
  tick();
 });
 document.querySelectorAll('.hwset').forEach(b=>b.onclick=async e=>{
  e.stopPropagation();
  const v=prompt('Heavy Water im Laderaum (Stück). Nach dem Nachfüllen einfach Enter drücken, 0 entfernt die Anzeige:',b.dataset.fill||'');
  if(v===null)return;
  if(v.trim()===''&&!b.dataset.fill)return;
  if(v.trim()==='0'){await post({action:'heavy_water',char:b.dataset.char});tick();return;}
  if(v.trim()===''){await post({action:'heavy_water',char:b.dataset.char,units:Number(b.dataset.fill),core:b.dataset.core||'t1'});tick();return;}
  const core=b.dataset.core||(confirm('Industrial Core II (T2, 200/min)?\\nOK = T2 · Abbrechen = T1 (100/min)')?'t2':'t1');
  await post({action:'heavy_water',char:b.dataset.char,units:Number(v.replace(/[^\\d]/g,''))||0,core});
  tick();
 });
}

// PvP/Missions-Ansicht: getrennt von der Miner-Ansicht, gleiche Filter.
const EWAR_LABEL={scramble:'🔴 Scram',disrupt:'Point',web:'Web',jam:'Jam',neut:'Neut',paint:'Paint',damp:'Damp',td:'TD'};
function cargoLine(cg){
 if(!cg)return '<div class="l">über EVE-Login</div>';
 const now=Date.now()/1000;
 const age=Math.max(0,Math.round((now-cg.as_of)/60));
 const nxt=Math.round((cg.next-now)/60);
 const when=new Date(cg.as_of*1000).toISOString().slice(11,16);
 return `<div class="l">Stand: vor ${age} min · EVE ${when} · ${nxt>0?'nächste in '+nxt+' min':'wird aktualisiert'}</div>`;
}
// Grafischer Fitting-Block: Schiffs-Render + Modul-Icons nach Slot, einklappbar.
// Bilder vom offiziellen EVE-Bilderdienst (wie die Portraits). Für beide Ansichten.
const SLOT_LBL={hi:'Hi',med:'Mid',low:'Low',rig:'Rig',sub:'Sub'};
function fittingSection(c){
 const ft=c.fitting;
 // Noch keine Fitting-Daten: nur für ESI-Chars den Bereich zeigen, mit Hinweis
 // (ESI-Assets aktualisieren nur ~1x/Stunde), statt ihn ganz auszublenden.
 if(!ft||!ft.mods||!ft.mods.length){
  if(!c.esi_linked)return '';
  return `<div class="fitsec"><span class="fittoggle" data-c="${esc(c.name)}">🔧 Fitting</span>
   <div class="fitbox" data-c="${esc(c.name)}" hidden><div class="l">Wird beim nächsten EVE-Login-Abgleich geladen (nach einem Umbau bis zu 1 Stunde).</div></div></div>`;
 }
 const age=Math.max(0,Math.round((Date.now()/1000-ft.as_of)/60));
 const row=g=>{const ms=ft.mods.filter(m=>m.grp===g);if(!ms.length)return '';
  return `<div class="fitrow"><span class="fitlbl">${SLOT_LBL[g]}</span><span class="fiticons">`
   +ms.map(m=>`<img class="fiticon" loading="lazy" src="https://images.evetech.net/types/${m.tid}/icon?size=64" title="${esc(m.name)}" alt="${esc(m.name)}">`).join('')
   +`</span></div>`;};
 return `<div class="fitsec">
   <span class="fittoggle" data-c="${esc(c.name)}">🔧 Fitting</span>
   <div class="fitbox" data-c="${esc(c.name)}" hidden>
    <div class="fitwrap">
     <img class="fitship" loading="lazy" src="https://images.evetech.net/types/${ft.ship_tid}/render?size=256" alt="">
     <div class="fitslots">${['hi','med','low','rig','sub'].map(row).join('')}</div>
    </div>
    <div class="l">Stand: vor ${age} min · aus EVE-Login</div>
   </div>
  </div>`;
}
function bindFit(){
 document.querySelectorAll('.fittoggle').forEach(t=>t.onclick=e=>{
  e.stopPropagation();
  const b=[...document.querySelectorAll('.fitbox')].find(x=>x.dataset.c===t.dataset.c);
  if(b)b.hidden=!b.hidden;});
}
function renderCombat(chars,summary){
 lastChars=chars;
 if(summary!==undefined)lastSummary=summary;
 syncCharFilter(chars);
 const f=localStorage.getItem('charFilter')||'';
 if(f&&chars.some(c=>c.name===f))chars=chars.filter(c=>c.name===f);
 const rf=localStorage.getItem('roleFilter')||'';
 if(rf)chars=chars.filter(c=>c.role===rf);
 const showOff=localStorage.getItem('showOffline')==='1';
 if(!showOff)chars=chars.filter(c=>c.active);
 // Flotten-Überblick oben
 const tB=chars.reduce((s,c)=>s+(c.bounty||0),0);
 const tL=chars.reduce((s,c)=>s+((c.cargo&&c.cargo.buy)||0),0);
 const tK=chars.reduce((s,c)=>s+(c.kills||0),0);
 $('#hero').innerHTML=`<div class="card" style="grid-column:1/-1"><div class="stats" style="grid-template-columns:repeat(3,1fr);margin:0">
   <div class="stat"><div class="l">⚔ Bounty (Session)</div><div class="v grn" style="font-size:24px">${fmtM(tB)}</div><div class="l">${tK} Kills</div></div>
   <div class="stat"><div class="l">Loot / Cargo</div><div class="v isk" style="font-size:24px">${fmtM(tL)}</div><div class="l">aus EVE-Login</div></div>
   <div class="stat"><div class="l">Session gesamt</div><div class="v isk" style="font-size:24px">${fmtM(tB+tL)}</div><div class="l">Bounty + Loot</div></div>
  </div></div>`;
 if(!chars.length){$('#empty').hidden=false;
  $('#empty').textContent=!showOff?'Gerade ist kein Charakter eingeloggt. Mit „💤 Offline zeigen" siehst du auch die abgemeldeten.':'Kein Charakter mit dieser Rolle.';
  $('#grid').innerHTML='';return;}
 $('#empty').hidden=true;
 $('#grid').innerHTML=chars.map(c=>{
  const min=collapsed.has(c.name);
  const shots=(c.hits_out||0)+(c.miss_out||0);
  const hit=shots?Math.round(100*c.hits_out/shots):null;
  const maxW=Math.max(1,...c.weapons.map(w=>w[1]));
  const sessISK=(c.bounty||0)+((c.cargo&&c.cargo.buy)||0);
  return `<div class="card ${min?'min':''}">
   <div class="chead" data-c="${esc(c.name)}">
    <span class="arr">▼</span>
    ${c.portrait?`<img class="pf" src="${c.portrait}" alt="">`:''}
    <span class="char">${esc(c.name)} <span class="sys">· ${esc(c.system)}${c.ship?' · '+esc(c.ship):''}</span></span>
    <select class="rolesel pill" data-c="${esc(c.name)}" title="Rolle zuweisen (für die Filter oben)">
     <option value=""${c.role?'':' selected'}>Rolle …</option>
     <option value="mining"${c.role==='mining'?' selected':''}>⛏ Mining</option>
     <option value="mission"${c.role==='mission'?' selected':''}>🎯 Missionen</option>
     <option value="pvp"${c.role==='pvp'?' selected':''}>⚔ PvP</option>
    </select>
    <span class="mini">${c.dps_in>0?'<span class="in">⚠ '+c.dps_in+' DPS rein</span> · ':''}${fmtM(sessISK)} ISK</span>
   </div>
   <div class="cbody">
    <div class="stats">
     <div class="stat"><div class="l">Bounty</div><div class="v grn">${fmtM(c.bounty||0)}</div></div>
     <div class="stat"><div class="l">Loot / Cargo</div><div class="v isk">${c.cargo?fmtM(c.cargo.buy):'—'}</div>${cargoLine(c.cargo)}</div>
     <div class="stat"><div class="l">Session gesamt</div><div class="v isk">${fmtM(sessISK)}</div></div>
    </div>
    ${(()=>{const so=c.spark_out||[],si=c.spark_in||[];const mx=Math.max(1,...so,...si);
      return (so.length>1||si.length>1)?`<div class="sect">Kampfverlauf (Schaden/min)</div>
       <div class="spark">${so.map(v=>`<div style="height:${Math.max(2,100*v/mx)}%"></div>`).join('')}</div>
       <div class="spark dmgin">${si.map(v=>`<div style="height:${Math.max(2,100*v/mx)}%"></div>`).join('')}</div>
       <div class="sub"><span class="out">▮ raus</span> · <span class="in">▮ rein</span> · gleiche Skala</div>`:'';})()}
    <div class="sect">⚔ Offense</div>
    <div class="stats">
     <div class="stat"><div class="l">Schaden raus</div><div class="v out">${fmt(c.dmg_out||0)}</div></div>
     <div class="stat"><div class="l">DPS</div><div class="v out">${c.dps_out}</div></div>
     <div class="stat"><div class="l">Trefferquote</div><div class="v">${hit==null?'—':hit+'%'}</div><div class="l">${shots?c.hits_out+' / '+shots:''}</div></div>
     <div class="stat"><div class="l">Kills</div><div class="v">${c.kills||0}</div></div>
    </div>
    ${c.weapons.length?`<div class="sect">Waffen</div><table>`+c.weapons.map(w=>
      `<tr><td>${esc(w[0])}<div class="bar" style="width:${100*w[1]/maxW}%"></div></td><td class="r">${fmt(w[1])} dmg</td></tr>`).join('')+`</table>`:''}
    ${c.top_targets.length?`<div class="sect">Top-Ziele</div><table>`+c.top_targets.map(t=>
      `<tr><td>${esc(t[0])}</td><td class="r">${fmt(t[1])}</td></tr>`).join('')+`</table>`:''}
    <div class="sect">🛡 Defense</div>
    <div class="stats">
     <div class="stat"><div class="l">Schaden rein</div><div class="v in">${fmt(c.dmg_in||0)}</div></div>
     <div class="stat"><div class="l">DPS rein</div><div class="v in">${c.dps_in}</div></div>
     <div class="stat"><div class="l">Gegner daneben</div><div class="v">${c.miss_in||0}</div></div>
    </div>
    ${c.ewar&&c.ewar.length?`<div class="cardwarn drone">⚠ EWAR gegen dich: `+c.ewar.map(e=>(EWAR_LABEL[e[0]]||e[0])+' ×'+e[1]).join(' · ')+`</div>`:''}
    ${c.top_attackers.length?`<div class="sect">Top-Angreifer</div><table>`+c.top_attackers.map(t=>
      `<tr><td>${esc(t[0])}</td><td class="r">${fmt(t[1])}</td></tr>`).join('')+`</table>`:''}
    ${(c.salvage&&(c.salvage.ok||c.salvage.empty||c.salvage.fail))?`<div class="sect">Salvage</div><div class="l">${c.salvage.ok} Wracks geborgen · ${c.salvage.empty} leer · ${c.salvage.fail} Fehlversuch</div>`:''}
    ${fittingSection(c)}
   </div>
  </div>`}).join('');
 document.querySelectorAll('.chead').forEach(h=>h.onclick=()=>toggleChar(h.dataset.c));
 document.querySelectorAll('.rolesel').forEach(s=>{
  s.onclick=e=>e.stopPropagation();
  s.onchange=async()=>{await post({action:'set_role',char:s.dataset.c,role:s.value});
   if(lastChars){lastChars.forEach(c=>{if(c.name===s.dataset.c)c.role=s.value;});renderCombat(lastChars,lastSummary);}};
 });
 bindFit();
}

function renderMonth(days){
 $('#empty').hidden=days.length>0;
 if(!days.length){$('#empty').textContent='Noch keine historischen Daten.';$('#grid').innerHTML='';return;}
 const max=Math.max(1,...days.map(d=>d.total));
 const sum=days.reduce((a,d)=>a+d.total,0), sumM3=days.reduce((a,d)=>a+d.m3,0);
 $('#grid').innerHTML=`<div class="card" style="grid-column:1/-1">
   <div class="char">Letzte 30 Tage</div>
   <div class="sub">${fmtM(sum)} ISK · ${fmt(sumM3)} m³ · Bewertung: aktuelle ${state.regions[state.region]}-Preise</div>
   <div class="chart">${days.map(d=>{
     const h1=110*d.ore_isk/max, h2=110*d.bounty/max;
     return `<div class="col" title="${d.day}: ${fmtM(d.total)} ISK">
       <div class="seg2" style="height:${h2}px"></div><div class="seg1" style="height:${h1}px"></div></div>`;}).join('')}</div>
   <div class="legend"><span><span class="dot" style="background:var(--cyan)"></span>Erz</span>
   <span><span class="dot" style="background:var(--green)"></span>Bounties</span></div>
   <table>${days.slice().reverse().map(d=>
    `<tr><td>${d.day}</td><td class="r">${fmt(d.m3)} m³</td><td class="r">${fmt(d.depleted)} Asteroiden</td><td class="r out">${fmtM(d.dmg_out)} dmg</td><td class="r isk">${fmtM(d.total)} ISK</td></tr>`).join('')}</table>
  </div>`;
}

function renderTotal(t){
 $('#empty').hidden=true;
 const maxOre=Math.max(1,...t.ores.map(o=>o.isk));
 $('#grid').innerHTML=`<div class="card">
   <div class="char">Gesamt${state.baseline_day?' (seit '+state.baseline_day+')':''}</div>
   <div class="sub">${t.days_active} aktive Tage · ${fmt(t.depleted)} Asteroiden leergebaggert</div>
   <div class="stats">
    <div class="stat"><div class="l">ISK gesamt</div><div class="v isk">${fmtM(t.total_isk)}</div></div>
    <div class="stat"><div class="l">Erz-Wert</div><div class="v isk">${fmtM(t.ore_isk)}</div></div>
    <div class="stat"><div class="l">Bounties</div><div class="v grn">${fmtM(t.bounty)}</div></div>
    <div class="stat"><div class="l">Erz gesamt</div><div class="v">${fmt(t.m3)} m³</div></div>
    <div class="stat"><div class="l">Bester Tag</div><div class="v isk">${fmtM(t.best_day.isk)}</div></div>
    <div class="stat"><div class="l">Schaden raus/rein</div><div class="v"><span class="out">${fmtM(t.dmg_out)}</span> / <span class="in">${fmtM(t.dmg_in)}</span></div></div>
   </div>
   <div class="sub">Bester Tag: ${t.best_day.day}</div>
  </div>
  <div class="card"><div class="char">Erz-Bilanz (nach Wert)</div><table>${t.ores.map(o=>
   `<tr><td>${o.ore}<div class="bar" style="width:${100*o.isk/maxOre}%"></div></td>
    <td class="r">${fmt(o.units)}</td><td class="r">${fmt(o.m3)} m³</td><td class="r isk">${fmtM(o.isk)}</td></tr>`).join('')}</table></div>
  <div class="card"><div class="char">Pro Charakter</div><table>${Object.entries(t.chars).map(([n,c])=>
   `<tr><td>${esc(n)}</td><td class="r">${fmt(c.m3)} m³</td><td class="r grn">${fmtM(c.bounty)}</td><td class="r isk">${fmtM(c.ore_isk+c.bounty)}</td></tr>`).join('')}</table></div>
  <div class="card"><div class="char">Komprimiert pro Charakter</div>
   <div class="sub">Alles, was über die Schiffs-Kompression gelaufen ist</div>
   <div style="overflow-x:auto"><table>${t.compressed.length?t.compressed.map(k=>
   `<tr><td style="white-space:nowrap">${esc(k.char)}</td><td>${esc(k.type)}</td><td class="r">${fmt(k.units)} Stk</td><td class="r">${fmt(k.m3)} m³</td><td class="r isk">${fmtM(k.isk)}</td></tr>`).join(''):'<tr><td>Noch nichts komprimiert</td></tr>'}</table></div></div>`;
}

let compPeriod=localStorage.getItem('compPeriod')||'today';
let lastAnalyse=null;
const PERIODS={today:'Heute',week:'7 Tage',month:'30 Tage',year:'12 Monate'};
let compOpen=new Set(lsGet('compOpen',[]));
function toggleComp(key){
 if(compOpen.has(key))compOpen.delete(key);else compOpen.add(key);
 localStorage.setItem('compOpen',JSON.stringify([...compOpen]));
 if(lastAnalyse)renderAnalyse(lastAnalyse);
}
function compCard(comp){
 const p=comp[compPeriod]||{total:{units:0,m3:0,isk:0,types:[]},chars:{}};
 const pills=Object.entries(PERIODS).map(([k,l])=>
  `<span class="pill ${k===compPeriod?'on':''}" data-p="${k}">${l}</span>`).join('');
 const tbl=rows=>rows.map(k=>
  `<tr><td>${k.type}</td><td class="r">${fmt(k.units)} Stk</td><td class="r">${fmt(k.m3)} m³</td><td class="r isk">${fmtM(k.isk)}</td></tr>`).join('');
 const row=(key,label,d)=>{
  const open=compOpen.has(key);
  return `<div class="chead" data-cc="${key}" style="padding:6px 0;border-top:1px solid var(--line)">
    <span class="arr" style="${open?'':'transform:rotate(-90deg)'}">▼</span>
    <span style="font-size:13px;font-weight:600;color:var(--white)">${label}</span>
    <span class="mini">${fmt(d.units)} Stk · ${fmt(d.m3)} m³ · <span class="isk">${fmtM(d.isk)} ISK</span></span>
   </div>${open?`<table style="margin:0 0 8px 18px">${tbl(d.types)}</table>`:''}`;
 };
 return `<div class="card" style="grid-column:1/-1"><div class="chead" style="cursor:default">
   <span class="char">Kompression</span><span class="mini" style="display:flex;gap:4px">${pills}</span></div>
  <div class="sub">${PERIODS[compPeriod]} gesamt: ${fmt(p.total.units)} Stk · ${fmt(p.total.m3)} m³ · <span class="isk">${fmtM(p.total.isk)} ISK</span></div>
  ${p.total.types.length?row('__total__','Gesamt nach Typ',p.total):'<div class="sub">Keine Kompression im Zeitraum.</div>'}
  ${Object.entries(p.chars).map(([n,c])=>row(n,n,c)).join('')}
 </div>`;
}
function renderAnalyse(a){
 lastAnalyse=a;
 $('#empty').hidden=true;
 let goalHtml='';
 if(a.goal){
  goalHtml=`<div class="card" style="grid-column:1/-1"><div class="char">Ziel: ${fmtM(a.goal.isk)} ISK${a.goal.deadline?' bis '+a.goal.deadline:''}</div>
   <div class="progress"><div style="width:${Math.min(100,a.goal.pct)}%"></div></div>
   <div class="sub">${fmtM(a.goal.current)} / ${fmtM(a.goal.isk)} (${a.goal.pct}%) · Ø letzte 7 Tage: ${fmtM(a.goal.avg7)}/Tag
   ${a.goal.eta_date?' · bei aktueller Rate erreicht am <b>'+a.goal.eta_date+'</b>':''}</div></div>`;
 }else{
  goalHtml=`<div class="card" style="grid-column:1/-1"><div class="sub">Kein Ziel gesetzt. Unter ⚙ Optionen kannst du ein ISK-Ziel mit Prognose anlegen.</div></div>`;
 }
 const maxP=Math.max(1,...a.playtime.map(p=>p.minutes));
 $('#grid').innerHTML=goalHtml+compCard(a.compression||{})+
  `<div class="card"><div class="char">Erz-Effizienz (ISK/m³)</div>
   <div class="sub">Was lohnt sich am meisten pro Laderaum?</div><table>${a.efficiency.map(e=>
   `<tr><td>${e.ore}</td><td class="r">${e.isk_per_m3} ISK/m³</td><td class="r">${fmt(e.m3)} m³</td><td class="r isk">${fmtM(e.isk)}</td></tr>`).join('')}</table></div>
  <div class="card"><div class="char">Waffen-Bilanz</div><table>${a.weapons.length?a.weapons.map(w=>
   `<tr><td>${esc(w[0])}</td><td class="r out">${fmt(w[1])} dmg</td></tr>`).join(''):'<tr><td class="r">Noch keine Kampfdaten</td></tr>'}</table></div>
  <div class="card"><div class="char">Spielzeit</div><table>${a.playtime.slice(-14).reverse().map(p=>
   `<tr><td>${p.day}<div class="bar" style="width:${100*p.minutes/maxP}%"></div></td>
    <td class="r">${Math.floor(p.minutes/60)}h ${p.minutes%60}m</td></tr>`).join('')}</table></div>
  <div class="card"><div class="char">Sicherheit</div>
   <div class="sub">Spieler-Angriffe (gesamt)</div><table>${a.pvp.length?a.pvp.map(p=>
   `<tr><td class="in">${p.attacker}</td><td class="r">auf ${p.char}</td><td class="r">${fmt(p.dmg)} dmg</td><td class="r">${p.days[p.days.length-1]}</td></tr>`).join(''):'<tr><td>Keine Spieler-Angriffe erkannt ✓</td></tr>'}</table></div>`;
 document.querySelectorAll('[data-p]').forEach(el=>el.onclick=()=>{
  compPeriod=el.dataset.p;localStorage.setItem('compPeriod',compPeriod);
  if(lastAnalyse)renderAnalyse(lastAnalyse);});
 document.querySelectorAll('[data-cc]').forEach(el=>el.onclick=()=>toggleComp(el.dataset.cc));
}

let pipWin=null;
const OV_CSS=`*{margin:0;box-sizing:border-box;font-family:'Segoe UI',system-ui,sans-serif}
body{background:#0b0e14;padding:8px;overflow-y:auto}
.hd{display:flex;justify-content:space-between;align-items:center;font-size:9px;
letter-spacing:1.5px;color:#5d6b80;margin-bottom:6px}
.hd b{color:#35c8e8}
.row{display:flex;align-items:center;gap:8px;background:#121722;border:1px solid #1e2636;
border-radius:8px;padding:6px 10px;margin-bottom:5px}
.dot{width:9px;height:9px;border-radius:50%;flex:none}
.ok{background:#4fd47f}.warn{background:#e8c645}
.bad{background:#e8564f;animation:p .9s infinite}
@keyframes p{50%{opacity:.25}}
.nm{font-weight:600;color:#fff;font-size:12px;line-height:1.2}
.sys{color:#35c8e8;font-size:9px;font-weight:400}
.st{font-size:9px;color:#e8c645}
.st.bad{color:#e8564f;background:none;animation:none}
.val{margin-left:auto;text-align:right;font-size:11px;color:#e8c645;font-weight:600;line-height:1.25}
.val small{display:block;font-size:9px;color:#5d6b80;font-weight:400}
.al{font-size:10px;border-radius:6px;padding:4px 8px;margin-top:4px;border:1px solid #1e2636;color:#5d6b80;background:#121722}
.al.pvp,.al.cargo,.al.drones{color:#e8564f;border-color:#e8564f;font-weight:600}
.al.depleted,.al.watch{color:#e8c645;border-color:#e8c645}
body.alarm{outline:3px solid #e8564f;outline-offset:-3px}`;

async function toggleOverlay(){
 if(pipWin){pipWin.close();pipWin=null;return;}
 if(!('documentPictureInPicture' in window)){
  alert('Das Mini-Overlay benötigt Chrome oder Edge (Document Picture-in-Picture).');return;}
 try{
  pipWin=await documentPictureInPicture.requestWindow({width:330,height:240});
 }catch(e){return;}
 const d=pipWin.document;
 const st=d.createElement('style');st.textContent=OV_CSS;d.head.appendChild(st);
 d.title='EVE Canary';
 d.body.innerHTML='<div id="ov"><div class="hd"><span>🐤 <b>CANARY</b></span></div></div>';
 pipWin.addEventListener('pagehide',()=>{pipWin=null;});
 overlayTick();
}
function mineIdle(c,st){
 return c.mine_idle&&st.idle_warn>0&&c.mine_idle>(c.idle_thr||st.idle_warn)&&c.mine_idle<1800;
}
function ovStatus(c,st){
 if(c.dps_in>0)return['bad','UNTER BESCHUSS'];
 if(c.cargo_full)return['bad','FRACHTRAUM VOLL'];
 const tw=c.tool_warns||[];
 const dr=tw.find(w=>w.drone);
 if(dr)return['bad','DROHNEN PRÜFEN ('+dr.tool+')'];
 if(tw.length)return['warn',tw[0].tool.toUpperCase()+(tw[0].count>1?' ×'+tw[0].count:'')+' AUS'];
 const lo=c.lasers_off||[];
 if(lo.length)return['warn',lo[0].tool.toUpperCase()+' AUS'];
 if(c.drones_idle)return['warn','DROHNEN OHNE ERZ'];
 if(c.laser_stalled)return['warn','LASER OHNE ERZ'];
 if(c.heavy_water&&c.heavy_water.on&&c.heavy_water.min_left<30)return['warn','HEAVY WATER ~'+c.heavy_water.min_left+' MIN'];
 if(c.rate_low)return['warn','ABBAURATE '+c.rate_low+'%'];
 if(mineIdle(c,st))return['warn','KEIN ERZ SEIT '+Math.round(c.mine_idle/60)+' MIN'];
 return['ok',''];
}
async function overlayTick(){
 if(!pipWin)return;
 try{
  const d=await (await fetch('/data?view=live')).json();
  const doc=pipWin.document, now=Date.now()/1000;
  doc.body.style.zoom={1:'1',2:'1.15',3:'1.3'}[fontsize]||'1';
  const alerts=(d.state.alerts||[]).filter(a=>now-a.ts<180).slice(-3).reverse();
  const hot=alerts.some(a=>(a.kind==='pvp'||a.kind==='cargo'||a.kind==='drones')&&now-a.ts<45);
  doc.body.classList.toggle('alarm',hot);
  doc.getElementById('ov').innerHTML=
   `<div class="hd"><span>🐤 <b>CANARY</b></span><span>${new Date().toLocaleTimeString()}</span></div>`+
   d.chars.map(c=>{const [cls,txt]=ovStatus(c,d.state);
    return `<div class="row"><span class="dot ${cls}"></span>
     <span><div class="nm">${esc(c.name)} <span class="sys">· ${esc(c.system)}</span></div>
     ${txt?`<div class="st ${cls==='bad'?'bad':''}">${txt}</div>`:''}</span>
     <span class="val">${fmtM(c.total_isk)}<small>${fmt(c.m3h)} m³/h</small></span></div>`;}).join('')+
   alerts.map(a=>`<div class="al ${a.kind}">[${new Date(a.ts*1000).toLocaleTimeString()}] ${esc(a.text)}</div>`).join('');
  // Das Overlay ist ein EIGENES Dokument, tr(document.body) erreicht es nicht.
  if(lang!=='de')tr(doc.body);
 }catch(e){}
}
setInterval(overlayTick,2000);
$('#ovToggle').onclick=toggleOverlay;
$('#ovBtn').onclick=toggleOverlay;

let intelNames=lsGet('intelNames',[]),intelSettled=false;
let intelBusy=false,intelAutoTs=Number(localStorage.getItem('intelAutoTs')||0);
function renderIntel(auto){
 if(!document.getElementById('intelBox')){
  $('#grid').innerHTML=`<div class="card" id="intelBox" style="grid-column:1/-1">
   <b>🚦 Bedrohungs-Ampel (Local-Scan)</b>
   <div style="font-size:12px;color:var(--dim);margin:6px 0">Im EVE-Local-Fenster in die Mitgliederliste klicken, dann <b>Strg+A</b> und <b>Strg+C</b>. Mit Auto-Scan reicht das schon, Canary erkennt die kopierte Liste von selbst.
   Alternativ hier einfügen und auf Scannen klicken. Quellen: zKillboard und ESI (öffentlich, ohne Login). Etwa ein Pilot pro Sekunde, Ergebnisse bleiben 12 Stunden gespeichert.</div>
   <label id="clipRow" style="font-size:12px;display:block;margin:6px 0"><input type="checkbox" id="clipWatch"> <b>Auto-Scan:</b> Zwischenablage überwachen. Strg+A/C im Local genügt, bei 🔴 gibt es Alarm auch ohne offenen Intel-Tab. <span style="color:var(--dim)">(Der Inhalt bleibt lokal, nur erkannte Pilotennamen werden bei ESI und zKillboard nachgeschlagen.)</span></label>
   <textarea id="intelIn" rows="5" style="width:100%" placeholder="Piloten-Namen einfügen …"></textarea>
   <div style="margin:8px 0"><button class="btn" id="intelGo">Scannen</button> <span id="intelStat" style="font-size:12px;color:var(--dim)"></span></div>
   <div id="intelTbl" style="overflow-x:auto"></div></div>`;
  $('#intelGo').onclick=()=>{
   intelNames=[...new Set($('#intelIn').value.split(/\\n/).map(s=>s.trim()).filter(s=>s&&!s.startsWith('[')))].slice(0,200);
   localStorage.setItem('intelNames',JSON.stringify(intelNames));
   intelSettled=false;
   $('#intelTbl').innerHTML='';
   intelPoll();
  };
  $('#clipWatch').checked=!!(state&&state.clip_watch);
  $('#clipWatch').onchange=()=>post({action:'clip_watch',on:$('#clipWatch').checked});
  // Zwischenablage-Auto-Scan gibt es nur unter Windows; sonst nur Einfügen von Hand
  if(state&&state.clip_ok===false){$('#clipRow').hidden=true;
   $('#intelIn').placeholder='Piloten-Namen einfügen … (Auto-Scan gibt es nur unter Windows)';}
  if(intelNames.length)$('#intelIn').value=intelNames.join('\\n');
 }
 if(auto&&auto.ts>intelAutoTs&&auto.names&&auto.names.length&&document.activeElement!==$('#intelIn')){
  // nicht überschreiben, während der Nutzer gerade im Feld tippt
  intelAutoTs=auto.ts;localStorage.setItem('intelAutoTs',intelAutoTs);
  intelNames=auto.names;
  localStorage.setItem('intelNames',JSON.stringify(intelNames));
  intelSettled=false;
  $('#intelIn').value=intelNames.join('\\n');
  $('#intelTbl').innerHTML='';
 }
 intelPoll();
}
async function intelPoll(){
 if(!intelNames.length||intelBusy||view!=='intel'||intelSettled)return;
 intelBusy=true;
 try{
  const r=await post({action:'threat_scan',names:intelNames});
  const res=r.results||{};
  // Fertig (nichts mehr offen)? Dann nicht mehr alle 2s neu abfragen/rendern,
  // sonst geht Textselektion und Link-Hover in der Tabelle laufend verloren.
  intelSettled=!r.pending;
  const order={red:0,yellow:1,unknown:2,green:3};
  const ICON={red:'🔴',yellow:'🟡',green:'🟢',unknown:'⚪'};
  const rows=intelNames.map(n=>[n,res[n]]).sort((a,b)=>{
   const ra=a[1]?(order[a[1].level]??2):4,rb=b[1]?(order[b[1].level]??2):4;
   return ra-rb||a[0].localeCompare(b[0]);});
  const cnt={red:0,yellow:0,green:0,unknown:0};
  rows.forEach(([n,d])=>{if(d&&cnt[d.level]!=null)cnt[d.level]++;});
  $('#intelStat').textContent=(r.pending?'prüfe … noch '+r.pending+' offen · ':'')+
   cnt.red+' rot · '+cnt.yellow+' gelb · '+cnt.green+' grün · '+cnt.unknown+' unbekannt';
  $('#intelTbl').innerHTML=`<table><tr><th></th><th>Pilot</th><th>Alter</th><th>Corp · Allianz</th>
   <th class="r">Kills 60d</th><th class="r">Miner-Kills</th><th class="r">Kills/Verluste</th>
   <th class="r">Danger</th><th class="r">Sec</th></tr>`+
   rows.map(([n,d])=>{
    if(!d)return '<tr><td>⏳</td><td>'+esc(n)+'</td><td colspan="7" style="color:var(--dim)">wird geprüft …</td></tr>';
    if(d.level==='unknown')return '<tr><td>⚪</td><td>'+esc(n)+'</td><td colspan="7" style="color:var(--dim)">'+esc(d.note||'')+'</td></tr>';
    const corp=esc((d.corp||'?')+(d.alliance?' · '+d.alliance:''));
    const age=d.age_days!=null?(d.age_days<365?d.age_days+' T':(d.age_days/365).toFixed(1)+' J'):'?';
    return `<tr class="lvl-${d.level}"><td>${ICON[d.level]}</td>
     <td><a href="https://zkillboard.com/character/${encodeURIComponent(d.id)}/" target="_blank" rel="noopener">${esc(n)}</a></td>
     <td>${age}</td><td>${corp}</td><td class="r">${d.recent_kills}</td>
     <td class="r${d.miner_kills>=3?' in':''}">${d.miner_kills}</td>
     <td class="r">${d.kills}/${d.losses}</td><td class="r">${d.danger}%</td>
     <td class="r">${d.sec}</td></tr>`;}).join('')+'</table>';
 }catch(e){}
 intelBusy=false;
}
function renderMissions(d){
 const m=d.missions||{},t=m.today||{};
 const live=(d.chars||[]).filter(c=>c.bounty>0||c.kills>0);
 const byDay={};(m.days||[]).forEach(x=>byDay[x.day]=x);
 const iso=n=>new Date(Date.now()-n*864e5).toISOString().slice(0,10);
 const y=byDay[iso(1)]||{};
 let wIsk=0,wMis=0;
 for(let n=0;n<7;n++){const x=byDay[iso(n)];if(x){wIsk+=x.total;wMis+=x.missions;}}
 $('#hero').innerHTML=heroTiles('🎯 Verdient heute',t.total||0,y.total||0,wIsk,
  (t.missions||0)+' Missionen',wMis+' Missionen · Ø '+fmtM(wIsk/7)+'/Tag');
 $('#grid').innerHTML=`
 <div class="card" style="grid-column:1/-1">
  <b>Heute im Detail (EVE-Zeit)</b>
  ${(m.asof||m.next)?(()=>{const now=Date.now()/1000;const p=['Aus dem Wallet-Journal (ESI)'];
    if(m.asof)p.push('Stand: vor '+Math.max(0,Math.round((now-m.asof)/60))+' min');
    if(m.next){const nx=Math.round((m.next-now)/60);p.push(nx>0?'nächster Abgleich in '+nx+' min':'Abgleich läuft gerade');}
    return `<div class="sub">${p.join(' · ')}. Das In-Game-Wallet ist sofort aktuell, ESI hängt bis zu 1 Stunde nach.</div>`;})():''}
  <div class="stats" style="margin-top:10px">
   <div class="stat"><div class="l">Missionen erledigt</div><div class="v out">${t.missions||0}</div></div>
   <div class="stat"><div class="l">Belohnungen</div><div class="v isk">${fmtM(t.reward||0)}</div></div>
   <div class="stat"><div class="l">Zeitboni</div><div class="v isk">${fmtM(t.bonus||0)}</div></div>
   <div class="stat"><div class="l">Bounties</div><div class="v grn">${fmtM(t.bounty||0)}</div></div>
  </div>
  ${(m.mine_systems&&m.mine_systems.length)?`<div class="sub" style="margin-top:8px">Bounties aus deinen Mining-Systemen (${m.mine_systems.join(', ')}) zählen hier nicht mit, das sind Belt-Ratten.</div>`:''}
  ${m.linked?'':'<div class="cardwarn" style="margin-top:10px">⚠ Kein EVE-Login verbunden. Belohnungen und Boni kommen aus dem Wallet-Journal (ESI), einzurichten unter ⚙ Optionen.</div>'}
  ${live.length?'<div class="sect">Live-Session (aus den Gamelogs)</div>'+live.map(c=>
   `<div class="sub">⚔ <b>${esc(c.name)}</b>${c.ship?' · '+esc(c.ship):''} · ${c.kills} Kills · ${fmtM(c.bounty)} Bounties · DPS ${c.dps_out} raus / ${c.dps_in} rein · Session ${c.session_min} min</div>`).join(''):''}
 </div>
 <div class="card" style="grid-column:1/-1">
  <div class="sect">Missionen einzeln (aus den Gamelogs)</div>
  ${(d.mission_log&&d.mission_log.length)?d.mission_log.map(x=>`
   <div style="border-top:1px solid var(--line);padding:10px 0">
    <div style="display:flex;flex-wrap:wrap;gap:6px;align-items:baseline">
     <b>${new Date(x.start*1000).toLocaleString().slice(0,16)}</b>
     <span class="sys">· ${x.min} min</span>
     <span style="margin-left:auto" class="isk"><b>${fmtM(x.total)} ISK</b></span>
    </div>
    <div class="sub">${x.kills} Kills · Bounty ${fmtM(x.bounty)} · Schaden ${fmt(x.dmg_out)} raus / ${fmt(x.dmg_in)} rein${x.hit!=null?' · Trefferquote '+x.hit+'%':''}${x.enemies.length?' · Top: '+esc(x.enemies[0][0]):''}</div>
    <div class="sub" style="margin-top:6px">${x.loot_isk!=null?'Loot: <b class="isk">'+fmtM(x.loot_isk)+'</b>':''}
     <span class="mloottoggle" data-mid="${esc(x.mid)}" style="cursor:pointer;color:var(--cyan);font-size:11px">${x.loot_isk!=null?'✎ Loot ändern':'＋ Loot eintragen'}</span></div>
    <div class="mlootedit" data-mid="${esc(x.mid)}" hidden>
     <textarea class="mlootin" data-mid="${esc(x.mid)}" rows="2" style="width:100%;margin-top:4px" placeholder="Frachtraum-Loot dieser Mission hier einfügen (im Spiel Strg+A, Strg+C)">${esc(x.loot_text)}</textarea>
     <div class="btnrow" style="margin-top:4px"><button class="btn mlootgo" data-mid="${esc(x.mid)}">Loot bewerten</button> <span class="mlootstat sub" data-mid="${esc(x.mid)}"></span></div>
    </div>
   </div>`).join(''):'<div class="sub">Noch keine abgeschlossenen Missionen erfasst. Eine Mission gilt als abgeschlossen, sobald du fürs nächste Mal wieder abdockst.</div>'}
 </div>
 <div class="card" style="grid-column:1/-1">
  <div class="sect">Letzte 30 Tage</div>
  ${(m.days&&m.days.length)?`<div style="overflow-x:auto"><table>
   <tr><th>Tag</th><th class="r">Missionen</th><th class="r">Belohnung</th><th class="r">Zeitbonus</th><th class="r">Bounties</th><th class="r">Gesamt</th></tr>`+
   m.days.map(x=>`<tr><td>${x.day}</td><td class="r">${x.missions}</td><td class="r isk">${fmtM(x.reward)}</td><td class="r isk">${fmtM(x.bonus)}</td><td class="r grn">${fmtM(x.bounty)}</td><td class="r isk"><b>${fmtM(x.total)}</b></td></tr>`).join('')+
   '</table></div>':'<div class="sub">Noch keine Journal-Daten. Nach dem ersten ESI-Abgleich (spätestens in einer Stunde) erscheinen hier die letzten 30 Tage.</div>'}
 </div>
 ${(m.foes&&m.foes.length)?`<div class="card" style="grid-column:1/-1">
  <div class="sect">Gegner (letzte 30 Tage)</div>
  <div style="overflow-x:auto"><table>
  <tr><th>Gegner</th><th class="r">Schaden ausgeteilt</th><th class="r">Schaden kassiert</th></tr>`+
  m.foes.map(f=>`<tr><td>${esc(f.name)}</td><td class="r out">${f.dealt?fmt(f.dealt):'&ndash;'}</td><td class="r in">${f.taken?fmt(f.taken):'&ndash;'}</td></tr>`).join('')+
  `</table></div>
  <div class="sub" style="margin-top:8px">Kommt direkt aus den Gamelogs. Belt-Ratten stehen hier mit drin, die lassen sich am Schaden nicht vom Missionsgegner trennen.</div>
 </div>`:''}
 ${(m.agents&&m.agents.length)?`<div class="card">
  <div class="sect">Top-Agenten</div><table>
  <tr><th>Agent</th><th class="r">Missionen</th><th class="r">ISK</th></tr>`+
  m.agents.map(a=>`<tr><td>${esc(a.agent)}</td><td class="r">${a.missions}</td><td class="r isk">${fmtM(a.isk)}</td></tr>`).join('')+'</table></div>':''}
 ${(m.chars&&m.chars.length)?`<div class="card">
  <div class="sect">Nach Charakter (gesamt)</div><table>
  <tr><th>Charakter</th><th class="r">Missionen</th><th class="r">ISK</th></tr>`+
  m.chars.map(c=>`<tr><td>${c.char}</td><td class="r">${c.missions}</td><td class="r isk">${fmtM(c.total)}</td></tr>`).join('')+'</table></div>':''}`;
 document.querySelectorAll('.mloottoggle').forEach(t=>t.onclick=()=>{
  const box=[...document.querySelectorAll('.mlootedit')].find(e=>e.dataset.mid===t.dataset.mid);
  if(box){box.hidden=!box.hidden; if(!box.hidden){const ta=box.querySelector('.mlootin'); if(ta)ta.focus();}}
 });
 document.querySelectorAll('.mlootgo').forEach(b=>b.onclick=async()=>{
  const mid=b.dataset.mid;
  const ta=[...document.querySelectorAll('.mlootin')].find(t=>t.dataset.mid===mid);
  const st=[...document.querySelectorAll('.mlootstat')].find(s=>s.dataset.mid===mid);
  st.textContent='Prüfe …';
  const r=await post({action:'mission_loot',mid,text:ta?ta.value:''});
  if(r&&r.ok){st.textContent='Loot: '+fmtM(r.isk)+(r.unknown&&r.unknown.length?' · nicht erkannt: '+r.unknown.join(', '):'');
   setTimeout(tick,600);}
  else st.textContent='Fehler';
 });
}
function renderRechner(){
 if(document.getElementById('calcBox'))return;
 $('#grid').innerHTML=`<div class="card" id="calcBox" style="grid-column:1/-1">
  <b>🧮 Ore Calculator</b>
  <div style="font-size:12px;color:var(--dim);margin:6px 0">Im Spiel den Frachtraum oder Container öffnen, alles markieren (Strg+A) und kopieren (Strg+C), dann hier einfügen.
  Einzelne Zeilen wie "Compressed Veldspar 50000" funktionieren genauso.</div>
  <textarea id="calcIn" rows="7" style="width:100%" placeholder="Compressed Veldspar	49.105&#10;Compressed Scordite	42.990"></textarea>
  <div style="margin:8px 0"><button class="btn" id="calcGo">Berechnen</button> <span id="calcStat" style="font-size:12px;color:var(--dim)"></span></div>
  <div id="calcOut" style="overflow-x:auto"></div></div>`;
 $('#calcGo').onclick=doCalc;
 const saved=localStorage.getItem('calcText');
 if(saved)$('#calcIn').value=saved;
}
async function doCalc(){
 const text=$('#calcIn').value;
 localStorage.setItem('calcText',text);
 $('#calcStat').textContent='Hole Preise von allen Handelsplätzen …';
 let r;
 try{r=await post({action:'calc',text});}catch(e){r=null;}
 if(!$('#calcOut'))return;  // Nutzer hat die Ansicht während der Abfrage gewechselt
 if(!r){$('#calcStat').textContent='Preisabfrage fehlgeschlagen.';return;}
 $('#calcStat').textContent='';
 if(!r.items||!r.items.length){
  $('#calcOut').innerHTML='<div class="sub">Keine bekannten Erz-Typen erkannt.'+(r.unknown&&r.unknown.length?' Nicht zuzuordnen: '+esc(r.unknown.join(' · ')):'')+'</div>';
  return;}
 const hubs=Object.values(r.hubs||{}).filter(h=>!h.error);
 if(!hubs.length){$('#calcOut').innerHTML='<div class="sub">Keine Preisdaten von den Handelsplätzen erhalten. Bitte später erneut versuchen.</div>';return;}
 const bestBuy=Math.max(...hubs.map(h=>h.buy));
 $('#calcOut').innerHTML=
  `<div class="stats" style="grid-template-columns:repeat(${hubs.length},1fr)">`+
  hubs.map(h=>`<div class="stat"${h.buy===bestBuy?' style="border-color:var(--gold)"':''}>
   <div class="l">${esc(h.name)}${h.buy===bestBuy?' ★':''}</div>
   <div class="v isk" style="font-size:20px">${fmtM(h.buy)}</div>
   <div class="l">Sofortverkauf · mit Sell-Order: ${fmtM(h.sell)}</div></div>`).join('')+`</div>
  <div class="sub" style="margin-top:8px">${fmt(r.m3)} m³ gesamt · ★ = bester Sofortverkauf · Einzelwerte zu Jita-Buy-Preisen:</div>
  <table><tr><th>Typ</th><th class="r">Menge</th><th class="r">m³</th><th class="r">ISK (Jita)</th></tr>`+
  r.items.map(i=>`<tr><td>${esc(i.name)}</td><td class="r">${fmt(i.qty)}</td><td class="r">${fmt(i.m3)}</td><td class="r isk">${fmtM(i.isk)}</td></tr>`).join('')+'</table>'+
  (r.unknown&&r.unknown.length?`<div class="sub" style="margin-top:8px">Nicht erkannt: ${esc(r.unknown.join(' · '))}</div>`:'');
}
// Ohne gültigen Log-Ordner zuerst einrichten, statt ein leeres Dashboard zu zeigen.
// Betrifft vor allem Linux: dort liegen die Logs im Wine-Präfix.
function renderSetup(){
 $('#hero').innerHTML='';$('#empty').hidden=true;$('#grid').innerHTML='';
 const box=$('#setup');box.hidden=false;
 if(box.dataset.built)return;   // nicht bei jedem Tick neu bauen, sonst kann niemand tippen
 box.dataset.built='1';
 box.innerHTML=`<div class="card" style="grid-column:1/-1">
  <b>📁 Log-Ordner einrichten</b>
  <div class="sub" style="margin:8px 0">Canary hat die EVE-Gamelogs nicht automatisch gefunden.
   Bitte den Ordner <b>Gamelogs</b> angeben, dann geht es weiter.</div>
  <div class="sub" style="margin:8px 0">Läuft EVE über <b>Steam/Proton</b>, liegt er im Wine-Präfix, etwa:<br>
   <code>~/.steam/steam/steamapps/compatdata/8500/pfx/drive_c/users/steamuser/Documents/EVE/logs/Gamelogs</code><br>
   Wichtig: bis einschließlich <b>Gamelogs</b>, nicht nur bis <code>logs</code>.</div>
  <div class="btnrow" style="margin-top:10px">
   <input id="setupDir" style="flex:1;min-width:280px" placeholder="Pfad zum Gamelogs-Ordner">
   <button class="btn" id="setupGo">Prüfen und übernehmen</button>
  </div>
  <div class="hint" id="setupStat" style="margin-top:8px"></div>
  <div class="sub" style="margin-top:12px">Im EVE-Client muss außerdem das Spielprotokoll aktiv sein:
   Esc &rarr; Einstellungen &rarr; „Spielprotokoll speichern".</div>
 </div>`;
 const go=async()=>{
  const st=$('#setupStat');st.textContent='Prüfe …';st.style.color='';
  const r=await post({action:'log_dir',path:$('#setupDir').value});
  st.textContent=r.msg||'';st.style.color=r.ok?'var(--green)':'var(--red)';
  if(r.ok){if(r.state)state=r.state;box.dataset.built='';box.hidden=true;box.innerHTML='';tick();}
 };
 $('#setupGo').onclick=go;
 $('#setupDir').onkeydown=e=>{if(e.key==='Enter')go();};
 if(state&&state.log_dir)$('#setupDir').value=state.log_dir;
 $('#setupDir').focus();
}
/* ---------------------------------------------------------------------------
   SPRACHE / LANGUAGE
   Der deutsche Text IST der Schluessel. Uebersetzt wird die FERTIGE Seite nach
   jedem Rendern, dadurch bleibt der restliche Code unberuehrt und eine fehlende
   Uebersetzung faellt automatisch auf Deutsch zurueck.
   Weitere Sprache: zweite Tabelle anlegen und in DICTS eintragen.
--------------------------------------------------------------------------- */
const EN = {
// Kopfleiste & Navigation
'Alle':'All','Alle Charaktere':'All characters','Alle einklappen':'Collapse all',
'Alle aufklappen':'Expand all','Charakter-Filter':'Character filter',
'Nur Mining-Charaktere':'Mining characters only','Nur Mission-Runner':'Mission runners only',
'Nur PvP-Charaktere':'PvP characters only','💤 Offline zeigen':'💤 Show offline',
'Standardmäßig zeigt Live nur eingeloggte Charaktere. Hier einschalten, um auch Offline-Charaktere zu sehen.':
 'Live normally shows only logged-in characters. Turn this on to see offline ones too.',
'Live':'Live','30 Tage':'30 days','Gesamt':'All time','Analyse':'Analysis',
'🚦 Intel':'🚦 Intel','🎯 Missionen':'🎯 Missions','🧮 Ore Calculator':'🧮 Ore calculator',
'⚙ Optionen':'⚙ Options','◱ Overlay':'◱ Overlay',
'◱ Mini-Overlay öffnen/schließen':'Open/close mini overlay',
'Sprache umschalten / switch language':'Sprache umschalten / switch language',
'Neue Version verfügbar, Klick installiert sie':'New version available, click to install',
// Hero-Leiste
'⛏ Geminert heute':'⛏ Mined today','🎯 Verdient heute':'🎯 Earned today',
'Gestern':'Yesterday','Letzte 7 Tage':'Last 7 days','Letzte 30 Tage':'Last 30 days',
'/Tag':'/day','aktive Tage':'active days','Bester Tag':'Best day',
// Charakterkarte
'ISK Trip':'ISK trip','ISK Session':'ISK session','Erz':'Ore','Erz gesamt':'Total ore',
'Erz-Wert':'Ore value','ISK gesamt':'Total ISK','Laderaum ≈':'Cargo ≈',
'Schaden raus/rein':'Damage out/in','DPS raus/rein':'DPS out/in',
'Kompression':'Compression','Komprimiert pro Charakter':'Compressed per character',
'Alles, was über die Schiffs-Kompression gelaufen ist':'Everything run through ship compression',
'Noch nichts komprimiert':'Nothing compressed yet','Pro Charakter':'Per character',
'Gesamt nach Typ':'Total by type','Menge':'Amount','Typ':'Type','Stk':'units',
'seit Abdocken':'since undocking','Asteroiden leergebaggert':'asteroids depleted',
'Asteroiden leergebaggert · Preise':'asteroids depleted · prices',
'per ⛽ setzen':'set via ⛽','Kern inaktiv, Verbrauch pausiert':'Core inactive, consumption paused',
'Bestand im Laderaum setzen':'Set amount in cargo hold','Spielzeit':'Played time',
'Waffen-Bilanz':'Weapon balance','Noch keine Kampfdaten':'No combat data yet',
'Nicht zuzuordnen':'Unassigned','Nicht erkannt':'Not recognised',
'Noch keine historischen Daten.':'No historical data yet.',
'Dieses Erz kennt Canary noch nicht, daher kein Wert. Bitte den Namen im Discord melden.':
 'Canary does not know this ore yet, so no value. Please report the name on Discord.',
'Für einzelne Erztypen fehlen Preisdaten':'Price data missing for some ore types',
'Noch nicht mit EVE-Login verbunden. Klick für Portrait, Schiff, Wallet und automatisches Heavy Water.':
 'Not linked to the EVE login yet. Click for portrait, ship, wallet and automatic Heavy Water.',
// Leere Zustände
'Gerade ist kein Charakter eingeloggt. Mit „💤 Offline zeigen" siehst du auch die abgemeldeten.':
 'No character is logged in right now. Use „💤 Show offline" to see the logged-out ones too.',
'Kein Charakter mit dieser Rolle. Tippe auf einer Karte auf das Rollen-Symbol, um sie zuzuweisen.':
 'No character with this role. Tap the role icon on a card to assign one.',
'Kein Ziel gesetzt. Unter ⚙ Optionen kannst du ein ISK-Ziel mit Prognose anlegen.':
 'No goal set. You can add an ISK goal with a forecast under ⚙ Options.',
// Startbildschirm
'Logdateien werden gelesen und analysiert …':'Reading and analysing log files …',
'Das passiert nur beim ersten Start. Je nach Log-Bestand kann es ein paar Minuten dauern, danach öffnet sich das Dashboard von selbst.':
 'This only happens on first start. Depending on how many logs you have it can take a few minutes, then the dashboard opens by itself.',
'Logdateien analysiert. Willkommen!':'log files analysed. Welcome!',
// Einrichtung Log-Ordner
'📁 Log-Ordner einrichten':'📁 Set up log folder',
'Canary hat die EVE-Gamelogs nicht automatisch gefunden. Bitte den Ordner':
 'Canary did not find the EVE game logs automatically. Please enter the folder',
'angeben, dann geht es weiter.':'and you are good to go.',
'Läuft EVE über':'If EVE runs through','liegt er im Wine-Präfix, etwa':'it sits in the Wine prefix, for example',
'Wichtig: bis einschließlich':'Important: include','nicht nur bis':'not just up to',
'Pfad zum Gamelogs-Ordner':'Path to the Gamelogs folder',
'Prüfen und übernehmen':'Check and apply','Prüfe …':'Checking …',
'Findet Canary die Logs nicht von selbst, hier den Ordner':'If Canary does not find the logs by itself, enter the folder',
'eintragen. Unter Linux liegt der im Wine-Präfix, bei Steam etwa':
 'here. On Linux it sits in the Wine prefix, with Steam for example',
'Übernehmen':'Apply','Log-Ordner':'Log folder',
// Optionen
'Schließen':'Close','Backup erstellen':'Create backup','🩺 Diagnose kopieren':'🩺 Copy diagnostics',
'Nach Update suchen':'Check for updates','Update installieren':'Install update',
'Alle vorhandenen Logs auswerten':'Evaluate all existing logs',
'Nur ab Installation zählen':'Count from installation onwards',
'Auswertung ab jetzt neu lesen':'Restart evaluation from now',
'Auswertung ab jetzt neu starten? Alte Daten bleiben gespeichert, werden aber ausgeblendet.':
 'Restart the evaluation from now? Old data stays stored but is hidden.',
'Baseline aufheben':'Clear baseline','Keine Baseline aktiv.':'No baseline active.',
'Aktive Baseline: zählt seit':'Active baseline: counting since',
'Desktop-Benachrichtigungen erlauben':'Allow desktop notifications',
'Sound bei Spieler-Angriff':'Sound on player attack',
'Sound bei leerem Asteroiden':'Sound on depleted asteroid',
'Sound bei Watchlist-Treffer':'Sound on watchlist hit',
'Watchlist speichern':'Save watchlist','Ziel speichern':'Save goal','Ziel löschen':'Clear goal',
'ISK-Ziel, z.B. 1000000000':'ISK goal, e.g. 1000000000','Ziel':'Goal',
'🎨 Darstellung':'🎨 Appearance','🔑 EVE-Account verbinden':'🔑 Connect EVE account',
'🔑 Mit EVE-Account verbinden':'🔑 Connect with EVE account',
'✨ Verbinde deinen EVE-Account, dann zeigt Canary automatisch Portrait, aktuelles Schiff, Wallet-Stand, Heavy Water und Missions-Einnahmen. Kein Setup nötig, einfach einloggen.':
 '✨ Connect your EVE account and Canary automatically shows portrait, current ship, wallet balance, Heavy Water and mission income. No setup needed, just log in.',
'Login konnte nicht gestartet werden.':'Could not start the login.',
'Installiert: EVE Canary v':'Installed: EVE Canary v','Neue Version verfügbar':'New version available',
'Update auf v':'Update to v','installieren? Canary startet danach automatisch neu.':
 '? Canary restarts automatically afterwards.',
'Update läuft …':'Update running …','Lade Update …':'Downloading update …',
'Update fehlgeschlagen.':'Update failed.','⬆ Update v':'⬆ Update v',
'In die Zwischenablage kopiert. Einfach an Askend schicken.':'Copied to the clipboard. Just send it to Askend.',
'Kopieren ging nicht, Text ist markiert: Strg+C drücken.':'Copying failed, the text is selected: press Ctrl+C.',
'Diagnose konnte nicht erstellt werden':'Could not create the diagnostics',
// Intel
'Im EVE-Local-Fenster in die Mitgliederliste klicken, dann':'Click the member list in the EVE local window, then',
'Piloten-Namen einfügen …':'Paste pilot names …','Scannen':'Scan',
'Zwischenablage überwachen. Strg+A/C im Local genügt, bei 🔴 gibt es Alarm auch ohne offenen Intel-Tab.':
 'Watch the clipboard. Ctrl+A/C in local is enough, 🔴 raises an alert even without the intel tab open.',
'Keine Spieler-Angriffe erkannt ✓':'No player attacks detected ✓',
'Bekannte Ganker...':'Known gankers...','Kills 60d':'Kills 60d','Kills/Verluste':'Kills/losses',
'Miner-Kills':'Miner kills','Sicherheit':'Security','Alter':'Age','Corp · Allianz':'Corp · alliance',
'Strg+A':'Ctrl+A','Strg+C':'Ctrl+C',
// Missionen
'Missionen erledigt':'Missions completed','Belohnungen':'Rewards','Zeitboni':'Time bonuses',
// Rechner
'Berechnen':'Calculate','Was lohnt sich am meisten pro Laderaum?':'What pays off most per cargo hold?',
'Sofortverkauf · mit Sell-Order':'Instant sale · with sell order',
'Hole Preise von allen Handelsplätzen …':'Fetching prices from all trade hubs …',
'Preisabfrage fehlgeschlagen.':'Price lookup failed.',
// Desktop-Meldungen
'EVE: SPIELER-ANGRIFF!':'EVE: PLAYER ATTACK!','EVE: Frachtraum voll!':'EVE: Cargo hold full!',
'EVE: Mining steht!':'EVE: Mining stopped!','EVE: Drohnen prüfen!':'EVE: Check drones!',
'EVE: Abbaurate gefallen!':'EVE: Mining rate dropped!','EVE: Bedrohung erkannt!':'EVE: Threat detected!',
'EVE: Heavy Water fast leer!':'EVE: Heavy Water almost empty!','EVE: Watchlist':'EVE: Watchlist',
'Speichern':'Save','nicht gefunden!':'not found!',
'Erz-Bilanz (nach Wert)':'Ore balance (by value)','Gegner (letzte 30 Tage)':'Enemies (last 30 days)',
'Klassisch (das gewohnte Canary-Design)':'Classic (the familiar Canary look)',
'Sekunden ohne Erz bis zur Stillstand-Warnung (0 = aus)':'Seconds without ore before the idle warning (0 = off)',
'🎯 Ziel & Zähler':'🎯 Goal & counters','7 Tage':'7 days','12 Monate':'12 months',
'Erz-Effizienz (ISK/m³)':'Ore efficiency (ISK/m³)','Waffen':'Weapons','und':'and',
'Schaden ausgeteilt':'Damage dealt','Schaden kassiert':'Damage taken',
'Top-Ziele':'Top targets','Top-Angreifer':'Top attackers',
'🤖 Drohnen ohne Erz':'🤖 Drones without ore',
'Komprimiert (Session)':'Compressed (session)','Rolle …':'Role …','Mining':'Mining',
'Watchlist (Local-Chat, ein Name pro Zeile)':'Watchlist (local chat, one name per line)',
'Spieler-Angriffe (gesamt)':'Player attacks (total)',
'Live-Session (aus den Gamelogs)':'Live session (from the game logs)',
// PvP/Missionen-Ansicht
'⛏ Mining':'⛏ Mining','⚔ PvP & Missionen':'⚔ PvP & missions','⚔ PvP':'⚔ PvP',
'⚔ Offense':'⚔ Offense','🛡 Defense':'🛡 Defense',
'Loot / Cargo':'Loot / cargo','Session gesamt':'Session total','Bounty':'Bounty',
'Schaden raus':'Damage out','Schaden rein':'Damage in','Trefferquote':'Hit rate',
'DPS rein':'DPS in','DPS raus':'DPS out',
'Kampfverlauf (Schaden/min)':'Combat over time (damage/min)','gleiche Skala':'same scale',
'▮ raus':'▮ out','▮ rein':'▮ in',
'Missionen einzeln (aus den Gamelogs)':'Missions individually (from the game logs)',
'Loot bewerten':'Value loot','noch nicht eingefügt':'not pasted yet',
'＋ Loot eintragen':'＋ Add loot','✎ Loot ändern':'✎ Edit loot',
'Frachtraum-Loot dieser Mission hier einfügen (im Spiel Strg+A, Strg+C)':"Paste this mission's cargo loot here (in game Ctrl+A, Ctrl+C)",
'Noch keine abgeschlossenen Missionen erfasst. Eine Mission gilt als abgeschlossen, sobald du fürs nächste Mal wieder abdockst.':'No completed missions recorded yet. A mission counts as complete once you undock again for the next one.',
'Gegner daneben':'Enemy misses','⚔ Bounty (Session)':'⚔ Bounty (session)',
'aus EVE-Login':'from EVE login','über EVE-Login':'via EVE login','Bounty + Loot':'Bounty + loot',
'Salvage':'Salvage','Kein Charakter mit dieser Rolle.':'No character with this role.',
'Rolle zuweisen (für die Filter oben)':'Assign role (for the filters above)',
'Heute':'Today','Heute im Detail (EVE-Zeit)':'Today in detail (EVE time)',
'Gegner':'Enemy','Missionen':'Missions',
'🚦 Bedrohungs-Ampel (Local-Scan)':'🚦 Threat traffic light (local scan)',
'🔔 Alarme & Wachen':'🔔 Alerts & watches','🖥 System & Daten':'🖥 System & data',
'. Mit Auto-Scan reicht das schon, Canary erkennt die kopierte Liste von selbst. Alternativ hier einfügen und auf Scannen klicken. Quellen: zKillboard und ESI (öffentlich, ohne Login). Etwa ein Pilot pro Sekunde, Ergebnisse bleiben 12 Stunden gespeichert.':
 '. With auto-scan that is already enough, Canary spots the copied list by itself. Alternatively paste it here and click Scan. Sources: zKillboard and ESI (public, no login). About one pilot per second, results are kept for 12 hours.',
'(Der Inhalt bleibt lokal, nur erkannte Pilotennamen werden bei ESI und zKillboard nachgeschlagen.)':
 '(The content stays local, only recognised pilot names are looked up at ESI and zKillboard.)',
'Kommt direkt aus den Gamelogs. Belt-Ratten stehen hier mit drin, die lassen sich am Schaden nicht vom Missionsgegner trennen.':
 'Comes straight from the game logs. Belt rats are included, damage alone cannot separate them from mission enemies.',
'Noch keine Journal-Daten. Nach dem ersten ESI-Abgleich (spätestens in einer Stunde) erscheinen hier die letzten 30 Tage.':
 'No journal data yet. After the first ESI sync (within an hour at the latest) the last 30 days appear here.',
'Im Spiel den Frachtraum oder Container öffnen, alles markieren (Strg+A) und kopieren (Strg+C), dann hier einfügen. Einzelne Zeilen wie "Compressed Veldspar 50000" funktionieren genauso.':
 'Open your cargo hold or a container in game, select everything (Ctrl+A) and copy (Ctrl+C), then paste it here. Single lines like "Compressed Veldspar 50000" work just as well.',
'Photon (angelehnt ans EVE-Interface: dunkel, kantig, Gold-Akzente)':
 'Photon (modelled on the EVE interface: dark, angular, gold accents)',
'Das Overlay ist ein schwebendes Always-on-top-Fenster mit Status und Alarmen, bleibt über dem EVE-Client (Fenstermodus/randlos). Benötigt Chrome oder Edge, Start nur per Klick.':
 'The overlay is a floating always-on-top window with status and alerts, staying above the EVE client (windowed or borderless). Needs Chrome or Edge, starts only by click.',
'Das Mini-Overlay benötigt Chrome oder Edge (Document Picture-in-Picture).':
 'The mini overlay needs Chrome or Edge (Document Picture-in-Picture).',
'Canary beim Systemstart automatisch mitstarten (still im Hintergrund, ohne Konsolenfenster)':
 'Start Canary automatically with the system (quietly in the background, no console window)',
'Rolle zuweisen (für die Filter oben)':'Assign role (for the filters above)',
'Schriftgröße (3 Stufen)':'Font size (3 steps)',
'Warte auf Gamelog-Daten … (EVE-Client an? Im Client „Spielprotokoll speichern" aktivieren.)':
 'Waiting for game log data … (Is the EVE client running? Enable „Log game to file" in the client.)',
'Heavy Water im Laderaum (Stück). Nach dem Nachfüllen einfach Enter drücken, 0 entfernt die Anzeige':
 'Heavy Water in the cargo hold (units). After refilling just press Enter, 0 removes the display',
'Piloten-Namen einfügen … (Auto-Scan gibt es nur unter Windows)':
 'Paste pilot names … (auto-scan is Windows only)',
'Always-on-top Mini-Overlay (Chrome/Edge)':'Always-on-top mini overlay (Chrome/Edge)',
'Open/Close Mini-Overlay':'Open/close mini overlay',
'🤖 Drohnen liefern gerade kein Erz (gestoppt, voll oder auf dem Rückweg).':
 '🤖 Drones are not delivering ore right now (stopped, full or on their way back).'
};
// Texte, die fest mit eingesetzten Zahlen verwachsen sind ("Erz (1.234 m³)") —
// die lassen sich nicht als ganzer Schluessel nachschlagen, daher als Muster.
// Bewusst OHNE Backslash geschrieben: Zeichenklassen wie [(] und [0-9] statt der
// ueblichen Kurzformen. PAGE ist ein normaler Python-String, dort waeren solche
// Escape-Sequenzen ungueltig und wuerden kuenftige Python-Versionen brechen.
const EN_PATTERNS = [
 [/^Erz [(]/, 'Ore ('], [/^Laderaum ≈/, 'Cargo ≈'],
 [/vs[.] gestern/, 'vs. yesterday'],
 [/aktive Tage/, 'active days'], [/Asteroiden leergebaggert/, 'asteroids depleted'],
 [/abgeschaltet, Drohnen prüfen!/, 'switched off, check drones!'],
 [/abgeschaltet, Ziel prüfen/, 'switched off, check target'],
 [/Seit ([0-9]+) Minuten kein Erz/, 'No ore for $1 minutes'],
 [/Kein Erz seit/, 'No ore for'],
 [/^Ziel: /, 'Goal: '], [/ Mrd/, ' bn'],
 [/ Stk/, ' units'], [/seit Abdocken/, 'since undocking'], [/Preise:/, 'Prices:'],
 [/Bewertung: aktuelle ([A-Za-z]+)-Preise/, 'valued at current $1 prices'],
 // Alarmtexte: die entstehen im Python-Teil und kommen fertig vom Server,
 // deshalb hier beim Anzeigen uebersetzen statt an der Quelle.
 [/Heavy Water fast leer, reicht noch etwa ([0-9]+) Minuten!/,
  'Heavy Water almost empty, about $1 minutes left!'],
 [/Laser und Drohnen prüfen!/, 'Check lasers and drones!'],
 // bewusst kurz gehalten: derselbe Satz steht als Alarm mit "!" und auf der
 // Karte mit "." am Ende — zwei lose Muster fangen beide Varianten.
 [/Abbaurate nur noch ([0-9]+)%/, 'Mining rate down to $1%'],
 [/Vermutlich ist ein Modul oder eine Drohne aus/, 'A module or a drone is probably off'],
 [/[/]Tag/, '/day'],
 [/Ø letzte 7 Tage:/, 'Ø last 7 days:'], [/Bester Tag:/, 'Best day:'],
 [/Seit ([0-9]+) min kein Erz/, 'No ore for $1 min'],
 [/DPS ([0-9]+) raus [/] ([0-9]+) rein/, 'DPS $1 out / $2 in'],
 // PvP/Missionen-Ansicht: Zeitstempel, Salvage, EWAR
 [/Stand: vor ([0-9]+) min/, 'As of $1 min ago'], [/nächste in ([0-9]+) min/, 'next in $1 min'],
 [/aus EVE-Login/, 'from EVE login'],
 [/Wird beim nächsten EVE-Login-Abgleich geladen/,
  'Loads at the next EVE login sync'], [/nach einem Umbau bis zu 1 Stunde/, 'up to 1 hour after a refit'],
 [/wird aktualisiert/, 'updating'],
 [/([0-9]+) Wracks geborgen/, '$1 wrecks salvaged'], [/([0-9]+) leer/, '$1 empty'],
 [/([0-9]+) Fehlversuch/, '$1 failed'], [/EWAR gegen dich:/, 'EWAR against you:'],
 [/gleiche Skala/, 'same scale'],
 [/Schaden ([0-9.]+) raus [/] ([0-9.]+) rein/, 'Damage $1 out / $2 in'],
 [/Trefferquote ([0-9]+)%/, 'Hit rate $1%'], [/([0-9]+) Kills/, '$1 kills'],
 [/Aus dem Wallet-Journal/, 'From the wallet journal'],
 [/nächster Abgleich in ([0-9]+) min/, 'next sync in $1 min'], [/Abgleich läuft gerade/, 'syncing now'],
 [/Das In-Game-Wallet ist sofort aktuell, ESI hängt bis zu 1 Stunde nach/,
  'The in-game wallet updates instantly, ESI lags up to 1 hour'],
 [/Log-Ordner:/, 'Log folder:'], [/Dateien:/, 'files:'], [/Installiert:/, 'Installed:'],
 [/: verbunden ·/, ': connected ·'], [/^trennen$/, 'disconnect'],
 [/Du hast die aktuellste Version/, 'You have the latest version'],
 [/prüfe … noch ([0-9]+) offen/, 'checking … $1 left'],
 [/ rot ·/, ' red ·'], [/ gelb ·/, ' yellow ·'], [/ grün ·/, ' green ·'],
 [/ unbekannt/, ' unknown'], [/Monate gesamt:/, 'months total:'],
 [/Bounties aus deinen Mining-Systemen/, 'Bounties from your mining systems'],
 [/zählen hier nicht mit, das sind Belt-Ratten/, 'are not counted here, those are belt rats'],
 [/ Missionen/, ' missions'], [/DROHNEN PRÜFEN/, 'CHECK DRONES'],
 [/[(]seit /, '(since '],
 // Overlay-Statustexte (eigenes Fenster, Grossschreibung)
 [/UNTER BESCHUSS/, 'UNDER FIRE'], [/FRACHTRAUM VOLL/, 'CARGO FULL'],
 [/DROHNEN OHNE ERZ/, 'DRONES WITHOUT ORE'], [/LASER OHNE ERZ/, 'LASER WITHOUT ORE'],
 [/ABBAURATE ([0-9]+)%/, 'MINING RATE $1%'], [/ AUS$/, ' OFF'],
 [/KEIN ERZ SEIT ([0-9]+) MIN/, 'NO ORE FOR $1 MIN'],
 [/bei aktueller Rate erreicht am/, 'reached at current rate on'],
 [/Frachtraum voll, Mining gestoppt!/, 'Cargo hold full, mining stopped!'],
 [/^SPIELER-ANGRIFF: /, 'PLAYER ATTACK: '], [/ schießt auf /, ' is shooting at '],
 [/^Watchlist: (.*) ist im Local aktiv!/, 'Watchlist: $1 is active in local!'],
];
const DICTS = {en:EN};
let lang = localStorage.getItem('uiLang');
if(!lang) lang = (navigator.language||'de').slice(0,2).toLowerCase()==='de' ? 'de' : 'en';
const ORIG = new WeakMap();          // Textknoten -> deutsches Original
// Uebersetzt einen Text oder gibt null zurueck, wenn nichts bekannt ist
function xlate(s){
 const dict = DICTS[lang]; if(!dict) return null;
 // Zeilenumbrueche und Mehrfach-Leerzeichen vereinheitlichen: im HTML stehen
 // laengere Saetze oft ueber mehrere Zeilen, sonst passt kein Schluessel darauf.
 const k = s.trim().replace(/\\s+/g, ' '); if(!k) return null;
 if(dict[k]){
  const vorn = s.match(/^\\s*/)[0], hinten = s.match(/\\s*$/)[0];
  return vorn + dict[k] + hinten;
 }
 if(lang === 'en'){
  // ALLE passenden Muster nacheinander anwenden, nicht beim ersten aufhoeren —
  // sonst bleibt der Rest eines Satzes deutsch stehen.
  let out = s, treffer = false;
  for(const [re, rep] of EN_PATTERNS) if(re.test(out)){ out = out.replace(re, rep); treffer = true; }
  if(treffer) return out;
 }
 return null;
}
function tr(root){
 const w = document.createTreeWalker(root, NodeFilter.SHOW_TEXT);
 const nodes = []; while(w.nextNode()) nodes.push(w.currentNode);
 for(const n of nodes){
  if(!ORIG.has(n)){
   if(lang === 'de' || xlate(n.nodeValue) === null) continue;   // nichts zu tun
   ORIG.set(n, n.nodeValue);
  }
  const orig = ORIG.get(n);
  const neu = (lang === 'de') ? null : xlate(orig);
  n.nodeValue = (neu === null) ? orig : neu;
 }
 for(const el of root.querySelectorAll('[title],[placeholder]')){
  for(const a of ['title','placeholder']){
   const cur = el.getAttribute(a); if(cur===null) continue;
   const key = 'o'+a;
   if(el.dataset[key]===undefined){
    if(lang === 'de' || xlate(cur) === null) continue;
    el.dataset[key] = cur;
   }
   const orig = el.dataset[key];
   const neu = (lang === 'de') ? null : xlate(orig);
   el.setAttribute(a, (neu === null) ? orig : neu);
  }
 }
}
function setLang(l){
 lang = l; try{ localStorage.setItem('uiLang', l); }catch(e){}
 // Aktive Sprache hervorheben. Eine einzelne Pille war missverstaendlich:
 // "EN" laesst sich als Zustand ODER als Ziel lesen.
 document.querySelectorAll('.langsel').forEach(b => b.classList.toggle('on', b.dataset.l === l));
 document.documentElement.lang = l;
 tr(document.body);
}
let tickBusy=false;
async function tick(){
 if(tickBusy)return;  // kein Request-Stau bei langsamem /data
 tickBusy=true;
 const reqView=view;  // View einfrieren: nach dem await zählt der Stand von JETZT
 try{
  const d=await (await fetch('/data?view='+reqView)).json();
  if(reqView!==view)return;  // Nutzer hat inzwischen gewechselt -> Antwort verwerfen
  state=d.state;regionPills();handleAlerts();updateBadge();bootScreen();
  if(state.log_ok===false){renderSetup();return;}
  if(!$('#setup').hidden){$('#setup').hidden=true;$('#setup').dataset.built='';}
  if(view!=='live'&&view!=='month'&&view!=='total'&&view!=='analyse')$('#empty').hidden=true;
  // Der Mining/PvP-Umschalter gehört nur zur Live-Ansicht
  document.querySelectorAll('.modesel').forEach(b=>b.hidden=view!=='live');
  if(view==='live'){lastChars=d.chars;lastSummary=d.summary;renderLiveView();}
  else if(view==='missionen')renderMissions(d);
  else{
   $('#hero').innerHTML='';
   if(view==='month')renderMonth(d.days);
   else if(view==='analyse')renderAnalyse(d.analyse);
   else if(view==='intel')renderIntel(d.intel_auto);
   else if(view==='rechner')renderRechner();
   else renderTotal(d.total);
  }
  if(lang!=='de')tr(document.body);   // frisch gerenderte Teile nachuebersetzen
 }catch(e){}
 finally{tickBusy=false;}
}
document.querySelectorAll('.langsel').forEach(b=>b.onclick=()=>{setLang(b.dataset.l);tick();});
setLang(lang);
tick();setInterval(tick,2000);
</script></body></html>"""


if __name__ == "__main__":
    try:
        # Zeilenweise ausgeben: bei umgeleiteter Ausgabe (Autostart, nohup,
        # Log-Datei) blieben Meldungen sonst im Puffer haengen.
        sys.stdout.reconfigure(line_buffering=True)
    except Exception:
        pass
    _log_ok, _log_n = log_dir_status()
    if not _log_ok:
        print("Hinweis: EVE-Gamelog-Ordner nicht gefunden."
              " Canary fragt beim Start im Browser danach.")
        if sys.platform.startswith("linux"):
            print("  Linux: EVE laeuft ueber Proton/Wine, der Ordner liegt im Praefix, z.B.")
            print("  ~/.steam/steam/steamapps/compatdata/8500/pfx/drive_c/users/"
                  "steamuser/Documents/EVE/logs/Gamelogs")
    else:
        print(f"Gamelog-Ordner: {CONFIG['log_dir']} ({_log_n} Logdateien)")
    if DB_PATH.exists():
        try:
            do_backup()
        except Exception:
            pass
    port = int(CONFIG.get("port", PORT_DEFAULT))

    class Server(ThreadingHTTPServer):
        # Windows: mit SO_REUSEADDR koennten mehrere Instanzen denselben Port
        # binden und sich gegenseitig die Anfragen wegschnappen. Deshalb aus.
        allow_reuse_address = False

    # Bis zu 12s auf den Port warten: nach einem Auto-Update startet der neue
    # Prozess evtl., bevor der alte den Socket (TIME_WAIT) freigegeben hat.
    srv = None
    for attempt in range(24):
        try:
            srv = Server(("127.0.0.1", port), Handler)
            break
        except OSError:
            time.sleep(0.5)
    if srv is None:
        print(f"EVE Canary läuft offenbar schon (Port {port} ist belegt).")
        print("Einfach das vorhandene Fenster nutzen: http://localhost:" + str(port))
        try:
            input("Enter zum Schließen ...")
        except EOFError:
            pass  # ohne Konsole (Autostart) einfach still beenden
        sys.exit(1)
    if DB_PATH.exists():
        try:
            do_backup()
        except Exception:
            pass
    rebuild_if_needed()   # nach Parser-Update einmal alle Logs frisch neu einlesen
    ingest.start()
    chatwatch.start()
    prices.start()
    esi.start()
    threat.start()
    clipwatch.start()
    print(f"EVE Canary läuft:  http://localhost:{port}")
    if "--no-browser" not in sys.argv:
        # Browser erst jetzt öffnen, wo der Port sicher gebunden ist
        try:
            import webbrowser
            threading.Timer(0.5, lambda: webbrowser.open(f"http://localhost:{port}")).start()
        except Exception:
            pass
    srv.serve_forever()
