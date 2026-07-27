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
import gzip
import hashlib
import json
import math
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

VERSION = "1.66.0"
UPDATE_FILES = ["eve_dashboard.py", "ore_types.json", "ore_refine.json",
                "eve_map.json",
                "mining_tools.json", "mission_sigs.json", "market_types.json",
                "README_INSTALL.md"]
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
    "CN-CHAT-02": "NPC-Funk aus aelteren Chatlogs nicht lesbar (Missionserkennung eingeschraenkt)",
    "CN-DB-01": "Datenbankfehler",
    "CN-NET-01": "Marktpreise nicht abrufbar",
    "CN-NET-02": "EVE-Serverstatus nicht abrufbar",
    "CN-NET-03": "System-Gefahrenlage nicht abrufbar",
    "CN-ESI-01": "ESI-Abfrage fehlgeschlagen",
    "CN-INTEL-01": "Bedrohungs-Abfrage fehlgeschlagen",
    "CN-CLIP-01": "Zwischenablage nicht lesbar",
    "CN-UPD-01": "Update fehlgeschlagen",
    "CN-CFG-01": "Einstellungen nicht speicherbar",
    "CN-SRV-01": "Interner Serverfehler",
}
ERRORS = deque(maxlen=60)
ERROR_SEEN = {}
ERROR_LOCK = threading.Lock()


def log_error(code, where, exc=None):
    """Fehler mit Code merken, damit er in der Diagnose auftaucht.
    Gleicher Code an gleicher Stelle wird gezaehlt statt 60x geloggt (sonst
    ueberschreibt ein Dauerfehler im 2s-Takt alles andere)."""
    if isinstance(exc, BaseException):
        loc = ""
        try:
            import traceback
            fr = traceback.extract_tb(exc.__traceback__)
            if fr:
                loc = f" @ {fr[-1].name}:{fr[-1].lineno}"
        except Exception:
            pass
        msg = f"{type(exc).__name__}: {exc}{loc}"
    else:
        msg = str(exc or "")
    key = (code, where, msg[:120])
    # Lock: log_error kommt aus vielen Threads; ohne Lock ist die Pruefung-dann-
    # Einfuegung nicht atomar (doppelte Eintraege / verlorene Zaehlung).
    with ERROR_LOCK:
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
# typeID -> (Name, Volumen je Einheit). Fuer das ESI Mining Ledger, das nur
# type_id + Stueckzahl liefert; so rechnen wir Einheiten in m³ um.
ORE_BY_TID = {v["typeID"]: (n, v.get("volume", 0.0)) for n, v in ORE_TYPES.items()}
# Refine-Ausbeute je Erz (Mineral-Mengen pro Batch, aus der SDE generiert, web-verifiziert):
# {"refine": {ore: {portion, out:[{tid,name,qty}]}}, "minerals": {name: tid}}
ORE_REFINE = load_json("ore_refine.json", {"refine": {}, "minerals": {}})
# Reprocessing-Skills: typeID -> Bonus je Stufe. Basis NPC-Station 50%.
REPROCESS_SKILLS = {3385: 0.03, 3389: 0.02}  # Reprocessing, Reprocessing Efficiency
MINING_TOOLS = sorted(load_json("mining_tools.json", []), key=len, reverse=True)
# Gruppen, die in Highsec regelmaessig Miner und Transporter abschiessen, aus
# oeffentlichen Killmails erhoben (Skript gank_groups.py, wird mitgeliefert und
# nicht bei jedem Nutzer gebaut). Struktur: {"stand", "zeitraum", "allianzen":
# {id: {name, miner, hauler, systeme}}, "corps": {...}}. Absichtlich NUR Zahlen
# und Namen, keine Wertung: die Oberflaeche schreibt "Achtung, N Miner-Kills".
GANK_GROUPS = load_json("gank_groups.json", {})


def gank_index(daten):
    """Nach Sicherheitsstufe getrennt: wer in Highsec minert, hat es mit
    anderen Gruppen zu tun als jemand in Lowsec. Welche Liste gilt, entscheidet
    der eigene Standort, nicht der Ort des Kills."""
    idx = {}
    for band in ("highsec", "lowsec"):
        d = daten.get(band) or {}
        idx[band] = ({int(k): v for k, v in (d.get("allianzen") or {}).items()},
                     {int(k): v for k, v in (d.get("corps") or {}).items()})
    return idx


GANK_IDX = gank_index(GANK_GROUPS)
# Missionserkennung über einzigartige Gegnernamen (nur geprüfte Signaturen).
MISSION_SIGS = {k.lower(): v for k, v in load_json("mission_sigs.json", {}).items()
                if not k.startswith("_")}
# Alle handelbaren Item-Namen -> typeID, fuer die Autovervollstaendigung der
# Marktpreis-Suche. Liegt als Datei bei; der Server haelt sie im Speicher und
# liefert nur die passenden Vorschlaege, damit die Oberflaeche leicht bleibt.
MARKET_TYPES = load_json("market_types.json", {})
# Vorsortiert nach Namenslaenge: kurze, exakte Treffer sollen oben stehen.
_MARKET_INDEX = sorted(((n.lower(), n) for n in MARKET_TYPES), key=lambda x: len(x[0]))


def market_suggest(q, limit=12):
    """Item-Namen-Vorschlaege zu einer Eingabe. Erst Namen, die mit der Eingabe
    beginnen, dann Namen, die sie enthalten. Gross-/Kleinschreibung egal."""
    q = (q or "").strip().lower()
    if len(q) < 2:
        return []
    starts, contains = [], []
    for low, name in _MARKET_INDEX:
        if low.startswith(q):
            starts.append(name)
            if len(starts) >= limit:
                break
        elif q in low and len(contains) < limit:
            contains.append(name)
    return (starts + contains)[:limit]


def detect_mission(enemies, dialogue=""):
    """Missionsname + Genauigkeit (%) aus Gegnernamen UND NPC-Funk (Local-Dialog).
    Der Funk ist die stärkere Quelle: er ist missions-spezifisch, kommt beim
    Reinwarpen und erkennt auch Missionen mit generischen Gegnern. Jede Signatur
    trägt eine Confidence; passt mehr als eine, gewinnt die mit der höchsten. Gibt
    {'name','conf'} oder None zurück (None = keine Mission erkannt)."""
    text = (" ".join(n for n, _ in (enemies or [])) + " " + (dialogue or "")).lower()
    best = None
    for sig, val in MISSION_SIGS.items():
        if sig and sig in text:
            name = val.get("m") if isinstance(val, dict) else val
            conf = int(val.get("c", 80)) if isinstance(val, dict) else 80
            if name and (best is None or conf > best["conf"]):
                best = {"name": name, "conf": conf}
    return best


# Fraktions-Erkennung aus den Gegnernamen: welchen Schaden du BEKOMMST (tanken)
# und welchen du am besten AUSTEILST (Schwaeche). Anders als der Missionsname
# funktioniert das fast immer, weil die Rat-Namen die Fraktion verraten, auch
# wenn Canary die Mission selbst nicht kennt. Quelle: EVE University Wiki
# "NPC damage types" (web-verifiziert 2026-07-25) und gegen die echten Kampflogs
# geprueft (Guristas Pith*, Blood Corp*, Angel Gist*, Serpentis Shadow*, Rogue
# Drone Alv*, Mordu's Legion, Federation Navy). Schadenscodes: em/therm/kin/exp.
# Reihenfolge: der erste Treffer je Gegner zaehlt, spezifische Praefixe zuerst.
FACTIONS = [
    ("Guristas",       ["pith", "guristas", "dread guri"],
     ["kin", "therm"], ["kin", "therm"], "jam"),
    ("Serpentis",      ["serpenti", "coreli", "corelum", "corelior", "coretus",
                        "coreatis", "shadow", "core admiral", "core lord",
                        "pleasure hub", "pleasure garden"],
     ["therm", "kin"], ["kin", "therm"], "damp"),
    ("Blood Raiders",  ["corpus", "corpii", "corpior", "corpum", "corpatis",
                        "corpse", "blood raider", "blood clone", "dark blood"],
     ["em", "therm"], ["em", "therm"], "neut"),
    ("Sansha",         ["sansha", "centii", "centus", "centior", "centum",
                        "centatis", "true sansha"],
     ["em", "therm"], ["em", "therm"], "td"),
    ("Angel Cartel",   ["gistii", "gistum", "gistatis", "gistior", "gist ",
                        "arch gist", "angel cartel", "domination"],
     ["exp", "kin"], ["exp", "kin"], "web"),
    ("Mordu's Legion", ["mordu"],
     ["kin", "therm"], ["kin", "em"], "scram"),
    ("Rogue Drones",   ["alvus", "alvi", "alvior", "alvum", "alvatis", "defeater",
                        "rogue drone"],
     ["therm", "em"], ["em", "therm"], None),
    ("Mercenaries",    ["mercenary"],
     ["therm", "kin"], ["kin", "therm"], "jam"),
    ("Federation Navy", ["federation navy", "roden shipyard", "federation ",
                         "gallente "],
     ["kin", "therm"], ["kin", "therm"], None),
    ("Caldari Navy",   ["caldari navy", "caldari state"],
     ["kin", "therm"], ["kin", "therm"], None),
    ("Amarr Navy",     ["amarr navy", "imperial "],
     ["em", "therm"], ["em", "therm"], None),
    ("Republic Fleet", ["republic fleet", "minmatar "],
     ["exp", "kin"], ["exp", "kin"], None),
    ("EoM",            ["equilibrium", "eom "],
     ["kin", "therm"], ["kin"], None),
]


def faction_info(enemies):
    """Aus einer Gegnerliste [(Name, Anzahl), …] die dominante Fraktion ableiten,
    inkl. Schaden-tanken/-schiessen und typischer EWAR. None, wenn kein Name auf
    eine bekannte Fraktion passt (dann lieber nichts anzeigen als falsch raten)."""
    scores = {}
    for name, cnt in (enemies or []):
        low = (name or "").lower()
        for fac, keys, _deal, _shoot, _ew in FACTIONS:
            if any(k in low for k in keys):
                scores[fac] = scores.get(fac, 0) + (cnt or 1)
                break
    if not scores:
        return None
    top = max(scores, key=scores.get)
    total = sum(scores.values()) or 1
    share = round(100 * scores[top] / total)
    if share < 50:            # zu gemischt fuer eine ehrliche Empfehlung
        return None
    prof = next(f for f in FACTIONS if f[0] == top)
    return {"fac": top, "deal": prof[2], "shoot": prof[3], "ewar": prof[4],
            "share": share}

REGIONS = {"10000002": "Jita", "10000043": "Amarr", "10000030": "Rens",
           "10000032": "Dodixie", "10000042": "Hek"}
# Handels-Systeme je Region: fuer den ESI-Orderbook-Preis filtern wir auf das
# eigentliche Hub-System, nicht die ganze Region (sonst zaehlen Randstationen mit).
HUB_SYSTEMS = {"10000002": 30000142,   # Jita
               "10000043": 30002187,   # Amarr
               "10000030": 30002510,   # Rens
               "10000032": 30002659,   # Dodixie
               "10000042": 30002053}   # Hek
PRICE_REFRESH = 900
ESI_PRICE_TTL = 300          # ESI cached Orders 5 min — so lange halten auch wir
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
# NBSP (\xa0) mit aufnehmen: manche Client-Sprachen (z.B. RU) nutzen ein
# geschuetztes Leerzeichen als Tausendertrenner — sonst wird "1<NBSP>234" zu "1".
NUM_RE = re.compile("([\\d][\\d.,\xa0 ]*)")
CHAR_FILE_RE = re.compile(r"^\d{8}_\d{6}_(\d+)\.txt$")
CHAT_LINE_RE = re.compile(r"^\[ [\d. :]+ \] ([^>]+?) > (.*)$")
CHAT_TS_RE = re.compile(r"^\[ (\d{4})\.(\d{2})\.(\d{2}) (\d{2}):(\d{2}):(\d{2}) \]")
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
# Reise-Zustaende: pausieren den Stillstand-Verlust (angedockt/unterwegs = kein Verlust).
DOCK_APPROACH_TEXTS = ["docking perimeter", "Andockperimeter", "Andock-Perimeter"]
WARP_TEXTS = ["Warp drive active", "Warpantrieb aktiv", " in warp", " im Warp"]
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
                 "undock": UNDOCK_TEXTS, "trade": TRADE_TEXTS,
                 "dock_approach": DOCK_APPROACH_TEXTS, "warp": WARP_TEXTS}

# Unerkannte notify-Meldungen sammeln. Bei Clients in anderen Sprachen als DE/EN
# fehlen die Muster oben — mit diesen Beispielen aus der Diagnose lassen sie sich
# exakt nachtragen, statt sie zu raten (geratene Muster greifen still nicht).
UNKNOWN_NOTIFY = deque(maxlen=80)
_UNKNOWN_SEEN = set()
# Wie oft die eingebauten Muster gegriffen haben. Stehen hier ueberall Nullen,
# ist die Client-Sprache noch nicht abgedeckt — das sieht man in der Diagnose
# sofort, ohne die Meldungen darunter lesen zu muessen.
LOG_TEXT_HITS = {"cargo_full": 0, "drone_unload": 0, "undock": 0, "trade": 0,
                 "dock_approach": 0, "warp": 0}


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
    return int(re.sub("[.,\xa0 ]", "", s) or 0)


def parse_line(raw):
    """Gamelog-Zeile -> Event-Dict oder None. Nur sprachunabhängige Signale."""
    m = TS_RE.match(raw.strip())
    if not m:
        return None
    y, mo, d, h, mi, s, tag, body = m.groups()
    # Eine halb geschriebene oder korrupte Zeile kann unmoegliche Werte liefern
    # (z.B. Monat 13, Stunde 25). datetime() wuerde ValueError werfen; das darf
    # die Zeile nur ueberspringen, nicht den Ingest-Thread auf ihr haengen lassen.
    try:
        ts = datetime(int(y), int(mo), int(d), int(h), int(mi), int(s),
                      tzinfo=timezone.utc).timestamp()
    except (ValueError, OverflowError):
        return None
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
        # Command Ship (Orca/Porpoise/Rorqual): das Log des Boosters nennt JEDEN
        # Flottenpiloten namentlich, der ueber den Kompressionsdienst komprimiert,
        # auch fremde Spieler. "FivaS compressed 1440 Plagioclase II-Grade using
        # your compression services." -> Flotten-Kompression je Pilot.
        mfc = re.search(r"^(.+?) compressed ([\d.,  ]+?) (.+?) using your compression services",
                        text)
        if not mfc:   # deutscher Client: "<Name> hat <N> <Erz> mithilfe Ihrer Kompressionsanlage komprimiert."
            mfc = re.search(r"^(.+?) hat ([\d.,  ]+?) (.+?) mithilfe .+? komprimiert", text)
        if mfc:
            raw = next((h for h in hints if not h.startswith("Compressed")), None) or mfc.group(3)
            return {**base, "kind": "fleet_compress",
                    "key": mfc.group(1).strip().rstrip("*").strip(),
                    "raw": raw.strip().rstrip("*").strip(),
                    "value": num(mfc.group(2))}
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
        # Reise-Zustaende (angedockt / im Warp) -> Stillstand-Verlust pausieren.
        if any(t in text for t in DOCK_APPROACH_TEXTS):
            LOG_TEXT_HITS["dock_approach"] += 1
            return {**base, "kind": "travel", "key": "dock", "value": 1}
        if any(t in text for t in WARP_TEXTS):
            LOG_TEXT_HITS["warp"] += 1
            return {**base, "kind": "travel", "key": "warp", "value": 1}
        note_unknown(text)
        return None
    elif tag == "None":
        text = STRIP_RE.sub("", body)
        if any(t in text for t in UNDOCK_TEXTS):
            LOG_TEXT_HITS["undock"] += 1
            # Zielsystem aus "Undocking from … to <System> solar system" bzw.
            # "Abdocken von … zum Sonnensystem <System>" mitnehmen (aktueller Ort).
            us = re.search(r"\bto ([^.]+?) solar system", text) \
                or re.search(r"Sonnensystem ([^.]+)", text)
            return {**base, "kind": "hold_reset", "key": "dock", "value": 1,
                    "system": us.group(1).strip() if us else None}
        # Sprung: "Jumping from X to Y" / "Springt von X nach Y" -> aktueller Ort = Y
        jm = re.search(r"Jumping from .+? to (.+)$", text) \
            or re.search(r"(?:Springt|Springe) von .+? nach (.+)$", text)
        if jm:
            return {**base, "kind": "jump", "key": jm.group(1).strip("* ."), "value": 1}
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
           "count_me": True, "ping": {},
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
        # Esi.poll mutiert Char-Dicts (wallet/ship/...) ohne CONFIG_LOCK; faellt
        # so ein Schreibzugriff mitten in json.dumps, wirft es RuntimeError
        # ("dictionary changed size during iteration"). Kurz erneut versuchen,
        # statt Einstellungen/Tokens still zu verlieren.
        data = None
        for _ in range(6):
            try:
                data = json.dumps(cfg or CONFIG, indent=1, ensure_ascii=False)
                break
            except RuntimeError:
                time.sleep(0.02)
        if data is None:
            log_error("CN-CFG-01", "save_config",
                      "Serialisierung fehlgeschlagen (nebenlaeufige Mutation)")
            return
        try:
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
# RLock (re-entrant): eine einzige SQLite-Verbindung fuer alle Threads. Jeder
# DB-Zugriff MUSS unter DB_LOCK laufen, sonst kollidieren gleichzeitige Abfragen
# (SQLITE_MISUSE "bad parameter or other API misuse"). Re-entrant, damit
# verschachtelte Helfer (all_rows -> baseline_filter -> meta_get) nicht verklemmen.
DB_LOCK = threading.RLock()
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
try:  # v1.21: NPC-Funk je Mission (fuer Erkennung + Anzeige)
    DB.execute("ALTER TABLE missions ADD COLUMN dialog TEXT")
    DB.commit()
except sqlite3.OperationalError:
    pass
try:  # v1.50: EWAR-Profil je Mission (Scram/Web/Jam/Neut … gegen dich)
    DB.execute("ALTER TABLE missions ADD COLUMN ewar TEXT")
    DB.commit()
except sqlite3.OperationalError:
    pass
# v1.54: Zeitachse/Verlauf. Schlanke Ereignis-Tabelle fuer Episoden, die sonst
# nirgends zeitgestempelt liegen: Mining-Trips und Bedrohungen. Kampf kommt aus
# missions, ISK aus journal (beide schon zeitgestempelt) und werden bei der
# Abfrage dazugemischt. detail = JSON mit den Feldern zum Rendern (i18n im Frontend).
DB.execute("""
CREATE TABLE IF NOT EXISTS events(char_id TEXT, ts REAL, kind TEXT, char TEXT,
    detail TEXT, UNIQUE(char_id, ts, kind));
""")
# v1.61: Blutspur-Radar. Roh-Kills der beobachteten Regionen (7 Tage Retention)
# sind die einzige Wahrheit; Rudel-Cluster werden beim Start daraus deterministisch
# neu gerechnet. pack_map = System-Stammdaten (Name, Sec, Position, Gate-Kanten,
# einmalig aus ESI, resumefaehig). pack_archive = 14-Tage-Wiedererkennung.
DB.execute("""CREATE TABLE IF NOT EXISTS pack_kills(
    kill_id INTEGER PRIMARY KEY, ts REAL, system_id INTEGER, region TEXT,
    score INTEGER, victim_ship INTEGER, value REAL, attackers TEXT,
    sim INTEGER DEFAULT 0)""")
DB.execute("""CREATE TABLE IF NOT EXISTS pack_map(
    system_id INTEGER PRIMARY KEY, region TEXT, name TEXT, sec REAL,
    x REAL, z REAL, gates TEXT)""")
DB.execute("""CREATE TABLE IF NOT EXISTS pack_archive(
    pack_id TEXT PRIMARY KEY, first_ts REAL, last_ts REAL, label TEXT,
    members TEXT, corps TEXT, score REAL)""")
DB.commit()


def meta_get(key, default=None):
    with DB_LOCK:
        r = DB.execute("SELECT value FROM meta WHERE key=?", (key,)).fetchone()
    return r[0] if r else default


# Parser-Version: hochzaehlen, wenn eine Parser-Aenderung ein Neu-Einlesen aller
# Logs noetig macht. "2" = englischer Client (Mining/Kompr. ohne hint) wird erfasst.
# "3" = Gegnernamen im Kampflog des englischen Clients (standen vorher alle als "?")
# "4" = Missions-Historie an Undock-Grenzen rueckwirkend aus allen Logs aufbauen
# "5" = Missionsort aus dem Gamelog (Undock-Ziel/Sprung) rueckwirkend nachtragen
# "6" = EWAR-Profil je Mission rueckwirkend aus allen Logs mitschreiben
# "7" = Mining-Trip-Episoden (Verlauf/Zeitachse) der letzten 48h aus Logs rekonstruieren
PARSE_VER = "7"


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


def log_event(char_id, char, kind, detail, ts=None):
    """Ein Zeitachsen-Ereignis ablegen (Mining-Trip, Bedrohung). detail = dict,
    wird als JSON gespeichert und im Frontend sprachabhaengig gerendert. Dedupe
    ueber UNIQUE(char_id, ts, kind), damit ein Re-Ingest nichts doppelt."""
    try:
        with DB_LOCK:
            DB.execute("INSERT OR IGNORE INTO events VALUES(?,?,?,?,?)",
                       (str(char_id), float(ts or time.time()), kind, char,
                        json.dumps(detail, ensure_ascii=False)))
            DB.commit()
    except Exception as e:
        log_error("CN-DB-01", "log_event", e)


def save_mission(m):
    """Abgeschlossene Mission speichern (mid=char:start). Bei erneutem Einlesen
    werden die Kampf- und Ort-Felder aktualisiert, der vom Nutzer eingefügte
    LOOT bleibt aber erhalten (nicht in der ON-CONFLICT-Aktualisierung)."""
    mid = f"{m['char_id']}:{int(m['start_ts'])}"
    DB.execute("""INSERT INTO missions
        (mid,char_id,char,start_ts,end_ts,system,dmg_out,dmg_in,kills,bounty,
         hits,miss_out,miss_in,weapons,enemies,loot_isk,loot_text,dialog,ewar)
        VALUES(?,?,?,?,?,?,?,?,?,?,?,?,?,?,?,?,?,?,?)
        ON CONFLICT(mid) DO UPDATE SET
         char=excluded.char, end_ts=excluded.end_ts, system=excluded.system,
         dmg_out=excluded.dmg_out, dmg_in=excluded.dmg_in, kills=excluded.kills,
         bounty=excluded.bounty, hits=excluded.hits, miss_out=excluded.miss_out,
         miss_in=excluded.miss_in, weapons=excluded.weapons, enemies=excluded.enemies,
         dialog=COALESCE(excluded.dialog, missions.dialog), ewar=excluded.ewar""",
        (mid, m["char_id"], m["char"], m["start_ts"], m["end_ts"], m["system"],
         m["dmg_out"], m["dmg_in"], m["kills"], m["bounty"], m["hits"],
         m["miss_out"], m["miss_in"], json.dumps(m["weapons"], ensure_ascii=False),
         json.dumps(m["enemies"], ensure_ascii=False), None, None, m.get("dialog"),
         json.dumps(m.get("ewar") or [], ensure_ascii=False)))


def do_backup():
    BACKUP_DIR.mkdir(exist_ok=True)
    name = f"dashboard_{datetime.now().strftime('%Y%m%d_%H%M%S')}.db"
    with DB_LOCK:
        DB.commit()
        # WAL-Modus: frisch geschriebene Zeilen stehen evtl. nur im -wal. Erst in
        # die Haupt-DB schreiben (TRUNCATE), sonst enthaelt die Kopie einen
        # veralteten Stand. Ist WAL aus, ist das ein No-op.
        try:
            DB.execute("PRAGMA wal_checkpoint(TRUNCATE)")
        except Exception:
            pass
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
    """Regelmaessig nach einer neuen Version schauen. 15 min ist praktisch das
    Minimum, weil raw.githubusercontent die version.json ~5 min cached; haeufiger
    zu fragen bringt nichts. Beim ersten Lauf (ts=0) wird sofort geprueft."""
    if time.time() - UPDATE_INFO["ts"] < 15 * 60:
        return
    UPDATE_INFO["ts"] = time.time()
    chk = check_update()
    if chk.get("ok"):
        UPDATE_INFO["available"] = bool(chk.get("available"))
        UPDATE_INFO["latest"] = chk.get("latest")


# --------------------------------------------- Installations-Zaehlung
PING_REPO = "Eve-Online-Askend/eve-canary"
PING_STATE = {"ts": 0.0}


def count_ping():
    """Zaehlt Installationen, ohne irgendetwas zu senden.

    Einmal pro UTC-Tag und einmal pro Monat wird eine winzige Datei vom
    GitHub-Release geholt, deren NAME den Zeitraum traegt (ping-2026-07.json).
    Uebertragen wird dabei nichts: keine Kennung, keine Version, keine
    Spieldaten. Es ist derselbe Vorgang wie der Update-Check. Gezaehlt wird
    allein bei GitHub, naemlich wie oft die Datei ausgeliefert wurde.

    Der Trick: weil jede Installation eine bestimmte Zeitraum-Datei hoechstens
    EINMAL holt, ist deren Download-Zaehler exakt die Zahl der Installationen,
    die in dem Zeitraum liefen. Keine Schaetzung, kein Hochrechnen, und der
    Wert steht ohne Zwischenspeicher direkt in der GitHub-API.

    Abschaltbar in den Optionen (count_me).
    """
    if not CONFIG.get("count_me", True):
        return
    if time.time() - PING_STATE["ts"] < 600:
        return
    PING_STATE["ts"] = time.time()
    now = time.gmtime()
    for kind, stamp in (("month", time.strftime("%Y-%m", now)),
                        ("day", time.strftime("%Y-%m-%d", now))):
        if (CONFIG.get("ping") or {}).get(kind) == stamp:
            continue
        try:
            # Monatsmarken haengen am Jahres-Release (stats-2026), Tagesmarken am
            # Monats-Release (stats-2026-07). So bleibt jedes Release klein genug,
            # dass die Homepage die Zaehler mit EINEM Aufruf lesen kann.
            tag = "stats-" + (stamp[:4] if len(stamp) == 7 else stamp[:7])
            fetch_url(f"https://github.com/{PING_REPO}/releases/download/"
                      f"{tag}/ping-{stamp}.json", timeout=20)
        except urllib.error.HTTPError as e:
            if e.code != 404:
                log_error("CN-UPD-01", f"count_ping({kind})", e)
                continue
            # Fuer diesen Zeitraum wurde keine Zaehldatei angelegt. Dann gilt er
            # als erledigt, sonst klopft die Installation den ganzen Tag dagegen.
        except Exception as e:
            log_error("CN-UPD-01", f"count_ping({kind})", e)
            continue
        with CONFIG_LOCK:
            p = dict(CONFIG.get("ping") or {})
            p[kind] = stamp
            CONFIG["ping"] = p
            save_config()


GANK_STATE = {"ts": 0.0}


def refresh_gank_list():
    """Die Gank-Gruppen-Liste einmal im Monat frisch von GitHub holen.

    Die Liste ist DATEN, kein Code: so bekommen auch Nutzer, die gerade kein
    Update einspielen, die aktuellen Zahlen. Erhoben wird sie zentral (siehe
    gank_groups.py), niemals hier, sonst wuerde jede Installation zKillboard
    hunderte Male abfragen."""
    global GANK_GROUPS, GANK_IDX
    if time.time() - GANK_STATE["ts"] < 3600:
        return
    GANK_STATE["ts"] = time.time()
    stamp = time.strftime("%Y-%m", time.gmtime())
    if CONFIG.get("gank_stamp") == stamp:
        return
    base = (CONFIG.get("update_url") or "").rstrip("/")
    if not base.startswith("https://"):
        return
    try:
        neu = json.loads(fetch_url(f"{base}/gank_groups.json", timeout=30).decode("utf-8"))
        # Nur uebernehmen, wenn es plausibel aussieht: eine kaputte oder leere
        # Antwort darf die mitgelieferte Liste nicht ueberschreiben.
        if not isinstance(neu.get("highsec"), dict) or not neu["highsec"].get("allianzen"):
            raise ValueError("unbrauchbare Liste")
        (APP_DIR / "gank_groups.json").write_text(
            json.dumps(neu, ensure_ascii=False, indent=1), encoding="utf-8")
        GANK_GROUPS = neu
        GANK_IDX = gank_index(neu)
    except urllib.error.HTTPError as e:
        if e.code != 404:                  # 404 = noch keine Liste veroeffentlicht,
            log_error("CN-UPD-01", "refresh_gank_list", e)   # das ist kein Fehler
        return
    except Exception as e:
        log_error("CN-UPD-01", "refresh_gank_list", e)
        return
    with CONFIG_LOCK:
        CONFIG["gank_stamp"] = stamp
        save_config()


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
        # Command-Ship-Booster: Pilotname -> {Erz: Einheiten}, die ueber den
        # Kompressionsdienst dieses Schiffs liefen (auch fremde Flottenmitglieder).
        self.fleet_compress = {}
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
        self.lost_m3 = 0.0        # in dieser Session durch Stillstand/Drosselung entgangenes Erz-Volumen
        self._lost_ts = None      # letzter Verrechnungs-Zeitpunkt des Verlustzaehlers
        self.traveling = None     # ts des letzten Dock-/Warp-Signals -> Verlust pausiert
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
        self.system = None            # aktueller Ort aus dem Gamelog (Undock/Sprung)
        self.mission_system = None    # Ort, an dem der Missionskampf begann
        self.rate_min = deque(maxlen=180)  # [Minute, {Erz: m3}] — fuer Sparkline + Raten-Waechter

    def feed(self, ev, live):
        now = time.time()
        if self.first_ts is None or ev["ts"] < self.first_ts:
            self.first_ts = ev["ts"]
        if self.last_event_ts is None or ev["ts"] > self.last_event_ts:
            self.last_event_ts = ev["ts"]
        k = ev["kind"]
        if k == "travel":
            # Angedockt oder im Warp: kein aktives Minen -> Verlustzaehler pausieren.
            self.traveling = ev["ts"]
            return
        if k == "ore":
            self.cargo_full = False
            self.traveling = None   # es kommt Erz -> wieder aktiv am Guertel
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
        elif k == "jump":
            self.system = ev["key"]      # aktueller Ort aus dem Gamelog
        elif k == "dmg_out":
            self.dmg_out += ev["value"]
            self.hits_out += 1
            if self.mission_system is None:   # Ort des ersten Kampfes = Missionsort
                self.mission_system = self.system
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
        elif k == "fleet_compress":
            d = self.fleet_compress.setdefault(ev["key"], {})
            d[ev["raw"]] = d.get(ev["raw"], 0) + ev["value"]
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
            self.traveling = None    # Undock/Trade -> Reise-Zustand zuruecksetzen
            if ev["key"] == "dock":
                # Station-Stopp: Karte beginnt einen neuen Trip, sonst zeigen
                # ISK/Erz-Werte laengst abgeladene Ladung an. Historie (DB)
                # bleibt davon unberuehrt.
                self.trips += 1
                self.mining = {}
                self.compressed = {}
                self.fleet_compress = {}
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
                self.mission_system = None
                self.depleted = 0
                self.lost_m3 = 0.0       # Stillstand-Verlust je Trip neu zaehlen
                self._lost_ts = None
                self.start = time.time()
                self.first_ts = ev["ts"]
                if ev.get("system"):     # Ziel des Undocks = aktueller Ort
                    self.system = ev["system"]
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
            if ev["ts"] - e[1] > 60:
                e[0] = 0  # alter Vorfall abgelaufen -> neu zaehlen (wie bei depleted)
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
        # Harte Mindestschwelle von 90 auf 60 s gesenkt (schnellere Meldung bei
        # engen Drohnenzyklen); der adaptive p90+30 schuetzt lange Rueckfluege.
        return max(60, p90 + 30) < now - self.drone_last < 1800

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

    def mission_dict(self, end_ts):
        """Die gerade abgeschlossene Mission als Datensatz — oder None, wenn
        seit dem letzten Undock kein Kampf stattfand (z.B. reiner Mining-Trip).
        Ort = wo der Kampf begann (aus dem Gamelog, zuverlaessig)."""
        if not (self.bounty or self.kills or self.dmg_out):
            return None
        return {"char_id": self.char_id, "char": self.name,
                "start_ts": self.first_ts or end_ts, "end_ts": end_ts,
                "system": self.mission_system or self.system or "?",
                "dmg_out": self.dmg_out, "dmg_in": self.dmg_in, "kills": self.kills,
                "bounty": self.bounty, "hits": self.hits_out,
                "miss_out": self.miss_out, "miss_in": self.miss_in,
                "weapons": sorted(self.weapons.items(), key=lambda x: -x[1])[:6],
                # Bis 30 Gegner speichern (statt 8): in L4s dominieren Strukturen
                # den Schaden, die fraktionsverratenden Rat-Schiffe stehen weiter
                # unten. Fuer die Fraktions-Erkennung in der Historie noetig.
                "enemies": sorted(self.targets.items(), key=lambda x: -x[1])[:30],
                "ewar": sorted(self.ewar.items(), key=lambda x: -x[1])}


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
                count_ping()
                refresh_gank_list()
            except Exception as e:
                log_error("CN-LOG-05", "Ingest.run", e)
            time.sleep(2)

    def hw_tick(self):
        """Schweres-Wasser-Buchhaltung: Verbrauch seit letztem Checkpoint abziehen,
        Stand in der Config sichern (uebersteht Neustarts), bei <30 min warnen."""
        now = time.time()
        with self.lock:
            by_name = {s.name: s for s in self.sessions.values()}
        # Die Eintraege werden hier mutiert UND parallel von do_POST/sync_ship
        # geschrieben. Deshalb die ganze Runde inkl. save_config unter CONFIG_LOCK
        # (RLock, save_config nimmt es reentrant erneut) — sonst zerreisst ein
        # paralleler json.dumps(CONFIG) oder ueberschreibt einen Wert.
        with CONFIG_LOCK:
            hw = CONFIG.get("heavy_water") or {}
            if not hw:
                return
            changed = False
            for char, e in list(hw.items()):
                if now - e.get("ck", 0) < 60:
                    continue
                e["ck"] = now
                s = by_name.get(char)
                if s is None:
                    continue
                rate = HW_RATE.get(e.get("core"), HW_RATE["t1"])
                active = s.core_active_since(e.get("ts", now))
                if active > 0:
                    e["units"] = max(0.0, e.get("units", 0.0) - active * rate)
                    e["ts"] = now
                    changed = True
                if (s.core_on() and not e.get("warned")
                        and e.get("units", 0.0) < rate * 1800):
                    e["warned"] = True
                    changed = True
                    mins = int(e.get("units", 0.0) / rate / 60)
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
                # Verlustzaehler ZUERST, unabhaengig von Alarm-Schwelle und
                # idle_alerted: gerade beim langen Stillstand soll er weiterlaufen.
                rs = s.rate_status()
                if s._lost_ts is None:
                    s._lost_ts = now
                dt = now - s._lost_ts
                s._lost_ts = now
                # Nur zaehlen, solange der Char plausibel am Guertel ist: Erz kam
                # in den letzten 3 min. Danach ist er vermutlich im Warp, angedockt
                # oder AFK -> das ist kein "Verlust" und wird nicht mitgezaehlt.
                at_belt = (s.last_ore_ts is not None and (now - s.last_ore_ts) < 180
                           and not s.traveling)   # nicht angedockt / nicht im Warp
                if rs and at_belt and 0 < dt < 20:   # dt-Sanitaet: kein Riesensprung
                    base, cur = rs
                    # nur echten Ausfall zaehlen (unter 85% der Normalrate), kein
                    # Rauschen. (base-cur) = fehlende m³/min, mal Intervall in Minuten.
                    if base > 0 and cur < 0.85 * base:
                        s.lost_m3 += (base - cur) * (dt / 60.0)
                if thr <= 0:
                    continue
                # Command Ships / Booster (Orca/Porpoise/Rorqual oder laufender
                # Industriekern) minen nicht selbst -> KEINE Mining-Stillstand- oder
                # Raten-Alarme, wie schon in der Charakter-Karte.
                if _is_booster(s):
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
            with DB_LOCK:
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
                lost_done = []       # beim Undock festgehaltener Stillstand-Verlust (Tag, ISK)
                mine_done = []       # Mining-Trip-Episoden fuer die Zeitachse (char_id, char, ts, detail)
                with open(f, "rb") as fh:
                    fh.seek(offset)
                    data = fh.read()
                cut = data.rfind(b"\n")
                if cut < 0:
                    done += 1
                    continue
                new_offset = offset + cut + 1
                now = time.time()
                mined_now = False   # Mining-System erst NACH Freigabe der Locks lernen
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
                                    md = sess.mission_dict(ev["ts"])
                                    if md:
                                        md["dialog"] = " ".join(chatwatch.dialogue(
                                            cid, md["start_ts"], ev["ts"]))[:2000] or None
                                        missions_done.append(md)
                                    # Trip-Mining festhalten, BEVOR feed() sess.mining leert
                                    # (beim Andocken haelt sess.mining genau diesen Trip).
                                    if sess.lost_m3 > 0:
                                        pm = prices.get(CONFIG["region"]) or {}
                                        vm3 = visk = 0.0
                                        for ore, u in sess.mining.items():
                                            i, vv = ore_value(ore, u, pm)
                                            visk += i
                                            vm3 += vv
                                        li = round(sess.lost_m3 * (visk / vm3)) if vm3 > 0 else 0
                                        if li > 0:
                                            lost_done.append((ev["day"], li))
                                    # Mining-Trip als Zeitachsen-Episode. m³ ist statisch
                                    # (Volumen, keine Preise noetig), ISK wird bei der Abfrage
                                    # mit aktuellen Preisen berechnet -> robust auch beim
                                    # Re-Ingest (Preise evtl. noch nicht geladen). Bis 48h
                                    # zurueck rekonstruieren, dedupe ueber UNIQUE.
                                    if now - ev["ts"] < 172800 and sess.mining:
                                        m3 = sum(u * ORE_TYPES.get(o, {}).get("volume", 0.0)
                                                 for o, u in sess.mining.items())
                                        if m3 > 0:
                                            top_ore = max(sess.mining, key=sess.mining.get)
                                            mins = max(1, round((ev["ts"] - (sess.first_ts or ev["ts"])) / 60))
                                            mine_done.append((sess.char_id, cname, ev["ts"],
                                                              {"ores": dict(sess.mining), "m3": round(m3),
                                                               "min": mins, "top": top_ore,
                                                               "sys": sess.system or "?"}))
                                sess.feed(ev, live=not catch_up)
                            # Live-Alarme nur für wirklich frische Ereignisse (< 10 min).
                            # Schaltet man später auf "alle Logs", werden sonst Jahre an
                            # historischen PvP-Treffern als Alarm + zKill-Abfrage ausgelöst.
                            if not catch_up and now - ev["ts"] < 600:
                                self.live_alerts(ev, cname)
                                if ev["kind"] == "ore":
                                    mined_now = True
                with DB_LOCK:
                    try:
                        for ev in batch:
                            if ev["kind"] in ("drone_engage", "hold_reset", "travel"):
                                continue  # reine Live-Signale, nicht historisieren
                            db_add(ev["day"], cid, cname, ev["kind"], ev["key"], ev["value"])
                            if ev["kind"] == "dmg_out" and "weapon" in ev:
                                db_add(ev["day"], cid, cname, "weapon", ev["weapon"], ev["value"])
                            if ev["kind"] == "dmg_in" and ev.get("player"):
                                db_add(ev["day"], cid, cname, "pvp_in", ev["key"], ev["value"])
                        for md in missions_done:
                            save_mission(md)
                        for lday, li in lost_done:
                            db_add(lday, cid, cname, "lost", "isk", li)
                        for ecid, ename, ets, edet in mine_done:
                            log_event(ecid, ename, "mine", edet, ets)
                        if batch:
                            ts = [ev["ts"] for ev in batch]
                            first_ts = min(first_ts or ts[0], *ts)
                            last_ts = max(last_ts or ts[0], *ts)
                            DB.execute("UPDATE files SET first_ts=?, last_ts=? WHERE name=?",
                                       (first_ts, last_ts, f.name))
                    except Exception as e:
                        # Historisierung fehlgeschlagen: das Offset TROTZDEM
                        # fortschreiben. Die Live-Session wurde oben bereits
                        # gefuettert; ein erneutes Einlesen derselben Zeilen wuerde
                        # die Mining-/Kampfwerte doppelt zaehlen.
                        log_error("CN-DB-01", "Ingest.tick historize", e)
                    DB.execute("UPDATE files SET offset=? WHERE name=?", (new_offset, f.name))
                    DB.commit()
                # Ausserhalb self.lock UND DB_LOCK: learn_mine_system macht Disk-I/O
                # (save_config); unter self.lock wuerde es HTTP-Snapshots blockieren.
                if mined_now:
                    self.learn_mine_system(cid)
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
        with CONFIG_LOCK:
            ms = CONFIG.setdefault("mine_systems", {})
            if sysname in ms:
                return
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
        self.npc = {}          # char_id -> deque[(ts, text)] NPC-/Missions-Funk (Absender "Message")
        self.offsets = {}      # file -> offset
        self.started_full = False
        # Jeder Local-Sprecher (name_lower -> {name, system, ts}), rollend, fuer die
        # passive Gank-Flotten-Erkennung (mehrere geflaggte Piloten derselben Corp).
        self.speakers = {}
        self.fleet_alerted = {}   # corp_lower -> letzter Alarm-Zeitpunkt (Cooldown)
        # Schuetzt self.npc: dialogue() (HTTP-/Ingest-Thread) liest, waehrend
        # tick()/backfill() (Chat-Thread) anhaengen -> sonst "deque mutated".
        self.lock = threading.Lock()

    def dialogue(self, cid, t0, t1=None):
        """NPC-Funk eines Zeitfensters als Liste von Texten (fuer Missionserkennung
        und Anzeige)."""
        with self.lock:
            items = list(self.npc.get(cid, ()))   # unter Lock kopieren, dann filtern
        return [txt for ts, txt in items
                if ts >= (t0 or 0) and (t1 is None or ts <= t1)]

    def chat_dir(self):
        if not CONFIG["log_dir"]:
            return None
        return Path(CONFIG["log_dir"]).parent / "Chatlogs"

    def _npc_line(self, line):
        """(cid-los) NPC-Text einer Local-Zeile oder None. Zieht den Zeitstempel
        aus der Zeile, damit auch nachtraeglich eingelesene Dateien stimmen."""
        cm = CHAT_LINE_RE.match(line)
        if not cm or cm.group(1).strip() != "Message":
            return None
        tm = CHAT_TS_RE.match(line)
        try:
            ts = (datetime(*(int(x) for x in tm.groups()),
                           tzinfo=timezone.utc).timestamp() if tm else time.time())
        except Exception:
            ts = time.time()
        return ts, cm.group(2).strip()

    def backfill(self):
        """Einmalig beim Start: NPC-/Missions-Funk aus ALLEN jüngeren Local-Dateien
        einlesen, nicht nur der neuesten. Eine Session kann in mehreren Dateien
        liegen; der Funk einer Vormittagsmission steht sonst in einer Datei, die
        der Live-Tail (nur die neueste) nie sieht. Danach werden die Offsets ans
        Dateiende gesetzt, damit die Live-Schleife nichts doppelt zählt."""
        d = self.chat_dir()
        if not d or not d.exists():
            return
        files = list(d.glob("Local_*.txt")) + list(d.glob("Lokal_*.txt"))
        # Nur die letzten Tage, sonst wächst der Speicher unnötig.
        files = [f for f in files if (time.time() - f.stat().st_mtime) < 3 * 86400]
        for f in sorted(files, key=lambda p: p.stat().st_mtime):   # alt -> neu
            m = re.search(r"_(\d+)\.txt$", f.name)
            if not m:
                continue
            cid = m.group(1)
            try:
                data = f.read_bytes()
            except Exception:
                continue
            usable = len(data) & ~1
            for line in data[:usable].decode("utf-16-le", "replace").splitlines():
                line = line.strip().lstrip("﻿").strip()
                cm = CHAT_LINE_RE.match(line)
                if not cm:
                    continue
                sender, msg = cm.group(1).strip(), cm.group(2).strip()
                if "EVE" in sender and ":" in msg:
                    self.systems[cid] = msg.rsplit(":", 1)[1].strip().rstrip("*")
                elif sender == "Message":
                    n = self._npc_line(line)
                    if n:
                        with self.lock:
                            self.npc.setdefault(cid, deque(maxlen=400)).append(n)
            self.offsets[f] = usable   # Live-Schleife setzt hier auf

    def run(self):
        try:
            self.backfill()
        except Exception as e:
            log_error("CN-CHAT-02", "ChatWatch.backfill", e)
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
                    elif sender == "Message":
                        # NPC-/Missions-Funk (kein Pilot!) — fuer die Missionserkennung
                        tm = CHAT_TS_RE.match(line)
                        try:
                            ts = (datetime(*(int(x) for x in tm.groups()),
                                           tzinfo=timezone.utc).timestamp() if tm else time.time())
                        except Exception:
                            ts = time.time()
                        with self.lock:
                            self.npc.setdefault(cid, deque(maxlen=400)).append((ts, msg))
                    elif self.started_full:
                        if watch and sender.lower() in watch:
                            alerts.push("watch", sender,
                                        f"Watchlist: {sender} ist im Local aktiv!")
                        # Jeden Local-Sprecher still einstufen; Alarm nur bei Rot
                        threat.request([sender], alert="red")
                        # Fuer die Gank-Flotten-Erkennung merken, WO und WANN er sprach.
                        self.speakers[sender.lower()] = {
                            "name": sender, "system": self.systems.get(cid, "?"),
                            "ts": time.time()}
            except OSError:
                pass
        self._fleet_watch()

    def _recent_hostiles(self, window=900):
        """Kuerzlich aktive Local-Sprecher, die zKill/ESI als geflaggt kennt, mit
        Corp/Level/System. Rein passiv aus den Chat-Nachrichten, kein Local-Kopieren."""
        now = time.time()
        # Alte Sprecher ausduennen, damit die Struktur nicht waechst.
        self.speakers = {k: v for k, v in self.speakers.items() if now - v["ts"] < window}
        out = []
        for v in self.speakers.values():
            prof = threat.cached(v["name"])            # zKill/ESI-Profil (gecacht)
            if not prof or prof.get("level") not in ("red", "yellow"):
                continue
            out.append({"name": v["name"], "system": v["system"],
                        "corp": prof.get("corp"), "alliance": prof.get("alliance"),
                        "level": prof.get("level"), "miner": prof.get("miner_kills", 0)})
        return out

    def fleet_groups(self):
        """Geflaggte Local-Sprecher nach Corp gruppieren. Eine Gruppe gilt als
        moegliche Gank-Flotte, wenn >=2 verschiedene geflaggte Piloten derselben
        Corp aktiv sind UND mindestens einer rot ist oder zusammen >=3 Miner-Kills."""
        groups = {}
        for h in self._recent_hostiles():
            key = (h["corp"] or "").lower()
            if not key:
                continue
            g = groups.setdefault(key, {"corp": h["corp"], "alliance": h["alliance"],
                                        "pilots": {}, "systems": set(), "miner": 0,
                                        "red": False})
            if h["name"] not in g["pilots"]:
                g["pilots"][h["name"]] = h["level"]
                g["miner"] += h["miner"] or 0
            g["systems"].add(h["system"])
            if h["level"] == "red":
                g["red"] = True
        out = []
        for g in groups.values():
            if len(g["pilots"]) >= 2 and (g["red"] or g["miner"] >= 3):
                out.append({"corp": g["corp"], "alliance": g["alliance"],
                            "pilots": sorted(g["pilots"]), "n": len(g["pilots"]),
                            "systems": sorted(s for s in g["systems"] if s and s != "?"),
                            "miner": g["miner"], "red": g["red"]})
        out.sort(key=lambda x: (-int(x["red"]), -x["n"]))
        return out

    def _fleet_watch(self):
        """Bei erkannter Gank-Flotte einen Alarm ausloesen (Cooldown je Corp)."""
        now = time.time()
        for g in self.fleet_groups():
            k = (g["corp"] or "").lower()
            if now - self.fleet_alerted.get(k, 0) < 600:   # max. 1 Alarm/10 min je Corp
                continue
            self.fleet_alerted[k] = now
            alerts.push("fleet", g["corp"],
                        f"🚨 Mögliche Gank-Flotte im Local: {g['n']} geflaggte Piloten "
                        f"von {g['corp']}, {g['miner']} Miner-Kills.")


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
        with DB_LOCK:
            rows = DB.execute("SELECT DISTINCT key FROM daily WHERE kind IN ('ore','compressed')").fetchall()
        for (ore,) in rows:
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
                    # Erz-Bewertung bevorzugt das frische CCP-Orderbuch (ESI), faellt
                    # aber je Typ auf Fuzzwork zurueck. hub_prices liefert (buy, sell);
                    # fuer die Mining-Anzeige zaehlt der Verkaufserloes = Buy-Preis.
                    pm = hub_prices(region, ids, prefer_esi=True)
                    self.cache[region] = {int(t): float(b) for t, (b, s) in pm.items()}
                    self.fetched[region] = time.time()
                    self.requested[region] = set(ids)
                except Exception as e:
                    log_error("CN-NET-01", f"Prices.run(region={region})", e)
                    self.fetched[region] = time.time() - PRICE_REFRESH + 60
                    # Auch bei Fehlschlag als "angefragt" merken: sonst bleibt
                    # new_ids gefuellt und der 60s-Backoff (ueber 'due') wird bei
                    # neuen Erzsorten umgangen -> Retry-Sturm alle 3s.
                    self.requested[region] = set(ids)
            time.sleep(3)


class ServerStatus(threading.Thread):
    """Status des EVE-Servers (Tranquility) vom oeffentlichen ESI-Endpunkt.
    Braucht keinen Login. Liefert Spielerzahl, ob VIP-Modus (Wartung) laeuft und
    seit wann der Server online ist."""
    daemon = True

    def __init__(self):
        super().__init__()
        self.state = {}        # players, vip, start_time, ok, checked
        self.err = 0

    def run(self):
        while True:
            try:
                req = urllib.request.Request(
                    "https://esi.evetech.net/latest/status/",
                    headers={"User-Agent": ESI_UA, "Accept": "application/json"})
                with urllib.request.urlopen(req, timeout=15) as r:
                    d = json.load(r)
                self.state = {"players": d.get("players"),
                              "vip": bool(d.get("vip")),
                              "start_time": d.get("start_time"),
                              "ok": True, "checked": time.time()}
                self.err = 0
                wait = 60          # normal alle 60 s
            except Exception as e:
                # Server offline/Downtime: kurze Zeit ist das normal (taegliche
                # Downtime ~11:00 EVE-Zeit), erst danach als Fehler melden.
                self.err += 1
                self.state = {"players": None, "vip": False, "start_time": None,
                              "ok": False, "checked": time.time()}
                if self.err == 3:
                    log_error("CN-NET-02", "ServerStatus.run", e)
                wait = 30          # bei Ausfall haeufiger nachsehen
            time.sleep(wait)


class SystemDanger(threading.Thread):
    """Lagebild je Sonnensystem aus OEFFENTLICHEN Daten: Schiffs-/Pod-/NPC-Kills
    und Sprungverkehr der letzten Stunde plus Sicherheitsstatus. Kein Login, kein
    Local-Kopieren. CCP aktualisiert diese Zahlen nur STUENDLICH — das ist ein
    Lagebild, keine Sekundenwarnung."""
    daemon = True

    def __init__(self):
        super().__init__()
        self.kills = {}    # system_id -> (ship, npc, pod)
        self.jumps = {}    # system_id -> ship_jumps
        self.sec = {}      # system_id -> security_status
        self.ids = {}      # name.lower() -> system_id
        self.want = set()  # noch aufzuloesende Systemnamen (aus den Logs)
        self.fetched = 0

    def for_system(self, name):
        """Gefahrenlage zu einem Systemnamen. Unbekannte Namen werden fuer den
        naechsten Zyklus zum Aufloesen vorgemerkt und liefern erstmal None."""
        if not name:
            return None
        sid = self.ids.get(name.lower())
        if not sid:
            self.want.add(name)
            return None
        k = self.kills.get(sid, (0, 0, 0))
        return {"sec": self.sec.get(sid), "ship_kills": k[0], "npc_kills": k[1],
                "pod_kills": k[2], "jumps": self.jumps.get(sid, 0),
                "checked": int(self.fetched)}

    def _pub(self, path):
        req = urllib.request.Request(ESI_BASE + path, headers={"User-Agent": ESI_UA})
        with urllib.request.urlopen(req, timeout=20) as r:
            return json.loads(r.read())

    def tick(self):
        # 1) offene Systemnamen (aus den Logs) zu IDs aufloesen + Sicherheitsstatus
        todo = [n for n in list(self.want) if n.lower() not in self.ids]
        if todo:
            try:
                req = urllib.request.Request(
                    ESI_BASE + "/universe/ids/", data=json.dumps(todo[:100]).encode(),
                    headers={"Content-Type": "application/json", "User-Agent": ESI_UA})
                with urllib.request.urlopen(req, timeout=20) as r:
                    data = json.loads(r.read())
                for s in data.get("systems", []):
                    self.ids[s["name"].lower()] = s["id"]
                    try:
                        info = self._pub(f"/universe/systems/{s['id']}/")
                        self.sec[s["id"]] = round(info.get("security_status", 0), 1)
                    except Exception:
                        pass
            except Exception:
                pass
        # 2) Kills + Verkehr sind stuendlich — hoechstens alle ~55 min neu holen
        if time.time() - self.fetched > 3300:
            k = {r["system_id"]: (r.get("ship_kills", 0), r.get("npc_kills", 0),
                                  r.get("pod_kills", 0)) for r in self._pub("/universe/system_kills/")}
            j = {r["system_id"]: r.get("ship_jumps", 0) for r in self._pub("/universe/system_jumps/")}
            self.kills, self.jumps, self.fetched = k, j, time.time()

    def run(self):
        time.sleep(8)
        while True:
            try:
                self.tick()
            except Exception as e:
                log_error("CN-NET-03", "SystemDanger.tick", e)
            time.sleep(120)   # Namen schnell aufloesen; Kills bleiben stuendlich


# ---------------------------------------------------------------- ESI (offizielles EVE-SSO, PKCE)
SSO_AUTH = "https://login.eveonline.com/v2/oauth/authorize"
SSO_TOKEN = "https://login.eveonline.com/v2/oauth/token"
ESI_BASE = "https://esi.evetech.net/latest"
ESI_SCOPES = ("esi-assets.read_assets.v1 esi-location.read_ship_type.v1 "
              "esi-wallet.read_character_wallet.v1 esi-location.read_online.v1 "
              "esi-ui.open_window.v1 esi-skills.read_skills.v1 "
              "esi-industry.read_character_mining.v1 esi-planets.manage_planets.v1")
# Mining-Skills, die den Erzertrag heben (typeID -> Ertrag je Stufe).
# Mining und Astrogeology sind die beiden Kern-Ertragsskills (+5% je Stufe).
MINING_YIELD_SKILLS = {3386: 0.05,   # Mining
                       3410: 0.05}   # Astrogeology
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


def _is_booster(s):
    """True, wenn dieser Char ein Command Ship (Orca/Porpoise/Rorqual per ESI)
    fliegt ODER einen Industriekern laufen hat. Solche Booster/Kompressoren minen
    nicht selbst nennenswert -> keine Mining-Stillstand-/Raten-Alarme (wie in der
    Karte). core_on() deckt Nutzer ohne ESI ab."""
    c = (CONFIG.get("esi") or {}).get("chars", {}).get(s.name) or {}
    if c.get("ship_type_id") in DRONE_ONLY_SHIP_IDS:
        return True
    if any(n in (c.get("ship") or "") for n in DRONE_ONLY_SHIP_NAMES):
        return True
    return s.core_on()


# Planetary Industry: Produkt-Tier aus der group_id des Typs (web-verifiziert).
# P1=1042, P2=1034, P3=1040, P4=1041; alle Rohstoff-Gruppen (1032/1033/1035, …) = P0.
PI_GROUP_TIER = {1042: "P1", 1034: "P2", 1040: "P3", 1041: "P4"}


def extractor_total(install, expiry, cycle, qty):
    """Gesamt-Extraktion eines Extractor-Programms ueber die ganze Laufzeit.
    Exakt nach der offiziellen EVE-Formel (developers.eveonline.com, PI-Guide):
    abklingender Grundwert mal Rausch-Oszillation. Liefert die erwartete
    Gesamtmenge in Einheiten (das, was der Client beim Programmieren anzeigt)."""
    if not (install and expiry and cycle and qty) or expiry <= install:
        return 0
    decay, noise = 0.012, 0.8
    bar_width = cycle / 900.0
    total = 0
    for c in range(int((expiry - install) // cycle)):
        t = (c + 0.5) * bar_width
        decay_value = qty / (1 + t * decay)
        ph = pow(qty, 0.7)
        s = max((math.cos(ph + t * (1 / 12.0)) + math.cos(ph / 2 + t * 0.2)
                 + math.cos(t * 0.5)) / 3, 0)
        total += int(bar_width * (decay_value * (1 + noise * s)))
    return total


class Esi(threading.Thread):
    """EVE-SSO-Login (PKCE, ohne Client-Secret) + periodischer Abgleich:
    Schweres Wasser im aktuellen Schiff, Kern-Typ aus der Fitting, Wallet."""
    daemon = True

    def __init__(self):
        super().__init__()
        self.pending = {}     # state -> code_verifier laufender Logins
        self.status = {}      # char -> Klartext-Status fuer die Optionen-Seite
        self.type_cache = {}  # type_id -> Name (Schiffstypen, öffentlicher Endpunkt)
        self.vol_cache = {}   # type_id -> Volumen je Einheit (fuer Mining-Ledger-m³)
        self.loc_cache = {}   # location_id -> Name (Stationen/Strukturen, fuer die Erz-Schatzkammer)
        self.planet_cache = {} # planet_id -> Name (Planetary Industry, langlebig)
        self.sys_cache = {}   # system_id -> Name (fuer Planeten-Kolonien)
        self.schem_cache = {} # schematic_id -> Produktname (PI-Fabriken)
        self.group_cache = {} # type_id -> group_id (fuer den PI-Tier)
        self.tid_cache = {}   # Produktname -> type_id (fuer Icon/Tier der Fabrik-Produkte)
        self.pi_alerted = {}  # (char, planet_id) -> Ablauf-ts, fuer den PI-Ablauf-Alarm ohne Wiederholung
        self.party_names = {} # id -> Name (Agenten aus dem Wallet-Journal)
        # Serialisiert den Token-Refresh: poll-Thread und HTTP-Thread (ui_open)
        # duerfen nicht gleichzeitig dasselbe Refresh-Token einloesen (CCP
        # invalidiert es beim ersten Gebrauch -> der zweite bekommt 400).
        self.token_lock = threading.Lock()

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
            with CONFIG_LOCK:
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

    def token_scopes(self, c):
        """Erteilte Scopes aus dem Access-Token (JWT-scp-Claim) lesen. So sehen
        wir, ob ein Char alle noetigen Berechtigungen hat oder neu verbunden
        werden muss (z.B. weil ein Scope nach seiner Verbindung dazukam)."""
        try:
            seg = (c.get("access") or "").split(".")[1]
            d = json.loads(base64.urlsafe_b64decode(seg + "==="))
            scp = d.get("scp")
            return set(scp) if isinstance(scp, list) else set((scp or "").split())
        except Exception:
            return set()

    def char_health(self, name, c):
        """ESI-Gesundheit eines Chars: verbunden UND alle Scopes erteilt -> ok.
        'missing' listet fehlende Scopes (Kurzform) fuer den Tooltip."""
        req = set(ESI_SCOPES.split())
        gr = self.token_scopes(c)
        return {"ok": self.status.get(name) == "verbunden" and req <= gr,
                "missing": sorted(s.split(".")[0].replace("esi-", "") for s in (req - gr))}

    def _access(self, c):
        if time.time() < c.get("exp", 0) and c.get("access"):
            return c["access"]
        with self.token_lock:
            # Double-Check: waehrend des Wartens hat evtl. ein anderer Thread schon
            # erneuert -> dann NICHT nochmal (sonst zweite Einloesung -> 400).
            if time.time() < c.get("exp", 0) and c.get("access"):
                return c["access"]
            tok = self._token_request({
                "grant_type": "refresh_token", "refresh_token": c["refresh"],
                "client_id": self.client_id()})
            with CONFIG_LOCK:
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

    def _post(self, c, path, params=None):
        """Schreibender ESI-Aufruf (z.B. Client-Fenster oeffnen). Leerer Body,
        Parameter in der Query — so verlangen es die UI-Endpunkte."""
        url = ESI_BASE + path + ("?" + urllib.parse.urlencode(params) if params else "")
        req = urllib.request.Request(url, data=b"", method="POST", headers={
            "Authorization": "Bearer " + self._access(c), "User-Agent": ESI_UA})
        with urllib.request.urlopen(req, timeout=20) as r:
            return r.status

    def ui_open(self, name, kind, oid):
        """Im laufenden Client des Charakters ein Fenster oeffnen. kind:
        'market' = Markt-Detail eines Item-Typs, 'info' = Info-Fenster einer ID.
        Setzt voraus, dass der Charakter online ist und der Scope erteilt wurde."""
        c = (self.cfg().get("chars") or {}).get(name)
        if not c:
            return "Charakter nicht verbunden."
        try:
            if kind == "market":
                self._post(c, "/ui/openwindow/marketdetails/", {"type_id": int(oid)})
            elif kind == "info":
                self._post(c, "/ui/openwindow/information/", {"target_id": int(oid)})
            else:
                return "Unbekannte Aktion."
            return None
        except urllib.error.HTTPError as e:
            if e.code == 403:
                return (f"{name} muss einmal neu verbunden werden "
                        "(neue Berechtigung 'Fenster oeffnen' noetig).")
            if e.code in (401, 400):
                return f"{name}: Login abgelaufen, bitte neu verbinden."
            return f"{name}: Client antwortet nicht (ist er offen und online?)."
        except Exception:
            return f"{name}: Client nicht erreichbar (offen und online?)."

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

    def type_volume(self, tid):
        """Volumen je Einheit fuer einen typeID. Erst aus der lokalen Erz-Tabelle,
        sonst oeffentlich von ESI (deckt Eis/Gas/Mondz ab). Gecacht."""
        if tid in ORE_BY_TID:
            return ORE_BY_TID[tid][1]
        if tid in self.vol_cache:
            return self.vol_cache[tid]
        try:
            req = urllib.request.Request(f"{ESI_BASE}/universe/types/{tid}/",
                                         headers={"User-Agent": ESI_UA})
            with urllib.request.urlopen(req, timeout=15) as r:
                v = float(json.loads(r.read()).get("volume") or 0.0)
        except Exception:
            v = 0.0
        self.vol_cache[tid] = v
        return v

    def sync_skills(self, name, c):
        """Mining-Skill-Bonus aus ESI (Scope esi-skills). Mining + Astrogeology
        heben den Ertrag je Stufe; Ergebnis als Prozent-Bonus abgelegt."""
        data, _ = self._get(c, f"/characters/{c['char_id']}/skills/")
        lvl = {s["skill_id"]: s.get("trained_skill_level", 0)
               for s in data.get("skills", [])}
        mult = 1.0
        for sid, per in MINING_YIELD_SKILLS.items():
            mult *= (1 + per * lvl.get(sid, 0))
        c["skill_bonus"] = round((mult - 1) * 100)
        # Reprocessing-Ausbeute (Basis NPC-Station 50%, mal Reprocessing + Reprocessing
        # Efficiency). Ohne Struktur-Rigs/Standings/Implantate/erz-spezifische Skills,
        # daher eine konservative Untergrenze fuer den Erz-Verwertungs-Berater.
        rep = 0.50
        for sid, per in REPROCESS_SKILLS.items():
            rep *= (1 + per * lvl.get(sid, 0))
        c["reprocess"] = round(rep, 4)
        c["skills_next"] = time.time() + 6 * 3600

    def sync_mining(self, name, c):
        """Mining Ledger aus ESI (Scope esi-industry): serverseitig geförderte
        Einheiten je Tag/Erztyp, in m³ umgerechnet. Die letzten 30 Tage sind der
        unfaelschbare Beleg der Foerderleistung."""
        cutoff = (datetime.now(timezone.utc).date() - timedelta(days=30)).isoformat()
        page, m3 = 1, 0.0
        while page <= 10:
            rows, _ = self._get(c, f"/characters/{c['char_id']}/mining/",
                                {"page": page})
            if not rows:
                break
            for r in rows:
                if (r.get("date") or "") >= cutoff:
                    m3 += r.get("quantity", 0) * self.type_volume(r.get("type_id"))
            if len(rows) < 1000:
                break
            page += 1
        c["mined_30d"] = round(m3)
        c["esi_mining"] = True
        c["mining_next"] = time.time() + 45 * 60

    def planet_info(self, pid):
        """Name + type_id eines Planeten aus dem oeffentlichen Universe-Endpunkt.
        type_id -> Planeten-Render (images.evetech.net). Gecacht."""
        if pid in self.planet_cache:
            return self.planet_cache[pid]
        info = {"name": f"#{pid}", "type_id": None}
        try:
            req = urllib.request.Request(f"{ESI_BASE}/universe/planets/{pid}/",
                                         headers={"User-Agent": ESI_UA})
            with urllib.request.urlopen(req, timeout=15) as r:
                d = json.loads(r.read())
            info = {"name": d.get("name") or f"#{pid}", "type_id": d.get("type_id")}
        except Exception:
            pass
        self.planet_cache[pid] = info
        return info

    def system_name(self, sid):
        """Systemname aus der System-ID (oeffentlich, gecacht)."""
        if not sid:
            return "?"
        if sid in self.sys_cache:
            return self.sys_cache[sid]
        nm = None
        try:
            req = urllib.request.Request(f"{ESI_BASE}/universe/systems/{sid}/",
                                         headers={"User-Agent": ESI_UA})
            with urllib.request.urlopen(req, timeout=15) as r:
                nm = json.loads(r.read()).get("name")
        except Exception:
            nm = None
        if nm:
            self.sys_cache[sid] = nm
        return nm or str(sid)

    def _pub(self, path):
        req = urllib.request.Request(ESI_BASE + path, headers={"User-Agent": ESI_UA})
        with urllib.request.urlopen(req, timeout=15) as r:
            return json.loads(r.read())

    def schematic_name(self, sid):
        """Produktname einer PI-Fabrik-Schematic (oeffentlich, gecacht)."""
        if sid in self.schem_cache:
            return self.schem_cache[sid]
        nm = None
        try:
            nm = self._pub(f"/universe/schematics/{sid}/").get("schematic_name")
        except Exception:
            nm = None
        if nm:
            self.schem_cache[sid] = nm
        return nm

    def type_group(self, tid):
        """group_id eines Typs (oeffentlich, gecacht) -> daraus der PI-Tier."""
        if tid in self.group_cache:
            return self.group_cache[tid]
        g = None
        try:
            g = self._pub(f"/universe/types/{tid}/").get("group_id")
        except Exception:
            g = None
        if g is not None:
            self.group_cache[tid] = g
        return g

    def name_tid(self, name):
        """type_id zu einem (Produkt-)Namen, fuer Icon + Tier der Fabrik-Produkte."""
        if name in self.tid_cache:
            return self.tid_cache[name]
        tid = None
        try:
            req = urllib.request.Request(
                ESI_BASE + "/universe/ids/", data=json.dumps([name]).encode(),
                headers={"Content-Type": "application/json", "User-Agent": ESI_UA})
            with urllib.request.urlopen(req, timeout=15) as r:
                its = json.loads(r.read()).get("inventory_types") or []
            tid = its[0]["id"] if its else None
        except Exception:
            tid = None
        if tid:
            self.tid_cache[name] = tid
        return tid

    def pi_tier(self, tid):
        """PI-Tier (P0-P4) aus der group_id des Produkttyps."""
        if not tid:
            return None
        return PI_GROUP_TIER.get(self.type_group(tid), "P0")

    def sync_planets(self, name, c):
        """Planetary Industry (Scope esi-planets): Kolonien + je Kolonie das Layout.
        Phase 1 zieht die reinen ESI-Fakten (Produkt, Koepfe, Ablauf) heraus, ohne
        Ertragsrechnung. Ablauf-/Install-Zeit werden zu Epoch-Sekunden fuer den
        Countdown im Frontend. Die dynamischen Lager-Fuellstaende sind bewusst NICHT
        dabei, die aktualisiert ESI erst beim Oeffnen im Client; das Extraktor-
        Programm dagegen steht stabil server-seitig."""
        cols, hdr = self._get(c, f"/characters/{c['char_id']}/planets/")
        try:
            exp = email.utils.parsedate_to_datetime(hdr["Expires"]).timestamp()
        except Exception:
            exp = time.time() + 600
        try:
            asof = email.utils.parsedate_to_datetime(hdr["Last-Modified"]).timestamp()
        except Exception:
            asof = time.time()

        def _ts(s):
            if not s:
                return None
            try:
                return datetime.fromisoformat(s.replace("Z", "+00:00")).timestamp()
            except Exception:
                return None
        out = []
        for col in cols:
            pid = col.get("planet_id")
            try:
                layout, _ = self._get(c, f"/characters/{c['char_id']}/planets/{pid}/")
            except Exception:
                layout = {}   # Layout-Hiccup: Kolonie trotzdem mit Basisdaten zeigen
            extractors, factories, schem_ids, contents = [], 0, [], {}
            for pin in layout.get("pins", []):
                ed = pin.get("extractor_details") or {}
                sid = pin.get("schematic_id") or (pin.get("factory_details") or {}).get("schematic_id")
                if pin.get("factory_details") or pin.get("schematic_id"):
                    factories += 1
                    if sid:
                        schem_ids.append(sid)
                ptid = ed.get("product_type_id")
                if ptid:
                    inst, exp_t = _ts(pin.get("install_time")), _ts(pin.get("expiry_time"))
                    cyc, qty = ed.get("cycle_time"), ed.get("qty_per_cycle")
                    extractors.append({
                        "product": self.type_name(ptid) or str(ptid),
                        "product_id": ptid,
                        "tier": self.pi_tier(ptid),
                        "heads": len(ed.get("heads") or []),
                        "cycle": cyc,
                        "install": inst,
                        "expiry": exp_t,
                        "total": extractor_total(inst, exp_t, cyc, qty)})
                # Gelagerte Materialien (Speicher/Startrampe/Fabrik): Menge je Typ,
                # spaeter mit Jita-Buy bewertet -> "wieviel ISK liegt auf dem Planeten".
                for it in (pin.get("contents") or []):
                    tid, amt = it.get("type_id"), it.get("amount") or 0
                    if tid:
                        contents[tid] = contents.get(tid, 0) + amt
            extractors.sort(key=lambda e: e.get("expiry") or 9e18)
            # Fabrik-Produkte: distinct Schematics -> Name, Tier, Icon, Anzahl Fabriken.
            pc = {}
            for s in schem_ids:
                pc[s] = pc.get(s, 0) + 1
            products = []
            for s, cnt in pc.items():
                pnm = self.schematic_name(s)
                if not pnm:
                    continue
                ptid = self.name_tid(pnm)
                products.append({"name": pnm, "count": cnt,
                                 "type_id": ptid, "tier": self.pi_tier(ptid)})
            products.sort(key=lambda p: (p.get("tier") or "z", p["name"]))
            pinfo = self.planet_info(pid)
            out.append({
                "planet_id": pid,
                "planet": pinfo["name"],
                "type_id": pinfo["type_id"],
                "type": col.get("planet_type"),
                "system": self.system_name(col.get("solar_system_id")),
                "upgrade": col.get("upgrade_level"),
                "pins": col.get("num_pins"),
                "factories": factories,
                "products": products,
                "extractors": extractors,
                "_contents": contents})
        # Preise fuer gelagerte Materialien UND Extraktor-Produkte (ein Abruf).
        all_tids = set()
        for col in out:
            all_tids |= set(col["_contents"])
            all_tids |= {e["product_id"] for e in col["extractors"] if e.get("product_id")}
        pm = hub_prices("10000002", all_tids, prefer_esi=True) if all_tids else {}
        for col in out:
            col["isk"] = round(sum(a * pm.get(t, (0, 0))[0]
                                   for t, a in col.pop("_contents").items()))
            col["ext_units"] = sum(e.get("total") or 0 for e in col["extractors"])
            col["ext_isk"] = round(sum((e.get("total") or 0) * pm.get(e["product_id"], (0, 0))[0]
                                       for e in col["extractors"] if e.get("product_id")))
        with CONFIG_LOCK:
            c["planets"] = {"as_of": int(asof), "next": int(exp) + 10, "cols": out}
        c["planets_next"] = exp + 10
        self._pi_alerts(name, out)

    def _pi_alerts(self, name, cols):
        """Ablauf-Alarm je Kolonie: warnt, wenn der frueheste Extraktor abgelaufen
        ist oder bald ablaeuft. Schwelle adaptiv (15% der Programmlaenge, gedeckelt
        auf 1 bis 12h). Cooldown ueber (char, planet) + gemerkte Ablaufzeit, damit
        ein neu programmierter Extraktor wieder alarmiert, sonst aber Ruhe ist."""
        now = time.time()
        for col in cols:
            exs = [e for e in (col.get("extractors") or []) if e.get("expiry")]
            if not exs:
                continue
            e = min(exs, key=lambda x: x["expiry"])
            exp = e["expiry"]
            length = (exp - e["install"]) if e.get("install") and exp > e["install"] else 0
            thr = min(12 * 3600, max(3600, 0.15 * length)) if length else 6 * 3600
            key = (name, col["planet_id"])
            if exp - now > thr:
                continue
            if self.pi_alerted.get(key) == exp:
                continue                       # fuer dieses Programm schon alarmiert
            self.pi_alerted[key] = exp
            n_soon = sum(1 for x in exs if x["expiry"] - now <= thr)
            more = f" · +{n_soon - 1} weitere" if n_soon > 1 else ""
            if exp <= now:
                txt = f"🪐 {name}: {col['planet']} · Extraktor abgelaufen{more}"
            else:
                mins = int((exp - now) // 60)
                left = f"{mins} min" if mins < 90 else f"{round(mins / 60)} Std"
                txt = f"🪐 {name}: {col['planet']} · Extraktor läuft in {left} ab{more}"
            alerts.push("pi", name, txt)

    def sync_ship(self, name, c, ship=None):
        """Heavy Water + Kern-Typ aus dem aktuellen Schiff uebernehmen.
        ship kann uebergeben werden (poll hat es schon geladen), sonst nachladen."""
        if ship is None:
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
            self.build_vault(name, c, items, asof, exp)
        except Exception as e:
            log_error("CN-ESI-01", "build_vault", e)
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
        pm = hub_prices("10000002", set(qty), prefer_esi=True) if qty else {}
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

    def loc_info(self, c, loc_id):
        """Name + Typ-ID eines Lagerorts (Typ-ID fuer das Stations-Icon). NPC-Stationen
        oeffentlich, Spieler-Strukturen ueber den Char-Token (nur mit Zugang). Gecacht."""
        if loc_id in self.loc_cache:
            return self.loc_cache[loc_id]
        nm = tid = None
        try:
            if 60000000 <= loc_id < 64000000:      # NPC-Station (oeffentlich, kein Token)
                req = urllib.request.Request(f"{ESI_BASE}/universe/stations/{loc_id}/",
                                             headers={"User-Agent": ESI_UA})
                with urllib.request.urlopen(req, timeout=15) as r:
                    d = json.loads(r.read())
                nm, tid = d.get("name"), d.get("type_id")
            elif 30000000 <= loc_id < 32000000:    # Sonnensystem = Erz im Erzladeraum/
                # Fleet-Hangar des Mining-Schiffs in diesem System. Oeffentlich
                # aufloesbar, kein Stations-Icon.
                req = urllib.request.Request(f"{ESI_BASE}/universe/systems/{loc_id}/",
                                             headers={"User-Agent": ESI_UA})
                with urllib.request.urlopen(req, timeout=15) as r:
                    d = json.loads(r.read())
                if d.get("name"):
                    nm = f"{d['name']} · im Schiff"
            elif loc_id >= 100000000:              # Upwell-Struktur (Zugang noetig)
                d, _ = self._get(c, f"/universe/structures/{loc_id}/")
                nm, tid = d.get("name"), d.get("type_id")
        except Exception:
            nm = tid = None
        if not nm:
            nm = f"Struktur #{loc_id}" if loc_id >= 100000000 else f"Ort #{loc_id}"
        info = {"name": nm, "type_id": tid}
        self.loc_cache[loc_id] = info
        return info

    def build_vault(self, name, c, items, asof, nxt):
        """Erz-Schatzkammer: gesamter Erz-Bestand (roh + komprimiert) ueber ALLE
        Lagerorte des Chars, aus den ESI-Assets. Menge, m³ und ISK-Wert (Jita-Buy)
        je Standort und Erztyp. Erz in Containern/Schiffen wird zum obersten
        Stations-/Struktur-Standort hochgereicht."""
        by_id = {it["item_id"]: it for it in items if "item_id" in it}
        ore_items = [it for it in items if it.get("type_id") in ORE_BY_TID]
        if not ore_items:
            with CONFIG_LOCK:
                c["vault"] = {"as_of": int(asof), "next": int(nxt),
                              "total_m3": 0, "total_isk": 0, "locs": []}
            return
        pm = hub_prices("10000002", set(it["type_id"] for it in ore_items), prefer_esi=True)
        locs = {}
        for it in ore_items:
            loc = it.get("location_id"); seen = set()
            while loc in by_id and loc not in seen:   # Container/Schiff -> Station hochreichen
                seen.add(loc); loc = by_id[loc].get("location_id")
            d = locs.setdefault(loc, {})
            d[it["type_id"]] = d.get(it["type_id"], 0) + it["quantity"]
        out, tot_m3, tot_isk = [], 0.0, 0.0
        for loc_id, ores in locs.items():
            orelist, lm3, lisk = [], 0.0, 0.0
            for tid, units in ores.items():
                oname, vol = ORE_BY_TID[tid]
                m3 = units * vol
                isk = units * pm.get(tid, (0, 0))[0]
                lm3 += m3; lisk += isk
                orelist.append({"ore": oname, "units": units,
                                "m3": round(m3), "isk": round(isk)})
            orelist.sort(key=lambda x: -x["isk"])
            tot_m3 += lm3; tot_isk += lisk
            out.append({"loc_id": loc_id, "name": self.loc_info(c, loc_id)["name"],
                        "m3": round(lm3), "isk": round(lisk), "ores": orelist})
        out.sort(key=lambda x: -x["isk"])
        with CONFIG_LOCK:
            c["vault"] = {"as_of": int(asof), "next": int(nxt),
                          "total_m3": round(tot_m3), "total_isk": round(tot_isk), "locs": out}

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
                    self.sync_ship(name, c, ship)
                # Online-Status (Scope esi-location.read_online.v1). Fehlt der Scope
                # (Char noch nicht neu verbunden), liefert ESI 403 -> still ignorieren,
                # dann greift der Log-Aktivitäts-Fallback.
                try:
                    onl, _ = self._get(c, f"/characters/{c['char_id']}/online/")
                    c["online"] = bool(onl.get("online"))
                except Exception:
                    c.pop("online", None)  # Scope fehlt/Fehler -> Log-Aktivität greift
                # Skills + Mining Ledger (neue Scopes). Fehlt der Scope (Char noch
                # nicht neu verbunden), kommt 403 -> still ueberspringen, dann bleibt
                # die MFP "geschaetzt" statt "ESI-verifiziert".
                try:
                    if time.time() >= c.get("skills_next", 0):
                        self.sync_skills(name, c)
                except Exception:
                    c.pop("skill_bonus", None)
                try:
                    if time.time() >= c.get("mining_next", 0):
                        self.sync_mining(name, c)
                except Exception:
                    c.pop("esi_mining", None)
                    c.pop("mined_30d", None)
                # Planetary Industry (neuer Scope). Fehlt er (Char noch nicht neu
                # verbunden), kommt 403 -> als "neu verbinden" markieren, nicht
                # dauernd nachfragen. Andere Fehler lassen die alten Daten stehen.
                try:
                    if time.time() >= c.get("planets_next", 0):
                        self.sync_planets(name, c)
                    c["planets_scope"] = True
                except urllib.error.HTTPError as e:
                    if e.code == 403:
                        c["planets_scope"] = False
                        c.pop("planets", None)
                        c["planets_next"] = time.time() + 1800
                except Exception:
                    pass
                c["poll_ts"] = time.time()   # ESI-Stand fuer die Steckbrief-Frische
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
# Blutspur-Radar: typische Gank-Huelle (ESI-verifizierte typeIDs) + CONCORD-Kennungen.
GANK_HULLS = {16240, 16242, 16236, 16238,   # Catalyst, Thrasher, Coercer, Cormorant
              4308, 4310, 4302, 4306}       # Talos, Tornado, Oracle, Naga
CONCORD_CORP = 1000125
CONCORD_FACTION = 500006


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
        with DB_LOCK:
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
                # _store (DB-Schreibzugriff) und das discard MUESSEN abgesichert sein:
                # eine Ausnahme hier wuerde sonst aus run() heraus den Daemon-Thread
                # beenden und alle weiteren Bedrohungs-Scans der Session lahmlegen.
                try:
                    self._store(raw, data)
                except Exception as e:
                    log_error("CN-INTEL-01", "ThreatIntel._store", e)
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


# ---------------------------------------------------------------- Blutspur-Radar
KMSTREAM = "https://killmail.stream/poll/"

# Wie nah muss ein Rudel am eigenen Standort sein, damit es ueberhaupt gemeldet
# wird. Beobachtet wird weiter die ganze Blase (pack_radius, Standard 20), die
# Karte zeigt auch alles. Gemeldet wird aber nur, was den eigenen Standort
# etwas angeht: ein Rudel 18 Spruenge weiter in einer anderen Region ist fuer
# den naechsten Undock ohne Bedeutung.
PACK_NEAR_JUMPS = 10   # Annaeherung (Distanz sinkt) wird ab hier gemeldet
PACK_INFO_JUMPS = 5    # "sitzt schon da"-Hinweis nur direkt in der Nachbarschaft
PACK_WATCH_JUMPS = 15  # bekannte Gank-Gruppen (gank_groups.json) frueher melden


class PackIntel(threading.Thread):
    """Blutspur: erkennt aktive Gank-Rudel der beobachteten Regionen aus dem
    oeffentlichen Killmail-Strom. Primaer killmail.stream-Longpoll (stdlib-
    freundlich, volle Killmails inkl. Angreifer), Fallback + Warm-Start ueber
    die zKill-Regional-API (max 1x/h, Cloudflare-Cache). Wer wiederholt
    gemeinsam toetet, wird als Rudel gefuehrt, mit Jagdgebiet, Richtung und
    ehrlichem 'zuletzt gesehen vor X min' (immer aus der Kill-Zeit, nie aus
    der Empfangszeit). Opt-in, default aus; ein Rudel ist erst nach seinem
    letzten Kill sichtbar (Echo-Prinzip, steht auch so im UI)."""
    daemon = True

    def __init__(self):
        super().__init__()
        self.lock = threading.Lock()   # schuetzt packs/member_index/heat/names
        self.packs = {}                # pack_id -> {members,set corps Counter,...}
        self.member_index = {}         # char_id -> pack_id
        self.heat = {}                 # system_id -> [kill_ts,...] (2h)
        self.names = {}                # id -> Name (Chars/Corps, /universe/names/)
        self.sysrow = {}               # system_id -> (region, name, sec, x, z, gates)
        self.region_ids = {}           # Regionsname -> region_id
        self.mode = "aus"              # aus|laden|live|fallback|tot
        self.map_progress = (0, 0)
        self.last_kill_ts = 0
        # Kill-Ticker: (kt, sysid, vship, value, kill_id). Die ID kommt mit,
        # damit die Zeile auf die Killmail bei zKillboard verlinken kann.
        self.recent = deque(maxlen=40)
        self.dist = {}                 # system_id -> Spruenge vom Zentrum
        self.center_id = None
        self.alerted = {}              # (pack_id, sprecher) -> last_seen beim Alarm
        self.near_alerted = {}         # (pack_id, system) -> ts (Gold-Hinweis)
        self.info_alerted = set()      # pack_id: Region-Hinweis schon gegeben
        self._seen = set()             # kill_ids (Dedupe, Session)
        self._pid = 0
        self._fails = 0
        self._last200 = time.time()
        self._probe = (0, 0.0)         # (Erfolge, letzter Probezeitpunkt)
        self._zkill_last = {}

    # ---- Konfiguration -------------------------------------------------
    def enabled(self):
        return bool(CONFIG.get("pack_radar"))

    def _queue(self):
        q = CONFIG.get("pack_queue")
        if not q:
            q = "eve-canary-" + os.urandom(8).hex()
            with CONFIG_LOCK:
                CONFIG["pack_queue"] = q
            save_config()
        return q

    def _get(self, url, timeout=30):
        req = urllib.request.Request(url, headers={
            "User-Agent": ESI_UA, "Accept-Encoding": "gzip"})
        with urllib.request.urlopen(req, timeout=timeout) as r:
            raw = r.read()
            if (r.headers.get("Content-Encoding") or "") == "gzip":
                raw = gzip.decompress(raw)
            return json.loads(raw)

    # ---- Karte / Stammdaten -------------------------------------------
    def _own_name(self):
        with ingest.lock:
            for s in ingest.sessions.values():
                if s.system:
                    return s.system
        return CONFIG.get("pack_center")

    def _load_map(self):
        """Ego-Blase aus der MITGELIEFERTEN Universums-Karte (eve_map.json, aus
        der SDE generiert): alle Systeme im Umkreis von pack_radius Spruengen
        (Default 20) um das eigene System, per Gate-BFS. Kein ESI-Crawl, kein
        lokaler Aufbau, die Blase steht in Millisekunden."""
        radius = int(CONFIG.get("pack_radius", 20) or 20)
        center = CONFIG.get("pack_center") or self._own_name()
        if not center:
            time.sleep(10)
            return
        emap = load_json("eve_map.json", None)
        if not emap or not emap.get("systems"):
            log_error("CN-PACK-02", "load_map",
                      "eve_map.json fehlt oder ist leer (Update unvollstaendig?)")
            time.sleep(60)
            return
        systems = {int(k): v for k, v in emap["systems"].items()}
        self.region_ids = {n: i for n, i in (emap.get("regions") or {}).items()}
        name2id = {v[0]: sid for sid, v in systems.items()}
        cid = name2id.get(center)
        if not cid:
            log_error("CN-PACK-02", "load_map", f"System {center} nicht in der Karte")
            time.sleep(30)
            return
        with CONFIG_LOCK:
            CONFIG["pack_center"] = center
        save_config()
        bubble = {cid: 0}
        frontier = [cid]
        depth = 0
        while frontier and depth < radius:
            depth += 1
            nxt = []
            for sid in frontier:
                for g in systems.get(sid, (None,) * 6)[5]:
                    if g in systems and g not in bubble:
                        bubble[g] = depth
                        nxt.append(g)
            frontier = nxt
        # sysrow-Format wie gehabt: (Region, Name, Sec, x, z, Gates)
        self.sysrow = {sid: (systems[sid][4], systems[sid][0], systems[sid][1],
                             systems[sid][2], systems[sid][3], systems[sid][5])
                       for sid in bubble}
        self.center_id = cid
        self.dist = dict(bubble)
        self.map_progress = (len(bubble), len(bubble))

    def _backfill_regions(self):
        """Die (max 3) Regionen mit den meisten Blasen-Systemen, fuer zKill."""
        cnt = {}
        for v in self.sysrow.values():
            if v[0]:
                cnt[v[0]] = cnt.get(v[0], 0) + 1
        return [r for r, _ in sorted(cnt.items(), key=lambda x: -x[1])[:3]]

    # ---- Kill-Verarbeitung ---------------------------------------------
    def _kill_score(self, km, sysid):
        """Gank-Relevanz 0..100 eines Kills (web-verifizierte Kennungen)."""
        sc = 0
        vship = (km.get("victim") or {}).get("ship_type_id")
        vgrp = esi.type_group(vship) if vship else None
        if vgrp in MINER_GROUPS:
            sc += 40
        atk = km.get("attackers") or []
        if any(a.get("corporation_id") == CONCORD_CORP
               or a.get("faction_id") == CONCORD_FACTION for a in atk):
            sc += 25
        row = self.sysrow.get(sysid)
        if row and (row[2] or 0) >= 0.45:
            sc += 15
        if any(a.get("ship_type_id") in GANK_HULLS for a in atk):
            sc += 15
        if vgrp == 29:                      # Pod-Nachsetzer
            sc += 5
        return min(sc, 100)

    def _ingest(self, km, src, persist=True):
        kid = km.get("killmail_id")
        sysid = km.get("solar_system_id")
        if not kid or kid in self._seen or sysid not in self.sysrow:
            return False
        self._seen.add(kid)
        kt = 0
        try:
            kt = datetime.fromisoformat(
                (km.get("killmail_time") or "").replace("Z", "+00:00")).timestamp()
        except Exception:
            kt = time.time()
        zkb = km.get("zkb") or {}
        if zkb.get("npc"):                 # reine NPC-Kills sind kein Rudel-Signal
            return False
        atk = [a for a in (km.get("attackers") or []) if a.get("character_id")]
        score = self._kill_score(km, sysid)
        self.last_kill_ts = max(self.last_kill_ts, kt)
        self.heat.setdefault(sysid, []).append(kt)
        self.recent.append((kt, sysid,
                            (km.get("victim") or {}).get("ship_type_id"),
                            zkb.get("totalValue"), kid))
        if persist:
            with DB_LOCK:
                DB.execute("INSERT OR IGNORE INTO pack_kills VALUES(?,?,?,?,?,?,?,?,?)",
                           (kid, kt, sysid, self.sysrow[sysid][0], score,
                            (km.get("victim") or {}).get("ship_type_id"),
                            zkb.get("totalValue"),
                            json.dumps([[a.get("character_id"), a.get("corporation_id"),
                                         a.get("ship_type_id"),
                                         a.get("alliance_id")] for a in atk]),
                            1 if src == "sim" else 0))
                DB.commit()
        self._cluster(kid, kt, sysid, score,
                      [[a.get("character_id"), a.get("corporation_id"),
                        a.get("ship_type_id"), a.get("alliance_id")] for a in atk])
        return True

    def _cluster(self, kid, kt, sysid, score, atk):
        """Inkrementelle Rudel-Zuordnung (Spez: overlap>=2 ODER overlap>=1 mit
        50% Anteil ODER overlap>=1 bei score>=60; Merge nur bei >=2 gemeinsamen)."""
        chars = {a[0] for a in atk if a[0]}
        if not chars or len(chars) > 30:    # Blob-Kappung: keine Rudel-Zuordnung
            return
        with self.lock:
            matches = []
            for pid, p in self.packs.items():
                ov = len(chars & p["members"])
                if ov >= 2 or (ov >= 1 and (ov / len(chars) >= 0.5 or score >= 60)):
                    matches.append((ov, pid))
            matches.sort(reverse=True)
            strong = [pid for ov, pid in matches if ov >= 2]
            if len(strong) > 1:             # Merge nur bei harter Ueberlappung
                base = strong[0]
                for pid in strong[1:]:
                    q = self.packs.pop(pid)
                    b = self.packs[base]
                    b["members"] |= q["members"]
                    b["kills"] += q["kills"]
                    b["corps"].update(q["corps"])
                    b["ships"].update(q["ships"])
                    b["systems"] = (q["systems"] + b["systems"])[-12:]
                    b["value"] += q["value"]
                target = base
            elif matches:
                target = matches[0][1]
            else:
                if len(chars) < 2 and score < 65:
                    return                   # Einzelgaenger nur bei hartem Gank
                self._pid += 1
                target = f"p{self._pid}"
                self.packs[target] = {"members": set(), "kills": 0, "score": 0.0,
                                      "first": kt, "last": 0, "systems": [],
                                      "corps": {}, "allis": {}, "ships": {},
                                      "value": 0.0,
                                      "kls": {}, "again": self._recognize(chars)}
            p = self.packs[target]
            dt = max(kt - p["last"], 0) if p["last"] else 0
            p["score"] = score + p["score"] * (0.5 ** (dt / 2700.0)) if p["last"] else float(score)
            p["members"] |= chars
            p["kills"] += 1
            p["last"] = max(p["last"], kt)
            if not p["systems"] or p["systems"][-1][0] != sysid:
                p["systems"].append((sysid, kt))
                p["systems"] = p["systems"][-12:]
            else:
                p["systems"][-1] = (sysid, kt)
            for a in atk:
                if a[1]:
                    p["corps"][a[1]] = p["corps"].get(a[1], 0) + 1
                # Alte Zeilen in pack_kills haben nur drei Felder, deshalb Laenge
                # pruefen statt blind auf a[3] zugreifen.
                if len(a) > 3 and a[3]:
                    p["allis"][a[3]] = p["allis"].get(a[3], 0) + 1
                if a[2]:
                    p["ships"][a[2]] = p["ships"].get(a[2], 0) + 1
                if a[0]:
                    p["kls"][a[0]] = p["kls"].get(a[0], 0) + 1
            for c in chars:
                self.member_index[c] = target
            # Annaeherungs-Warnung: die Kill-Distanz zum Zentrum sinkt. Feuert je
            # Rudel nur, wenn es NAEHER kommt als je zuvor gemeldet (kein
            # Dauergeplapper). Bekannte Gank-Gruppen werden frueher gemeldet.
            d = self.dist.get(sysid)
            if d is not None and self._visible(p):
                prevd = p.get("dist")
                p["dist_prev"] = prevd
                p["dist"] = d
                best = p.get("dist_alerted")
                flag = self._flagged(p)
                grenze = PACK_WATCH_JUMPS if flag else PACK_NEAR_JUMPS
                if (prevd is not None and d < prevd and d <= grenze
                        and (best is None or d < best)):
                    p["dist_alerted"] = d
                    sysn = (self.sysrow.get(sysid) or (None, "?"))[1]
                    if flag:
                        alerts.push("pack" if d <= 5 else "packinfo", self._label(p),
                                    f"🩸 Achtung, {flag['name']}: Rudel nähert sich, "
                                    f"{prevd} → {d} Sprünge ({sysn}). "
                                    f"{flag['miner']} Miner-Kills zuletzt.")
                    elif d <= 3:
                        alerts.push("pack", self._label(p),
                                    f"🩸 Rudel [{self._label(p)}] nähert sich deinem "
                                    f"System: noch {d} Sprünge ({sysn})")
                    else:
                        alerts.push("packinfo", self._label(p),
                                    f"🩸 Rudel [{self._label(p)}] nähert sich: "
                                    f"{prevd} → {d} Sprünge ({sysn})")

    def _recognize(self, chars):
        """14-Tage-Wiedererkennung: >=50% Mitglieder-Ueberlappung mit dem Archiv."""
        try:
            with DB_LOCK:
                rows = DB.execute("SELECT label, members FROM pack_archive "
                                  "WHERE last_ts>?", (time.time() - 14 * 86400,)).fetchall()
            for label, mj in rows:
                old = set(json.loads(mj or "[]"))
                if old and len(chars & old) / max(len(chars), 1) >= 0.5:
                    return label
        except Exception:
            pass
        return None

    def _status(self, p, now):
        age = now - p["last"]
        return "aktiv" if age <= 1200 else ("abklingend" if age <= 5400 else "inaktiv")

    def _flagged(self, p):
        """Gehoert das Rudel zu einer bekannten Gank-Gruppe? Allianz zuerst:
        die einschlaegigen Gruppen sind Allianzen (Safety., CODE.), auf
        Corp-Ebene zerfallen sie in viele kleine Einheiten. NPC-Anfaengercorps
        stehen bewusst nicht in der Liste, sonst gaelte jeder Neuling als
        verdaechtig. Liefert den Eintrag aus gank_groups.json oder None."""
        allis, corps = GANK_IDX.get(self._band()) or ({}, {})
        for aid in (p.get("allis") or {}):
            if aid in allis:
                return dict(allis[aid], art="alliance")
        for cid in (p.get("corps") or {}):
            if cid in corps:
                return dict(corps[cid], art="corp")
        return None

    def _band(self):
        """Highsec oder Lowsec, bestimmt durch das EIGENE System (Userwunsch:
        wer in Lowsec minert, will die Lowsec-Gruppen sehen, nicht die
        Highsec-Ganker). sysrow: (region, name, sec, x, z, gates)."""
        row = self.sysrow.get(self.center_id)
        return "highsec" if (row and row[2] >= 0.45) else "lowsec"

    def _visible(self, p):
        # Bekannte Gank-Gruppen immer zeigen, auch unter der Punkte-Schwelle:
        # bei denen ist schon ein einzelner Kill in der Naehe eine Ansage.
        if self._flagged(p):
            return True
        return (p["score"] >= 50 and
                (len(p["members"]) >= 2 and p["kills"] >= 2 or p["score"] >= 65))

    def _prune(self, now):
        with self.lock:
            for pid in [pid for pid, p in self.packs.items() if now - p["last"] > 86400]:
                p = self.packs.pop(pid)
                try:
                    label = self._label(p)
                    with DB_LOCK:
                        DB.execute("INSERT OR REPLACE INTO pack_archive VALUES(?,?,?,?,?,?,?)",
                                   (pid, p["first"], p["last"], label,
                                    json.dumps(sorted(p["members"])),
                                    json.dumps(sorted(p["corps"])), p["score"]))
                        DB.commit()
                except Exception:
                    pass
                for c in [c for c, x in self.member_index.items() if x == pid]:
                    del self.member_index[c]
            cut = now - 7200
            for sid in list(self.heat):
                self.heat[sid] = [t for t in self.heat[sid] if t > cut]
                if not self.heat[sid]:
                    del self.heat[sid]
        with DB_LOCK:
            DB.execute("DELETE FROM pack_kills WHERE ts<?", (now - 7 * 86400,))
            DB.commit()

    def _label(self, p):
        top = max(p["corps"], key=p["corps"].get) if p["corps"] else None
        nm = self.names.get(top) or (f"Corp #{top}" if top else "Unbekannt")
        return nm

    def _resolve_names(self):
        ids = set()
        with self.lock:
            for p in self.packs.values():
                ids |= set(list(p["members"])[:60])
                ids |= set(p["corps"])
        ids -= set(self.names)
        ids = [i for i in ids if isinstance(i, int)][:900]
        if not ids:
            return
        try:
            req = urllib.request.Request(
                ESI_BASE + "/universe/names/", data=json.dumps(ids).encode(),
                headers={"Content-Type": "application/json", "User-Agent": ESI_UA})
            with urllib.request.urlopen(req, timeout=25) as r:
                for x in json.loads(r.read()):
                    self.names[x["id"]] = x["name"]
        except Exception:
            pass

    # ---- zKill (Warm-Start + Fallback) ----------------------------------
    def _zkill(self, past=10800):
        regions = self._backfill_regions()
        need = [r for r in regions if r not in self.region_ids]
        if need:
            try:
                req = urllib.request.Request(
                    ESI_BASE + "/universe/ids/", data=json.dumps(need).encode(),
                    headers={"Content-Type": "application/json", "User-Agent": ESI_UA})
                with urllib.request.urlopen(req, timeout=20) as r:
                    for x in json.loads(r.read()).get("regions", []):
                        self.region_ids[x["name"]] = x["id"]
            except Exception:
                pass
        for rname in regions:
            rid = self.region_ids.get(rname)
            if not rid or time.time() - self._zkill_last.get(rname, 0) < 3600:
                continue
            self._zkill_last[rname] = time.time()
            try:
                rows = self._get(f"https://zkillboard.com/api/regionID/{rid}"
                                 f"/pastSeconds/{past}/", timeout=45)
                for km in sorted(rows, key=lambda k: k.get("killmail_time") or ""):
                    self._ingest(km, "zkill")
            except Exception as e:
                log_error("CN-PACK-01", f"zkill {rname}", e)

    # ---- Alarme ----------------------------------------------------------
    def _alarms(self, now):
        # ROT: bekanntes Rudel-Mitglied spricht in einem eigenen Local.
        speakers = dict(chatwatch.speakers)
        for low, sp in speakers.items():
            if now - sp.get("ts", 0) > 900:
                continue
            prof = threat.cached(sp.get("name") or low) or {}
            cid = prof.get("id")
            pid = self.member_index.get(cid)
            if not pid:
                continue
            with self.lock:
                p = self.packs.get(pid)
                if not p or self._status(p, now) == "inaktiv" or p["score"] < 50:
                    continue
                key = (pid, low)
                if self.alerted.get(key) == p["last"]:
                    continue
                self.alerted[key] = p["last"]
                label = self._label(p)
                n = len(p["members"])
                mins = max(0, int((now - p["last"]) // 60))
                sysn = (self.sysrow.get(p["systems"][-1][0]) or (None, "?"))[1] \
                    if p["systems"] else "?"
            alerts.push("pack", sp.get("name") or low,
                        f"🩸 Bekanntes Rudel im Local: {sp.get('name') or low} gehört zu "
                        f"Rudel [{label}] ({n} Piloten, zuletzt aktiv vor {mins} min in {sysn})")
        # GOLD (Options-Schalter): Sprecher ist nur in der CORP eines aktiven
        # Rudels, stand selbst aber auf keiner Killmail (faengt Scouts).
        if CONFIG.get("pack_corp_alert"):
            corp_map = {}
            with self.lock:
                for pid, p in self.packs.items():
                    if self._status(p, now) == "inaktiv" or not self._visible(p):
                        continue
                    for c in p["corps"]:
                        nm = self.names.get(c)
                        if nm:
                            corp_map[nm.lower()] = (pid, self._label(p))
            for low, sp in speakers.items():
                if now - sp.get("ts", 0) > 900:
                    continue
                prof = threat.cached(sp.get("name") or low) or {}
                if prof.get("id") and self.member_index.get(prof.get("id")):
                    continue                      # echtes Mitglied -> ROT oben
                hit = corp_map.get((prof.get("corp") or "").lower())
                if not hit:
                    continue
                key = ("corp", hit[0], low)
                if now - self.near_alerted.get(key, 0) < 900:
                    continue
                self.near_alerted[key] = now
                alerts.push("packinfo", sp.get("name") or low,
                            f"🩸 Rudel-Corp im Local: {sp.get('name') or low} "
                            f"ist in der Corp von Rudel [{hit[1]}]")
        # GOLD: Rudel-Kill nahe (<=2 Spruenge) an einem eigenen System.
        own = set()
        with ingest.lock:
            for s in ingest.sessions.values():
                if s.system and s.last_event_ts and now - s.last_event_ts < 900:
                    own.add(s.system)
        if own:
            name2id = {v[1]: sid for sid, v in self.sysrow.items() if v[1]}
            own_ids = {name2id[n] for n in own if n in name2id}
            near = set()
            for oid in own_ids:
                near |= self._bfs(oid, 2)
            with self.lock:
                for pid, p in self.packs.items():
                    if not p["systems"] or not self._visible(p):
                        continue
                    sid, kt = p["systems"][-1]
                    if sid in near and now - kt < 3600 \
                            and self._status(p, now) != "inaktiv":
                        key = (pid, sid)
                        if now - self.near_alerted.get(key, 0) < 900:
                            continue
                        self.near_alerted[key] = now
                        sysn = (self.sysrow.get(sid) or (None, "?"))[1]
                        alerts.push("packinfo", self._label(p),
                                    f"🩸 Rudel [{self._label(p)}]: Kill in der Nähe ({sysn})")

    def _start_info(self, now):
        """Einmaliger Hinweis je Rudel, aber NUR wenn es wirklich in der Naehe
        sitzt (<= PACK_INFO_JUMPS Spruenge vom eigenen Standort).

        Vorher meldete das jedes Rudel der ganzen Blase, also auch welche, die
        20 Spruenge weit weg in einer anderen Region wueten. Das ist fuer den
        eigenen Standort ohne Belang und war reines Rauschen (Userwunsch
        2026-07-26: nur melden, wenn sich etwas dem Standort naehert oder
        direkt daneben sitzt)."""
        with self.lock:
            for pid, p in self.packs.items():
                if pid in self.info_alerted or not self._visible(p):
                    continue
                if self._status(p, now) != "aktiv":
                    continue
                d = p.get("dist")
                if d is None or d > PACK_INFO_JUMPS:
                    continue
                self.info_alerted.add(pid)
                mins = max(1, int((now - p["first"]) // 60))
                sysn = (self.sysrow.get(p["systems"][-1][0]) or (None, "?"))[1] \
                    if p["systems"] else "?"
                alerts.push("packinfo", self._label(p),
                            f"🩸 Rudel [{self._label(p)}] ist {d} Sprünge entfernt aktiv "
                            f"({sysn}, seit {mins} min, {len(p['members'])} Piloten)")

    def _bfs(self, start, depth):
        seen = {start}
        frontier = {start}
        for _ in range(depth):
            nxt = set()
            for sid in frontier:
                row = self.sysrow.get(sid)
                for g in (row[5] if row else []):
                    if g not in seen:
                        seen.add(g)
                        nxt.add(g)
            frontier = nxt
        return seen

    # ---- Snapshot fuer das Frontend --------------------------------------
    def snapshot(self):
        now = time.time()
        out = {"on": self.enabled(), "mode": self.mode,
               "center": CONFIG.get("pack_center"),
               "radius": int(CONFIG.get("pack_radius", 20) or 20),
               "corp_alert": bool(CONFIG.get("pack_corp_alert")),
               "follow": bool(CONFIG.get("pack_follow")),
               "map_progress": list(self.map_progress),
               "last_kill_age": int(now - self.last_kill_ts) if self.last_kill_ts else None,
               "packs": [], "roster": [], "maps": [], "kills": []}
        if not self.enabled():
            return out
        with self.lock:
            for pid, p in self.packs.items():
                st = self._status(p, now)
                if st == "inaktiv" or not self._visible(p):
                    continue
                syss = [( (self.sysrow.get(s) or (None, "?"))[1], int(t)) for s, t in p["systems"][-5:]]
                ships = sorted(p["ships"], key=p["ships"].get, reverse=True)[:4]
                mem = sorted(p["kls"].items(), key=lambda x: -x[1])[:8]
                out["packs"].append({
                    "id": pid, "label": self._label(p), "again": p.get("again"),
                    "dist": p.get("dist") if p.get("dist") is not None
                            else (self.dist.get(p["systems"][-1][0])
                                  if p["systems"] else None),
                    "dist_prev": p.get("dist_prev"),
                    "status": st, "score": round(p["score"]),
                    "members": len(p["members"]), "kills": p["kills"],
                    "last_seen": int(p["last"]),
                    "last_system": syss[-1][0] if syss else "?",
                    "systems": [s for s, _ in syss],
                    "ships": [esi.type_name(t) or str(t) for t in ships],
                    # Bekannte Gank-Gruppe? Dann Zahlen mitgeben, damit die
                    # Oberflaeche belegen kann, warum sie Achtung schreibt.
                    "achtung": self._flagged(p),
                    "top": [{"id": c, "name": self.names.get(c) or str(c), "kills": k}
                            for c, k in mem]})
                for c, k in mem:
                    out["roster"].append({"id": c, "name": self.names.get(c) or str(c),
                                          "pack": self._label(p), "kills": k,
                                          "last_seen": int(p["last"]),
                                          "status": st})
            out["packs"].sort(key=lambda x: -x["score"])
            out["roster"].sort(key=lambda x: -x["kills"])
            out["roster"] = out["roster"][:30]
            # Kill-Ticker: jeder Spieler-Kill der Blase, klassifiziert.
            for kt2, sid2, vship, val, kid2 in list(self.recent)[::-1][:25]:
                row = self.sysrow.get(sid2)
                g = esi.type_group(vship) if vship else None
                klass = ("pod" if g == 29 else
                         "miner" if g in (463, 543) else
                         "booster" if g in (941, 883) else
                         "hauler" if g in (28, 380, 1202, 513, 902) else "kill")
                out["kills"].append({
                    "ts": int(kt2), "system": row[1] if row else "?",
                    "jumps": self.dist.get(sid2),
                    "ship": esi.type_name(vship) or "?", "klass": klass,
                    "value": val, "id": kid2})
            # EINE Ego-Karte: eigenes System in der Mitte, Blase drumherum.
            own_names = set()
            with ingest.lock:
                for s in ingest.sessions.values():
                    if s.system:
                        own_names.add(s.system)
            pack_sys = {}
            for pk in out["packs"]:
                pack_sys.setdefault(pk["last_system"], []).append(pk["label"])
            # Anzeige-Ausschnitt: NUR die Nachbarschaft (~20-35 Systeme) rund um
            # das Zentrum, damit die Karte lesbar bleibt. Beobachtet und gewarnt
            # wird weiter ueber die ganze pack_radius-Blase.
            depth = 2
            for cand in (2, 3, 4, 5, 6):
                depth = cand
                if sum(1 for d in self.dist.values() if d <= cand) >= 20:
                    break
            if sum(1 for d in self.dist.values() if d <= depth) > 40 and depth > 2:
                depth -= 1
            rows = [(sid, v) for sid, v in self.sysrow.items()
                    if v[3] is not None and self.dist.get(sid, 99) <= depth]
            crow = self.sysrow.get(self.center_id)
            if rows and crow and crow[3] is not None:
                cx, cz = crow[3], crow[4]
                mx = max(max(abs(v[3] - cx) for _, v in rows), 1.0)
                mz = max(max(abs(v[4] - cz) for _, v in rows), 1.0)
                idx = {}
                systems = []
                for i, (sid, v) in enumerate(rows):
                    idx[sid] = i
                    systems.append({
                        "name": v[1], "sec": v[2],
                        "x": round(500 + 460 * (v[3] - cx) / mx),
                        "y": round(350 - 310 * (v[4] - cz) / mz),
                        "heat": len(self.heat.get(sid, [])),
                        "own": v[1] in own_names or sid == self.center_id,
                        "jumps": self.dist.get(sid),
                        "packs": pack_sys.get(v[1], [])})
                # Entzerrung: zu nah beieinander projizierte Systeme sanft
                # auseinanderdruecken (Zentrum bleibt fest), sonst kleben
                # z.B. Jita/Ikuchi/New Caldari unlesbar aufeinander.
                pin = idx.get(self.center_id)
                for _ in range(40):
                    moved = False
                    for i in range(len(systems)):
                        for j in range(i + 1, len(systems)):
                            a, b = systems[i], systems[j]
                            dx = b["x"] - a["x"]
                            dy = b["y"] - a["y"]
                            d2 = dx * dx + dy * dy
                            if d2 < 40 * 40:
                                d = (d2 ** 0.5) or 1.0
                                ux, uy = (dx / d, dy / d) if d > 1 else (1.0, 0.3)
                                push = (40 - d)
                                if i == pin:
                                    b["x"] += ux * push
                                    b["y"] += uy * push
                                elif j == pin:
                                    a["x"] -= ux * push
                                    a["y"] -= uy * push
                                else:
                                    a["x"] -= ux * push / 2
                                    a["y"] -= uy * push / 2
                                    b["x"] += ux * push / 2
                                    b["y"] += uy * push / 2
                                moved = True
                    if not moved:
                        break
                for s2 in systems:
                    s2["x"] = round(min(max(s2["x"], 30), 970))
                    s2["y"] = round(min(max(s2["y"], 30), 645))
                edges = set()
                for sid, v in rows:
                    for g2 in v[5]:
                        if g2 in idx:
                            edges.add((min(idx[sid], idx[g2]),
                                       max(idx[sid], idx[g2])))
                # Richtungspfeil NUR bei echter Bewegung: >=2 verschiedene Systeme
                # binnen 45 min und <=4 Spruenge, sonst gilt "stationaer".
                arrows = []
                for p in self.packs.values():
                    if not self._visible(p) or self._status(p, now) == "inaktiv":
                        continue
                    seq = [(s, t) for s, t in p["systems"] if s in idx]
                    if len(seq) >= 2:
                        (s1, t1), (s2, t2) = seq[-2], seq[-1]
                        if s1 != s2 and t2 - t1 <= 2700 and s2 in self._bfs(s1, 4):
                            a, b = systems[idx[s1]], systems[idx[s2]]
                            arrows.append({"x1": a["x"], "y1": a["y"],
                                           "x2": b["x"], "y2": b["y"]})
                # Kill-Spuren: die Systemfolge jedes sichtbaren Rudels als Pfad
                # (nur Punkte im Anzeige-Ausschnitt; die Spur "betritt" die Karte,
                # sobald das Rudel in die Nachbarschaft kommt).
                trails = []
                for p in self.packs.values():
                    if not self._visible(p) or self._status(p, now) == "inaktiv":
                        continue
                    pts = [{"x": systems[idx[s]]["x"], "y": systems[idx[s]]["y"],
                            "age": int(now - t)}
                           for s, t in p["systems"] if s in idx]
                    if pts:
                        trails.append({"label": self._label(p), "pts": pts})
                out["maps"].append({"region": CONFIG.get("pack_center") or "?",
                                    "systems": systems, "edges": sorted(edges),
                                    "arrows": arrows, "trails": trails,
                                    "depth": depth})
        return out

    # ---- Lokale Anflug-Simulation (nur sim_mode, wie der Missions-Simulator) --
    def sim_run(self):
        """Demo: eine Gank-Flotte naehert sich ueber bis zu 20 Systeme dem
        eigenen Standort. Kills sind sim-markiert; am Ende 'spricht' der
        Rudel-Kopf im eigenen Local und loest den ECHTEN Rot-Alarm-Pfad aus."""
        if getattr(self, "sim_on", False) or not self.sysrow:
            return
        self.sim_on = True
        try:
            target_name = None
            with ingest.lock:
                for s in ingest.sessions.values():
                    if s.system:
                        target_name = s.system
            name2id = {v[1]: sid for sid, v in self.sysrow.items() if v[1]}
            tid = (name2id.get(target_name) or name2id.get("Gisleres")
                   or name2id.get("Uedama")
                   or (next(iter(name2id.values())) if name2id else None))
            if not tid:
                log_error("CN-PACK-03", "sim_run", "kein Zielsystem in der Karte")
                return
            # Anflug-Route: BFS vom Ziel nach aussen, tiefsten Ast nehmen,
            # dann umdrehen -> die Flotte kommt von weit draussen auf dich zu.
            prev = {tid: None}
            frontier, order = [tid], [tid]
            while frontier:
                nxt = []
                for sy in frontier:
                    row = self.sysrow.get(sy)
                    for g in (row[5] if row else []):
                        if g in self.sysrow and g not in prev:
                            prev[g] = sy
                            nxt.append(g)
                            order.append(g)
                frontier = nxt
            path, cur = [], order[-1]
            while cur is not None:
                path.append(cur)
                cur = prev[cur]
            path = path[-20:] if len(path) > 20 else path      # ... -> Ziel
            chars = [999100101, 999100102, 999100103, 999100104]
            corp = 998100001
            self.names[corp] = "SIM Wolfsrudel"
            for i, c in enumerate(chars):
                self.names[c] = f"SIM Ganker {i + 1}"
            kid = 990000000 + int(time.time()) % 900000
            for sid in path:
                if not self.enabled() or not self.sim_on:
                    return
                kid += 1
                km = {"killmail_id": kid,
                      "killmail_time": datetime.now(timezone.utc).strftime(
                          "%Y-%m-%dT%H:%M:%SZ"),
                      "solar_system_id": sid,
                      "attackers": [{"character_id": c, "corporation_id": corp,
                                     "ship_type_id": 16240} for c in chars],
                      "victim": {"ship_type_id": 17478},
                      "zkb": {"npc": False, "totalValue": 38000000}}
                self._ingest(km, "sim")
                now = time.time()
                self._start_info(now)
                self._alarms(now)
                time.sleep(7)
            # Finale: Rudel-Kopf erscheint als Local-Sprecher am Zielsystem.
            nm = self.names[chars[0]]
            with DB_LOCK:
                DB.execute("INSERT OR REPLACE INTO threat VALUES(?,?,?)",
                           (nm, json.dumps({"id": chars[0], "corp": "SIM Wolfsrudel",
                                            "level": "red", "kills": 40, "losses": 2,
                                            "danger": 90, "sec": -2.0,
                                            "miner_kills": 12, "recent_kills": 15}),
                            time.time()))
                DB.commit()
            chatwatch.speakers[nm.lower()] = {
                "name": nm, "system": (self.sysrow.get(tid) or (None, "?"))[1],
                "ts": time.time()}
            self._alarms(time.time())
        except Exception as e:
            log_error("CN-PACK-03", "sim_run", e)
        finally:
            self.sim_on = False

    def recenter(self, name):
        """Beobachtetes System manuell setzen: Blase + Cluster neu aufbauen.
        Liefert False, wenn das System nicht in der Sternenkarte existiert."""
        emap = load_json("eve_map.json", None) or {}
        names = {v[0] for v in (emap.get("systems") or {}).values()}
        if name not in names:
            return False
        with CONFIG_LOCK:
            CONFIG["pack_center"] = name
        save_config()
        with self.lock:
            self.packs.clear()
            self.member_index.clear()
            self.heat.clear()
            self.alerted.clear()
            self.near_alerted.clear()
            self.info_alerted.clear()
        self._seen.clear()
        self.last_kill_ts = 0
        self.recent.clear()
        self.sysrow = {}          # run()-Schleife baut die Blase neu auf
        self.dist = {}
        self.mode = "laden"
        return True

    def sim_reset(self):
        """Alle Sim-Spuren entfernen und die Cluster aus den echten Kills
        deterministisch neu aufbauen."""
        self.sim_on = False
        with DB_LOCK:
            DB.execute("DELETE FROM pack_kills WHERE sim=1")
            DB.execute("DELETE FROM threat WHERE name LIKE 'SIM Ganker%'")
            DB.commit()
        for k in [k for k in list(chatwatch.speakers) if k.startswith("sim ganker")]:
            chatwatch.speakers.pop(k, None)
        with self.lock:
            self.packs.clear()
            self.member_index.clear()
            self.heat.clear()
            self.alerted.clear()
            self.near_alerted.clear()
            self.info_alerted.clear()
        self._seen.clear()
        self.last_kill_ts = 0
        with DB_LOCK:
            rows = DB.execute("SELECT kill_id,ts,system_id,score,attackers "
                              "FROM pack_kills WHERE ts>? AND sim=0 ORDER BY ts",
                              (time.time() - 86400,)).fetchall()
        for kid, ts, sysid, score, aj in rows:
            self._seen.add(kid)
            self._cluster(kid, ts, sysid, score, json.loads(aj or "[]"))
            self.last_kill_ts = max(self.last_kill_ts, ts)

    # ---- Hauptschleife ----------------------------------------------------
    def run(self):
        time.sleep(8)
        while True:
            try:
                if not self.enabled():
                    self.mode = "aus"
                    time.sleep(20)
                    continue
                if not self.sysrow or any(v[1] is None for v in self.sysrow.values()):
                    self.mode = "laden"
                    self._load_map()
                    if not self.sysrow:
                        time.sleep(20)     # noch kein eigenes System bekannt
                        continue
                    # Cluster deterministisch aus den Roh-Kills der letzten 24h
                    with DB_LOCK:
                        rows = DB.execute(
                            "SELECT kill_id,ts,system_id,score,attackers FROM pack_kills "
                            "WHERE ts>? AND sim=0 ORDER BY ts", (time.time() - 86400,)).fetchall()
                    for kid, ts, sysid, score, aj in rows:
                        self._seen.add(kid)
                        if sysid not in self.sysrow:
                            continue           # Kill aus frueherer Regions-Wahl
                        self._cluster(kid, ts, sysid, score, json.loads(aj or "[]"))
                        self.last_kill_ts = max(self.last_kill_ts, ts)
                    self._zkill()
                    self._resolve_names()
                    self._start_info(time.time())
                    self.mode = "live"
                if self.mode in ("live", "tot"):
                    try:
                        data = self._get(KMSTREAM + self._queue(), timeout=70)
                        self._last200 = time.time()
                        self._fails = 0
                        self.mode = "live"
                        for km in (data if isinstance(data, list) else []):
                            self._ingest(km, "poll")
                    except Exception:
                        self._fails += 1
                        time.sleep(min(5 * 2 ** min(self._fails, 4), 60))
                    if self._fails >= 5 or time.time() - self._last200 > 300:
                        self.mode = "fallback"
                        self._probe = (0, 0.0)
                else:                       # fallback: zKill stuendlich + Proben
                    self._zkill(3600)
                    ok, last = self._probe
                    if time.time() - last >= 600:
                        try:
                            data = self._get(KMSTREAM + self._queue(), timeout=70)
                            ok += 1
                            for km in (data if isinstance(data, list) else []):
                                self._ingest(km, "poll")
                            if ok >= 2:
                                self.mode = "live"
                                self._fails = 0
                                self._last200 = time.time()
                        except Exception:
                            ok = 0
                        self._probe = (ok, time.time())
                    time.sleep(30)
                now = time.time()
                # Folge-Modus: Blase wandert (gedrosselt) mit dem eigenen Standort.
                if CONFIG.get("pack_follow"):
                    own = self._own_name()
                    if (own and own != CONFIG.get("pack_center")
                            and now - getattr(self, "_recenter_ts", 0) > 120):
                        self._recenter_ts = now
                        self.recenter(own)
                        continue
                self._resolve_names()
                self._alarms(now)
                self._start_info(now)
                self._prune(now)
            except Exception as e:
                log_error("CN-PACK-03", "PackIntel.run", e)
                time.sleep(30)


ingest = Ingest()
chatwatch = ChatWatch()
prices = Prices()
esi = Esi()
threat = ThreatIntel()
clipwatch = ClipWatch()
serverstatus = ServerStatus()
danger = SystemDanger()
packintel = PackIntel()


# ---------------------------------------------------------------- Abfragen
def ore_value(ore, units, pm):
    """ISK und Volumen eines Erz-Postens. Bewertet wird zum Preis der
    komprimierten Variante (Komprimieren ist 1:1 in Stück), denn das ist der
    Wert, der beim Verkauf wirklich ankommt. Gibt es keine komprimierte
    Variante oder keinen Preis dafür, gilt der Rohpreis. Volumen immer vom Rohtyp."""
    if not ore or not isinstance(ore, str):
        return 0.0, 0.0
    t = ORE_TYPES.get(ore, {})
    comp = ORE_TYPES.get("Compressed " + ore)
    price = pm.get(comp["typeID"]) if comp else None
    if price is None:
        price = pm.get(t.get("typeID"), 0.0)
    return units * price, units * t.get("volume", 0.0)


def refine_value(ore, units, yield_frac, pm):
    """ISK, wenn man 'units' des Erzes raffiniert: Mineral-Mengen aus der SDE-
    Tabelle (pro Batch von 'portion' Einheiten) mal Ausbeute mal Jita-Buy-Preis.
    Kompression aendert die Mineralien nicht, daher gilt dieselbe Tabelle."""
    r = (ORE_REFINE.get("refine") or {}).get(ore)
    if not r or not units:
        return 0.0
    portion = r.get("portion") or 100
    batches = units / portion
    tot = 0.0
    for o in r.get("out", []):
        tot += o["qty"] * batches * yield_frac * pm.get(o["tid"], (0, 0))[0]
    return tot


def query_ore_advisor(region):
    """Verwertungs-Berater: fuer den gesamten GELAGERTEN Erz-Bestand (Stationen)
    drei Wege gegenuebergestellt, je fuer den gewaehlten Hub: roh verkaufen,
    komprimiert verkaufen (1:1 Stueck, nur Volumen kleiner), raffinieren+Mineralien
    verkaufen. Ausbeute aus den echten Reprocessing-Skills (bester Char), NPC-50%-Basis."""
    # Bestand je Roh-Erz aggregieren (komprimiert -> Roh, 1:1 in Stueck).
    units = {}
    for nm, c in ((CONFIG.get("esi") or {}).get("chars", {})).items():
        v = c.get("vault") or {}
        for l in v.get("locs", []):
            if 30000000 <= (l.get("loc_id") or 0) < 32000000:   # im Schiff, kein Bestand
                continue
            for o in (l.get("ores") or []):
                key = re.sub(r"^(Batch )?Compressed ", "", o["ore"])
                units[key] = units.get(key, 0) + o["units"]
    if not units:
        return None
    # Beste Reprocessing-Ausbeute ueber die verbundenen Chars.
    yields = [(c.get("reprocess"), nm) for nm, c in
              ((CONFIG.get("esi") or {}).get("chars", {})).items() if c.get("reprocess")]
    yfrac, ychar = (max(yields) if yields else (0.50, None))
    # Preise fuer Roh, Komprimiert und alle Mineralien in einem Abruf.
    tids = set()
    for ore in units:
        t = ORE_TYPES.get(ore)
        if t:
            tids.add(t["typeID"])
        comp = ORE_TYPES.get("Compressed " + ore)
        if comp:
            tids.add(comp["typeID"])
    for o_ in ((ORE_REFINE.get("refine") or {}).values()):
        for m in o_.get("out", []):
            tids.add(m["tid"])
    pm = hub_prices(str(region), tids, prefer_esi=True) if tids else {}
    rows = []
    t_raw = t_comp = t_ref = 0.0
    for ore, u in units.items():
        t = ORE_TYPES.get(ore, {})
        comp = ORE_TYPES.get("Compressed " + ore)
        raw = u * pm.get(t.get("typeID"), (0, 0))[0]
        cmp_ = u * pm.get(comp["typeID"], (0, 0))[0] if comp else 0.0
        ref = refine_value(ore, u, yfrac, pm)
        best = max((("raw", raw), ("comp", cmp_), ("refine", ref)), key=lambda x: x[1])[0]
        t_raw += raw
        t_comp += cmp_
        t_ref += ref
        rows.append({"ore": ore, "units": u, "raw": round(raw), "comp": round(cmp_),
                     "refine": round(ref), "best": best})
    rows.sort(key=lambda r: -max(r["raw"], r["comp"], r["refine"]))
    tot = {"raw": round(t_raw), "comp": round(t_comp), "refine": round(t_ref)}
    overall = max(tot, key=tot.get)
    return {"hub": REGIONS.get(str(region), str(region)), "yield": yfrac,
            "yield_char": ychar, "totals": tot, "best": overall, "rows": rows}


def baseline_filter(rows):
    b_day = meta_get("baseline_day")
    if not b_day:
        return list(rows)
    with DB_LOCK:
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
    with DB_LOCK:
        rows = DB.execute(q, args).fetchall()
    return baseline_filter(rows)


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
            listed = False
            try:
                n = sum(1 for f in p.iterdir() if CHAR_FILE_RE.match(f.name))
                listed = True
            except OSError as e:
                log_error("CN-LOG-04", "log_dir_status", e)
            # "keine Gamelogs" nur melden, wenn das Auflisten auch geklappt hat —
            # sonst steht neben dem echten Fehler (CN-LOG-04) eine falsche Meldung.
            if listed and n == 0:
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
        # Flotten-Kompression: was ueber den Kompressionsdienst dieses (Booster-)
        # Schiffs lief, je Pilot aggregiert (auch fremde Flottenmitglieder). Wert
        # ueber die komprimierte Variante, wie beim eigenen Erz.
        fleet_comp = []
        for pname, pores in s.fleet_compress.items():   # NICHT 'ores' (das ist oben die Erz-Liste!)
            fu = fm3 = fisk = 0.0
            for oname, ounits in pores.items():
                i, v = ore_value(oname, ounits, pm)
                fu += ounits; fm3 += v; fisk += i
            fleet_comp.append({"name": pname, "units": round(fu),
                               "m3": round(fm3), "isk": round(fisk)})
        fleet_comp.sort(key=lambda k: -k["m3"])
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
            rem = max(0.0, hw_cfg.get("units", 0.0)
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
        # Echtes Command Ship (Orca/Porpoise/Rorqual) am Steuer? Booster/Kompressor,
        # kein reiner Miner -> gar keine Mining-Nörgel-Warnungen (auch keine Drohnen-
        # Idle-Warnung, die feuert sonst wenn er die Drohnen einzieht).
        is_cmd = (((esi_char or {}).get("ship_type_id") in DRONE_ONLY_SHIP_IDS)
                  or any(n in _shipname for n in DRONE_ONLY_SHIP_NAMES))
        drone_only = (is_cmd or s.core_on())
        chars.append({
            "heavy_water": hw,
            "active": active,
            "role": (CONFIG.get("roles") or {}).get(s.name, ""),
            "portrait": portrait_url(s.name),
            "esi_linked": esi_char is not None,
            "ship": (esi_char or {}).get("ship"),
            # Command Ship (Orca/Porpoise/Rorqual) am Steuer? Nur dann macht der
            # Flotten-Block Sinn. NUR ueber den echten Schiffstyp/-namen, NICHT ueber
            # drone_only (das ist auch bei Drohnen-Mining/aktivem Kern True und wuerde
            # z.B. einen komprimierenden Hulk faelschlich als Command Ship markieren).
            "command_ship": is_cmd,
            "wallet": (esi_char or {}).get("wallet"),
            "cargo": (esi_char or {}).get("cargo"),
            # ESI-verifizierte Mining-Daten (nur wenn neue Scopes erteilt)
            "esi_mining": bool((esi_char or {}).get("esi_mining")),
            "mined_30d": (esi_char or {}).get("mined_30d"),
            "skill_bonus": (esi_char or {}).get("skill_bonus"),
            "trips": s.trips,
            "compressed": comp, "fleet_compress": fleet_comp, "tool_warns": s.tool_warns(),
            "lasers_off": [] if drone_only else [{"tool": t, "since": int(i["since"]),
                            "before": round(i["before"] or 0, 1)}  # m³/min vor dem Stopp
                           for t, i in sorted(s.lasers_off.items())],
            # Bei Command Ships / Drohnen-Boostern (Orca/Porpoise/Rorqual, aktiver
            # Kern) NICHT die generische "Abbaurate runter"-Warnung zeigen — die
            # ergibt dort keinen Sinn (kein reiner Miner). Wie schon bei laser_stalled.
            "rate_low": None if drone_only else (lambda rs: round(100 * rs[1] / rs[0])
                         if rs and 0 < rs[1] < 0.55 * rs[0] else None)(s.rate_status()),
            "cargo_full": s.cargo_full and (time.time() - s.cargo_ts) < 300,
            # Command Ships sind Booster, keine Drohnen-Miner: die Drohnen-Idle-
            # Warnung feuert dort nur, wenn er die Drohnen einzieht -> ausblenden.
            "drones_idle": False if is_cmd else s.drones_idle(),
            "laser_stalled": False if drone_only else s.laser_stalled(),
            "hold_isk": round(hold_isk), "hold_m3": round(hold_m3),
            "hold_prices": hold_prices,
            "mine_idle": round(time.time() - s.last_ore_ts) if s.last_ore_ts else None,
            "idle_thr": round(s.idle_threshold(int(CONFIG.get("idle_warn", 240) or 0))),
            "name": s.name, "session_min": round(mins),
            "system": s.system or chatwatch.systems.get(s.char_id, "?"),
            "danger": danger.for_system(s.system or chatwatch.systems.get(s.char_id)),
            "ores": ores, "m3": round(m3), "ore_isk": round(ore_isk),
            # Tatsaechlicher Stillstand-Verlust dieser Session (kumuliert), zum
            # ISK/m³-Schnitt der Session bewertet.
            "lost_isk": round(s.lost_m3 * (ore_isk / m3)) if m3 > 0 else 0,
            # Pausiert der Verlustzaehler gerade? (angedockt/Warp oder kein Erz in 3 min)
            # Dann ist die Zahl eingefroren, nicht steigend -> in der UI so kennzeichnen.
            "lost_paused": bool(s.traveling) or s.last_ore_ts is None
                           or (time.time() - s.last_ore_ts) > 180,
            "m3h": round(m3 / mins * 60), "bounty": s.bounty, "kills": s.kills,
            "total_isk": round(ore_isk + s.bounty),
            "dmg_out": s.dmg_out, "dmg_in": s.dmg_in,
            "dps_out": s.dps(s.win_out), "dps_in": s.dps(s.win_in),
            "depleted": s.depleted,
            "weapons": sorted(s.weapons.items(), key=lambda x: -x[1])[:6],
            # Volle Gegnerliste (bis 60), damit z. B. Abyss-Runs ohne Bounty alle
            # bekaempften Typen zeigen. enemy_types = Anzahl verschiedener Gegner,
            # die einzige ehrlich belegbare "Kill"-naehe Zahl (EVE loggt keine Tode).
            "top_targets": sorted(s.targets.items(), key=lambda x: -x[1])[:60],
            "enemy_types": len(s.targets),
            "top_attackers": sorted(s.attackers.items(), key=lambda x: -x[1])[:12],
            "mission": detect_mission(sorted(s.targets.items(), key=lambda x: -x[1]),
                                      " ".join(chatwatch.dialogue(s.char_id, s.first_ts))),
            "faction": faction_info(sorted(s.targets.items(), key=lambda x: -x[1])),
            "npc": chatwatch.dialogue(s.char_id, s.first_ts)[-3:],
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


ESI_PRICE_CACHE = {}   # (region, tid) -> {"ts", "buy", "sell"}
ESI_PRICE_LOCK = threading.Lock()
# Zuletzt genutzte Preisquelle je Region, fuer die Anzeige "Preise: ESI/Jita" bzw.
# den Fuzzwork-Fallback. "esi" = frisches CCP-Orderbuch, "fuzzwork" = Ausweichquelle.
PRICE_SOURCE = {}


def esi_orderbook(region, ids):
    """Bestes Kauf-/Verkaufsgebot je Typ direkt aus dem CCP-Orderbuch, gefiltert
    auf das Hub-System. Oeffentlich (kein Login). Cache 5 min je (Region, Typ).
    Liefert nur, was ESI hergibt — der Aufrufer faellt fuer den Rest auf Fuzzwork
    zurueck. So gilt: frische ESI-Preise bevorzugt, sonst das alte System."""
    sysid = HUB_SYSTEMS.get(str(region))
    if not sysid:
        return {}
    out = {}
    now = time.time()
    for tid in ids:
        key = (str(region), int(tid))
        with ESI_PRICE_LOCK:
            e = ESI_PRICE_CACHE.get(key)
            if e and now - e["ts"] < ESI_PRICE_TTL:
                out[int(tid)] = (e["buy"], e["sell"])
                continue
        buy, sell, page, pages = 0.0, 0.0, 1, 1
        try:
            while page <= pages and page <= 10:
                url = (f"{ESI_BASE}/markets/{region}/orders/"
                       f"?type_id={int(tid)}&order_type=all&page={page}")
                req = urllib.request.Request(url, headers={"User-Agent": ESI_UA})
                with urllib.request.urlopen(req, timeout=15) as r:
                    orders = json.loads(r.read())
                    pages = int(r.headers.get("X-Pages") or 1)
                for o in orders:
                    if o.get("system_id") != sysid:
                        continue
                    p = float(o.get("price") or 0)
                    if o.get("is_buy_order"):
                        if p > buy:
                            buy = p
                    elif sell == 0.0 or p < sell:
                        sell = p
                page += 1
        except Exception:
            continue   # dieser Typ nicht ueber ESI -> Aufrufer nimmt Fuzzwork
        with ESI_PRICE_LOCK:
            ESI_PRICE_CACHE[key] = {"ts": now, "buy": buy, "sell": sell}
        out[int(tid)] = (buy, sell)
    return out


def fuzzwork_prices(region, ids):
    """Buy/Sell aus der Fuzzwork-Aggregation (eine Anfrage fuer viele Typen)."""
    url = (f"https://market.fuzzwork.co.uk/aggregates/?region={region}"
           f"&types={','.join(map(str, sorted(ids)))}")
    with urllib.request.urlopen(url, timeout=15) as r:
        data = json.load(r)
    return {int(k): (float(v["buy"]["max"]), float(v["sell"]["min"]))
            for k, v in data.items()}


def hub_prices(region, ids, prefer_esi=False):
    """Buy/Sell-Preise für die angefragten Typen in einer Region, 15 min Cache.
    Mit prefer_esi=True zuerst das frische CCP-Orderbuch (ESI), fuer alles was ESI
    nicht liefert Fuzzwork als Fallback. Ohne prefer_esi bleibt es bei Fuzzwork
    (schnelle Sammelabfrage, z.B. fuer den Mehr-Hub-Vergleich im Rechner)."""
    with CALC_LOCK:
        e = CALC_CACHE.get(region)
        if e and time.time() - e["ts"] < PRICE_REFRESH and ids <= set(e["prices"]):
            return dict(e["prices"])
    fetched = {}
    if prefer_esi:
        try:
            fetched = esi_orderbook(region, ids)
        except Exception:
            fetched = {}
    PRICE_SOURCE[str(region)] = "esi" if (prefer_esi and fetched) else "fuzzwork"
    result = dict(fetched)
    # Jeden Typ ergaenzen, bei dem ESI eine Seite (oder beide) mit 0 liefert:
    # sonst wuerde z.B. ein Item mit Buy-Orders aber ohne Sell-Order faelschlich
    # Sell=0 zeigen, obwohl Fuzzwork einen Sell-Preis kennt.
    incomplete = {t for t in ids
                  if result.get(t, (0.0, 0.0))[0] == 0 or result.get(t, (0.0, 0.0))[1] == 0}
    if incomplete:
        try:
            fz = fuzzwork_prices(region, incomplete)
            for t in incomplete:
                eb, es = result.get(t, (0.0, 0.0))
                fb, fs = fz.get(t, (0.0, 0.0))
                # ESI-Seite bevorzugen, nur die fehlende (0) Seite aus Fuzzwork.
                result[t] = (eb or fb, es or fs)
        except Exception:
            if not result:
                raise
    with CALC_LOCK:
        merged = CALC_CACHE.get(region, {}).get("prices", {})
        merged.update(result)
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
            # Case-insensitiv indexieren: ESI liefert den kanonischen Namen
            # ("Tritanium"), der Nutzer tippt evtl. "tritanium" -> sonst wird 0
            # gecacht und das Item gilt dauerhaft als unbekannt.
            found = {t["name"].lower(): t["id"] for t in data.get("inventory_types", [])}
        except Exception as e:
            log_error("CN-NET-01", "resolve_item_ids", e)
        with DB_LOCK:
            for n in batch:
                tid = found.get(n.lower())
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


def market_item(name):
    """Einzelnes Item per exaktem Namen suchen und Preise ueber alle Handelshubs
    zeigen. Namen loest ESI (/universe/ids/, gross-/kleinschreibungs-egal) auf,
    Preise kommen aus dem frischen CCP-Orderbuch (Fuzzwork nur als Fallback)."""
    name = (name or "").strip()
    if not name:
        return {"ok": False, "msg": "Bitte einen Item-Namen eingeben."}
    tid, canon = None, name
    try:
        req = urllib.request.Request(
            ESI_BASE + "/universe/ids/", data=json.dumps([name]).encode(),
            headers={"Content-Type": "application/json", "User-Agent": ESI_UA})
        with urllib.request.urlopen(req, timeout=15) as r:
            data = json.loads(r.read())
        for t in data.get("inventory_types", []):
            tid, canon = t["id"], t["name"]
            break
    except Exception:
        return {"ok": False, "msg": "Marktabfrage nicht möglich (keine Verbindung?)."}
    if not tid:
        return {"ok": False,
                "msg": f"„{name}“ nicht gefunden. Bitte den Item-Namen genau wie im Spiel schreiben."}
    hubs = {}
    for rid, rname in REGIONS.items():
        try:
            b, s = hub_prices(rid, {tid}, prefer_esi=True).get(tid, (0, 0))
            hubs[rid] = {"name": rname, "buy": round(b, 2), "sell": round(s, 2)}
        except Exception:
            hubs[rid] = {"name": rname, "error": True}
    return {"ok": True, "type_id": tid, "name": canon, "hubs": hubs,
            "src": PRICE_SOURCE.get("10000002", "fuzzwork")}


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
    with DB_LOCK:
        play_rows = DB.execute(
            "SELECT name, char_name, first_ts, last_ts FROM files "
            "WHERE first_ts IS NOT NULL AND skipped=0").fetchall()
    for name, cname, first_ts, last_ts in play_rows:
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
        # timedelta wirft bei riesigen Werten OverflowError (winziger Schnitt +
        # grosses Ziel). Nur bei plausibler Reichweite ein Datum berechnen.
        eta_date = None
        if eta_days is not None and 0 <= eta_days < 3650000:
            try:
                eta_date = (datetime.now() + timedelta(days=eta_days)).strftime("%Y-%m-%d")
            except (OverflowError, ValueError):
                eta_date = None
        goal_info = {"isk": goal["isk"], "deadline": goal.get("deadline"),
                     "current": total["total_isk"],
                     "pct": round(100 * total["total_isk"] / goal["isk"], 1),
                     "avg7": round(avg), "eta_days": eta_days, "eta_date": eta_date}
    # Durch Stillstand/Drosselung entgangenes ISK (beim Docken je Trip erfasst)
    lost_isk = sum(v for _, _, _, kind, _, v in all_rows(kinds=["lost"]))
    return {"weapons": sorted(weapons.items(), key=lambda x: -x[1])[:10],
            "pvp": pvp_list, "efficiency": eff_list, "playtime": play_list,
            "goal": goal_info, "depleted_total": total["depleted"],
            "lost_isk": round(lost_isk), "compression": compression_periods()}


def state_info():
    return {"region": CONFIG["region"], "regions": REGIONS, "mode": CONFIG["mode"],
            # Lokaler Demo-Schalter: blendet den "Simulation"-Play-Button im
            # Missionen-Tab ein. Steht nur in der lokalen config.json (wird nie
            # mit ausgeliefert), fuer Nutzer ohne das Flag existiert der Button nicht.
            "sim": bool(CONFIG.get("sim_mode")),
            "baseline_day": meta_get("baseline_day"), "log_dir": CONFIG["log_dir"],
            "idle_warn": int(CONFIG.get("idle_warn", 240) or 0),
            "clip_watch": bool(CONFIG.get("clip_watch")),
            "count_me": bool(CONFIG.get("count_me", True)),
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
            "price_src": PRICE_SOURCE.get(str(CONFIG["region"]), "fuzzwork"),
            "watchlist": CONFIG.get("watchlist", []), "goal": CONFIG.get("goal"),
            "esi": {"client_id": (CONFIG.get("esi") or {}).get("client_id", ""),
                    "cb": esi.redirect_uri(),
                    "chars": [dict({"name": n, "status": esi.status.get(n, "warte auf Abgleich …"),
                                    "ship": c.get("ship"), "wallet": c.get("wallet")},
                                   **esi.char_health(n, c))
                              for n, c in (CONFIG.get("esi") or {}).get("chars", {}).items()]},
            "server": serverstatus.state,
            "alerts": alerts.list()}


def query_mission_history(limit=40):
    """Einzelne Missionen (aus den Gamelogs, an Undock-Grenzen getrennt), neueste
    zuerst, inkl. vom Nutzer eingefügtem Loot."""
    # Mehr Zeilen holen als angezeigt werden, weil gleich Belt-Ratten-Sessions
    # herausgefiltert werden (Mining-Trips, in denen nur die Flotten-Bounty ein
    # paar Gürtel-Ratten enthält). Ohne den Puffer bliebe die Liste sonst leer.
    with DB_LOCK:
        rows = DB.execute(
            """SELECT mid,char,start_ts,end_ts,system,dmg_out,dmg_in,kills,bounty,
                      hits,miss_out,miss_in,weapons,enemies,loot_isk,loot_text,dialog,
                      char_id,ewar
               FROM missions ORDER BY start_ts DESC LIMIT ?""", (limit * 5,)).fetchall()
        # Verifizierte Missions-Belohnungen aus dem Wallet-Journal (Server-Wahrheit).
        # Jede wird gleich der Mission zugeordnet, die kurz davor endete.
        jrows = DB.execute(
            "SELECT char, ts, ref_type, amount FROM journal "
            "WHERE ref_type LIKE 'agent_mission%'").fetchall()
    # (mid, char, start, end) je Missionszeile fuer die Zuordnung unten.
    cand = [(x[0], x[1], x[2] or 0, x[3] or 0) for x in rows]
    verified = {}
    for jchar, jts, jref, jamt in jrows:
        best_mid, best_gap = None, None
        for mid_, mchar, mst, met in cand:
            if mchar != jchar or jts < mst - 300:
                continue
            gap = jts - (met or mst)           # Belohnung faellt nach Kampfende
            if -300 <= gap <= 3600 and (best_gap is None or abs(gap) < best_gap):
                best_gap, best_mid = abs(gap), mid_
        if best_mid is None:
            continue
        v = verified.setdefault(best_mid, {"reward": 0, "bonus": 0})
        if jref == "agent_mission_reward":
            v["reward"] += jamt or 0
        else:
            v["bonus"] += jamt or 0
    out = []
    for r in rows:
        if len(out) >= limit:
            break
        (mid, char, st, et, sysn, do, di, kills, bounty, hits, mo, mi,
         wj, ej, loot, loot_text, dialog, char_id, ewj) = r
        shots = (hits or 0) + (mo or 0)
        enemies = json.loads(ej or "[]")
        # Fehlt der gespeicherte Funk (aeltere Mission, oder Reingest lief vor dem
        # Chat-Watcher), aus dem heute im Speicher gehaltenen NPC-Funk nachfuellen.
        if not dialog and char_id:
            dialog = " ".join(chatwatch.dialogue(str(char_id), st or 0, et or None))[:2000]
        mission = detect_mission(enemies, dialog or "")
        # Belt-Ratten raus: eine echte Mission ist entweder erkannt, oder hat
        # spuerbaren eigenen Schaden (>5000), oder echte Bounty (>100k). Reine
        # Flotten-Bounty beim Mining (winziger/kein Schaden, Kleinst-Bounty von
        # Guertel-Ratten) faellt hier raus, das ist keine Mission.
        if not mission and (do or 0) < 5000 and (bounty or 0) < 100000:
            continue
        # NPC-Funk: bis zu 3 aussagekräftige Zeilen als Story-Schnipsel
        dlines = [d.strip() for d in re.split(r"(?<=[.!?])\s+", dialog or "") if len(d.strip()) > 12][:3]
        ver = verified.get(mid)
        vreward = round(ver["reward"]) if ver else None
        vbonus = round(ver["bonus"]) if ver else None
        out.append({
            "mid": mid, "char": char, "start": int(st or 0), "end": int(et or 0),
            "min": round(((et or 0) - (st or 0)) / 60), "system": sysn or "?",
            "dmg_out": do or 0, "dmg_in": di or 0, "kills": kills or 0,
            "bounty": round(bounty or 0), "hit": round(100 * hits / shots) if shots else None,
            "mission": mission, "npc": dlines, "faction": faction_info(enemies),
            "ewar": json.loads(ewj or "[]"),
            "reward": vreward, "bonus": vbonus,
            "weapons": json.loads(wj or "[]"), "enemies": enemies,
            "loot_isk": round(loot) if loot else None, "loot_text": loot_text or "",
            "total": round((bounty or 0) + (loot or 0) + (vreward or 0) + (vbonus or 0))})
    return out


def query_timelines():
    """Zeitachse/Verlauf je Charakter: chronologischer Strom aus Mining-Trips
    (events-Tabelle), Kampf-Episoden (missions) und ISK-Ereignissen (Wallet-Journal).
    Liefert die letzten 48 Stunden; das Frontend filtert zusaetzlich auf heute/Trip.
    trip_start je Char kommt aus der laufenden Live-Session."""
    now = time.time()
    midnight = datetime.now(timezone.utc).replace(hour=0, minute=0, second=0,
                                                  microsecond=0).timestamp()
    cut = now - 172800          # letzte 48 Stunden; Frontend filtert auf heute/Trip
    pm = prices.get(CONFIG["region"]) or {}
    per = {}   # char -> list of items

    def add(char, item):
        per.setdefault(char, []).append(item)

    with DB_LOCK:
        mrows = DB.execute(
            """SELECT char, start_ts, end_ts, system, kills, bounty, dmg_out, dmg_in,
                      enemies, ewar FROM missions WHERE start_ts>=?""", (cut,)).fetchall()
        erows = DB.execute(
            "SELECT char, ts, detail FROM events WHERE ts>=? AND kind='mine'", (cut,)).fetchall()
        jrows = DB.execute(
            "SELECT char, ts, ref_type, amount, party FROM journal WHERE ts>=? "
            "AND ref_type LIKE 'agent_mission%'", (cut,)).fetchall()

    for char, st, et, sysn, kills, bounty, do, di, ej, ewj in mrows:
        enemies = json.loads(ej or "[]")
        mission = detect_mission(enemies, "")
        # Belt-Ratten raus, wie in der Missions-Historie
        if not mission and (do or 0) < 5000 and (bounty or 0) < 100000:
            continue
        add(char, {"ts": int(st or 0), "kind": "combat",
                   "mission": mission, "faction": faction_info(enemies),
                   "kills": kills or 0, "bounty": round(bounty or 0),
                   "dmg_out": do or 0, "dmg_in": di or 0,
                   "min": round(((et or 0) - (st or 0)) / 60),
                   "sys": sysn or "?", "ewar": json.loads(ewj or "[]")})
    for char, ts, det in erows:
        try:
            d = json.loads(det or "{}")
        except Exception:
            d = {}
        # ISK jetzt mit aktuellen Preisen aus den gespeicherten Erz-Mengen
        ores = d.get("ores") or {}
        isk = sum(ore_value(o, u, pm)[0] for o, u in ores.items())
        add(char, {"ts": int(ts), "kind": "mine", "m3": d.get("m3", 0),
                   "isk": round(isk), "min": d.get("min", 0),
                   "ore": d.get("top"), "sys": d.get("sys", "?")})
    for char, ts, ref, amount, party in jrows:
        add(char, {"ts": int(ts),
                   "kind": "bonus" if ref == "agent_mission_time_bonus_reward" else "reward",
                   "amount": round(amount or 0), "agent": party or ""})

    trip = {}
    nowi = int(now)
    with ingest.lock:
        for s in ingest.sessions.values():
            if s.first_ts:
                trip[s.name] = int(s.first_ts)
            # Laufende Aktivitaet dieses Trips als "live"-Eintrag oben, damit der
            # Verlauf nicht leer wirkt, waehrend man gerade mint/kaempft (die
            # abgeschlossenen Episoden kommen erst beim Andocken/Missionsende).
            if not (s.last_event_ts and now - s.last_event_ts < 300):
                continue
            mins = max(1, round((now - (s.first_ts or now)) / 60))
            # Mining zuerst: ein Miner mit Flotten-Bounty (kills>0, aber dmg_out=0)
            # ist KEIN Kampf. Kampf nur bei echtem ausgeteiltem Schaden.
            if s.mining:
                vm3 = visk = 0.0
                top_ore, top_u = None, 0
                for ore, u in s.mining.items():
                    i, vv = ore_value(ore, u, pm)
                    visk += i
                    vm3 += vv
                    if u > top_u:
                        top_u, top_ore = u, ore
                if vm3 > 0:
                    add(s.name, {"ts": nowi, "kind": "live", "sub": "mine",
                                 "m3": round(vm3), "isk": round(visk), "min": mins,
                                 "ore": top_ore, "sys": s.system or "?"})
            elif s.dmg_out > 0:
                add(s.name, {"ts": nowi, "kind": "live", "sub": "combat",
                             "kills": s.kills, "bounty": round(s.bounty), "min": mins,
                             "sys": s.mission_system or s.system or "?",
                             "mission": detect_mission(
                                 sorted(s.targets.items(), key=lambda x: -x[1]), "")})
    chars = []
    for char, items in per.items():
        items.sort(key=lambda x: -x["ts"])
        chars.append({"char": char, "items": items[:80], "trip_start": trip.get(char)})
    chars.sort(key=lambda c: c["char"])
    return {"chars": chars, "day_start": int(midnight), "now": int(now)}


def query_profiles():
    """Spielstil-Radar je Charakter: 6 Achsen (Mining, Missionen, PvP, Kampfkraft,
    Industrie, Ertrag) ueber die letzten 30 Tage. Skaliert RELATIV zu deinen
    Chars (Achsen-Bestwert der Flotte = 100%), damit die Form den Spielstil-Mix
    zeigt und nicht von willkuerlichen Obergrenzen oder der Datenmenge abhaengt.
    Ertrag = erwirtschaftete ISK (Mining-Wert + Bounty + Missions-Belohnungen)."""
    now = time.time()
    pm = prices.get(CONFIG["region"]) or {}
    rows = all_rows(30, ("ore", "dmg_out", "pvp_in", "compressed", "bounty"))
    agg = {}

    def a(c):
        return agg.setdefault(c, {"mine": 0.0, "combat": 0.0, "pvp": 0.0,
                                  "industry": 0.0, "mine_isk": 0.0, "bounty": 0.0})
    for day, cid, cname, kind, key, val in rows:
        d = a(cname)
        v = val or 0
        if kind == "ore":
            d["mine"] += v * ORE_TYPES.get(key, {}).get("volume", 0.0)
            d["mine_isk"] += ore_value(key, v, pm)[0]
        elif kind == "dmg_out":
            d["combat"] += v
        elif kind == "pvp_in":
            d["pvp"] += v
        elif kind == "compressed":
            d["industry"] += v * ORE_TYPES.get(key, {}).get("volume", 0.0)
        elif kind == "bounty":
            d["bounty"] += v
    # Missionen: Anzahl + Belohnungs-ISK (Reward + Zeitbonus) aus dem Journal, 30d
    miss, miss_isk = {}, {}
    with DB_LOCK:
        jr = DB.execute("SELECT char, ref_type, amount FROM journal WHERE ts>=? "
                        "AND ref_type LIKE 'agent_mission%'", (now - 30 * 86400,)).fetchall()
    for c, ref, amount in jr:
        if ref == "agent_mission_reward":
            miss[c] = miss.get(c, 0) + 1
        miss_isk[c] = miss_isk.get(c, 0) + (amount or 0)
    order = ("mine", "missions", "pvp", "combat", "industry", "ertrag")
    raws = {}
    for c in set(agg) | set(miss) | set(miss_isk):
        d = agg.get(c, {"mine": 0, "combat": 0, "pvp": 0, "industry": 0, "mine_isk": 0, "bounty": 0})
        raws[c] = {"mine": d["mine"], "missions": miss.get(c, 0), "pvp": d["pvp"],
                   "combat": d["combat"], "industry": d["industry"],
                   "ertrag": d["mine_isk"] + d["bounty"] + miss_isk.get(c, 0)}
    # Achsen-Bestwert ueber alle Chars = 100%.
    axmax = {k: max([r[k] for r in raws.values()] + [0]) for k in order}
    # Steckbrief-Infos: Corp/Allianz/Sec aus dem Threat-Cache (zKill/ESI), Portrait/
    # Wallet/Schiff/Vault aus der ESI-Config, System live aus der Session.
    echars = (CONFIG.get("esi") or {}).get("chars", {})
    sysmap = {}
    with ingest.lock:
        for s in ingest.sessions.values():
            if s.system:
                sysmap[s.name] = s.system
    active = [c for c in raws if any(raws[c][k] for k in order)]
    threat.request(active)     # loest Corp/Allianz/Sec fuer die eigenen Chars auf (gecacht)
    out = []
    for c in active:
        raw = raws[c]
        axes = [{"key": k, "raw": round(raw[k]),
                 "value": round(100 * raw[k] / axmax[k]) if axmax[k] else 0} for k in order]
        ec = echars.get(c, {})
        cid = ec.get("char_id")
        prof = threat.cached(c) or {}
        sysn = sysmap.get(c) or (chatwatch.systems.get(str(cid)) if cid else None)
        out.append({"char": c, "axes": axes,
                    "portrait": portrait_url(c), "wallet": ec.get("wallet"),
                    "ship": ec.get("ship"), "sec": prof.get("sec"),
                    "corp": prof.get("corp"), "alliance": prof.get("alliance"),
                    "system": sysn or "?",
                    "ore_isk": (ec.get("vault") or {}).get("total_isk"),
                    "poll_ts": ec.get("poll_ts")})
    out.sort(key=lambda x: x["char"])
    return out


def query_vault():
    """Erz-Schatzkammer: Erz-Bestand aller ESI-verbundenen Chars (aus den Assets),
    Gesamtsumme (m³/ISK) plus Aufschluesselung je Char und Standort."""
    chars, tot_m3, tot_isk, oldest, soonest = [], 0, 0, None, None
    for nm, c in ((CONFIG.get("esi") or {}).get("chars", {})).items():
        v = c.get("vault")
        if not v:
            continue
        # Nur GELAGERTES Erz zeigen (Stationen/Strukturen). Erz, das gerade im
        # Mining-Schiff liegt, hat einen Sonnensystem-Standort (30000000-32000000)
        # und wird hier ausgeblendet — samt seiner Menge/ISK in den Summen.
        locs, cm3, cisk = [], 0, 0
        for l in v.get("locs", []):
            if 30000000 <= (l.get("loc_id") or 0) < 32000000:
                continue
            info = esi.loc_info(c, l["loc_id"])
            locs.append({**l, "name": info["name"], "icon": info.get("type_id")})
            cm3 += l.get("m3", 0)
            cisk += l.get("isk", 0)
        if not locs:                       # nur Erz im Schiff -> Char nicht listen
            continue
        tot_m3 += cm3
        tot_isk += cisk
        oldest = v["as_of"] if oldest is None else min(oldest, v.get("as_of") or oldest)
        if v.get("next"):
            soonest = v["next"] if soonest is None else min(soonest, v["next"])
        chars.append({"name": nm, "total_m3": round(cm3), "total_isk": round(cisk),
                      "locs": locs, "as_of": v.get("as_of"), "next": v.get("next")})
    chars.sort(key=lambda x: -x["total_isk"])
    return {"total_m3": round(tot_m3), "total_isk": round(tot_isk), "as_of": oldest,
            "next": soonest, "chars": chars}


def query_planeten():
    """Planetary Industry: Kolonien aller PI-verbundenen Chars. Liefert eine flache,
    nach Ablauf sortierte Extraktor-Liste (die 'was zuerst nachfuellen'-Tafel) plus
    die Kolonien je Char fuer die einklappbaren Bloecke, dazu Kennzahlen und die
    Chars, die den neuen Scope noch nicht erteilt haben."""
    now = time.time()
    chars, extractors, reconnect = [], [], []
    n_col = n_ex = n_soon = n_exp = 0
    total_isk = total_ext_isk = 0
    prodagg = {}
    oldest = soonest = None
    for nm, c in ((CONFIG.get("esi") or {}).get("chars", {})).items():
        if c.get("planets_scope") is False:
            reconnect.append(nm)
            continue
        p = c.get("planets")
        cols = (p or {}).get("cols") or []
        if not cols:
            continue
        oldest = p["as_of"] if oldest is None else min(oldest, p.get("as_of") or oldest)
        if p.get("next"):
            soonest = p["next"] if soonest is None else min(soonest, p["next"])
        for col in cols:
            n_col += 1
            for e in (col.get("extractors") or []):
                n_ex += 1
                exp = e.get("expiry")
                if not exp:
                    continue
                if exp <= now:
                    n_exp += 1
                elif exp - now <= 6 * 3600:
                    n_soon += 1
                extractors.append({"char": nm, "planet": col["planet"],
                                   "type": col.get("type"), "type_id": col.get("type_id"),
                                   "product": e.get("product"),
                                   "product_id": e.get("product_id"), "tier": e.get("tier"),
                                   "heads": e.get("heads"), "total": e.get("total"),
                                   "expiry": exp})
            # Fabrik-Produkte flottenweit aufsummieren (fuer den Gesamtausstoss)
            for pr in (col.get("products") or []):
                a = prodagg.setdefault(pr["name"], {"name": pr["name"], "tier": pr.get("tier"),
                                                    "type_id": pr.get("type_id"), "count": 0})
                a["count"] += pr.get("count", 1)
        cisk = sum(col.get("isk", 0) for col in cols)
        cext = sum(col.get("ext_isk", 0) for col in cols)
        total_isk += cisk
        total_ext_isk += cext
        chars.append({"name": nm, "cols": cols, "isk": cisk, "ext_isk": cext,
                      "as_of": p.get("as_of"), "next": p.get("next")})
    extractors.sort(key=lambda x: x.get("expiry") or 9e18)
    chars.sort(key=lambda x: x["name"])
    order = {"P0": 0, "P1": 1, "P2": 2, "P3": 3, "P4": 4}
    products = sorted(prodagg.values(), key=lambda p: (order.get(p.get("tier"), 9), p["name"]))
    return {"chars": chars, "extractors": extractors, "reconnect": reconnect,
            "as_of": oldest, "next": soonest, "n_char": len(chars),
            "n_col": n_col, "n_ex": n_ex, "n_soon": n_soon, "n_exp": n_exp,
            "total_isk": total_isk, "total_ext_isk": total_ext_isk, "products": products}


def query_missions():
    """Missions-Statistik aus dem Wallet-Journal: Tage, Quellen, Agenten, Chars.
    Bounties aus bekannten Mining-Systemen bleiben draussen (Belt-Ratten)."""
    mine_sys = CONFIG.get("mine_systems") or {}
    mine_ids = {i for i in mine_sys.values() if i}
    with DB_LOCK:
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
        # Nie cachen: sonst serviert der Browser bei einem Reload alte /data-
        # Antworten (z.B. alte Standort-Namen), obwohl der Server längst neue liefert.
        self.send_header("Cache-Control", "no-store, no-cache, must-revalidate")
        self.send_header("Pragma", "no-cache")
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
                data["intel_auto"] = {"ts": clipwatch.ts, "names": clipwatch.names,
                                      "fleets": chatwatch.fleet_groups()}
                data["blutspur"] = packintel.snapshot()
            elif view == "missionen":
                data["missions"] = query_missions()
                data["mission_log"] = query_mission_history()
                data["chars"] = snapshot_live()
            elif view == "vault":
                data["vault"] = query_vault()
                data["vault"]["advisor"] = query_ore_advisor(CONFIG["region"])
            elif view == "planeten":
                data["planeten"] = query_planeten()
            elif view == "timeline":
                data["timeline"] = query_timelines()
            elif view == "profil":
                data["profiles"] = query_profiles()
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
        elif action == "pack_cfg":
            # Blutspur-Radar konfigurieren (an/aus, Corp-Eskalation). Opt-in;
            # der PackIntel-Thread greift die Aenderung binnen ~20s auf.
            with CONFIG_LOCK:
                if "on" in body:
                    CONFIG["pack_radar"] = bool(body.get("on"))
                if "corp" in body:
                    CONFIG["pack_corp_alert"] = bool(body.get("corp"))
            save_config()
            ok = True
            if "follow" in body:
                with CONFIG_LOCK:
                    CONFIG["pack_follow"] = bool(body.get("follow"))
                save_config()
                if body.get("follow"):
                    own = packintel._own_name()
                    if own and own != CONFIG.get("pack_center"):
                        ok = packintel.recenter(own)
            if body.get("center"):
                with CONFIG_LOCK:
                    CONFIG["pack_follow"] = False
                ok = packintel.recenter(str(body.get("center")).strip())
            self._send(json.dumps({"ok": ok}))
            return
        elif action == "pack_sim_run" and CONFIG.get("sim_mode"):
            # Anflug-Demo starten (nur lokal, wie der Missions-Simulator).
            threading.Thread(target=packintel.sim_run, daemon=True).start()
            self._send(json.dumps({"ok": True}))
            return
        elif action == "pack_sim_reset" and CONFIG.get("sim_mode"):
            packintel.sim_reset()
            self._send(json.dumps({"ok": True}))
            return
        elif action == "pack_sim" and CONFIG.get("sim_mode"):
            # Nur lokal (sim_mode): synthetische Kills fuer die Gate-Drills.
            n = 0
            for km in (body.get("kills") or [])[:50]:
                if packintel._ingest(km, "sim"):
                    n += 1
            packintel._resolve_names()
            self._send(json.dumps({"ok": True, "ingested": n}))
            return
        elif action == "count_me":
            CONFIG["count_me"] = bool(body.get("on"))
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
            names = [str(n).strip() for n in (body.get("names") or [])][:200]
            names = [n for n in names if n]
            results = threat.request(names, prio=True)
            self._send(json.dumps({"ok": True, "results": results,
                                   "pending": threat.pending()}))
            return
        elif action == "market_suggest":
            self._send(json.dumps({"items": market_suggest(body.get("q") or "")}))
            return
        elif action == "market_item":
            self._send(json.dumps(market_item(body.get("name") or "")))
            return
        elif action == "ui_open":
            # Fenster im laufenden Client oeffnen (Markt-Detail oder Info).
            err = esi.ui_open(str(body.get("char") or ""),
                              str(body.get("kind") or ""), body.get("id"))
            self._send(json.dumps({"ok": err is None, "msg": err or "Im Client geöffnet."}))
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
            CONFIG["watchlist"] = [str(n).strip() for n in (body.get("names") or []) if str(n).strip()][:50]
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
.copyright{margin:14px 0;font-size:10px;line-height:1.5;color:var(--dim);text-align:justify}
.copyright b{color:var(--dim);letter-spacing:.5px}
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
.vinfo{background:var(--inset);border:1px solid var(--line);border-radius:8px;
 padding:8px 12px;margin:10px 0}
.vitog{color:var(--cyan);font-size:12px;cursor:pointer;user-select:none}
.vitxt p{margin:8px 0 0;font-size:13px;line-height:1.5}
.vitxt .vidata{color:var(--dim);font-size:12px}
html[data-skin=photon] .vinfo{border-radius:1px}
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
.alert.pi{border-color:var(--gold);color:var(--gold);font-weight:600}
.alert.pack{border-color:var(--red);color:var(--red);font-weight:600}
.alert.packinfo{border-color:var(--gold);color:var(--gold)}
.cardwarn{border:1px solid var(--gold);color:var(--gold);border-radius:7px;
padding:7px 10px;font-size:12px;font-weight:600;margin-bottom:8px;overflow:hidden}
.cardwarn.drone{border-color:var(--red);color:var(--red)}
.cardnote{border:1px solid var(--line);background:var(--inset);color:var(--dim);border-radius:7px;
padding:7px 10px;font-size:12px;line-height:1.5;margin:2px 0 8px}
.warnbadge{color:var(--gold);font-weight:600}
.warnbadge.drone{color:var(--red)}
.pill.upd{border-color:var(--gold);color:var(--gold);animation:updpulse 2.4s ease-in-out infinite}
@keyframes updpulse{0%,100%{box-shadow:0 0 0 rgba(232,198,69,0)}50%{box-shadow:0 0 9px rgba(232,198,69,.45)}}
#updBanner{display:none;margin:10px 0;padding:12px 16px;border:1px solid var(--gold);border-radius:8px;
background:rgba(232,198,69,.10);align-items:center;gap:14px;flex-wrap:wrap}
#updBanner:not([hidden]){display:flex}
#updBanner .ub-txt{flex:1;min-width:220px;font-size:14px;color:var(--txt)}
#updBanner .ub-txt b{color:var(--gold)}
#updBanner .ub-sub{display:block;font-size:12px;color:var(--dim);margin-top:2px}
#updBanner button{background:var(--gold);color:#1a1400;border:none;border-radius:6px;
padding:8px 16px;font-weight:600;cursor:pointer;font-size:13px}
#updBanner button:disabled{opacity:.6;cursor:default}
.pill.srv{cursor:default}
.pill.srv .dot{display:inline-block;width:7px;height:7px;border-radius:50%;margin-right:5px;vertical-align:middle}
.pill.srv.up .dot{background:var(--green);box-shadow:0 0 5px var(--green)}
.pill.srv.down .dot{background:var(--red);box-shadow:0 0 5px var(--red)}
.pill.srv.vip .dot{background:var(--gold);box-shadow:0 0 5px var(--gold)}
.pill.srv b{color:var(--txt);font-weight:600}
.laserok{float:right;border:1px solid var(--line);border-radius:20px;padding:1px 9px;
color:var(--dim);cursor:pointer;font-weight:400;margin-left:8px}
.laserok:hover{color:var(--txt);border-color:var(--txt)}
.hwset{cursor:pointer;opacity:.55}
.hwset:hover{opacity:1}
tr.lvl-red td{background:rgba(232,86,79,.10)}
tr.lvl-yellow td{background:rgba(228,179,76,.07)}
#intelTbl a{color:inherit}
#grid{display:grid;grid-template-columns:repeat(auto-fit,minmax(420px,1fr));gap:14px;align-items:start}
@media (max-width:900px){#grid{grid-template-columns:1fr}}
#hero:not(:empty){margin-bottom:14px}
.card.mfp{background:linear-gradient(135deg,var(--card),var(--inset));border-color:var(--line)}
.mfphead{display:flex;align-items:center;justify-content:space-between;gap:10px}
.mfptitle{font-size:12px;letter-spacing:.08em;text-transform:uppercase;color:var(--dim)}
.mfprank{font-size:12px;font-weight:700;padding:3px 10px;border-radius:20px;border:1px solid var(--line)}
.mfpmain{display:flex;align-items:baseline;gap:8px;flex-wrap:wrap;margin:8px 0 10px}
.mfpval{font-size:40px;font-weight:800;line-height:1}
.mfpunit{font-size:15px;color:var(--dim);font-weight:600}
.mfpsub{font-size:11px;color:var(--dim);margin-left:auto}
.mfpbarwrap{height:7px;background:var(--inset);border-radius:20px;overflow:hidden}
.mfpbar{height:100%;border-radius:20px;transition:width .6s ease}
.mfpval.gold,.mfprank.gold{color:var(--gold)} .mfpbar.gold{background:var(--gold)} .mfprank.gold{border-color:var(--gold)}
.mfpval.cyan,.mfprank.cyan{color:var(--cyan)} .mfpbar.cyan{background:var(--cyan)} .mfprank.cyan{border-color:var(--cyan)}
.mfpval.green,.mfprank.green{color:var(--green)} .mfpbar.green{background:var(--green)} .mfprank.green{border-color:var(--green)}
.mfpval.dim,.mfprank.dim{color:var(--dim)} .mfpbar.dim{background:var(--dim)}
.mfpver{margin-top:9px;font-size:12px;color:var(--green)}
.mfpver b{color:var(--white)}
.fleetcomp{width:100%;border-collapse:collapse;margin-top:5px;font-size:12.5px}
.fleetcomp td{padding:3px 0;border-top:1px solid var(--line)}
.fleetcomp td:first-child{color:var(--white)}
.mfphr{display:flex;align-items:center;gap:10px}
.mfpshare{background:var(--inset);border:1px solid var(--line);color:var(--dim);font-size:12px;
  font-weight:600;padding:4px 11px;border-radius:20px;cursor:pointer;font-family:inherit}
.mfpshare:hover{color:var(--cyan);border-color:var(--cyan)}
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
.mtag{font-size:12px;color:var(--gold)}
.mtag.mtired{color:var(--dim);font-style:italic}
.mconf{color:var(--dim);font-weight:600;font-size:11px}
.ftag{display:flex;flex-wrap:wrap;gap:6px 10px;align-items:center;margin-top:8px;font-size:12px}
.fbadge{font-weight:700;color:var(--cyan)}
.fshoot b{color:var(--gold)} .ftank b{color:#ff9b57}
.fdim{color:var(--dim);font-size:11px}
.falpha{font-size:9px;font-weight:700;letter-spacing:.06em;text-transform:uppercase;color:var(--bg);background:var(--gold);border-radius:3px;padding:1px 5px}
.vreward{margin-top:6px;color:var(--green)}
.alphabanner{background:rgba(200,160,60,.1);border:1px solid var(--gold);border-radius:10px;padding:9px 13px;font-size:12px;color:var(--txt);line-height:1.5}
.btn.simon{border-color:var(--red);color:var(--red)}
.tlwins{margin-left:8px}
.tlchip{display:inline-block;font-size:11px;padding:2px 9px;margin-left:4px;border:1px solid var(--line);border-radius:11px;color:var(--dim);cursor:pointer}
.tlchip.on{border-color:var(--cyan);color:var(--cyan)}
.tlrow{display:flex;gap:10px;align-items:baseline;padding:5px 0;border-top:1px solid var(--line);font-size:13px}
.tlrow:first-of-type{border-top:none}
.tlt{color:var(--dim);font-variant-numeric:tabular-nums;flex:none;width:40px}
.tlsrc{font-size:10px;color:var(--dim);border:1px solid var(--line);border-radius:3px;padding:0 4px;margin-left:4px}
.tlrow.live{background:rgba(200,60,60,.06)}
.tllive{color:var(--red);animation:mlpulse 1.4s infinite}
.steckbrief{display:flex;gap:18px;flex-wrap:wrap;align-items:flex-start}
.sbinfo{flex:0 0 190px;min-width:160px}
.sbradar{flex:1;min-width:250px}
.sbpf{width:74px;height:74px;border-radius:50%;object-fit:cover;border:2px solid var(--cyan);display:block}
.sbpf-none{display:flex;align-items:center;justify-content:center;font-size:34px;background:var(--inset);border:2px solid var(--line)}
.sbname{font-size:17px;color:var(--white);font-weight:600;margin:8px 0 6px}
.sbrow{font-size:13px;margin:3px 0;color:var(--txt)}
.sbfresh{margin-top:8px}
/* Planetary Industry: Dringlichkeitszeilen + einklappbare Char-Bloecke. */
.pirow{display:grid;grid-template-columns:12px 130px 1fr 150px 140px;align-items:center;gap:10px;padding:6px 2px;border-top:1px solid var(--line);font-size:13px}
.pirow:first-of-type{border-top:none}
.pichar{font-weight:600;overflow:hidden;text-overflow:ellipsis;white-space:nowrap}
.piplanet{overflow:hidden;text-overflow:ellipsis;white-space:nowrap}
.piprod{color:var(--dim);overflow:hidden;text-overflow:ellipsis;white-space:nowrap}
.piexp{text-align:right;font-variant-numeric:tabular-nums;font-weight:600;white-space:nowrap}
.pidot{width:9px;height:9px;border-radius:50%;background:var(--dim)}
.pidot.ok,.piexp.ok{color:var(--green)}.pidot.ok{background:var(--green)}
.pidot.warn,.piexp.warn{color:var(--gold)}.pidot.warn{background:var(--gold)}
.pidot.bad,.piexp.bad{color:var(--red)}.pidot.bad{background:var(--red)}
.pidot.dim{background:var(--line)}
.picol{border-top:1px solid var(--line)}
.picol:first-of-type{border-top:none}
.pihead{padding:8px 0}
.picolrow{display:flex;gap:12px;align-items:flex-start;padding:9px 2px 10px;border-top:1px solid var(--line)}
.picol .picolrow:first-of-type{border-top:none}
.piplanetimg{width:46px;height:46px;border-radius:50%;flex:none;background:var(--inset)}
.picolbody{flex:1;min-width:0}
.picolhead{display:flex;gap:8px;align-items:baseline;flex-wrap:wrap;margin-bottom:4px}
.piexrow{display:grid;grid-template-columns:12px 20px 1fr max-content;align-items:center;gap:8px;padding:3px 2px;font-size:12px}
.piicon{width:18px;height:18px;border-radius:3px}
.piname{overflow:hidden;text-overflow:ellipsis;white-space:nowrap}
.piplanet{display:flex;align-items:center;gap:6px;min-width:0}
.piglobe{width:18px;height:18px;border-radius:50%;flex:none}
.pinm{overflow:hidden;text-overflow:ellipsis;white-space:nowrap}
.pistat2{border-top:1px solid var(--line);margin-top:10px;padding-top:8px;font-size:12px}
.pistat2>b{display:block;margin-bottom:5px}
.pwatch{background:var(--red);color:#fff;border-radius:4px;padding:1px 6px;
 font-size:11px;font-weight:700;letter-spacing:.4px;white-space:nowrap}
html[data-skin=photon] .pwatch{border-radius:1px}
.pinear{display:flex;align-items:baseline;gap:10px;padding:4px 0;flex-wrap:wrap}
.pinearmid{min-width:200px}
.pitier{display:inline-block;font-size:9px;font-weight:700;line-height:1;padding:2px 4px;border-radius:4px;margin-left:4px;vertical-align:middle;border:1px solid currentColor;opacity:.9}
.pitier.P0{color:var(--dim)}.pitier.P1{color:var(--green)}.pitier.P2{color:var(--cyan)}.pitier.P3{color:#b07de8}.pitier.P4{color:var(--gold)}
.piprodline{font-size:12px;margin:3px 0 7px;display:flex;flex-wrap:wrap;gap:5px 12px;align-items:center}
.piprd{display:inline-flex;align-items:center;gap:4px;white-space:nowrap}
.piicon2{width:16px;height:16px;border-radius:3px;flex:none}
.esichk{font-size:10px;font-weight:700;padding:1px 6px;border-radius:5px;margin-left:6px;vertical-align:middle;border:1px solid currentColor;white-space:nowrap;cursor:help}
.esichk.ok{color:var(--green)}
.esichk.bad{color:var(--red)}
.advrow{display:flex;gap:10px;flex-wrap:wrap;margin:8px 0 2px}
.advopt{flex:1;min-width:130px;background:var(--inset);border:1px solid var(--line);border-radius:9px;padding:10px 12px}
.advopt.best{border-color:var(--green)}
.advopt .l{font-size:12px;color:var(--dim)}
.advopt .v{font-size:20px;font-weight:600;margin-top:2px}
.advrec{color:var(--green);font-weight:700;font-size:10px;border:1px solid var(--green);border-radius:4px;padding:1px 4px;margin-left:4px}
.advtbl{margin-top:10px}
.advtbl td.advb{color:var(--green);font-weight:700}
@media(max-width:640px){.pirow{grid-template-columns:12px 1fr max-content}.pirow .pichar,.pirow .piprod{display:none}}
/* Live-Missionskampf: EVE-HUD an den Design-Tokens. Verlauf ueber var(--card)/
   var(--inset) (theme-fest), Radius/Border wie die uebrigen Karten, Schaden
   raus=Cyan / rein=Rot / ISK=Gold wie in der ganzen App. */
.mlive{position:relative;grid-column:1/-1;background:linear-gradient(160deg,var(--card),var(--inset));border:1px solid var(--line);border-radius:10px;overflow:hidden}
.mlive::after{content:'';position:absolute;left:0;top:0;bottom:0;width:3px;background:var(--cyan);opacity:.8}
.mlive+.mlive{margin-top:12px}
.mlive-head{display:flex;justify-content:space-between;align-items:center;gap:8px;flex-wrap:wrap;padding:9px 14px 9px 17px;border-bottom:1px solid var(--line)}
.mlive-title{font-size:12px;font-weight:700;letter-spacing:.16em;color:var(--cyan);text-transform:uppercase}
.mlive-phase{font-size:11px;font-weight:600;letter-spacing:0;text-transform:none;color:var(--dim);margin-left:8px}
.mlive-title .dot{display:inline-block;width:7px;height:7px;border-radius:50%;background:var(--red);margin-right:7px;box-shadow:0 0 8px var(--red);animation:mlpulse 1.4s infinite;vertical-align:middle}
@keyframes mlpulse{0%,100%{opacity:1}50%{opacity:.3}}
.mlive-sys{font-size:11px;color:var(--dim)}
.mlive-body{display:grid;grid-template-columns:1fr auto 1fr;align-items:center;gap:14px;padding:20px 16px}
.mlive-side{text-align:center}
.mlive-side .l{font-size:10px;letter-spacing:.14em;text-transform:uppercase;color:var(--dim);margin-bottom:5px}
.mlive-num{font-size:30px;font-weight:800;line-height:1;font-variant-numeric:tabular-nums}
.mlive-num.out{color:var(--cyan)}
.mlive-num.in{color:var(--red)}
.mlive-dps{font-size:11px;color:var(--dim);margin-top:5px}
.mlive-center{display:flex;flex-direction:column;align-items:center;gap:7px}
.mlive-ring{position:relative;width:96px;height:96px;border-radius:50%;padding:3px;background:var(--cyan);box-shadow:0 0 0 1px var(--line),0 0 16px rgba(53,200,232,.25)}
.mlive-ring img{width:100%;height:100%;border-radius:50%;object-fit:cover;display:block;border:2px solid var(--card)}
.mlive-ring.noimg{background:var(--inset);border:1px solid var(--cyan);display:flex;align-items:center;justify-content:center;font-size:34px}
.mlive-nm{font-size:15px;font-weight:700;color:var(--txt)}
.mlive-foot{display:grid;grid-template-columns:repeat(3,1fr);border-top:1px solid var(--line)}
.mlive-foot .cell{text-align:center;padding:11px 6px}
.mlive-foot .cell+.cell{border-left:1px solid var(--line)}
.mlive-foot .l{font-size:10px;letter-spacing:.1em;text-transform:uppercase;color:var(--dim);margin-bottom:4px}
.mlive-foot .v{font-size:19px;font-weight:800;font-variant-numeric:tabular-nums}
.mlive-extra{padding:2px 16px 14px}
@media(max-width:560px){.mlive-body{grid-template-columns:1fr;gap:18px}.mlive-num{font-size:26px}}
.npc{margin-top:6px;padding:6px 9px;border-left:2px solid var(--gold);background:rgba(200,160,60,.07);border-radius:3px;font-size:11px;color:var(--dim);font-style:italic;line-height:1.5}
.dngline{display:flex;align-items:center;gap:6px;margin-top:2px}
.dngdot{display:inline-block;width:7px;height:7px;border-radius:50%;flex:none}
.dngdot.g{background:var(--green)}.dngdot.y{background:var(--gold)}.dngdot.r{background:var(--red)}
.mkt input{width:100%;box-sizing:border-box}
.mkt table{width:100%;border-collapse:collapse;margin-top:8px}
.mkt th,.mkt td{text-align:left;padding:4px 8px;border-bottom:1px solid var(--line);font-size:12px}
.mkt td.r,.mkt th.r{text-align:right}
.mkt .uibtn{font-size:11px;padding:2px 8px;margin-left:4px}
.mktwrap{position:relative;flex:1;min-width:200px}
.mktwrap input{width:100%;box-sizing:border-box}
.mktsug{position:absolute;top:100%;left:0;right:0;z-index:30;background:var(--card);border:1px solid var(--line);border-top:none;max-height:260px;overflow-y:auto;box-shadow:0 6px 16px rgba(0,0,0,.35)}
.mktsug div{padding:6px 10px;cursor:pointer;font-size:12px;white-space:nowrap;overflow:hidden;text-overflow:ellipsis}
.mktsug div:hover,.mktsug div.sel{background:var(--inset)}
.mtag a{color:var(--cyan);margin-left:6px}
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
 <span class="pill srv" id="srvStatus" hidden title="EVE-Server (Tranquility)"></span>
 <span class="pill upd" id="updBadge" hidden title="Neue Version verfügbar, Klick installiert sie"></span>
 <span class="pill" id="ovToggle" title="Always-on-top Mini-Overlay (Chrome, Edge, Firefox)">◱ Overlay</span>
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
 <span data-v="timeline">🕑 Verlauf</span>
 <span data-v="profil">🪪 Steckbrief</span>
 <span data-v="planeten">🪐 Planeten</span>
 <span data-v="vault">💎 Erz-Schatzkammer</span>
 <span data-v="rechner">💰 ISKray</span>
</nav>
<div id="viewinfo"></div>
<div id="updBanner" hidden></div>
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
  bleibt über dem EVE-Client (Fenstermodus/randlos). In Chrome und Edge klickbar, in Firefox als Bild. Start nur per Klick.</div>
 </div>

 <div class="optgroup">
  <div class="sect">🔔 Alarme &amp; Wachen</div>
  <label><input type="checkbox" id="sndPvp" checked> Sound bei Spieler-Angriff</label>
  <label><input type="checkbox" id="sndDep" checked> Sound bei leerem Asteroiden</label>
  <label><input type="checkbox" id="sndWatch" checked> Sound bei Watchlist-Treffer</label>
  <label><input type="checkbox" id="ttsAlerts"> 🔊 Sprachansagen bei Alarmen (spricht Charakter und Warnung)</label>
  <div id="ttsVoiceRow" style="margin:2px 0 4px 22px;font-size:13px;color:var(--dim)"><span>Stimme:</span> <select id="ttsVoice" class="pill"><option value="">Standard</option></select> <span id="ttsVoiceHint" hidden style="color:var(--gold);font-size:11px"></span></div>
  <label><input type="checkbox" id="iskCoach"> 💸 ISK-Verlust anzeigen, wenn ein Strip Miner steht</label>
  <div style="margin-top:6px"><button class="btn" id="alertTest">🔔 Alarm testen</button>
   <span class="hint" style="margin:0 0 0 6px">löst einen Beispielalarm aus: Ton, Sprache und Banner, je nach Häkchen oben. Alarme kommen sonst nur bei einem echten Ereignis.</span></div>
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
  <label><input type="checkbox" id="countMe"> Anonym mitzählen lassen</label>
  <div class="hint">Einmal am Tag holt Canary eine leere Datei von GitHub, deren Name nur das Datum enthält. Gesendet wird dabei nichts: keine Kennung, keine Namen, keine Spieldaten. GitHub zählt nur, wie oft die Datei ausgeliefert wurde, und daraus wird sichtbar, wie viele Installationen es gibt. Ohne diese Zahl gibt es keinen Nachweis für die EVE-Partnerschaft.</div>
  <div style="margin-top:10px"><b>Main-Charakter (für das Teilen-Bild)</b>
   <div class="hint">Welcher Name auf dem geteilten Mining-Fleet-Power-Bild steht. Automatisch = Command Ship, sonst der aktivste Miner.</div>
   <select id="mainCharSel" class="pill" style="margin-top:4px"><option value="">Automatisch</option></select></div>
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

 <div class="copyright">
  <b>COPYRIGHT NOTICE</b><br>
  EVE Online and the EVE logo are trademarks of Fenris Creations (formerly CCP). All rights are reserved worldwide. All other trademarks are the property of their respective owners.
  EVE Online, the EVE logo, EVE and all associated logos and designs are the intellectual property of Fenris Creations. All artwork, screenshots, characters, vehicles, storylines, world facts or other recognizable features of the intellectual property relating to these trademarks are likewise the intellectual property of Fenris Creations.
  EVE Canary is a third-party tool and is not affiliated with, endorsed by, or sponsored by Fenris Creations. Fenris Creations is in no way responsible for the content on or functioning of this tool, nor can it be liable for any damage arising from its use.
 </div>

 <div style="text-align:right"><button class="btn" id="close">Schließen</button></div>
</dialog>

<script>
const $=s=>document.querySelector(s);
const fmt=n=>Math.round(n).toLocaleString();
const fmtM=n=>n>=1e9?(n/1e9).toFixed(2)+' Mrd':n>=1e6?(n/1e6).toFixed(1)+' M':fmt(n);
// Wie fmtM, kuerzt aber auch Tausender mit K ab (fuer kompakte m³-Werte).
const fmtC=n=>n>=1e6?fmtM(n):n>=1e3?(n/1e3).toFixed(n>=1e4?0:1)+' K':fmt(n);
// Einzelpreis: bei grossen Werten wie fmtM, bei kleinen mit Nachkommastellen,
// damit Cent-Preise (Erz ~4 ISK) nicht auf ganze Zahlen gerundet werden.
const fmtP=n=>n>=1e6?fmtM(n):n>=1000?fmt(n):(n||0).toLocaleString(undefined,{maximumFractionDigits:2});
// HTML-Escape: Spieler-/Corp-/Schiffsnamen aus Logs, ESI und zKillboard sind
// fremdbestimmt und dürfen nie ungefiltert in innerHTML landen (XSS).
const esc=s=>String(s==null?'':s).replace(/[&<>"']/g,c=>({'&':'&amp;','<':'&lt;','>':'&gt;','"':'&quot;',"'":'&#39;'}[c]));
function lsGet(key,fallback){try{const v=localStorage.getItem(key);return v==null?fallback:JSON.parse(v);}catch(e){return fallback;}}
const VIEWS=['live','month','total','analyse','intel','missionen','timeline','profil','planeten','vault','rechner'];
let view=location.pathname.replace(/^\\//,'')||'live', state=null, lastAlertId=Number(localStorage.getItem('lastAlertId')||0);
if(!VIEWS.includes(view))view='live';
window.addEventListener('popstate',()=>{
 view=location.pathname.replace(/^\\//,'')||'live';
 if(!VIEWS.includes(view))view='live';
 document.querySelectorAll('nav span').forEach(x=>x.classList.toggle('on',x.dataset.v===view));
 renderViewInfo();
 tick();
});

const savedTheme=localStorage.getItem('theme');
if(savedTheme)document.documentElement.dataset.theme=savedTheme;
else if(matchMedia('(prefers-color-scheme: light)').matches)document.documentElement.dataset.theme='light';
const savedSkin=localStorage.getItem('skin');
if(savedSkin)document.documentElement.dataset.skin=savedSkin;
$('#autostart').onchange=async()=>{const r=await post({action:'autostart',on:$('#autostart').checked});if(r.state)state=r.state;syncOpts();};
$('#countMe').onchange=()=>post({action:'count_me',on:$('#countMe').checked});
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

// Kurze Erklaerung je Bereich, in einfacher Sprache: was macht der Tab, und
// woher kommen die Daten. Der Datenherkunfts-Satz ist Absicht, damit jeder
// nachlesen kann, was den Rechner verlaesst.
const VIEW_INFO={
 live:{d:'Hier siehst du, was gerade passiert. Für jeden Charakter eine Karte mit Erz, ISK, Schaden und Warnungen. Die Zahlen werden alle zwei Sekunden frisch aus deinen Logdateien gelesen.',
  q:'Daten: die Logdateien, die dein EVE-Client auf diesem Rechner schreibt. Marktpreise von Fuzzwork. Wenn du den EVE-Login benutzt, kommen Schiff, Kontostand und Frachtraum-Wert dazu, die sind bis zu eine Stunde alt.'},
 month:{d:'Die letzten 30 Tage, ein Balken für jeden Tag. So siehst du auf einen Blick, an welchen Tagen du viel geschafft hast.',
  q:'Daten: die Datenbank von Canary auf diesem Rechner, gefüllt aus deinen Logdateien.'},
 total:{d:'Alles zusammengezählt, seit Canary mitschreibt: Erz, ISK, Schaden und Gegner, aufgeteilt nach Charakter.',
  q:'Daten: die Datenbank von Canary auf diesem Rechner, gefüllt aus deinen Logdateien.'},
 analyse:{d:'Auswertung über längere Zeit. Welche Waffen du benutzt, wer dich angegriffen hat, welches Erz am meisten einbringt und zu welchen Zeiten du spielst.',
  q:'Daten: die Datenbank von Canary auf diesem Rechner, dazu Marktpreise von Fuzzwork.'},
 intel:{d:'Zwei Werkzeuge gegen böse Überraschungen. Die Ampel bewertet Piloten, die im Local schreiben. Die Blutspur zeigt Rudel, die in deiner Nähe Schiffe abschießen, und warnt, wenn sie näher kommen.',
  q:'Daten: deine Chatlogs auf diesem Rechner. Zu gefundenen Namen fragt Canary öffentliche Quellen: zKillboard und die EVE-Datenbank. Die Abschuss-Meldungen kommen von einem öffentlichen Killmail-Dienst. Über dich wird nichts gesendet.'},
 missionen:{d:'Deine Missionen. Was du gerade bekämpfst, welche Mission es vermutlich ist, gegen welche Fraktion es geht und was am Ende dabei herauskam.',
  q:'Daten: deine Logdateien für den Kampf. Mit EVE-Login zusätzlich das Wallet-Journal für die Belohnung, das ist bis zu eine Stunde alt. Wichtig: der Missionsname steht in keiner Datei. Canary erkennt ihn an den Gegnern und schreibt dazu, wie sicher es sich ist.'},
 timeline:{d:'Dein Tag als Zeitstrahl. Jeder Mining-Trip, jeder Kampf und jede Belohnung ist ein Eintrag, von jetzt nach hinten.',
  q:'Daten: deine Logdateien und, wenn du den EVE-Login benutzt, die Belohnungen aus dem Wallet-Journal.'},
 profil:{d:'Ein Steckbrief je Charakter: Bild, Corp, Schiff und Vermögen. Das Netz daneben zeigt, worin dieser Charakter stark ist, im Vergleich zu deinen anderen.',
  q:'Daten: die Datenbank von Canary für das Netz. Mit EVE-Login Bild, Kontostand und Schiff. Corp und Sicherheitsstatus über öffentliche Quellen.'},
 planeten:{d:'Deine Planeten-Fabriken. Wann läuft ein Extraktor ab, was liegt im Lager, was wird produziert und was ist es wert.',
  q:'Daten: nur über den EVE-Login. Achtung: die Lagerstände sind so aktuell, wie du die Kolonie zuletzt im Spiel geöffnet hast. Die Ablaufzeiten stimmen dagegen immer.'},
 vault:{d:'Dein Erz in den Stationen, und der Rat, was sich mehr lohnt: roh verkaufen, komprimiert verkaufen oder einschmelzen.',
  q:'Daten: EVE-Login für den Bestand, Marktpreise von Fuzzwork. Der Einschmelz-Wert ist vorsichtig gerechnet, dein echter Erlös liegt eher darüber.'},
 rechner:{d:'Ein Preisrechner. Frachtraum im Spiel markieren, kopieren, hier einfügen, und du siehst sofort, was es an welchem Handelsplatz wert ist.',
  q:'Daten: Marktpreise von Fuzzwork für die großen Handelsplätze. Der Text, den du einfügst, bleibt auf deinem Rechner.'}};
function renderViewInfo(){
 const box=$('#viewinfo');if(!box)return;
 const inf=VIEW_INFO[view],offen=lsGet('viewinfo',true),schl=view+'|'+offen;
 if(box.dataset.k===schl)return;   // sonst baut der 2s-Takt den Kasten dauernd neu
 box.dataset.k=schl;
 if(!inf){box.innerHTML='';return;}
 // Pfeil in eigenem Element: sonst haengt er im uebersetzten Text mit drin
 box.innerHTML='<div class="vinfo"><span class="vitog"><span class="viarr">'+(offen?'▾':'▸')+'</span> Was ist das?</span>'
  +(offen?'<div class="vitxt"><p>'+inf.d+'</p><p class="vidata">'+inf.q+'</p></div>':'')+'</div>';
 box.querySelector('.vitog').onclick=()=>{
  localStorage.setItem('viewinfo',JSON.stringify(!offen));
  renderViewInfo();
  if(lang!=='de')tr(document.body);   // frisch gebaut -> sonst kurz deutsch
 };
 if(lang!=='de')tr(document.body);
}
document.querySelectorAll('nav span').forEach(el=>el.onclick=()=>{
 document.querySelectorAll('nav span').forEach(x=>x.classList.remove('on'));
 el.classList.add('on');view=el.dataset.v;
 // Direkt umschalten: tick() faellt aus, solange noch eine Abfrage laeuft
 // (tickBusy), der Kasten haette sonst bis zu zwei Sekunden den alten Text.
 renderViewInfo();
 history.pushState(null,'','/'+(view==='live'?'':view));tick();});
document.querySelectorAll('nav span').forEach(x=>x.classList.toggle('on',x.dataset.v===view));

['sndPvp','sndDep','sndWatch'].forEach(id=>{
 const el=$('#'+id);
 el.checked=localStorage.getItem(id)!=='0';
 el.onchange=()=>localStorage.setItem(id,el.checked?'1':'0');});
// Zusatzoptionen: standardmaessig AUS (opt-in), erst bei '1' aktiv.
['ttsAlerts','iskCoach'].forEach(id=>{
 const el=$('#'+id); if(!el)return;
 el.checked=localStorage.getItem(id)==='1';
 el.onchange=()=>localStorage.setItem(id,el.checked?'1':'0');});
// Test-Knopf: schickt einen Beispielalarm durch den ECHTEN Pfad (Banner + Ton +
// Sprache je nach Haekchen). Der Klick entsperrt zugleich die Audio-Ausgabe.
(function(){const b=$('#alertTest'); if(!b)return; b.onclick=()=>{
 const id=(state.alerts||[]).reduce((m,a)=>Math.max(m,a.id||0),lastAlertId||0)+1;
 state.alerts=[...(state.alerts||[]),{id,ts:Date.now()/1000,kind:'cargo',char:'Test',
   text:(lang==='en'?'Test: sample alert':'Test: Beispielalarm')}];
 handleAlerts();
};})();
// Stimmen-Auswahl fuer die Sprachansage (Angebot haengt von System/Browser ab).
function fillVoices(){
 const sel=$('#ttsVoice'); if(!sel||!('speechSynthesis' in window))return;
 const cur=localStorage.getItem('ttsVoice')||'';
 const voices=speechSynthesis.getVoices();
 sel.innerHTML='<option value="">Standard</option>'+voices.map(v=>
  `<option value="${esc(v.voiceURI)}"${v.voiceURI===cur?' selected':''}>${esc(v.name)} (${esc(v.lang)})</option>`).join('');
 // Firefox liefert unter Windows oft KEINE Stimmen ueber die Web-Speech-API.
 // Dann ehrlich darauf hinweisen, statt nur "Standard" ohne Erklaerung zu zeigen.
 const hint=$('#ttsVoiceHint');
 if(hint){
  if(voices.length===0){hint.hidden=false;
   hint.textContent='keine Stimmen im Browser (bei Firefox unter Windows häufig). Für auswählbare Stimmen Chrome oder Edge nutzen.';
  }else hint.hidden=true;
 }
}
function previewVoice(){
 if(!('speechSynthesis' in window))return;
 try{speechSynthesis.cancel();}catch(e){}
 speak(lang==='en'?'Voice test. Askend: cargo full.':'Stimmtest. Askend: Frachtraum voll.');
}
(function(){const sel=$('#ttsVoice'); if(!sel)return;
 if('speechSynthesis' in window){fillVoices(); speechSynthesis.onvoiceschanged=fillVoices;
  [300,1200,2500].forEach(t=>setTimeout(fillVoices,t));}   // Firefox liefert Stimmen oft verspaetet
 sel.onchange=()=>{localStorage.setItem('ttsVoice',sel.value); previewVoice();};
})();

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
 $('#countMe').checked=state.count_me!==false;
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
 // Main-Charakter-Auswahl aus den bekannten Chars fuellen (fuers Teilen-Bild)
 const ms=$('#mainCharSel');
 if(ms){const names=[...new Set((lastChars||[]).map(c=>c.name))].sort();
  const cur=localStorage.getItem('mainChar')||'';
  ms.innerHTML='<option value="">Automatisch</option>'+names.map(n=>`<option value="${esc(n)}"${n===cur?' selected':''}>${esc(n)}</option>`).join('');
  ms.value=names.includes(cur)?cur:'';}
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

// Sprachansage (opt-in). Nutzt die eingebaute Sprachausgabe des Browsers,
// komplett lokal, kostenlos. Spammige Einzel-Asteroiden ('depleted') bewusst nicht.
// Beliebigen Text mit der gewaehlten Stimme sprechen (zentraler Helfer).
function speak(text){
 if(!('speechSynthesis' in window))return;
 try{const u=new SpeechSynthesisUtterance(text);
  const sel=localStorage.getItem('ttsVoice')||'';
  const v=sel?speechSynthesis.getVoices().find(x=>x.voiceURI===sel):null;
  if(v){u.voice=v;u.lang=v.lang;}else{u.lang=lang==='en'?'en-US':'de-DE';}
  u.rate=1.05; speechSynthesis.speak(u);}catch(e){}
}
function speakAlert(a){
 if(localStorage.getItem('ttsAlerts')!=='1')return;
 const en=(lang==='en');
 const P=en?{pvp:'under attack',cargo:'cargo full',drones:'check drones',idle:'mining stopped',
             rate:'mining rate dropped',hw:'heavy water low',watch:'watchlist hit',intel:'threat detected',pi:'extractor expiring',pack:'known pack in local'}
           :{pvp:'unter Beschuss',cargo:'Frachtraum voll',drones:'Drohnen prüfen',idle:'Mining steht',
             rate:'Abbaurate gefallen',hw:'Heavy Water fast leer',watch:'Watchlist-Treffer',intel:'Bedrohung erkannt',pi:'Extraktor läuft ab',pack:'bekanntes Rudel im Local'};
 const phrase=P[a.kind]; if(!phrase)return;
 speak((a.char?a.char+': ':'')+phrase);
}
// Karten-Warnungen (Strip Miner aus, Drohnen im Leerlauf) sind KEINE Banner-Alarme,
// werden aber per Sprache angesagt, sobald sie NEU auftreten (kein Dauergeplapper).
let voiceSeen={}, voiceReady=false;
function voiceWatch(chars){
 if(localStorage.getItem('ttsAlerts')!=='1'||!('speechSynthesis' in window)){voiceReady=false;return;}
 const en=(lang==='en'), cur={};
 for(const c of (chars||[])){
  if(!c.active)continue;
  const keys=[];
  (c.lasers_off||[]).forEach(w=>keys.push('LO|'+w.tool));
  if(c.drones_idle)keys.push('DI');
  cur[c.name]=new Set(keys);
 }
 if(!voiceReady){voiceSeen=cur; voiceReady=true; return;}  // erster Lauf: nur merken, nicht ansagen
 for(const name in cur){
  const prev=voiceSeen[name]||new Set();
  const fresh=[...cur[name]].filter(k=>!prev.has(k));
  const lo=fresh.filter(k=>k.startsWith('LO|'));
  if(lo.length===1)speak(name+': '+lo[0].slice(3)+(en?' off':' aus'));
  else if(lo.length>1)speak(name+': '+lo.length+(en?' strip miners off':' Strip Miner aus'));
  if(fresh.includes('DI'))speak(name+': '+(en?'drones idle, no ore':'Drohnen liefern kein Erz'));
 }
 voiceSeen=cur;
}
function handleAlerts(){
 const list=state.alerts||[];
 const now=Date.now()/1000;
 $('#alerts').innerHTML=list.filter(a=>now-a.ts<300).slice(-4).reverse().map(a=>{
  const t=new Date(a.ts*1000).toLocaleTimeString();
  return `<div class="alert ${a.kind}">[${t}] ${esc(a.text)}</div>`}).join('');
 // Notification-API kann fehlen (aelterer Browser/WebView, kein Secure-Context).
 // Ohne diese Pruefung wuerde jeder tick() hier werfen und die Seite bliebe leer.
 const canNotify=('Notification' in window)&&Notification.permission==='granted';
 const notify=(title,a)=>{if(canNotify)new Notification(title,{body:a.text});};
 for(const a of list){
  if(a.id<=lastAlertId)continue;
  lastAlertId=a.id;                 // immer hochsetzen, auch fuer alte Alarme
  // Alte Alarme (frisches Profil/privates Fenster: lastAlertId=0 -> ganze Historie)
  // nicht nachtoenen; im Banner erscheinen sie ohnehin nur < 300 s.
  if(now-a.ts>=300)continue;
  speakAlert(a);                    // opt-in Sprachansage (filtert selbst nach Art)
  if(a.kind==='pvp'){
   if($('#sndPvp').checked)beep(880,3,0.18);
   notify('EVE: SPIELER-ANGRIFF!',a);
  }else if(a.kind==='depleted'&&$('#sndDep').checked)beep(520,1,0.12);
  else if(a.kind==='drones'){
   if($('#sndDep').checked)beep(590,2,0.15);
   notify('EVE: Drohnen prüfen!',a);
  }
  else if(a.kind==='cargo'){
   if($('#sndDep').checked)beep(700,3,0.18);
   notify('EVE: Frachtraum voll!',a);
  }
  else if(a.kind==='idle'){
   if($('#sndDep').checked)beep(470,2,0.2);
   notify('EVE: Mining steht!',a);
  }
  else if(a.kind==='rate'){
   if($('#sndDep').checked)beep(505,2,0.18);
   notify('EVE: Abbaurate gefallen!',a);
  }
  else if(a.kind==='watch'){
   if($('#sndWatch').checked)beep(660,2,0.15);
   notify('EVE: Watchlist',a);
  }
  else if(a.kind==='intel'){
   if($('#sndWatch').checked)beep(770,3,0.16);
   notify('EVE: Bedrohung erkannt!',a);
  }
  else if(a.kind==='hw'){
   if($('#sndDep').checked)beep(430,2,0.2);
   notify('EVE: Heavy Water fast leer!',a);
  }
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
// Deutliche Update-Meldung als Banner. Text gleich in der aktiven Sprache bauen,
// damit die dynamische Versionsnummer nicht in tr() haengen bleibt.
function updateBanner(){
 const u=(state&&state.update)||{};
 const b=$('#updBanner'); if(!b)return;
 if(b.dataset.busy==='1')return;            // waehrend des Updates nicht neu aufbauen
 if(!(u.available&&u.latest)){b.hidden=true;b.innerHTML='';return;}
 const en=(lang==='en');
 b.hidden=false;
 b.innerHTML=`<div class="ub-txt"><b>${en?'Update available':'Update verfügbar'}: v${esc(u.latest)}</b>`
  +`<span class="ub-sub">${en?'A newer version of Canary is online. Update now to get the latest features.'
                            :'Eine neuere Version von Canary ist online. Jetzt aktualisieren für die neuesten Funktionen.'}</span></div>`
  +`<button id="ubGo">${en?'Update now':'Jetzt aktualisieren'}</button>`;
 $('#ubGo').onclick=runUpdate;
}
async function runUpdate(){
 const b=$('#updBanner'), badge=$('#updBadge'), en=(lang==='en');
 if(b){b.dataset.busy='1';b.hidden=false;
  b.innerHTML=`<div class="ub-txt"><b>${en?'Updating …':'Update läuft …'}</b>`
   +`<span class="ub-sub">${en?'Downloading and restarting. The page reloads by itself.'
                             :'Wird geladen und neu gestartet, die Seite lädt gleich von selbst neu.'}</span></div>`;}
 if(badge)badge.textContent=en?'Updating …':'Update läuft …';
 let r;try{r=await post({action:'do_update'});}catch(e){r=null;}
 if(r&&r.ok&&r.updated){waitForRestart();return;}
 if(b)b.dataset.busy='';
 alert((r&&(r.error||r.message))||(en?'Update failed.':'Update fehlgeschlagen.'));
 updateBanner();updateBadge();
}
async function waitForRestart(){
 // Erst neu laden, wenn der neu gestartete Server wirklich wieder antwortet —
 // sonst laeuft der Refresh in einen kurzen Moment ohne Server (Fehlerseite).
 for(let i=0;i<45;i++){
  await new Promise(r=>setTimeout(r,1000));
  try{const resp=await fetch('/data?view=live',{cache:'no-store'});
      if(resp.ok){const d=await resp.json(); if(d&&d.state){location.reload();return;}}}catch(e){}
 }
 location.reload();
}
// Serverstatus (Tranquility). Text und Titel gleich in der aktiven Sprache
// bauen — dann muss tr() hier nichts nachtraeglich uebersetzen (die Spielerzahl
// wechselt jede Minute, ein zwischengespeicherter Titel wuerde sonst einfrieren).
function serverBadge(){
 const s=(state&&state.server)||{};
 const b=$('#srvStatus'); if(!b)return;
 if(!s.checked){b.hidden=true;return;}
 const en=(lang==='en');
 b.hidden=false; b.classList.remove('up','down','vip');
 if(!s.ok){
  b.classList.add('down');
  b.innerHTML='<span class="dot"></span>'+(en?'Server offline':'Server offline');
  b.title=en?'EVE server (Tranquility) unreachable, maybe downtime'
            :'EVE-Server (Tranquility) nicht erreichbar, evtl. Downtime';
  return;
 }
 if(s.vip){
  b.classList.add('vip');
  b.innerHTML='<span class="dot"></span>'+(en?'VIP only':'Nur VIP');
  b.title=en?'Server in VIP mode (maintenance), only certain accounts'
            :'Server im VIP-Modus (Wartung), nur bestimmte Accounts';
  return;
 }
 b.classList.add('up');
 const n=(s.players!=null)?s.players.toLocaleString(en?'en-US':'de-DE'):'?';
 b.innerHTML='<span class="dot"></span>TQ <b>'+n+'</b>';
 let tip=en?('EVE server (Tranquility) online · '+n+' players')
           :('EVE-Server (Tranquility) online · '+n+' Spieler');
 if(s.start_time){
  const up=Math.max(0,(Date.now()-new Date(s.start_time).getTime())/3600000);
  tip+=en?(' · up '+up.toFixed(1)+' h'):(' · seit '+up.toFixed(1).replace('.',',')+' h online');
 }
 b.title=tip;
}
$('#updBadge').onclick=runUpdate;
function regionPills(){
 $('#regions').innerHTML=Object.entries(state.regions).map(([id,n])=>
  `<span class="pill ${id===state.region?'on':''}" data-r="${id}">${n}</span>`).join('');
 document.querySelectorAll('#regions .pill').forEach(p=>p.onclick=async()=>{
  await post({action:'region',region:p.dataset.r});tick();});
}

let collapsed=new Set(lsGet('collapsed',[]));
// Master-Umschalter der Live-Ansicht: Miner vs. PvP/Missionen. Strikt getrennt.
let liveMode=localStorage.getItem('liveMode')||'mining';
// Solange der Rollen-Picker offen ist, das Grid NICHT neu bauen — sonst wuerde
// das offene Dropdown beim naechsten Log-Eintrag zerstoert und faellt zu.
let rolePickerBusy=false;
function renderLiveView(){
 if(rolePickerBusy)return;
 if(lastChars)(liveMode==='combat'?renderCombat:renderLive)(lastChars,lastSummary);
}
function toggleChar(name){
 if(collapsed.has(name))collapsed.delete(name);else collapsed.add(name);
 localStorage.setItem('collapsed',JSON.stringify([...collapsed]));
 renderLiveView();
}
let lastChars=null,lastSummary=null;
// ---- Lokale Missions-Simulation (nur Frontend, keine Logs/DB, nie hochgeladen) ----
// Sichtbar nur mit lokalem sim_mode-Flag. Ein Demo-Char durchlaeuft komplette
// Missions-Zyklen (Abdocken -> Warp -> Anflug -> Kampf -> Andocken) und fuellt
// dabei eine Historie aus 50 Missionen mit zufaelligem Loot. Wichtig: nach jedem
// Render tr() aufrufen, sonst flackert die UI zwischen DE (frisch gerendert) und
// EN (vom Poll nachuebersetzt).
let lastMissionD=null;
const SIM={on:false,char:null,timer:null,history:[],summary:null};
const SIM_FACS=[
 {fac:'Guristas',shoot:['kin','therm'],deal:['kin','therm'],ewar:'jam',
  rats:['Pith Eradicator','Pith Destroyer','Dire Pithum Abolisher','Pithatis Enforcer'],
  missions:['Guristas Extravaganza','The Rogue Slave Trader','Worlds Collide','Dread Pirate Scarlet']},
 {fac:'Serpentis',shoot:['kin','therm'],deal:['therm','kin'],ewar:'damp',
  rats:['Coreli Guardian Patroller','Corelum Chief Safeguard','Shadow Serpentis Sentinel'],
  missions:['Serpentis Extravaganza','Silence the Informant','Gone Berserk','Pleasure Hub Takedown']},
 {fac:'Angel Cartel',shoot:['exp','kin'],deal:['exp','kin'],ewar:'web',
  rats:['Gistum Centurion','Arch Gistii Outlaw','Gist Warlord'],
  missions:['Angel Extravaganza','Vengeance','Buzz Kill','Stop the Thief']},
 {fac:'Blood Raiders',shoot:['em','therm'],deal:['em','therm'],ewar:'neut',
  rats:['Corpus Prophet','Corpatis Fanatic','Corpum Arch Priest'],
  missions:['The Damsel in Distress','Unauthorized Military Presence','Blood Raider Retort']},
 {fac:'Sansha',shoot:['em','therm'],deal:['em','therm'],ewar:'td',
  rats:['Centus Slavelord','Centii Enslaver','True Sansha Lord'],
  missions:['The Right Hand of Zazzmatazz','Portal to War','Sansha Command Relay']},
 {fac:'Rogue Drones',shoot:['em','therm'],deal:['therm','em'],ewar:null,
  rats:['Alvus Ruler','Defeater Alvatis','Strain Render Alvi'],
  missions:['Rogue Drone Harassment','Infiltrated Outposts','Cleanup Operation']},
];
const SIM_SYS=['Anttiri','Juunigaishi','Kusomonmon','Osoggur','Nourvukaiken','Akkilen','Hasmijaala','Uotila'];
const SIM_PHASES=[
 {k:'undock',n:1,de:'🛰 Abgedockt',en:'🛰 Undocked'},
 {k:'warp',n:2,de:'🚀 Warp zum Missionsort',en:'🚀 Warping to mission'},
 {k:'approach',n:1,de:'➡ Anflug aufs Objekt',en:'➡ Approaching objective'},
 {k:'combat',n:0,de:'⚔ Im Kampf',en:'⚔ In combat'},
 {k:'dock',n:1,de:'⚓ Andocken, Mission fertig',en:'⚓ Docking, mission complete'},
];
function simRi(a,b){return a+Math.floor(Math.random()*(b-a+1));}
function simPick(a){return a[Math.floor(Math.random()*a.length)];}
// Eine abgeschlossene Demo-Mission (Format wie query_mission_history).
function simMission(endTs){
 const f=simPick(SIM_FACS), min=simRi(5,42), kills=simRi(6,32);
 const reward=simRi(120,700)*1000, bonus=Math.round(reward*(0.6+Math.random()*0.6));
 const bounty=kills*simRi(18000,120000), loot=Math.random()<0.8?simRi(120,7200)*1000:null;
 const ew=(f.ewar&&Math.random()<0.7)?[[f.ewar,simRi(1,14)]]:[];
 return {mid:'sim:'+endTs+':'+simRi(1,9999),char:'Rihan Vex',start:endTs-min*60,end:endTs,min:min,
   system:simPick(SIM_SYS),dmg_out:simRi(14000,120000),dmg_in:simRi(2000,26000),kills:kills,
   bounty:bounty,hit:simRi(78,99),mission:{name:simPick(f.missions),conf:simRi(70,95)},npc:[],
   faction:{fac:f.fac,deal:f.deal,shoot:f.shoot,ewar:f.ewar,share:simRi(80,100)},ewar:ew,
   reward:reward,bonus:bonus,weapons:[],enemies:f.rats.map(r=>[r,simRi(2000,40000)]),
   loot_isk:loot,loot_text:loot?(lang==='en'?'(simulated loot)':'(simuliertes Loot)'):'',
   total:reward+bonus+bounty+(loot||0)};
}
// 50 Missionen ueber die letzten 7 Tage streuen und Tages-/Heute-Summen bauen.
function simBuild(){
 const now=Math.floor(Date.now()/1000), list=[];
 for(let i=0;i<50;i++)list.push(simMission(now-simRi(0,7*86400)));
 list.sort((a,b)=>b.start-a.start);
 SIM.history=list;
 const days={};
 for(const m of list){
  const day=new Date(m.start*1000).toISOString().slice(0,10);
  const d=days[day]||(days[day]={day:day,missions:0,reward:0,bonus:0,bounty:0,total:0});
  d.missions++; d.reward+=m.reward; d.bonus+=m.bonus; d.bounty+=m.bounty; d.total+=m.reward+m.bonus+m.bounty;
 }
 const today=new Date().toISOString().slice(0,10);
 SIM.summary={linked:true,asof:now-120,next:now+2400,mine_systems:[],foes:[],agents:[],chars:[],
   today:days[today]||{day:today,missions:0,reward:0,bonus:0,bounty:0,total:0},
   days:Object.values(days).sort((a,b)=>a.day<b.day?1:-1)};
}
// Neuer Missions-Run (Char frisch, Phase 0).
function simNewRun(){
 const f=simPick(SIM_FACS);
 return {active:true,name:'Rihan Vex (Demo)',ship:'Dominix',system:simPick(SIM_SYS),session_min:0,
   dmg_out:0,dmg_in:0,dps_out:0,dps_in:0,kills:0,enemy_types:f.rats.length,bounty:0,
   portrait:'https://images.evetech.net/characters/2121914571/portrait?size=64',
   mission:{name:simPick(f.missions),conf:simRi(72,95)},
   faction:{fac:f.fac,deal:f.deal,shoot:f.shoot,ewar:f.ewar,share:simRi(82,100)},
   ewar:f.ewar?[[f.ewar,0]]:[],top_targets:f.rats.map(r=>[r,1]),
   phase:(lang==='en'?SIM_PHASES[0].en:SIM_PHASES[0].de),
   _fac:f,_phase:0,_phaseLeft:SIM_PHASES[0].n,_combatLeft:simRi(6,13),_start:Date.now()};
}
function simRender(){
 if(view!=='missionen')return;
 renderMissions(lastMissionD||{missions:{},chars:[]});
 if(lang!=='de')tr(document.body);   // wie der Poll -> kein DE/EN-Flackern
}
function simStep(){
 const c=SIM.char; if(!c)return;
 const ph=SIM_PHASES[c._phase];
 c.phase=(lang==='en'?ph.en:ph.de);
 let advance=false;
 if(ph.k==='combat'){
  const secs=Math.max(1,(Date.now()-c._start)/1000);
  c.dmg_out+=simRi(400,1400); c.dmg_in+=simRi(120,600);
  if(Math.random()<0.7){c.kills++; c.bounty+=simPick([25000,45000,62000,90000,120000]);}
  if(c.ewar.length&&Math.random()<0.35)c.ewar[0][1]++;
  c.dps_out=Math.round(c.dmg_out/secs); c.dps_in=Math.round(c.dmg_in/secs*10)/10;
  c.session_min=Math.floor(secs/60);
  if(--c._combatLeft<=0)advance=true;
 }else if(--c._phaseLeft<=0)advance=true;
 if(advance){
  if(ph.k==='dock'){
   const loot=Math.random()<0.85?simRi(150,6800)*1000:null;
   const reward=simRi(150,650)*1000, bonus=Math.round(reward*(0.6+Math.random()*0.5));
   const end=Math.floor(Date.now()/1000);
   SIM.history.unshift({mid:'sim:live:'+end,char:'Rihan Vex',start:end-Math.max(1,c.session_min)*60-120,
     end:end,min:Math.max(1,c.session_min),system:c.system,dmg_out:c.dmg_out,dmg_in:c.dmg_in,
     kills:c.kills,bounty:c.bounty,hit:simRi(80,99),mission:c.mission,npc:[],faction:c.faction,
     ewar:c.ewar.filter(e=>e[1]>0),reward:reward,bonus:bonus,weapons:[],
     enemies:c._fac.rats.map(r=>[r,simRi(2000,40000)]),loot_isk:loot,
     loot_text:loot?(lang==='en'?'(simulated loot)':'(simuliertes Loot)'):'',
     total:reward+bonus+c.bounty+(loot||0)});
   if(SIM.summary){const t=SIM.summary.today;t.missions++;t.reward+=reward;t.bonus+=bonus;t.bounty+=c.bounty;t.total+=reward+bonus+c.bounty;}
   SIM.char=simNewRun();
  }else{
   c._phase++; c._phaseLeft=SIM_PHASES[c._phase].n||1;
  }
 }
 simRender();
}
function toggleSim(){
 if(SIM.on){clearInterval(SIM.timer);SIM.on=false;SIM.char=null;SIM.timer=null;}
 else{SIM.on=true;simBuild();SIM.char=simNewRun();SIM.timer=setInterval(simStep,2600);}
 simRender();
}
$('#charFilter').value=localStorage.getItem('charFilter')||'';
$('#charFilter').onchange=()=>{
 localStorage.setItem('charFilter',$('#charFilter').value);
 // Konkreten Char waehlen hebt den Rollen-Filter auf, sonst koennen sich beide
 // widersprechen (Char X + Rolle Mining -> leer). Pille "Alle" wieder aktiv setzen.
 if($('#charFilter').value){
  localStorage.setItem('roleFilter','');
  document.querySelectorAll('.rolef').forEach(x=>x.classList.toggle('on',x.dataset.role===''));
 }
 if(view==='planeten')renderPlaneten(lastPlaneten);else renderLiveView();};
{const ms=$('#mainCharSel'); if(ms)ms.onchange=()=>localStorage.setItem('mainChar',ms.value);}
$('#collapseAll').onclick=()=>{
 const pi=view==='planeten';
 const names=(pi?(lastPlaneten&&lastPlaneten.chars||[]):(lastChars||[])).map(c=>c.name);
 if(names.length&&names.every(n=>collapsed.has(n)))names.forEach(n=>collapsed.delete(n));
 else names.forEach(n=>collapsed.add(n));
 localStorage.setItem('collapsed',JSON.stringify([...collapsed]));
 if(pi)renderPlaneten(lastPlaneten);else renderLiveView();};
// Rollen-Filter-Pills (Alle / Mining / Missionen / PvP)
(function(){const rf=localStorage.getItem('roleFilter')||'';
 document.querySelectorAll('.rolef').forEach(p=>{
  p.classList.toggle('on',p.dataset.role===rf);
  p.onclick=()=>{localStorage.setItem('roleFilter',p.dataset.role);
   // Rolle waehlen = ALLE Chars dieser Rolle, darum den Charakter-Filter zuruecksetzen
   // (sonst blieb ein zuvor gewaehlter einzelner Char haengen und nur der zeigte sich).
   localStorage.setItem('charFilter','');
   const cf=document.getElementById('charFilter'); if(cf)cf.value='';
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
// Mining Fleet Power: eine Hashrate-artige Zahl fuer die Foerderleistung der
// ganzen Flotte in m³/min. Stufe 1 (hier) rechnet aus der real geloggten Rate,
// darum als "geschaetzt" gekennzeichnet; das ESI-Siegel kommt in Stufe 2.
// Missions-Kachel: Name + Genauigkeit in % + Guide-Link. m ist {name,conf} oder null.
function missionHtml(m){
 if(!m||!m.name)return '';
 const c=m.conf!=null?` <span class="mconf">~${m.conf}% sicher</span>`:'';
 return `🎯 ${esc(m.name)}${c} <a href="https://duckduckgo.com/?q=${encodeURIComponent('EVE Online '+m.name+' mission guide')}" target="_blank" rel="noopener">Guide</a>`;
}
function mfpTier(m){
 if(m>=15000)return {n:'Rorqual-Overlord',c:'gold'};
 if(m>=6000)return {n:'Erz-Baron',c:'gold'};
 if(m>=2500)return {n:'Industrie-Flotte',c:'cyan'};
 if(m>=1000)return {n:'Flotten-Operator',c:'cyan'};
 if(m>=300)return {n:'Gürtel-Miner',c:'green'};
 return {n:'Prospektor',c:'dim'};
}
// Dauerleistung eines Chars aus der echten Minutenrate (Top-5-Schnitt der letzten
// 60 min), NICHT aus der hochgerechneten m³/h. So spiegelt die Zahl die reale
// Foerderleistung waehrend des Minens, ohne Fruehsession-Ausreisser.
function sustainedRate(c){
 const a=[...(c.spark||[])].sort((x,y)=>y-x).slice(0,5);
 return a.length?a.reduce((s,v)=>s+v,0)/a.length:0;
}
// Alle MFP-Kennzahlen einer Flotte an einer Stelle, damit Karte und Share-Bild
// exakt dieselben Werte zeigen.
function mfpValues(chars){
 const miners=chars.filter(c=>c.active&&autoRole(c)==='mining');
 const m3min=miners.reduce((s,c)=>s+sustainedRate(c),0);
 const ver=miners.filter(c=>c.esi_mining);
 const mined=ver.reduce((s,c)=>s+(c.mined_30d||0),0);
 const bonusVals=ver.map(c=>c.skill_bonus).filter(b=>b!=null);
 const avgBonus=bonusVals.length?Math.round(bonusVals.reduce((s,b)=>s+b,0)/bonusVals.length):null;
 const top=[...miners].sort((a,b)=>sustainedRate(b)-sustainedRate(a))[0];
 // Name fuers Teilen: gesetzter Main-Char > Command-Ship-Pilot (Flottenchef) >
 // Top-Miner. So steht auf dem geteilten Bild der gewuenschte Char, nicht zufaellig
 // der mit der hoechsten Rate.
 const act=chars.filter(c=>c.active);
 const mainName=(localStorage.getItem('mainChar')||'');
 let owner='';
 if(mainName&&act.some(c=>c.name===mainName))owner=mainName;
 else{const b=act.find(c=>c.command_ship);owner=b?b.name:(top?top.name:'');}
 return {miners,m3min,ver,mined,avgBonus,tier:mfpTier(m3min),
         fullVer:ver.length>0&&ver.length===miners.length,owner};
}
function fleetPowerCard(chars){
 const v=mfpValues(chars);
 if(!v.miners.length)return '';
 const t=v.tier, n=v.miners.length;
 const pct=Math.min(100,100*v.m3min/15000);   // Balken relativ zu 15000 = voll
 let sub;
 if(v.fullVer)sub=n+' '+(n===1?'Schiff':'Schiffe')+' · ✅ ESI-verifiziert';
 else if(v.ver.length)sub=v.ver.length+' von '+n+' ESI-verifiziert · Rest geschätzt';
 else sub=n+' '+(n===1?'Schiff':'Schiffe')+' · geschätzt aus Log';
 const verLine=v.mined>0
   ?`<div class="mfpver">✅ ESI-verifiziert: <b>${fmtC(v.mined)} m³</b> in 30 Tagen gefördert · Ø ${fmtC(v.mined/30)}/Tag${v.avgBonus!=null?' · Skill-Bonus +'+v.avgBonus+'%':''}</div>`
   :'';
 return `<div class="card mfp" style="grid-column:1/-1">
   <div class="mfphead">
    <span class="mfptitle">⚡ Mining Fleet Power</span>
    <span class="mfphr">
     <span class="mfprank ${t.c}">${t.n}</span>
     <button class="mfpshare" onclick="shareMfp(this)" title="Als Bild teilen">📤 Teilen</button>
    </span>
   </div>
   <div class="mfpmain">
    <span class="mfpval ${t.c}">${fmt(Math.round(v.m3min))}</span>
    <span class="mfpunit">m³/min</span>
    <span class="mfpsub">${sub}</span>
   </div>
   <div class="mfpbarwrap"><div class="mfpbar ${t.c}" style="width:${pct}%"></div></div>
   ${verLine}
  </div>`;
}
// Stufe 3: teilbares Bild. Zeichnet die MFP als sauberes PNG (Zahl, Rang, Siegel,
// Canary-Branding, Homepage-Link), laedt es herunter und legt es zusaetzlich in
// die Zwischenablage. Nichts Externes, alles per Canvas.
const MFP_COLOR={gold:'--gold',cyan:'--cyan',green:'--green',dim:'--dim'};
function shareMfp(btn){
 const v=mfpValues(lastChars||[]);
 if(!v.miners.length)return;
 const en=(lang==='en');
 const cs=getComputedStyle(document.documentElement);
 const C=(name,fb)=>((cs.getPropertyValue(name)||'').trim())||fb;
 const bg=C('--bg','#0b0e13'),card=C('--card','#141922'),line=C('--line','#2a313d'),
   dim=C('--dim','#8a94a6'),white=C('--white','#eaf0f7'),cyan=C('--cyan','#5fc1d4'),
   accent=C(MFP_COLOR[v.tier.c]||'--cyan','#5fc1d4');
 const W=1200,H=630,cv=document.createElement('canvas');cv.width=W;cv.height=H;
 const x=cv.getContext('2d');
 const rr=(px,py,pw,ph,r)=>{x.beginPath();x.moveTo(px+r,py);x.arcTo(px+pw,py,px+pw,py+ph,r);
   x.arcTo(px+pw,py+ph,px,py+ph,r);x.arcTo(px,py+ph,px,py,r);x.arcTo(px,py,px+pw,py,r);x.closePath();};
 x.fillStyle=bg;x.fillRect(0,0,W,H);
 rr(40,40,W-80,H-80,22);x.fillStyle=card;x.fill();x.lineWidth=2;x.strokeStyle=line;x.stroke();
 const PX=90;
 // Kopf: Vogel + Marke
 x.textBaseline='alphabetic';
 x.font='bold 46px sans-serif';x.fillStyle=white;
 x.fillText('🐤',PX,140);
 x.fillStyle=cyan;x.fillText('EVE',PX+70,140);
 x.fillStyle=white;x.fillText('CANARY',PX+70+x.measureText('EVE ').width,140);
 // Label
 x.font='600 26px sans-serif';x.fillStyle=dim;
 x.fillText((en?'MINING FLEET POWER':'MINING FLEET POWER').toUpperCase(),PX,210);
 // Rang-Chip oben rechts
 const rank=en?tierEn(v.tier.n):v.tier.n;
 x.font='bold 26px sans-serif';const rw=x.measureText(rank).width+44;
 rr(W-90-rw,96,rw,52,26);x.strokeStyle=accent;x.lineWidth=2;x.stroke();
 x.fillStyle=accent;x.textAlign='center';x.fillText(rank,W-90-rw/2,131);x.textAlign='left';
 // Grosse Zahl
 x.font='800 150px sans-serif';x.fillStyle=accent;
 const num=fmt(Math.round(v.m3min));x.fillText(num,PX,360);
 const nw=x.measureText(num).width;
 x.font='600 44px sans-serif';x.fillStyle=dim;x.fillText('m³/min',PX+nw+22,360);
 // Balken
 const bw=W-2*PX,pct=Math.min(1,v.m3min/15000);
 rr(PX,392,bw,14,7);x.fillStyle=line;x.fill();
 rr(PX,392,Math.max(14,bw*pct),14,7);x.fillStyle=accent;x.fill();
 // Siegel / Beleg
 x.font='600 30px sans-serif';
 if(v.mined>0){
  x.fillStyle=C('--green','#57c98a');
  const txt=en?`✅ ESI-verified · ${fmtC(v.mined)} m³ / 30 days`+(v.avgBonus!=null?` · skill +${v.avgBonus}%`:'')
              :`✅ ESI-verifiziert · ${fmtC(v.mined)} m³ / 30 T`+(v.avgBonus!=null?` · Skill +${v.avgBonus}%`:'');
  x.fillText(txt,PX,470);
 }else{
  x.fillStyle=dim;x.fillText(en?'estimated from log':'geschätzt aus Log',PX,470);
 }
 // Flotte + Besitzer
 x.font='400 26px sans-serif';x.fillStyle=dim;
 const nm=v.miners.length;
 x.fillText((en?`${nm} ${nm===1?'ship':'ships'}`:`${nm} ${nm===1?'Schiff':'Schiffe'}`)
   +(v.owner?` · ${v.owner}${nm>1?' +'+(nm-1):''}`:''),PX,516);
 // Fuss: Homepage
 x.font='600 26px sans-serif';x.fillStyle=cyan;
 x.fillText('eve-online-askend.github.io/eve-canary',PX,560);
 // Ausgabe: Download + Zwischenablage
 cv.toBlob(function(blob){
  if(!blob)return;
  try{const u=URL.createObjectURL(blob);const a=document.createElement('a');
   a.href=u;a.download='eve-canary-fleet-power.png';a.click();
   setTimeout(()=>URL.revokeObjectURL(u),5000);}catch(e){}
  try{navigator.clipboard.write([new ClipboardItem({'image/png':blob})]);}catch(e){}
  if(btn){const o=btn.textContent;btn.textContent=en?'✓ Saved':'✓ Gespeichert';
   setTimeout(()=>{try{btn.textContent=o;}catch(e){}},2500);}
 },'image/png');
}
function tierEn(n){const m={'Rorqual-Overlord':'Rorqual Overlord','Erz-Baron':'Ore Baron',
 'Industrie-Flotte':'Industrial Fleet','Flotten-Operator':'Fleet Operator',
 'Gürtel-Miner':'Belt Miner','Prospektor':'Prospector'};return m[n]||n;}
// "Aktuelle Flotte": nur wenn ein Command Ship (Orca/Porpoise/Rorqual) am Steuer
// sitzt. Zeigt Flottengroesse (getrackte aktive Mining-Chars), Mining Power und die
// ueber die Flotte komprimierte Menge. Ohne Booster keine Kachel (dann reicht MFP).
function fleetCard(chars){
 const active=chars.filter(c=>c.active);
 const boosters=active.filter(c=>c.command_ship);
 if(!boosters.length)return '';                       // nur mit Command Ship
 // Welches Command Ship (Schiff · Pilot), bei mehreren alle.
 const ship=boosters.map(c=>esc(c.ship||'Command Ship')+' ('+esc(c.name)+')').join(', ');
 // Wer komprimiert wie viel, aus dem BOOSTER-Log: fleet_compress nennt jeden
 // Flottenpiloten namentlich (auch Fremde), c.compressed des Boosters ist seine
 // eigene Kompression. So sieht man die ganze Flotte, nicht nur eigene Boxen.
 const fc={};
 const add=(n,m3,isk)=>{const c=fc[n]||{m3:0,isk:0};fc[n]={m3:c.m3+m3,isk:c.isk+isk};};
 boosters.forEach(b=>{
  (b.fleet_compress||[]).forEach(f=>add(f.name,f.m3||0,f.isk||0));
  const own=(b.compressed||[]).reduce((a,x)=>({m3:a.m3+(x.m3||0),isk:a.isk+(x.isk||0)}),{m3:0,isk:0});
  if(own.m3>0)add(b.name,own.m3,own.isk);
 });
 const per=Object.entries(fc).map(([n,v])=>[n,v.m3,v.isk]).sort((a,b)=>b[1]-a[1]);
 const totM3=per.reduce((s,p)=>s+p[1],0), totIsk=per.reduce((s,p)=>s+p[2],0);
 const list=per.length
   ?`<div class="mfpver">🗜 ${per.length} ${per.length===1?'Spieler komprimiert':'Spieler komprimieren'}:</div>`
    +`<table class="fleetcomp">`+per.map(([n,m3,isk])=>
      `<tr><td>${esc(n)}</td><td class="r">${fmt(m3)} m³</td><td class="r isk">${fmtM(isk)} ISK</td></tr>`).join('')
    +`</table>`
   :`<div class="mfpver" style="color:var(--dim)">🗜 Noch keiner komprimiert diese Session</div>`;
 return `<div class="card mfp" style="grid-column:1/-1">
   <div class="mfphead"><span class="mfptitle">🛰 Aktuelle Flotte</span>
    <span class="mfprank cyan">✅ Command Ship erkannt</span></div>
   <div class="mfpmain">
    <span class="mfpval cyan">${fmtC(totM3)}</span>
    <span class="mfpunit">m³ komprimiert</span>
    <span class="mfpsub">≈ ${fmtM(totIsk)} ISK · Boost: ${ship}</span>
   </div>
   ${list}
  </div>`;
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
 $('#hero').innerHTML=fleetPowerCard(chars)+fleetCard(chars)+heroBar(summary);
 if(!chars.length){$('#empty').hidden=false;
  $('#empty').textContent=!showOff?'Gerade ist kein Charakter eingeloggt. Mit „💤 Offline zeigen" siehst du auch die abgemeldeten.':(rf?'Kein Charakter mit dieser Rolle. Tippe auf einer Karte auf das Rollen-Symbol, um sie zuzuweisen.':'Warte auf Gamelog-Daten … (EVE-Client an? Im Client „Spielprotokoll speichern" aktivieren.)');
  $('#grid').innerHTML='';return;}
 $('#empty').hidden=true;
 $('#grid').innerHTML=safeCards(chars);
 wireCards();
}
// Mining-Karte eines Charakters (Erz, m³, Heavy Water, Lager, Gefahr).
function miningCardHtml(c){
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
    <span class="mini">${c.cargo_full?'<span class="warnbadge drone">⚠ Frachtraum voll!</span> · ':''}${(c.tool_warns||[]).map(w=>'<span class="warnbadge'+(w.drone?' drone':'')+'">⚠ '+esc(w.tool)+(w.count>1?' ×'+w.count:'')+'</span> · ').join('')}${(c.lasers_off||[]).map(w=>'<span class="warnbadge">⛔ '+esc(w.tool)+' aus</span> · ').join('')}${c.heavy_water&&c.heavy_water.on&&c.heavy_water.min_left<30?'<span class="warnbadge drone">⛽ HW ~'+c.heavy_water.min_left+' min</span> · ':''}${c.drones_idle?'<span class="warnbadge">🤖 Drohnen ohne Erz</span> · ':''}${c.laser_stalled?'<span class="warnbadge">⛏ Laser ohne Erz</span> · ':''}${c.rate_low?'<span class="warnbadge">⚠ Rate '+c.rate_low+'%</span> · ':''}${mineIdle(c,state)?'<span class="warnbadge">⚠ Kein Erz seit '+Math.round(c.mine_idle/60)+' min</span> · ':''}${fmtM(c.total_isk)} ISK · ${fmt(c.m3h)} m³/h${c.dps_in>0?' · <span class=\"in\">⚠ '+c.dps_in+' DPS rein</span>':''}</span>
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
   ${(localStorage.getItem('iskCoach')==='1'&&c.lost_isk>=1000&&!c.command_ship)?`<div class="cardwarn">💸 ${lang==='en'?'Downtime loss this session':'Stillstand-Verlust diese Session'}: ≈ ${fmtM(c.lost_isk)} ISK${c.lost_paused?(lang==='en'?' <span style="color:var(--dim);font-weight:400">(paused, docked/warp)</span>':' <span style="color:var(--dim);font-weight:400">(pausiert, angedockt/Warp)</span>'):''}</div>`:''}
   <div class="sub">${c.trips>0?'Trip '+(c.trips+1)+' · seit Abdocken':'Session'} ${c.session_min} min · ${c.depleted} Asteroiden leergebaggert · Preise: ${state.price_src==='esi'?'ESI · ':''}${state.regions[state.region]}</div>
   ${dangerLine(c)}
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
   ${c.spark.length>1?(()=>{const sp=c.spark,n=sp.length,peak=Math.max(...sp),avg=Math.round(sp.reduce((a,b)=>a+b,0)/n);
     return `<div class="spark" title="${lang==='en'?'Ore mined per minute, one bar per minute':'Gefördertes Erz pro Minute, ein Balken je Minute'}">${sp.map((v,i)=>`<div title="${lang==='en'?'min':'Min'} -${n-1-i}: ${fmt(v)} m³" style="height:${Math.max(3,100*v/maxS)}%"></div>`).join('')}</div>
     <div class="sub">${lang==='en'?'Mining m³/min · last':'Mining m³/min · letzte'} ${n} min · ${lang==='en'?'peak':'Spitze'} ${fmt(peak)} · Ø ${fmt(avg)}</div>`;})():''}
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
   </div>
  </div>`;
}
// Ohne gesetzte Rolle versucht Canary die Karte selbst zu erraten: wer Schaden
// macht (oder Waffen/Ziele hat) und nicht mint, bekommt die Kampf-Karte; wer mint
// und nicht kaempft, die Mining-Karte. Nur wenn es eindeutig ist. Sonst entscheidet
// der oben gewaehlte Modus. So muss man fuer Kampf-Chars keine Rolle mehr setzen.
function autoRole(c){
 if(c.role)return c.role;
 const mining=(c.m3||0)>0||(c.ores&&c.ores.length>0);
 const combat=(c.dmg_out||0)>0||(c.weapons&&c.weapons.length>0)||(c.top_targets&&c.top_targets.length>0);
 if(combat&&!mining)return 'pvp';
 if(mining&&!combat)return 'mining';
 return liveMode==='combat'?'pvp':'mining';
}
// Karte je nach Rolle waehlen: Mining-Chars -> Mining-Karte, alle anderen
// (Missionen/PvP) -> Kampf-Karte. So sieht man in einer gemischten Flotte
// fuer jeden das Richtige.
function cardHtml(c){
 return autoRole(c)==='mining'?miningCardHtml(c):combatCardHtml(c);
}
// Grid robust rendern: ein Char, dessen Karte einen Fehler wirft, darf nicht das
// ganze Grid leeren. Er bekommt eine kleine Fehler-Karte (mit Grund), der Rest steht.
function safeCards(chars){
 return chars.map(c=>{
  try{return cardHtml(c);}
  catch(e){console.error('cardHtml',c&&c.name,e);
   return `<div class="card"><div class="chead"><span class="char">${esc((c&&c.name)||'?')}</span></div>`
     +`<div class="cardwarn">⚠ Anzeige-Fehler: ${esc(e&&e.message||String(e))}</div></div>`;}
 }).join('');
}
// Event-Handler fuer beide Kartentypen; Selektoren, die im jeweiligen Grid nicht
// vorkommen, treffen einfach nichts.
function wireCards(){
 document.querySelectorAll('.chead').forEach(h=>h.onclick=()=>toggleChar(h.dataset.c));
 document.querySelectorAll('.rolesel').forEach(s=>{
  s.onclick=e=>e.stopPropagation();  // Klick soll die Karte nicht ein-/ausklappen
  s.onfocus=()=>rolePickerBusy=true;         // offen -> Grid-Neubau pausieren
  s.onblur=()=>rolePickerBusy=false;
  s.onchange=async()=>{rolePickerBusy=false;await post({action:'set_role',char:s.dataset.c,role:s.value});
   if(lastChars){lastChars.forEach(c=>{if(c.name===s.dataset.c)c.role=s.value;});renderLiveView();}};
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
// Fraktions-Tipp (Alpha): welchen Schaden du bekommst (tanken) und welchen du
// am besten austeilst (schiessen). Kommt aus den Gegnernamen im Kampflog.
const DMG_LABEL={de:{em:'EM',therm:'Thermal',kin:'Kinetik',exp:'Explosiv'},
                 en:{em:'EM',therm:'Thermal',kin:'Kinetic',exp:'Explosive'}};
function dmgList(codes){const M=DMG_LABEL[lang==='en'?'en':'de'];return (codes||[]).map(c=>M[c]||c).join('/');}
function factionHtml(f){
 if(!f||!f.fac)return '';
 const mixed=f.share!=null&&f.share<85?` <span class="fdim">~${f.share}%</span>`:'';
 const ew=f.ewar?(EWAR_LABEL[f.ewar]||f.ewar):'';
 return `<div class="ftag">
   <span class="fbadge">🛡️ ${esc(f.fac)}${mixed}</span>
   <span class="fshoot">${lang==='en'?'shoot':'schieße'} <b>${dmgList(f.shoot)}</b></span>
   <span class="ftank">${lang==='en'?'tank':'tanke'} <b>${dmgList(f.deal)}</b></span>
   ${ew?`<span class="fdim">${lang==='en'?'their EWAR':'ihr EWAR'}: ${ew}</span>`:''}
   <span class="falpha" title="${lang==='en'?'Experimental, being verified':'Experimentell, wird noch geprüft'}">Alpha</span>
  </div>`;
}
// EWAR gegen dich als kompakte Zeile (Missions-Historie und Live-Karte).
function ewarHtml(ewar){
 if(!ewar||!ewar.length)return '';
 return `<div class="cardwarn drone">⚠ ${lang==='en'?'EWAR against you':'EWAR gegen dich'}: `
   +ewar.map(e=>(EWAR_LABEL[e[0]]||e[0])+' ×'+e[1]).join(' · ')+`</div>`;
}
function cargoLine(cg){
 if(!cg)return '<div class="l">über EVE-Login</div>';
 const now=Date.now()/1000;
 const age=Math.max(0,Math.round((now-cg.as_of)/60));
 const nxt=Math.round((cg.next-now)/60);
 const when=new Date(cg.as_of*1000).toISOString().slice(11,16);
 return `<div class="l">Stand: vor ${age} min · EVE ${when} · ${nxt>0?'nächste in '+nxt+' min':'wird aktualisiert'}</div>`;
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
 $('#grid').innerHTML=safeCards(chars);
 wireCards();
}
// Kampf-Karte eines Charakters (Bounty, Loot, Offense/Defense, Waffen).
function combatCardHtml(c){
  const min=collapsed.has(c.name);
  const shots=(c.hits_out||0)+(c.miss_out||0);
  const hit=shots?Math.round(100*c.hits_out/shots):null;
  const maxW=Math.max(1,...c.weapons.map(w=>w[1]));
  const sessISK=(c.bounty||0)+((c.cargo&&c.cargo.buy)||0);
  // Kampf da, aber keine Bounty-Zeile im Log (Client-Meldung aus) -> Hinweis,
  // damit klar ist warum Kills/Bounty 0 sind. Erst ab mehreren Gegnertypen,
  // damit es nicht schon zu Sessionbeginn faelschlich aufpoppt.
  const noBountyData=(c.dmg_out||0)>0&&!(c.bounty>0)&&!(c.kills>0)&&(c.enemy_types||0)>=2;
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
    ${c.mission
      ?`<div class="mtag" style="margin-top:8px">${missionHtml(c.mission)}</div>`
      :(((c.dmg_out||0)>0||(c.top_targets&&c.top_targets.length))
        ?`<div class="mtag mtired" style="margin-top:8px" title="Keine Mission erkannt. Entweder Ratting ohne feste Mission oder eine Signatur, die Canary noch nicht kennt.">🔍 Keine Erkennungsdaten gefunden</div>`
        :'')}
    ${factionHtml(c.faction)}
    ${(c.npc&&c.npc.length)?`<div class="npc">${c.npc.map(l=>`<div>💬 ${esc(l)}</div>`).join('')}</div>`:''}
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
     ${c.kills>0
       ?`<div class="stat"><div class="l">Kills</div><div class="v">${c.kills}</div></div>`
       :`<div class="stat"><div class="l">Gegner bekämpft</div><div class="v">${c.enemy_types||0}</div><div class="l" title="EVE protokolliert keine NPC-Tode. Ohne Bounty ist die Zahl der bekämpften Gegnertypen der einzige gesicherte Wert.">Typen · aus Log</div></div>`}
    </div>
    ${noBountyData?`<div class="cardnote">ℹ️ Für diese Mission liegen keine Bounty-Daten im Log vor, daher werden Kills und Bounty hier nicht gezählt. In EVE die Bounty-Meldungen im Combat-Log aktivieren, dann zählt Canary sie live mit. Die echte Bounty-ISK kommt bei EVE-Login aus dem Wallet.</div>`:''}
    ${c.weapons.length?`<div class="sect">Waffen</div><table>`+c.weapons.map(w=>
      `<tr><td>${esc(w[0])}<div class="bar" style="width:${100*w[1]/maxW}%"></div></td><td class="r">${fmt(w[1])} dmg</td></tr>`).join('')+`</table>`:''}
    ${c.top_targets.length?`<div class="sect">${c.kills>0?'Top-Ziele':'Bekämpfte Gegner · '+(c.enemy_types||c.top_targets.length)+' Typen'}</div><table>`+c.top_targets.map(t=>
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
   </div>
  </div>`;
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
  <div class="card"><div class="char">Stillstand-Verlust</div>
   <div class="sub">Geschätzt entgangenes ISK, weil Laser oder Drohnen standen oder die Rate einbrach (je Trip beim Docken erfasst).</div>
   <div class="v isk" style="font-size:22px">${fmtM(a.lost_isk||0)}</div></div>
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
// Firefox/Safari-Overlay: Video-Picture-in-Picture mit einer live gezeichneten Canvas
// (diese Browser haben kein Document-PiP, aber Video-PiP ist echtes Always-on-top).
let ffVid=null, ffCanvas=null, ffCtx=null, ffStream=null;
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
 // Schon offen? Beide Pfade sauber schliessen.
 if(pipWin){pipWin.close();pipWin=null;return;}
 if(ffVid){try{if(document.pictureInPictureElement)await document.exitPictureInPicture();}catch(e){}ffCleanup();return;}
 // Chrome/Edge: reiches, klickbares HTML-Overlay via Document-PiP.
 if('documentPictureInPicture' in window){
  try{pipWin=await documentPictureInPicture.requestWindow({width:330,height:260});}catch(e){return;}
  const d=pipWin.document;
  const st=d.createElement('style');st.textContent=OV_CSS;d.head.appendChild(st);
  d.title='EVE Canary';
  d.body.innerHTML='<div id="ov"><div class="hd"><span>🐤 <b>CANARY</b></span></div></div>';
  pipWin.addEventListener('pagehide',()=>{pipWin=null;});
  overlayTick();
  return;
 }
 // Firefox/Safari: Video-PiP mit Canvas (Bild-Overlay, echtes Always-on-top).
 const vid=document.createElement('video');
 if(!('requestPictureInPicture' in vid)||!document.pictureInPictureEnabled){
  alert('Dein Browser unterstützt kein schwebendes Overlay (kein Picture-in-Picture).');return;}
 ffCanvas=document.createElement('canvas');ffCanvas.width=340;ffCanvas.height=320;
 ffCtx=ffCanvas.getContext('2d');
 drawOverlayCanvas(null);                        // erste Zeichnung, bevor der Stream startet
 ffStream=ffCanvas.captureStream(4);
 vid.srcObject=ffStream;vid.muted=true;vid.playsInline=true;
 vid.style.cssText='position:fixed;left:-10000px;top:0;width:340px;height:320px;opacity:0';
 document.body.appendChild(vid);ffVid=vid;
 vid.addEventListener('leavepictureinpicture',ffCleanup);
 try{await vid.play();await vid.requestPictureInPicture();}
 catch(e){ffCleanup();alert('Overlay konnte nicht gestartet werden ('+(e&&e.message||e)+').');return;}
 overlayTick();
}
function ffCleanup(){
 try{if(ffStream)ffStream.getTracks().forEach(t=>t.stop());}catch(e){}
 try{if(ffVid&&ffVid.parentNode)ffVid.parentNode.removeChild(ffVid);}catch(e){}
 ffVid=ffCanvas=ffCtx=ffStream=null;
}
function ovColor(cls){return cls==='bad'?'#e8564f':cls==='warn'?'#e8c645':'#57c98a';}
// Overlay-Inhalt fuer Firefox/Safari auf die Canvas zeichnen (dasselbe wie das
// HTML-Overlay, nur als Bild). d=null -> Platzhalter.
function drawOverlayCanvas(d){
 const x=ffCtx; if(!x)return; const W=ffCanvas.width,H=ffCanvas.height;
 x.fillStyle='#0b0e13';x.fillRect(0,0,W,H);x.textBaseline='alphabetic';
 x.font='bold 16px sans-serif';x.fillStyle='#eaf0f7';x.textAlign='left';x.fillText('🐤 CANARY',10,24);
 x.font='12px sans-serif';x.fillStyle='#8a94a6';x.textAlign='right';x.fillText(new Date().toLocaleTimeString(),W-10,22);
 x.strokeStyle='#2a313d';x.lineWidth=1;x.beginPath();x.moveTo(8,32);x.lineTo(W-8,32);x.stroke();
 if(!d){x.textAlign='left';x.fillStyle='#8a94a6';x.font='13px sans-serif';x.fillText('warte auf Daten ...',12,58);return;}
 const now=Date.now()/1000; let y=50;
 (d.chars||[]).slice(0,6).forEach(c=>{
  const r=ovStatus(c,d.state),cls=r[0],txt=r[1];
  x.beginPath();x.arc(14,y+1,5,0,7);x.fillStyle=ovColor(cls);x.fill();
  x.textAlign='left';x.fillStyle='#eaf0f7';x.font='bold 14px sans-serif';
  x.fillText(c.name+' · '+(c.system||'?'),26,y+5);
  if(txt){x.fillStyle=cls==='bad'?'#e8564f':'#e8c645';x.font='12px sans-serif';x.fillText(txt,26,y+22);}
  x.textAlign='right';x.fillStyle='#eaf0f7';x.font='13px sans-serif';x.fillText(fmtM(c.total_isk),W-10,y+5);
  x.fillStyle='#8a94a6';x.font='11px sans-serif';x.fillText(fmt(c.m3h)+' m³/h',W-10,y+21);
  y+=37;
 });
 const alerts=(d.state.alerts||[]).filter(a=>now-a.ts<180).slice(-3).reverse();
 x.textAlign='left';x.font='11px sans-serif';
 alerts.forEach(a=>{
  x.fillStyle=(a.kind==='pvp'||a.kind==='cargo'||a.kind==='drones')?'#e8564f':'#e8c645';
  let t='['+new Date(a.ts*1000).toLocaleTimeString()+'] '+a.text; if(t.length>54)t=t.slice(0,53)+'…';
  x.fillText(t,10,y+4); y+=17;
 });
 if(alerts.some(a=>(a.kind==='pvp'||a.kind==='cargo'||a.kind==='drones')&&now-a.ts<45)){
  x.strokeStyle='#e8564f';x.lineWidth=3;x.strokeRect(1.5,1.5,W-3,H-3);}
}
function mineIdle(c,st){
 // Command Ships (Orca/Porpoise/Rorqual) minen nicht selbst nennenswert, sie
 // boosten und komprimieren -> kein "Kein Erz seit X min"-Alarm. Dort greift nur
 // die Drohnen-Idle-Warnung (drones_idle).
 if(c.command_ship)return false;
 return c.mine_idle&&st.idle_warn>0&&c.mine_idle>(c.idle_thr||st.idle_warn)&&c.mine_idle<1800;
}
// Der Stillstand-Verlust wird jetzt im Backend als tatsaechlicher, kumulierter
// Session-Wert gerechnet (c.lost_isk) und als eine Zeile angezeigt, statt als
// mehrere Frontend-Schaetzungen pro Warnung.
// Lagebild des aktuellen Systems aus offenen Daten (stuendlich). Bewusst als
// ruhige Info-Zeile, kein Alarm: eine Sekundenwarnung ist damit nicht moeglich.
function dangerLine(c){
 const d=c.danger; if(!d) return '';
 const sec=(d.sec!=null)?d.sec.toFixed(1):'?';
 const risk=d.ship_kills>=10?'r':(d.ship_kills>=4?'y':'g');
 const pods=d.pod_kills?', '+d.pod_kills+' Kapseln':'';
 return `<div class="sub dngline"><span class="dngdot ${risk}"></span>Sicherheit ${sec}`
  +` · Verluste letzte Stunde: ${d.ship_kills} Schiffe${pods} · Verkehr ${fmt(d.jumps)} Sprünge</div>`;
}
function ovStatus(c,st){
 if(c.dps_in>0)return['bad','UNTER BESCHUSS'];
 if(c.cargo_full)return['bad','FRACHTRAUM VOLL'];
 const tw=c.tool_warns||[];
 const dr=tw.find(w=>w.drone);
 if(dr)return['bad','DROHNEN PRÜFEN ('+esc(dr.tool)+')'];
 if(tw.length)return['warn',esc(tw[0].tool.toUpperCase())+(tw[0].count>1?' ×'+tw[0].count:'')+' AUS'];
 const lo=c.lasers_off||[];
 if(lo.length)return['warn',esc(lo[0].tool.toUpperCase())+' AUS'];
 if(c.drones_idle)return['warn','DROHNEN OHNE ERZ'];
 if(c.laser_stalled)return['warn','LASER OHNE ERZ'];
 if(c.heavy_water&&c.heavy_water.on&&c.heavy_water.min_left<30)return['warn','HEAVY WATER ~'+c.heavy_water.min_left+' MIN'];
 if(c.rate_low)return['warn','ABBAURATE '+c.rate_low+'%'];
 if(mineIdle(c,st))return['warn','KEIN ERZ SEIT '+Math.round(c.mine_idle/60)+' MIN'];
 return['ok',''];
}
async function overlayTick(){
 if(!pipWin&&!ffVid)return;
 try{
  const d=await (await fetch('/data?view=live')).json();
  if(ffVid){drawOverlayCanvas(d);return;}   // Firefox/Safari: Canvas neu zeichnen
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
// Live-Warnung: geflaggte Local-Sprecher nach Corp gruppiert (Gank-Flotte).
function fleetWarnHtml(fleets){
 if(!fleets||!fleets.length)return '';
 return `<div class="cardwarn drone" style="margin:0 0 10px">🚨 <b>${lang==='en'?'Possible gank fleet in local':'Mögliche Gank-Flotte im Local'}</b> `
  +`<span style="color:var(--dim);font-weight:400">${lang==='en'?'(from chat, passive)':'(aus dem Chat, passiv)'}</span></div>`
  +fleets.map(g=>`<div style="border-top:1px solid var(--line);padding:8px 0">
    <div><b style="color:var(--red)">${esc(g.corp)}</b>${g.alliance?` <span class="sub">[${esc(g.alliance)}]</span>`:''}
     · ${g.n} ${lang==='en'?'flagged pilots':'geflaggte Piloten'}${g.red?` <span class="warnbadge">🔴</span>`:''}
     ${g.systems&&g.systems.length?`· ${esc(g.systems.join(', '))}`:''}
     ${g.miner?`· ${g.miner} ${lang==='en'?'miner kills':'Miner-Kills'}`:''}</div>
    <div class="sub">${g.pilots.map(esc).join(', ')}</div></div>`).join('');
}
function renderIntel(auto,bs){
 if(!document.getElementById('intelBox')){
  $('#grid').innerHTML=`<div class="card" id="fleetWarn" style="grid-column:1/-1;display:none"></div>
   <div style="grid-column:1/-1;display:flex;gap:8px" id="intelModeRow">
    <span class="pill imode" data-im="scan">🚦 Local-Scan</span>
    <span class="pill imode" data-im="pack">🩸 Blutspur</span></div>
   <div id="packBox" style="grid-column:1/-1;display:none;flex-direction:column;gap:14px"></div>
   <div class="card" id="intelBox" style="grid-column:1/-1">
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
  document.querySelectorAll('.imode').forEach(p=>p.onclick=()=>{
   localStorage.setItem('intelMode',p.dataset.im);syncIntelMode();
   if(p.dataset.im==='pack'&&lastBs)renderBlutspur(lastBs);});
  syncIntelMode();
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
 const fw=document.getElementById('fleetWarn');
 if(fw){const h=fleetWarnHtml(auto&&auto.fleets);fw.innerHTML=h;fw.style.display=h?'':'none';}
 lastBs=bs||lastBs;
 if((localStorage.getItem('intelMode')||'scan')==='pack')renderBlutspur(lastBs);
 else intelPoll();
}
function syncIntelMode(){
 const m=localStorage.getItem('intelMode')||'scan';
 document.querySelectorAll('.imode').forEach(p=>p.classList.toggle('on',p.dataset.im===m));
 const ib=document.getElementById('intelBox'),pb=document.getElementById('packBox');
 if(ib)ib.style.display=m==='scan'?'':'none';
 if(pb)pb.style.display=m==='pack'?'flex':'none';
}
// ---- Blutspur: Gank-Rudel aus dem oeffentlichen Killmail-Strom ----
let lastBs=null;
function packAge(sec,en){
 const m=Math.max(0,Math.round(sec/60));
 const t=m<90?m+' min':Math.round(m/60)+' h';
 return en?(t+' ago'):('vor '+t);
}
function packMapSvg(mp,en){
 const S=mp.systems||[];
 const edges=(mp.edges||[]).map(e=>{const a=S[e[0]],b=S[e[1]];
  return `<line x1="${a.x}" y1="${a.y}" x2="${b.x}" y2="${b.y}" style="stroke:var(--line)" stroke-width="1.2"/>`;}).join('');
 // Kill-Spur je Rudel: verbundene Segmente, aeltere Abschnitte blasser.
 const trails=(mp.trails||[]).map(t=>{
  let seg='';
  for(let i=1;i<t.pts.length;i++){const a=t.pts[i-1],b=t.pts[i];
   const op=Math.max(0.25,1-(a.age/7200));
   seg+=`<line x1="${a.x}" y1="${a.y}" x2="${b.x}" y2="${b.y}" style="stroke:var(--red)" stroke-width="2.5" stroke-opacity="${op.toFixed(2)}"/>`;}
  if(t.pts.length){const last=t.pts[t.pts.length-1];
   seg+=`<circle cx="${last.x}" cy="${last.y}" r="7" fill="none" style="stroke:var(--red)" stroke-width="2.5"><title>${esc(t.label)}</title></circle>`;}
  return seg;}).join('');
 const arrows=(mp.arrows||[]).map(a=>
  `<line x1="${a.x1}" y1="${a.y1}" x2="${a.x2}" y2="${a.y2}" style="stroke:var(--red)" stroke-width="2" stroke-dasharray="6 4"><title>${en?'estimated from kill order':'aus Kill-Reihenfolge geschätzt'}</title></line>`).join('');
 const dots=S.map(s=>{
  const sec=s.sec>=0.45?'var(--green)':(s.sec>0?'var(--gold)':'var(--red)');
  const heat=s.heat?`<circle cx="${s.x}" cy="${s.y}" r="${Math.min(9+s.heat*2,20)}" style="fill:var(--red)" fill-opacity="0.16"/>`:'';
  const own=s.own?`<circle cx="${s.x}" cy="${s.y}" r="11" fill="none" style="stroke:var(--cyan)" stroke-width="2.5"/>`:'';
  const pk=(s.packs&&s.packs.length)?`<text x="${s.x}" y="${s.y-13}" text-anchor="middle" style="font-size:13px">🩸</text>`:'';
  return heat+own+`<circle cx="${s.x}" cy="${s.y}" r="4.5" style="fill:${sec}"><title>${esc(s.name||'')} · Sec ${s.sec!=null?s.sec:'?'}${s.jumps!=null?` · ${s.jumps} ${en?'jumps':'Sprünge'}`:''}${s.heat?` · ${s.heat} Kills/2h`:''}</title></circle>`+pk
   +`<text x="${s.x}" y="${s.y+19}" text-anchor="middle" style="fill:var(--${s.own?'cyan':'dim'});font-size:10px">${esc(s.name||'')}</text>`;}).join('');
 return `<div style="overflow-x:auto"><svg viewBox="0 0 1000 700" style="width:100%;height:auto">${edges}${trails}${arrows}${dots}</svg></div>`
  +`<div class="sub">${en?'dot = system (colour = sec) · red halo = kills last 2h · cyan ring = you · red line = pack kill trail · 🩸 = pack last seen here':'Punkt = System (Farbe = Sec) · roter Halo = Kills der letzten 2h · Cyan-Ring = du · rote Linie = Kill-Spur des Rudels · 🩸 = Rudel zuletzt hier'}</div>`;
}
function renderBlutspur(bs){
 const box=document.getElementById('packBox'); if(!box)return;
 // Nicht neu rendern, waehrend der Nutzer gerade das System-Feld tippt,
 // sonst wirft der 2s-Tick die Eingabe raus (gleiche Falle wie beim Intel-Feld).
 if(document.activeElement&&document.activeElement.id==='packCenter')return;
 const en=lang==='en', now=Date.now()/1000;
 if(!bs){box.innerHTML='';return;}
 if(!bs.on){
  box.innerHTML=`<div class="card"><b>🩸 Blutspur</b>
   <div class="sub" style="margin:8px 0">${en?'Detects active gank packs in your regions almost live from the public killmail stream: who repeatedly kills together, where they hunt, with an honest "last seen X min ago". Public data only (killmail.stream and zKillboard), nothing leaves your machine.':'Erkennt aktive Gank-Rudel deiner Regionen fast live aus dem öffentlichen Killmail-Strom: wer wiederholt gemeinsam tötet, wo sie jagen, mit ehrlichem „zuletzt gesehen vor X min". Nur öffentliche Daten (killmail.stream und zKillboard), nichts verlässt deinen Rechner.'}</div>
   <div class="sub" style="margin-bottom:10px">${en?'Watches everything within':'Beobachtet alles im Umkreis von'} <b>${bs.radius||20} ${en?'jumps around your system':'Sprüngen um dein System'}</b>${bs.center?' ('+esc(bs.center)+')':''} · ${en?'radius via pack_radius in config.json':'Radius über pack_radius in der config.json'}</div>
   <button class="btn" id="packOn">${en?'Enable Blood Trail':'Blutspur einschalten'}</button></div>`;
  const b=document.getElementById('packOn'); if(b)b.onclick=()=>post({action:'pack_cfg',on:true});
  return;
 }
 const badge= bs.mode==='live'?`<span class="esichk ok">● ${en?'live feed':'Live-Feed'}</span>`
  :bs.mode==='fallback'?`<span class="esichk" style="color:var(--gold)">● ${en?'fallback, hourly':'Fallback, stündlich'}</span>`
  :bs.mode==='laden'?`<span class="esichk" style="color:var(--cyan)">● ${en?'loading …':'lädt …'}</span>`
  :`<span class="esichk bad">● ${en?'feed down':'Feed tot'}</span>`;
 const age=bs.last_kill_age!=null?`${en?'last kill in region':'letzter Kill der Region'}: ${packAge(bs.last_kill_age,en)}`:(en?'no region kills yet':'noch keine Kills der Region');
 let html=`<div class="card"><div class="chead"><span class="char">🩸 Blutspur</span> ${badge}
   <span class="sub" style="margin-left:auto">${bs.center?esc(bs.center)+' · '+(bs.radius||20)+(en?' jumps':' Sprünge')+' · ':''}${age}</span></div>
  <div class="sub" style="margin-top:5px">🕯 ${en?'Honest by design: a pack becomes visible only AFTER its latest kill (echo principle), and only pilots who appear on killmails count. Silent campers stay invisible. Every age is computed from kill time, never receive time.':'Ehrlich per Bauart: ein Rudel wird erst NACH seinem letzten Kill sichtbar (Echo-Prinzip), und nur Piloten, die auf Killmails stehen, zählen. Stille Camper bleiben unsichtbar. Jede Zeitangabe kommt aus der Kill-Zeit, nie aus der Empfangszeit.'}</div>
  <div style="margin-top:9px;display:flex;align-items:center;gap:14px;flex-wrap:wrap">
   <label style="font-size:12px"><input type="checkbox" id="packCorp" ${bs.corp_alert?'checked':''}> ${en?'Corp escalation: hint when a local speaker is only in a pack corp':'Corp-Eskalation: Hinweis, wenn ein Local-Sprecher nur in einer Rudel-Corp ist'}</label>
   <button class="btn" id="packOff" style="font-size:11px">${en?'Disable':'Ausschalten'}</button>
   <span style="font-size:12px;margin-left:6px">${en?'Watched system:':'Beobachtetes System:'}</span>
   <button class="btn" id="packFollow" style="font-size:11px${bs.follow?';border-color:var(--cyan);color:var(--cyan)':''}">📍 ${en?'Use current location':'Aktuellen Standort nutzen'}${bs.follow?' ✓':''}</button>
   <input id="packCenter" placeholder="${esc(bs.center||'')}" style="width:120px;font-size:12px;padding:3px 7px;background:var(--inset);border:1px solid var(--line);border-radius:6px;color:var(--txt)">
   <button class="btn" id="packCenterGo" style="font-size:11px">${en?'Set':'Setzen'}</button>
   <span id="packCenterStat" class="sub">${bs.follow?(en?'follows your location':'folgt deinem Standort'):(en?'fixed':'fest gewählt')}</span></div>
  <div class="alphabanner" style="margin-top:10px">🧪 <b>${en?'Alpha phase, module in development':'Alpha-Phase, Modul in Entwicklung'}</b> · ${en?'pack detection, scores and warnings are still being tuned against real traffic. Feedback welcome.':'Rudel-Erkennung, Scores und Warnungen werden noch am echten Verkehr feinjustiert. Rückmeldungen willkommen.'}</div></div>`;
 if(bs.mode==='laden'){const mp=bs.map_progress||[0,0];
  html+=`<div class="card"><div class="sub">🗺 ${en?'Building region map':'Karte wird aufgebaut'} (${mp[0]}/${mp[1]} ${en?'systems':'Systeme'}) · ${en?'one-time, takes a few minutes, radar starts right after':'einmalig, dauert ein paar Minuten, danach startet das Radar von selbst'}</div></div>`;}
 // EINE kompakte Ansicht: Karte + Annaeherung + letzte Kills in einer Karte.
 let inner='';
 const mp0=(bs.maps||[])[0];
 if(mp0)inner+=`<div class="sub" style="margin-bottom:4px">🗺 ${esc(bs.center||'')} ${en?'centered':'zentriert'} · ${en?'neighbourhood':'Nachbarschaft'} ${mp0.depth} ${en?'jumps':'Sprünge'} · ${en?'watching':'überwacht'} ${bs.radius||20} ${en?'jumps':'Sprünge'}</div>`+packMapSvg(mp0,en);
 const near=(bs.packs||[]).filter(p=>p.dist!=null||p.last_system).sort((a,b)=>(a.dist??99)-(b.dist??99));
 if(near.length){
  inner+=`<div class="pistat2"><b>⚠ ${en?'Approach watch':'Annäherung'}</b>`+near.slice(0,6).map(p=>{
   const d=p.dist,cls=d!=null&&d<=3?'bad':(d!=null&&d<=10?'warn':'dim');
   const col=d!=null&&d<=3?'red':(d!=null&&d<=10?'gold':'dim');
   const trend=(p.dist_prev!=null&&p.dist_prev!==d)?`${p.dist_prev} → ${d}`:(d!=null?`${d}`:'?');
   // Bekannte Gank-Gruppe: Markierung mit Beleg, bewusst als Zahl und nicht
   // als Urteil ("Achtung, 58 Miner-Kills" statt "Ganker").
   const w=p.achtung?`<span class="pwatch" title="${esc(p.achtung.name)}: ${p.achtung.miner} ${en?'miner kills':'Miner-Kills'}, ${p.achtung.hauler} ${en?'hauler kills':'Transporter-Kills'} ${en?'in':'in'} ${p.achtung.systeme} ${en?'systems':'Systemen'}">${en?'CAUTION':'ACHTUNG'} ${esc(p.achtung.name)} · ${p.achtung.miner} ${en?'miner kills':'Miner-Kills'}</span> `:'';
   return `<div class="pinear"><span class="pidot ${cls}"></span>
     <b style="color:var(--${col});flex:none">${trend} ${en?'jumps':'Sprünge'}</b>
     <span class="pinearmid">${w}[${esc(p.label)}] · ${p.members} ${en?'pilots':'Piloten'} · ${en?'last seen':'zuletzt'} ${packAge(now-p.last_seen,en)} in ${esc(p.last_system)}</span>
     <span class="sub">${(p.top||[]).slice(0,3).map(m=>`<a href="https://zkillboard.com/character/${m.id}/" target="_blank" rel="noopener">${esc(m.name)}</a>`).join(' · ')}</span></div>`;
  }).join('')+`</div>`;
 } else if(bs.mode!=='laden'){
  inner+=`<div class="sub" style="margin-top:8px">${en?'No pack visible right now. Not a safety guarantee: packs appear only after their latest kill.':'Gerade kein Rudel sichtbar. Keine Sicherheits-Garantie: Rudel erscheinen erst nach ihrem letzten Kill.'}</div>`;
 }
 if((bs.kills||[]).length){
  const K={miner:['⛏','MINING','red'],booster:['🐋','BOOSTER','red'],hauler:['🚚','HAULER','gold'],pod:['💊','POD','dim'],kill:['⚔','KILL','dim']};
  inner+=`<div class="pistat2"><b>📡 ${en?'Latest kills in the bubble':'Letzte Kills in der Blase'}</b><table class="fleetcomp">`
   +bs.kills.slice(0,8).map(k=>{const c=K[k.klass]||K.kill;
    // Schiffsname verlinkt auf die Killmail. k.id fehlt nur bei Eintraegen,
    // die noch aus einer aelteren Fassung im Ticker liegen -> dann Klartext.
    const schiff=k.id?`<a href="https://zkillboard.com/kill/${encodeURIComponent(k.id)}/" target="_blank" rel="noopener" title="${en?'Open killmail on zKillboard':'Killmail auf zKillboard öffnen'}">${esc(k.ship)}</a>`:esc(k.ship);
    return `<tr><td>${c[0]}</td><td>${new Date(k.ts*1000).toLocaleTimeString().slice(0,5)}</td><td>${esc(k.system)}</td><td class="r">${k.jumps!=null?k.jumps+(en?' j':' Spr.'):''}</td><td><span class="pitier" style="color:var(--${c[2]})">${c[1]}</span> ${schiff}</td><td class="r isk">${k.value?fmtM(k.value):''}</td></tr>`;}).join('')
   +`</table></div>`;
 }
 html+=`<div class="card">${inner}</div>`;
 box.innerHTML=html;
 const pc=document.getElementById('packCorp'); if(pc)pc.onchange=()=>post({action:'pack_cfg',corp:pc.checked});
 const po=document.getElementById('packOff'); if(po)po.onclick=()=>post({action:'pack_cfg',on:false});
 const pf=document.getElementById('packFollow');
 if(pf)pf.onclick=()=>post({action:'pack_cfg',follow:true});
 const cg=document.getElementById('packCenterGo');
 const ci=document.getElementById('packCenter');
 if(ci)ci.onkeydown=e=>{if(e.key==='Enter'&&cg){e.preventDefault();cg.click();ci.blur();}};
 if(cg)cg.onclick=async()=>{
  const v=(document.getElementById('packCenter').value||'').trim();
  if(!v)return;
  const r=await post({action:'pack_cfg',center:v});
  const st=document.getElementById('packCenterStat');
  if(st)st.textContent=r&&r.ok?(lang==='en'?'rebuilding bubble …':'Blase wird neu aufgebaut …'):(lang==='en'?'system not found':'System nicht gefunden');
 };
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
// ---- Verlauf / Zeitachse: chronologischer Ereignisstrom je Charakter ----
let lastTimeline=null, tlWin=localStorage.getItem('tlWin')||'48h';
function tlRow(it){
 const t=new Date(it.ts*1000).toLocaleTimeString().slice(0,5);
 if(it.kind==='live'){
  const now=lang==='en'?'now':'jetzt';
  if(it.sub==='combat'){
   const nm=it.mission?missionHtml(it.mission):(lang==='en'?'<b>Combat</b>':'<b>Kampf</b>');
   return `<div class="tlrow live"><span class="tlt">${now}</span><span><span class="tllive">●</span> ${lang==='en'?'live':'läuft'} ⚔ ${nm} · ${it.kills} Kills · <span class="isk">${fmtM(it.bounty)}</span> · ${it.min} min${it.sys&&it.sys!=='?'?' · '+esc(it.sys):''}</span></div>`;
  }
  return `<div class="tlrow live"><span class="tlt">${now}</span><span><span class="tllive">●</span> ${lang==='en'?'mining now':'am Minen'} ⛏ ${fmt(it.m3)} m³ · <span class="isk">${fmtM(it.isk)}</span> · ${it.min} min${it.ore?' · '+esc(it.ore):''}${it.sys&&it.sys!=='?'?' · '+esc(it.sys):''}</span></div>`;
 }
 if(it.kind==='mine')
  return `<div class="tlrow"><span class="tlt">${t}</span><span>⛏ <b>Mining-Trip</b> ${fmt(it.m3)} m³ · <span class="isk">${fmtM(it.isk)}</span> · ${it.min} min${it.ore?' · '+esc(it.ore):''}${it.sys&&it.sys!=='?'?' · '+esc(it.sys):''}</span></div>`;
 if(it.kind==='combat'){
  const nm=it.mission?missionHtml(it.mission):(lang==='en'?'<b>Combat</b>':'<b>Kampf</b>');
  return `<div class="tlrow"><span class="tlt">${t}</span><span>⚔ ${nm} · ${it.kills} Kills · <span class="isk">${fmtM(it.bounty)}</span> · ${it.min} min${it.sys&&it.sys!=='?'?' · '+esc(it.sys):''}</span></div>`;
 }
 if(it.kind==='reward')
  return `<div class="tlrow"><span class="tlt">${t}</span><span>✅ <b>${lang==='en'?'Mission reward':'Missions-Belohnung'}</b> <span class="isk">${fmtM(it.amount)}</span>${it.agent?' · '+esc(it.agent):''} <span class="tlsrc">ESI</span></span></div>`;
 if(it.kind==='bonus')
  return `<div class="tlrow"><span class="tlt">${t}</span><span>⏱ <b>${lang==='en'?'Time bonus':'Zeitbonus'}</b> <span class="isk">${fmtM(it.amount)}</span> <span class="tlsrc">ESI</span></span></div>`;
 return '';
}
function renderTimeline(tl){
 lastTimeline=tl=tl||{}; const chars=tl.chars||[]; const now=tl.now||Date.now()/1000;
 if(!['48h','today','trip'].includes(tlWin))tlWin='48h';
 $('#hero').innerHTML='';
 const chip=(k,l)=>`<span class="tlchip${tlWin===k?' on':''}" data-w="${k}">${l}</span>`;
 let html=`<div class="card" style="grid-column:1/-1">
   <b>🕑 ${lang==='en'?'Timeline':'Verlauf'}</b>
   <span class="tlwins">${chip('48h',lang==='en'?'Last 48h':'Letzte 48h')}${chip('today',lang==='en'?'Today':'Heute')}${chip('trip',lang==='en'?'Current trip':'Aktueller Trip')}</span>
   <div class="sub" style="margin-top:6px">${lang==='en'?'Per character, EVE time. Log events are instant, ESI events are marked. Mining trips and missions appear as they complete.':'Pro Charakter, EVE-Zeit. Log-Ereignisse sofort, ESI-Ereignisse markiert. Mining-Trips und Missionen erscheinen, sobald sie abgeschlossen sind.'}</div></div>`;
 if(!chars.length)
  html+=`<div class="card" style="grid-column:1/-1"><div class="sub">${lang==='en'?'Nothing in the last 48h yet. Live activity shows at the top while a character is active; completed mining trips appear on docking.':'In den letzten 48h noch nichts. Laufende Aktivität steht oben, sobald ein Char aktiv ist; abgeschlossene Mining-Trips erscheinen beim Andocken.'}</div></div>`;
 for(const c of chars){
  let cut;
  if(tlWin==='today')cut=tl.day_start||0;
  else if(tlWin==='trip')cut=c.trip_start||tl.day_start||0;
  else cut=0;   // 48h: alles Gelieferte (Server hat schon auf 48h geschnitten)
  const items=(c.items||[]).filter(it=>it.ts>=cut);
  html+=`<div class="card" style="grid-column:1/-1">
    <div class="chead" style="cursor:default"><span class="char">${esc(c.char)}</span> <span class="sub">· ${items.length} ${lang==='en'?'events':'Ereignisse'}</span></div>
    ${items.length?items.map(tlRow).join(''):`<div class="sub">${lang==='en'?'Nothing in this window.':'Nichts in diesem Zeitfenster.'}</div>`}</div>`;
 }
 $('#grid').innerHTML=html;
 document.querySelectorAll('.tlchip').forEach(ch=>ch.onclick=()=>{tlWin=ch.dataset.w;localStorage.setItem('tlWin',tlWin);renderTimeline(lastTimeline);});
}
// ---- Spielstil-Radar je Charakter (6 Achsen, letzte 30 Tage) ----
const PROF_LABELS={de:{mine:'Mining',missions:'Missionen',pvp:'PvP',combat:'Kampfkraft',industry:'Industrie',ertrag:'Ertrag'},
                   en:{mine:'Mining',missions:'Missions',pvp:'PvP',combat:'Combat',industry:'Industry',ertrag:'Earnings'}};
// Achsen-Wert mit passender Einheit fuer den Hover-Tooltip.
function profVal(key,raw){
 if(key==='ertrag')return fmtM(raw)+' ISK';
 if(key==='missions')return raw+' '+(lang==='en'?'missions':'Missionen');
 if(key==='mine')return fmt(raw)+' m³';
 if(key==='industry')return fmt(raw)+' m³ '+(lang==='en'?'compressed':'komprimiert');
 return fmt(raw)+' '+(lang==='en'?'damage':'Schaden');   // pvp / combat
}
function radarSvg(axes){
 const cx=160,cy=140,R=92,n=axes.length;
 const L=PROF_LABELS[lang==='en'?'en':'de'];
 const ang=i=>(-90+i*360/n)*Math.PI/180;
 const pt=(i,r)=>[cx+Math.cos(ang(i))*r,cy+Math.sin(ang(i))*r];
 const poly=r=>axes.map((_,i)=>pt(i,r).map(v=>v.toFixed(1)).join(',')).join(' ');
 let grid='';for(const f of [0.25,0.5,0.75,1])grid+=`<polygon points="${poly(R*f)}" fill="none" stroke="var(--line)" stroke-width="1"/>`;
 const spokes=axes.map((_,i)=>{const [x,y]=pt(i,R);return `<line x1="${cx}" y1="${cy}" x2="${x.toFixed(1)}" y2="${y.toFixed(1)}" stroke="var(--line)" stroke-width="1"/>`;}).join('');
 const dv=a=>Math.max(0,Math.min(100,a.value));
 const tip=a=>esc((L[a.key]||a.key)+': '+profVal(a.key,a.raw));
 const dpoly=axes.map((a,i)=>pt(i,R*dv(a)/100).map(v=>v.toFixed(1)).join(',')).join(' ');
 // je Achse ein groesserer, unsichtbarer Hover-Kreis (leicht zu treffen) + der sichtbare Punkt
 const dots=axes.map((a,i)=>{const [x,y]=pt(i,R*dv(a)/100);const t=tip(a);
   return `<circle cx="${x.toFixed(1)}" cy="${y.toFixed(1)}" r="10" fill="transparent"><title>${t}</title></circle>`
     +`<circle cx="${x.toFixed(1)}" cy="${y.toFixed(1)}" r="3.2" style="fill:var(--red)" pointer-events="none"/>`;}).join('');
 const labels=axes.map((a,i)=>{const [x,y]=pt(i,R+16);const anc=Math.abs(x-cx)<8?'middle':(x>cx?'start':'end');
   return `<text x="${x.toFixed(1)}" y="${y.toFixed(1)}" text-anchor="${anc}" dominant-baseline="middle" style="fill:var(--dim);font-size:11px;cursor:default">${esc(L[a.key]||a.key)}<title>${tip(a)}</title></text>`;}).join('');
 return `<svg viewBox="0 0 320 280" style="width:100%;max-width:340px;height:auto">${grid}${spokes}<polygon points="${dpoly}" style="fill:var(--cyan);fill-opacity:.22;stroke:var(--cyan)" stroke-width="2"/>${dots}${labels}</svg>`;
}
function renderProfiles(list){
 $('#hero').innerHTML=''; list=list||[];
 const en=lang==='en', L=PROF_LABELS[en?'en':'de'], now=Date.now()/1000;
 let html=`<div class="card" style="grid-column:1/-1"><b>🪪 ${en?'Character sheet':'Steckbrief'}</b>
   <div class="sub" style="margin-top:6px">${en?'Per character: portrait, wallet, corp, ship, system and a playstyle radar over the last 30 days. Wallet/corp/ship from ESI, system live from the log; radar scaled relative to your strongest character per axis.':'Pro Charakter: Portrait, Wallet, Corp, Schiff, System und ein Spielstil-Radar über die letzten 30 Tage. Wallet/Corp/Schiff aus ESI, System live aus dem Log; Radar relativ zu deinem stärksten Char je Achse.'}</div></div>`;
 if(!list.length)html+=`<div class="card" style="grid-column:1/-1"><div class="sub">${en?'No activity in the last 30 days yet.':'In den letzten 30 Tagen noch keine Aktivität.'}</div></div>`;
 for(const p of list){
  const top=[...p.axes].sort((a,b)=>b.value-a.value)[0];
  const fresh=p.poll_ts?`🛰 ${en?'ESI as of':'ESI-Stand vor'} ${Math.max(0,Math.round((now-p.poll_ts)/60))} min · ${en?'synced every ~2 min':'Abgleich alle ~2 min'}`:(en?'🛰 no EVE login':'🛰 kein EVE-Login');
  const info=`<div class="sbinfo">
    ${p.portrait?`<img class="sbpf" src="${p.portrait}" alt="">`:'<div class="sbpf sbpf-none">👤</div>'}
    <div class="sbname">${esc(p.char)} ${esiBadge(p.char)}</div>
    <div class="sbrow">💰 <b class="isk">${p.wallet!=null?fmtM(p.wallet)+' ISK':'—'}</b></div>
    <div class="sbrow">🏢 ${p.corp?esc(p.corp):`<span class="sub">${en?'syncing …':'wird abgeglichen …'}</span>`}${p.alliance?' · '+esc(p.alliance):''}</div>
    <div class="sbrow">🚀 ${p.ship?esc(p.ship):'—'}${p.sec!=null?' · Sec '+p.sec:''}</div>
    <div class="sbrow">📍 ${p.system&&p.system!=='?'?esc(p.system):'—'}</div>
    <div class="sbrow">💎 ${p.ore_isk!=null?fmtM(p.ore_isk)+' ISK '+(en?'ore':'Erz'):'—'}</div>
    <div class="sub sbfresh">${fresh}</div></div>`;
  const radar=`<div class="sbradar"><div class="sub" style="text-align:center;margin-bottom:2px">${en?'focus':'Schwerpunkt'}: ${esc(L[top.key]||top.key)}</div>${radarSvg(p.axes)}</div>`;
  html+=`<div class="card"><div class="steckbrief">${info}${radar}</div></div>`;
 }
 $('#grid').innerHTML=html;
}
function renderVault(v){
 v=v||{}; const chars=v.chars||[];
 if(!chars.length){
  $('#grid').innerHTML='<div class="card" style="grid-column:1/-1"><div class="sub">Noch keine Asset-Daten. Verbinde deine Chars per EVE-Login (⚙ Optionen). Nach dem ersten Abgleich (bis zu 1 Stunde) erscheint hier dein Erz-Bestand.</div></div>';
  return;
 }
 const now=Date.now()/1000;
 const stand=v.as_of?'Stand: vor '+Math.max(0,Math.round((now-v.as_of)/60))+' min':'';
 const nxt=v.next?(()=>{const z=Math.round((v.next-now)/60);return z>0?'nächster Abgleich in '+z+' min':'Abgleich läuft gerade';})():'';
 let html=`<div class="card mfp" style="grid-column:1/-1">
   <div class="mfphead"><span class="mfptitle">💎 Erz-Schatzkammer</span></div>
   <div class="mfpmain">
    <span class="mfpval gold">${fmtC(v.total_m3||0)}</span>
    <span class="mfpunit">m³ Erz</span>
    <span class="mfpsub">≈ ${fmtM(v.total_isk||0)} ISK · ${chars.length} ${chars.length===1?'Char':'Chars'}${stand?' · '+stand:''}${nxt?' · '+nxt:''}</span>
   </div></div>`;
 const a=v.advisor;
 if(a&&a.rows&&a.rows.length){
  const en=lang==='en';
  const opt=(k,label)=>`<div class="advopt${a.best===k?' best':''}"><div class="l">${label}${a.best===k?` <span class="advrec">${en?'best':'empfohlen'}</span>`:''}</div><div class="v isk">${fmtM(a.totals[k]||0)}</div></div>`;
  const yld=Math.round((a.yield||0.5)*100);
  html+=`<div class="card" style="grid-column:1/-1">
    <div class="chead"><span class="char">💡 ${en?'Best way to process':'Bester Verwertungsweg'}</span> <span class="sub">· ${en?'valued for':'bewertet für'} ${esc(a.hub)}</span></div>
    <div class="advrow">
      ${opt('raw',en?'Sell raw':'Roh verkaufen')}
      ${opt('comp',en?'Sell compressed':'Komprimiert verkaufen')}
      ${opt('refine',en?'Refine to minerals':'Zu Mineralien raffinieren')}
    </div>
    <div class="sub" style="margin-top:6px">${en?'Refine yield':'Refine-Ausbeute'} ${yld}%${a.yield_char?' ('+esc(a.yield_char)+')':''} · ${en?'NPC station 50% base from your reprocessing skills; excludes structure rigs, standings, implants and ore-specific skills that raise it, so refine is a conservative floor. Compressing changes only volume, not the minerals.':'NPC-Station 50% Basis aus deinen Reprocessing-Skills; ohne Struktur-Rigs, Standings, Implantate und erz-spezifische Skills, die es erhöhen, Refine ist also eine konservative Untergrenze. Komprimieren ändert nur das Volumen, nicht die Mineralien.'}</div>`;
  const rws=a.rows.slice(0,12);
  html+=`<table class="fleetcomp advtbl"><tr><th>${en?'Ore':'Erz'}</th><th class="r">${en?'Units':'Menge'}</th><th class="r">${en?'Raw':'Roh'}</th><th class="r">${en?'Compressed':'Kompr.'}</th><th class="r">${en?'Refine':'Raffiniert'}</th></tr>`
   +rws.map(r=>`<tr><td>${esc(r.ore)}</td><td class="r">${fmt(r.units)}</td><td class="r${r.best==='raw'?' advb':''}">${fmtM(r.raw)}</td><td class="r${r.best==='comp'?' advb':''}">${fmtM(r.comp)}</td><td class="r${r.best==='refine'?' advb':''}">${fmtM(r.refine)}</td></tr>`).join('')
   +(a.rows.length>rws.length?`<tr><td colspan="5" class="sub">… ${a.rows.length-rws.length} ${en?'more ore types':'weitere Erz-Typen'}</td></tr>`:'')
   +`</table></div>`;
 }
 chars.forEach(c=>{
  html+=`<div class="card" style="grid-column:1/-1">
   <div class="chead"><span class="char">${esc(c.name)} <span class="sys">· ${fmtC(c.total_m3)} m³ · ${fmtM(c.total_isk)} ISK</span></span>${esiBadge(c.name)}</div>`;
  if(!c.locs.length){html+='<div class="sub">Kein Erz im Bestand.</div></div>';return;}
  c.locs.forEach(l=>{
   html+=`<div style="border-top:1px solid var(--line);padding:8px 0">
     <div style="display:flex;gap:7px;align-items:center;flex-wrap:wrap">${l.icon?`<img src="https://images.evetech.net/types/${l.icon}/icon?size=32" alt="" width="24" height="24" style="border-radius:3px;flex:none" onerror="this.style.display='none'">`:''}<b>${esc(l.name)}</b>
      <span style="margin-left:auto" class="isk">${fmtC(l.m3)} m³ · <b>${fmtM(l.isk)} ISK</b></span></div>
     <table class="fleetcomp">`+l.ores.map(o=>
       `<tr><td>${esc(o.ore)}</td><td class="r">${fmt(o.units)} Stk</td><td class="r">${fmt(o.m3)} m³</td><td class="r isk">${fmtM(o.isk)} ISK</td></tr>`).join('')
     +`</table></div>`;
  });
  html+='</div>';
 });
 $('#grid').innerHTML=html;
}
// Planetary Industry: Ueberblick + nach Ablauf sortierte Extraktor-Tafel +
// einklappbare Char-Bloecke. Countdown wird bei jedem Tick (2s) neu gerechnet.
let lastPlaneten=null;
function piType(t,en){
 const M={barren:['🟤','Barren','Öde'],temperate:['🟢','Temperate','Gemäßigt'],
  gas:['🟠','Gas','Gas'],ice:['🔵','Ice','Eis'],lava:['🔴','Lava','Lava'],
  oceanic:['🔵','Oceanic','Ozean'],plasma:['🟣','Plasma','Plasma'],storm:['⚪','Storm','Sturm']};
 const m=M[t]; return m?m[0]+' '+(en?m[1]:m[2]):(t||'');
}
// Reiner Typ-Name ohne Emoji (das Planeten-Render steht jetzt daneben).
function piTypeName(t,en){const p=piType(t,en);const i=p.indexOf(' ');return i>0?p.slice(i+1):p;}
function piGlobe(tid,cls){return tid?`<img class="${cls}" src="https://images.evetech.net/types/${tid}/icon?size=128" onerror="this.style.visibility='hidden'">`:'';}
// Produkt-Tier-Badge (P0-P4) mit fester Farbe je Stufe.
function piTierBadge(t){return t?`<span class="pitier ${t}">${t}</span>`:'';}
// Produkt-Chips (Icon + Name + Tier + Anzahl) fuer "Produziert".
function piProdList(products){return (products||[]).map(p=>
  `<span class="piprd">${p.type_id?`<img class="piicon2" src="https://images.evetech.net/types/${p.type_id}/icon?size=32" onerror="this.style.display='none'">`:''}${esc(p.name)}${piTierBadge(p.tier)}${p.count>1?' ×'+p.count:''}</span>`).join('');}
// ESI-Statusabzeichen je Charakter: gruen = verbunden + alle Scopes, rot = neu
// verbinden noetig. Nutzt state.esi.chars (kommt in jeder /data-Antwort mit).
function esiBadge(name){
 const c=((state.esi&&state.esi.chars)||[]).find(x=>x.name===name);
 if(!c)return '';
 const en=lang==='en';
 if(c.ok)return `<span class="esichk ok" title="${en?'ESI connected, all scopes granted':'ESI verbunden, alle Berechtigungen erteilt'}">✅ ESI</span>`;
 const miss=(c.missing&&c.missing.length)?' ('+(en?'missing: ':'fehlt: ')+c.missing.join(', ')+')':'';
 return `<span class="esichk bad" title="${(en?'ESI needs checking, reconnect this character (⚙ Options)':'ESI prüfen, diesen Charakter neu verbinden (⚙ Optionen)')+miss}">🔴 ESI</span>`;
}
function piLeft(expiry,en){
 if(!expiry)return {cls:'dim',txt:en?'no extractor':'kein Extraktor'};
 const s=expiry-Date.now()/1000;
 if(s<=0){const m=Math.round(-s/60), a=m<90?m+' min':Math.round(m/60)+' h';
  return {cls:'bad',txt:en?('expired '+a+' ago'):('abgelaufen vor '+a)};}
 const m=Math.round(s/60);
 const txt=m<90?('in '+m+' min'):(m<60*24?('in '+Math.round(m/60)+' h'):('in '+Math.round(m/1440)+(en?' d':' t')));
 return {cls:s<6*3600?'warn':'ok',txt};
}
function renderPlaneten(pl){
 lastPlaneten=pl=pl||{chars:[],extractors:[],reconnect:[]};
 const en=lang==='en', now=Date.now()/1000;
 syncCharFilter(pl.chars||[]);
 if(!(pl.chars||[]).length){
  const msg=(pl.reconnect||[]).length
   ?(en?`Reconnect your characters for Planetary Industry in ⚙ Options (new read-only permission "planets"). ${pl.reconnect.length} char(s) waiting.`
        :`Verbinde deine Charaktere für Planetary Industry neu (⚙ Optionen, neue Nur-Lese-Berechtigung „Planeten"). ${pl.reconnect.length} Char(s) warten.`)
   :(en?'No planetary colonies found on your connected characters. Connect a character with active PI via ⚙ Options.'
        :'Keine Planeten-Kolonien auf deinen verbundenen Charakteren gefunden. Verbinde einen Char mit aktiver PI über ⚙ Optionen.');
  $('#grid').innerHTML=`<div class="card" style="grid-column:1/-1"><b>🪐 Planetary Industry</b><div class="sub" style="margin-top:6px">${msg}</div></div>`;
  return;
 }
 const asof=pl.as_of?((en?'as of ':'Stand vor ')+Math.max(0,Math.round((now-pl.as_of)/60))+(en?' min ago':' min')):'';
 const nxt=pl.next?(()=>{const z=Math.round((pl.next-now)/60);return z>0?(en?'next sync in '+z+' min':'nächster Abgleich in '+z+' min'):(en?'syncing now':'Abgleich läuft gerade');})():'';
 const fresh=`🛰 ${[asof,nxt].filter(Boolean).join(' · ')}${asof||nxt?' · ':''}${en?'only as fresh as last opened in client':'so aktuell wie zuletzt im Client geöffnet'}`;
 const stored=(pl.total_isk?` · <span class="isk">≈ ${fmtM(pl.total_isk)} ISK ${en?'stored':'gelagert'}</span>`:'')
   +(pl.total_ext_isk?` · <span class="sub">~${fmtM(pl.total_ext_isk)} ISK ${en?'raw extraction':'Extraktion roh'}</span>`:'');
 const urg=(pl.n_exp||pl.n_soon)
  ?`<span style="color:var(--${pl.n_exp?'red':'gold'})">⚠ ${pl.n_exp?pl.n_exp+(en?' expired · ':' abgelaufen · '):''}${pl.n_soon}${en?' expiring < 6h':' laufen in < 6h ab'}</span>`
  :`<span style="color:var(--green)">${en?'all running':'alles läuft'}</span>`;
 const prodline=pl.products&&pl.products.length?`<div class="piprodline">🏭 <span class="sub">${en?'Produces':'Produziert'}:</span> ${piProdList(pl.products)}</div>`:'';
 let html=`<div class="card mfp" style="grid-column:1/-1"><div class="mfphead"><span class="mfptitle">🪐 Planetary Industry</span></div>
   <div class="mfpmain"><span class="mfpval gold">${pl.n_col}</span><span class="mfpunit">${en?'colonies':'Kolonien'}</span>
    <span class="mfpsub">${pl.n_char} ${pl.n_char===1?'Char':'Chars'} · ${pl.n_ex}${en?' extractors':' Extraktoren'} · ${urg}${stored}</span></div>
   ${prodline}
   <div class="sub" style="margin-top:8px">${fresh}</div></div>`;
 // Was zuerst nachfüllen (char-übergreifend, nach Ablauf sortiert)
 html+=`<div class="card" style="grid-column:1/-1"><div class="chead"><span class="char">${en?'What to reload first':'Was zuerst nachfüllen'}</span> <span class="sub">· ${en?'sorted by expiry':'nach Ablauf sortiert'}</span></div>`;
 const board=(pl.extractors||[]).slice(0,12);
 if(!board.length)html+=`<div class="sub">${en?'No extractors.':'Keine Extraktoren.'}</div>`;
 board.forEach(e=>{const L=piLeft(e.expiry,en);
  html+=`<div class="pirow"><span class="pidot ${L.cls}"></span>
    <span class="pichar">${esc(e.char)}</span>
    <span class="piplanet">${piGlobe(e.type_id,'piglobe')}<span class="pinm">${esc(e.planet)}</span> <span class="sub">${piTypeName(e.type,en)}</span></span>
    <span class="piprod">${esc(e.product||'?')}${piTierBadge(e.tier)}</span>
    <span class="piexp ${L.cls}">${L.txt}</span></div>`;});
 if((pl.extractors||[]).length>board.length)html+=`<div class="sub" style="padding-top:6px">… ${pl.extractors.length-board.length} ${en?'more':'weitere'}</div>`;
 html+=`</div>`;
 // Nach Charakter (einklappbar, respektiert den Char-Filter)
 const f=localStorage.getItem('charFilter')||'';
 const list=f?pl.chars.filter(c=>c.name===f):pl.chars;
 html+=`<div class="card" style="grid-column:1/-1"><div class="chead"><span class="char">${en?'By character':'Nach Charakter'}</span></div>`;
 list.forEach(c=>{const isc=collapsed.has(c.name);
  html+=`<div class="picol"><div class="chead pihead" data-pi="${esc(c.name)}" style="cursor:pointer">
    <span class="char">${isc?'▸':'▾'} ${esc(c.name)} <span class="sub">· ${c.cols.length} ${c.cols.length===1?(en?'colony':'Kolonie'):(en?'colonies':'Kolonien')}</span></span>${esiBadge(c.name)}${c.isk?`<span class="isk" style="margin-left:auto">≈ ${fmtM(c.isk)} ISK</span>`:''}</div>`;
  if(!isc)c.cols.forEach(col=>{
   let body=`<div class="picolhead"><b>${esc(col.planet)}</b> <span class="sub">${piTypeName(col.type,en)} · ${esc(col.system||'')} · ${en?'level':'Stufe'} ${col.upgrade||0} · ${col.pins||0} Pins</span>${col.isk?`<span class="isk" style="margin-left:auto">≈ ${fmtM(col.isk)} ISK ${en?'stored':'gelagert'}</span>`:''}</div>`;
   if((col.products||[]).length)body+=`<div class="piprodline">🏭 <span class="sub">${en?'Produces':'Produziert'}:</span> ${piProdList(col.products)}</div>`;
   (col.extractors||[]).forEach(e=>{const L=piLeft(e.expiry,en);
    body+=`<div class="piexrow"><span class="pidot ${L.cls}"></span>${e.product_id?`<img class="piicon" src="https://images.evetech.net/types/${e.product_id}/icon?size=32" onerror="this.style.visibility='hidden'">`:`<span class="piicon"></span>`}<span class="piname">${esc(e.product||'?')}${piTierBadge(e.tier)} <span class="sub">· ${e.heads} ${en?'heads':'Köpfe'}${e.total?' · ~'+fmtC(e.total)+(en?' units':' Stk'):''}</span></span><span class="piexp ${L.cls}">${L.txt}</span></div>`;});
   if(!(col.extractors||[]).length)body+=`<div class="sub">${en?'No active extractors':'Keine aktiven Extraktoren'}</div>`;
   html+=`<div class="picolrow">${col.type_id?`<img class="piplanetimg" src="https://images.evetech.net/types/${col.type_id}/icon?size=128" onerror="this.style.visibility='hidden'">`:`<span class="piplanetimg"></span>`}<div class="picolbody">${body}</div></div>`;});
  html+=`</div>`;});
 if((pl.reconnect||[]).length)html+=`<div class="sub" style="padding:8px 0 0">· ${pl.reconnect.length} ${en?'char(s) not connected for planets yet':'Chars noch nicht für Planeten verbunden'}</div>`;
 html+=`</div>`;
 $('#grid').innerHTML=html;
 document.querySelectorAll('.pihead').forEach(h=>h.onclick=()=>{
  const n=h.dataset.pi;
  if(collapsed.has(n))collapsed.delete(n);else collapsed.add(n);
  try{localStorage.setItem('collapsed',JSON.stringify([...collapsed]));}catch(e){}
  renderPlaneten(lastPlaneten);});
}
// Live-Kampfkachel(n) fuer Chars, die gerade eine Mission fliegen: Portrait
// mittig, Schaden raus links, Schaden rein rechts, darunter Gesamtschaden,
// eliminierte Gegner (Kills, sonst bekaempfte Typen) und eingesammelte Bounty.
function renderMissionLive(chars){
 // Nur wer WIRKLICH kämpft: eigener ausgeteilter Schaden > 0. So taucht ein
 // Miner, der beim Flotten-Mining nur Bounty-Anteile für Gürtel-Ratten bekommt
 // (kills>0, aber dmg_out=0, z.B. Askend im Hulk), hier nicht als Mission auf.
 // Ausnahme: der Sim-Demo-Char (hat c.phase) wird auch in Reise-Phasen gezeigt.
 const act=(chars||[]).filter(c=>c.active&&autoRole(c)!=='mining'
   &&(c.phase||(c.dmg_out||0)>0));
 if(!act.length)return '';
 return act.map(c=>{
  const out=c.dmg_out||0,inc=c.dmg_in||0,tot=out+inc;
  // Eliminierte Gegner: EVE loggt keine NPC-Tode. Mit Bounty-Meldungen kennen wir
  // die Kills, sonst zeigen wir ehrlich die Zahl der bekaempften Gegnertypen.
  const hasKills=(c.kills||0)>0;
  const elimN=hasKills?c.kills:(c.enemy_types||0);
  const elimL=hasKills?(lang==='en'?'Enemies eliminated':'Gegner eliminiert')
                      :(lang==='en'?'Enemies engaged':'Gegner bekämpft');
  const elimTip=hasKills?'':(lang==='en'
    ?'EVE does not log NPC kills. Without bounty data this is the number of enemy types fought.'
    :'EVE protokolliert keine NPC-Tode. Ohne Bounty-Daten ist dies die Zahl der bekämpften Gegnertypen.');
  return `<div class="mlive">
   <div class="mlive-head">
    <span class="mlive-title"><span class="dot"></span>${lang==='en'?'Live mission':'Live-Mission'}${c.phase?` <span class="mlive-phase">${esc(c.phase)}</span>`:''}</span>
    <span class="mlive-sys">${esc(c.name)}${c.ship?' · '+esc(c.ship):''}${c.system&&c.system!=='?'?' · '+esc(c.system):''} · ${c.session_min||0} min</span>
   </div>
   <div class="mlive-body">
    <div class="mlive-side">
     <div class="l">${lang==='en'?'Damage out':'Schaden raus'}</div>
     <div class="mlive-num out">${fmt(out)}</div>
     <div class="mlive-dps">DPS ${c.dps_out||0}</div>
    </div>
    <div class="mlive-center">
     <div class="mlive-ring${c.portrait?'':' noimg'}">${c.portrait?`<img src="${c.portrait}" alt="">`:'👤'}</div>
     <div class="mlive-nm">${esc(c.name)}</div>
     ${c.mission?`<div class="mtag">${missionHtml(c.mission)}</div>`:`<div class="mtag mtired" title="Keine Mission erkannt. Entweder Ratting ohne feste Mission oder eine Signatur, die Canary noch nicht kennt.">🔍 Keine Erkennungsdaten gefunden</div>`}
    </div>
    <div class="mlive-side">
     <div class="l">${lang==='en'?'Damage in':'Schaden rein'}</div>
     <div class="mlive-num in">${fmt(inc)}</div>
     <div class="mlive-dps">DPS ${c.dps_in||0}</div>
    </div>
   </div>
   <div class="mlive-foot">
    <div class="cell"><div class="l">${lang==='en'?'Total damage':'Schaden gesamt'}</div><div class="v">${fmt(tot)}</div></div>
    <div class="cell"${elimTip?` title="${elimTip}"`:''}><div class="l">${elimL}</div><div class="v">${elimN}</div></div>
    <div class="cell"><div class="l">${lang==='en'?'Bounty collected':'Bounty eingesammt'}</div><div class="v isk">${fmtM(c.bounty||0)}</div></div>
   </div>
   ${(c.faction||(c.ewar&&c.ewar.length))?`<div class="mlive-extra">${factionHtml(c.faction)}${ewarHtml(c.ewar)}</div>`:''}
  </div>`;
 }).join('');
}
function renderMissions(d){
 lastMissionD=d;                         // fuer die lokale Simulation merken
 // Lokale Demo (nur mit sim_mode-Flag, reine Frontend-Simulation): Live-Char,
 // 50-Missionen-Historie und Journal-Summen einspeisen, nichts davon aus DB/Logs.
 if(SIM.on&&SIM.char)d=Object.assign({},d,{
   chars:[SIM.char].concat(d.chars||[]),
   mission_log:(SIM.history||[]).concat(d.mission_log||[]),
   missions:SIM.summary||d.missions});
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
 <div class="alphabanner" style="grid-column:1/-1">🧪 <b>${lang==='en'?'Alpha phase, module in development':'Alpha-Phase, Modul in Entwicklung'}</b> · ${lang==='en'?'faction tips and verified rewards are still being checked against real logs. Feedback welcome.':'Fraktions-Tipps und verifizierte Belohnungen werden noch an echten Logs geprüft. Rückmeldungen willkommen.'}</div>
 ${state.sim?`<div style="grid-column:1/-1;display:flex;justify-content:flex-end;gap:8px;align-items:center">
   <span class="sub" style="color:var(--dim)">${lang==='en'?'Local demo (not shipped)':'Lokale Demo (nicht ausgeliefert)'}</span>
   <button class="btn${SIM.on?' simon':''}" onclick="toggleSim()">${SIM.on?(lang==='en'?'⏹ Stop simulation':'⏹ Simulation stoppen'):(lang==='en'?'▶ Start simulation':'▶ Simulation starten')}</button></div>`:''}
 ${renderMissionLive(d.chars)}
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
     <span class="sys">${x.system&&x.system!=='?'?'· '+esc(x.system)+' ':''}· ${x.min} min</span>
     ${x.mission?`<span class="mtag">${missionHtml(x.mission)}</span>`:''}
     <span style="margin-left:auto" class="isk"><b>${fmtM(x.total)} ISK</b></span>
    </div>
    <div class="sub">${x.kills} Kills · Bounty ${fmtM(x.bounty)} · Schaden ${fmt(x.dmg_out)} raus / ${fmt(x.dmg_in)} rein${x.hit!=null?' · Trefferquote '+x.hit+'%':''}${x.enemies.length?' · Top: '+esc(x.enemies[0][0]):''}</div>
    ${(x.reward!=null||x.bonus!=null)?`<div class="sub vreward">✅ ${lang==='en'?'ESI verified':'ESI-verifiziert'}: ${lang==='en'?'reward':'Belohnung'} <b class="isk">${fmtM(x.reward||0)}</b>${x.bonus?` + ${lang==='en'?'time bonus':'Zeitbonus'} <b class="isk">${fmtM(x.bonus)}</b>`:''}${x.min>0?` · ${fmtM(Math.round(((x.reward||0)+(x.bonus||0))/(x.min/60)))}/h`:''}</div>`:''}
    ${factionHtml(x.faction)}
    ${ewarHtml(x.ewar)}
    ${(x.npc&&x.npc.length)?`<div class="npc">${x.npc.map(l=>`<div>💬 ${esc(l)}</div>`).join('')}</div>`:''}
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
  <div class="sub" style="margin-top:8px">Kommt direkt aus den Gamelogs. Reine Belt-Ratten-Trips (nur Flotten-Bounty ohne echten Kampf) werden herausgefiltert.</div>
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
  let r;try{r=await post({action:'mission_loot',mid,text:ta?ta.value:''});}catch(e){r=null;}
  if(r&&r.ok){st.textContent='Loot: '+fmtM(r.isk)+(r.unknown&&r.unknown.length?' · nicht erkannt: '+r.unknown.join(', '):'');
   setTimeout(tick,600);}
  else st.textContent=r?'Fehler':'Server nicht erreichbar';
 });
}
function renderRechner(){
 if(document.getElementById('calcBox'))return;
 $('#grid').innerHTML=`<div class="card mkt" id="mktBox" style="grid-column:1/-1">
  <b>🔎 Einzel-Item</b>
  <div style="font-size:12px;color:var(--dim);margin:6px 0">Item-Namen tippen, Canary schlägt passende vor. Preise kommen aus dem aktuellen Orderbuch (ESI) über alle Handelsplätze.</div>
  <div class="btnrow"><span class="mktwrap"><input id="mktIn" placeholder="z.B. Tritanium" autocomplete="off"><div id="mktSug" class="mktsug" hidden></div></span><button class="btn" id="mktGo">Suchen</button></div>
  <span id="mktStat" class="sub"></span>
  <div id="mktOut" style="overflow-x:auto"></div></div>
 <div class="card" id="calcBox" style="grid-column:1/-1">
  <b>📦 Frachtraum</b>
  <div style="font-size:12px;color:var(--dim);margin:6px 0">Im Spiel den Frachtraum oder Container öffnen, alles markieren (Strg+A) und kopieren (Strg+C), dann hier einfügen.
  Einzelne Zeilen wie "Compressed Veldspar 50000" funktionieren genauso.</div>
  <textarea id="calcIn" rows="7" style="width:100%" placeholder="Compressed Veldspar	49.105&#10;Compressed Scordite	42.990"></textarea>
  <div style="margin:8px 0"><button class="btn" id="calcGo">Berechnen</button> <span id="calcStat" style="font-size:12px;color:var(--dim)"></span></div>
  <div id="calcOut" style="overflow-x:auto"></div></div>`;
 $('#calcGo').onclick=doCalc;
 $('#mktGo').onclick=()=>{$('#mktSug').hidden=true;doMarket();};
 $('#mktIn').oninput=()=>{clearTimeout(mktSugTimer);mktSugTimer=setTimeout(doSuggest,160);};
 $('#mktIn').onkeydown=e=>{
  const box=$('#mktSug');
  if(box&&!box.hidden&&mktSugItems.length){
   if(e.key==='ArrowDown'){mktSugI=Math.min(mktSugI+1,mktSugItems.length-1);paintSug();e.preventDefault();return;}
   if(e.key==='ArrowUp'){mktSugI=Math.max(mktSugI-1,0);paintSug();e.preventDefault();return;}
   if(e.key==='Enter'&&mktSugI>=0){pickSug(mktSugItems[mktSugI]);e.preventDefault();return;}
   if(e.key==='Escape'){box.hidden=true;return;}
  }
  if(e.key==='Enter'){if(box)box.hidden=true;doMarket();}
 };
 // Klick ausserhalb schliesst die Vorschlagsliste
 // Nur EINMAL binden: renderRechner laeuft bei jedem Wechsel auf den Tab erneut,
 // sonst sammeln sich mit jedem Besuch weitere globale Click-Listener an.
 if(!window._mktClickBound){window._mktClickBound=true;
  document.addEventListener('click',e=>{if(!e.target.closest('.mktwrap')){const b=document.getElementById('mktSug');if(b)b.hidden=true;}});}
 const saved=localStorage.getItem('calcText');
 if(saved)$('#calcIn').value=saved;
}
let mktSugTimer=null, mktSugItems=[], mktSugI=-1;
async function doSuggest(){
 const q=$('#mktIn')?$('#mktIn').value.trim():'';
 const box=$('#mktSug'); if(!box)return;
 if(q.length<2){box.hidden=true;box.innerHTML='';return;}
 let r;try{r=await post({action:'market_suggest',q});}catch(e){r=null;}
 if(!document.getElementById('mktSug'))return;
 mktSugItems=(r&&r.items)||[]; mktSugI=-1; paintSug();
}
function paintSug(){
 const box=$('#mktSug'); if(!box)return;
 if(!mktSugItems.length){box.hidden=true;box.innerHTML='';return;}
 box.hidden=false;
 box.innerHTML=mktSugItems.map((n,i)=>`<div data-i="${i}"${i===mktSugI?' class="sel"':''}>${esc(n)}</div>`).join('');
 box.querySelectorAll('div').forEach(d=>d.onclick=()=>pickSug(mktSugItems[+d.dataset.i]));
}
function pickSug(name){
 if($('#mktIn'))$('#mktIn').value=name;
 const b=$('#mktSug'); if(b){b.hidden=true;b.innerHTML='';}
 mktSugItems=[]; doMarket();
}
async function doMarket(){
 const name=$('#mktIn').value.trim();
 if(!name)return;
 $('#mktStat').textContent='Suche Preise …';$('#mktOut').innerHTML='';
 let r;try{r=await post({action:'market_item',name});}catch(e){r=null;}
 if(!$('#mktOut'))return;
 if(!r){$('#mktStat').textContent='Marktabfrage fehlgeschlagen.';return;}
 if(!r.ok){$('#mktStat').textContent=r.msg||'Nicht gefunden.';return;}
 $('#mktStat').textContent='';
 const hubs=Object.values(r.hubs||{}).filter(h=>!h.error);
 const bestBuy=hubs.length?Math.max(...hubs.map(h=>h.buy)):0;
 // Charakter-Auswahl fuer "im Client oeffnen" (nur verbundene Charaktere)
 const chars=((state.esi&&state.esi.chars)||[]).map(c=>c.name);
 const picker=chars.length
  ?`<select id="mktChar" class="pill">`+chars.map(n=>`<option>${esc(n)}</option>`).join('')+`</select>`
   +`<button class="btn uibtn" id="mktOpenMkt" data-tid="${r.type_id}">Markt im Client öffnen</button>`
  :`<span class="sub">Für „im Client öffnen“ zuerst einen Charakter über den EVE-Login verbinden.</span>`;
 $('#mktOut').innerHTML=`<div style="display:flex;align-items:center;gap:10px;margin:6px 0"><img src="https://images.evetech.net/types/${r.type_id}/icon?size=64" alt="" width="46" height="46" style="border-radius:4px;flex:none" onerror="this.style.display='none'"><div style="font-size:13px"><b>${esc(r.name)}</b> <span class="sub">· Preisquelle: ${r.src==='esi'?'ESI':'Fuzzwork'}</span></div></div>`
  +`<table><tr><th>Handelsplatz</th><th class="r">Sofortverkauf (Buy)</th><th class="r">Kaufen (Sell)</th></tr>`
  +hubs.map(h=>`<tr><td>${esc(h.name)}${h.buy===bestBuy&&bestBuy>0?' ★':''}</td><td class="r isk">${h.buy>0?fmtP(h.buy):'—'}</td><td class="r">${h.sell>0?fmtP(h.sell):'—'}</td></tr>`).join('')
  +`</table><div class="btnrow" style="margin-top:10px;align-items:center">${picker}</div>`;
 const om=$('#mktOpenMkt');
 if(om)om.onclick=()=>uiOpen('market',om.dataset.tid);
}
async function uiOpen(kind,tid){
 const char=$('#mktChar')?$('#mktChar').value:'';
 $('#mktStat').textContent='Öffne im Client …';
 let r;try{r=await post({action:'ui_open',char,kind,id:Number(tid)});}catch(e){r=null;}
 $('#mktStat').textContent=r?(r.msg||''):'Client nicht erreichbar.';
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
  let r;try{r=await post({action:'log_dir',path:$('#setupDir').value});}catch(e){r=null;}
  if(!r){st.textContent='Server nicht erreichbar.';st.style.color='var(--red)';return;}
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
'🚦 Intel':'🚦 Intel','🎯 Missionen':'🎯 Missions','💰 ISKray':'💰 ISKray','🕑 Verlauf':'🕑 Timeline','🪪 Steckbrief':'🪪 Character sheet','🪐 Planeten':'🪐 Planets',
'🔎 Einzel-Item':'🔎 Single item','📦 Frachtraum':'📦 Cargo',
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
'🔊 Sprachansagen bei Alarmen (spricht Charakter und Warnung)':'🔊 Spoken alerts (says character and warning)',
'💸 ISK-Verlust anzeigen, wenn ein Strip Miner steht':'💸 Show ISK lost when a strip miner is idle',
'🔔 Alarm testen':'🔔 Test alert','Stimme:':'Voice:',
'Stillstand-Verlust':'Downtime loss',
'Geschätzt entgangenes ISK, weil Laser oder Drohnen standen oder die Rate einbrach (je Trip beim Docken erfasst).':'Estimated ISK missed because lasers or drones were idle or the rate dropped (recorded per trip on docking).',
'löst einen Beispielalarm aus: Ton, Sprache und Banner, je nach Häkchen oben. Alarme kommen sonst nur bei einem echten Ereignis.':'triggers a sample alert: sound, speech and banner, depending on the boxes above. Alerts otherwise only fire on a real event.',
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
'Gegner bekämpft':'Enemies fought','Typen · aus Log':'types · from log',
'🔍 Keine Erkennungsdaten gefunden':'🔍 No recognition data found',
'🛰 Aktuelle Flotte':'🛰 Current fleet','m³ komprimiert':'m³ compressed',
'💎 Erz-Schatzkammer':'💎 Ore treasury','m³ Erz':'m³ of ore','Kein Erz im Bestand.':'No ore in storage.',
'Main-Charakter (für das Teilen-Bild)':'Main character (for the share image)','Automatisch':'Automatic',
'Welcher Name auf dem geteilten Mining-Fleet-Power-Bild steht. Automatisch = Command Ship, sonst der aktivste Miner.':'Which name appears on the shared Mining Fleet Power image. Automatic = command ship, otherwise the most active miner.',
'keine Stimmen im Browser (bei Firefox unter Windows häufig). Für auswählbare Stimmen Chrome oder Edge nutzen.':'no voices in this browser (common in Firefox on Windows). Use Chrome or Edge to pick a voice.',
'Noch keine Asset-Daten. Verbinde deine Chars per EVE-Login (⚙ Optionen). Nach dem ersten Abgleich (bis zu 1 Stunde) erscheint hier dein Erz-Bestand.':'No asset data yet. Connect your chars via the EVE login (⚙ Options). After the first sync (up to one hour) your ore stock shows up here.',
'✅ Command Ship erkannt':'✅ Command ship detected',
'🗜 Noch keiner komprimiert diese Session':'🗜 No one has compressed this session yet',
'ℹ️ Für diese Mission liegen keine Bounty-Daten im Log vor, daher werden Kills und Bounty hier nicht gezählt. In EVE die Bounty-Meldungen im Combat-Log aktivieren, dann zählt Canary sie live mit. Die echte Bounty-ISK kommt bei EVE-Login aus dem Wallet.':'ℹ️ No bounty data in the log for this session, so kills and bounty are not counted here. Enable the bounty messages in the EVE combat log and Canary will count them live. The actual bounty ISK comes from the wallet when you use the EVE login.',
'Rorqual-Overlord':'Rorqual Overlord','Erz-Baron':'Ore Baron','Industrie-Flotte':'Industrial Fleet',
'Flotten-Operator':'Fleet Operator','Gürtel-Miner':'Belt Miner','Prospektor':'Prospector',
'✅ ESI-verifiziert:':'✅ ESI-verified:','📤 Teilen':'📤 Share',
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
'Kommt direkt aus den Gamelogs. Reine Belt-Ratten-Trips (nur Flotten-Bounty ohne echten Kampf) werden herausgefiltert.':
 'Comes straight from the game logs. Pure belt-rat trips (fleet bounty without real combat) are filtered out.',
'Noch keine Journal-Daten. Nach dem ersten ESI-Abgleich (spätestens in einer Stunde) erscheinen hier die letzten 30 Tage.':
 'No journal data yet. After the first ESI sync (within an hour at the latest) the last 30 days appear here.',
'Im Spiel den Frachtraum oder Container öffnen, alles markieren (Strg+A) und kopieren (Strg+C), dann hier einfügen. Einzelne Zeilen wie "Compressed Veldspar 50000" funktionieren genauso.':
 'Open your cargo hold or a container in game, select everything (Ctrl+A) and copy (Ctrl+C), then paste it here. Single lines like "Compressed Veldspar 50000" work just as well.',
'Photon (angelehnt ans EVE-Interface: dunkel, kantig, Gold-Akzente)':
 'Photon (modelled on the EVE interface: dark, angular, gold accents)',
'Das Overlay ist ein schwebendes Always-on-top-Fenster mit Status und Alarmen, bleibt über dem EVE-Client (Fenstermodus/randlos). In Chrome und Edge klickbar, in Firefox als Bild. Start nur per Klick.':
 'The overlay is a floating always-on-top window with status and alerts, staying above the EVE client (windowed or borderless). Clickable in Chrome and Edge, an image in Firefox. Starts only by click.',
'Das Mini-Overlay benötigt Chrome oder Edge (Document Picture-in-Picture).':
 'The mini overlay needs Chrome or Edge (Document Picture-in-Picture).',
'Canary beim Systemstart automatisch mitstarten (still im Hintergrund, ohne Konsolenfenster)':
 'Start Canary automatically with the system (quietly in the background, no console window)',
'Was ist das?':'What is this?',
'Hier siehst du, was gerade passiert. Für jeden Charakter eine Karte mit Erz, ISK, Schaden und Warnungen. Die Zahlen werden alle zwei Sekunden frisch aus deinen Logdateien gelesen.':
 'This shows what is happening right now. One card per character with ore, ISK, damage and warnings. The numbers are read fresh from your log files every two seconds.',
'Daten: die Logdateien, die dein EVE-Client auf diesem Rechner schreibt. Marktpreise von Fuzzwork. Wenn du den EVE-Login benutzt, kommen Schiff, Kontostand und Frachtraum-Wert dazu, die sind bis zu eine Stunde alt.':
 'Data: the log files your EVE client writes on this machine. Market prices from Fuzzwork. If you use the EVE login, ship, wallet balance and cargo value are added, those can be up to an hour old.',
'Die letzten 30 Tage, ein Balken für jeden Tag. So siehst du auf einen Blick, an welchen Tagen du viel geschafft hast.':
 'The last 30 days, one bar per day. That way you can see at a glance which days went well.',
'Daten: die Datenbank von Canary auf diesem Rechner, gefüllt aus deinen Logdateien.':
 'Data: the Canary database on this machine, filled from your log files.',
'Alles zusammengezählt, seit Canary mitschreibt: Erz, ISK, Schaden und Gegner, aufgeteilt nach Charakter.':
 'Everything added up since Canary started recording: ore, ISK, damage and enemies, split by character.',
'Auswertung über längere Zeit. Welche Waffen du benutzt, wer dich angegriffen hat, welches Erz am meisten einbringt und zu welchen Zeiten du spielst.':
 'A look at the longer run. Which weapons you use, who attacked you, which ore pays best and what times you play.',
'Daten: die Datenbank von Canary auf diesem Rechner, dazu Marktpreise von Fuzzwork.':
 'Data: the Canary database on this machine, plus market prices from Fuzzwork.',
'Zwei Werkzeuge gegen böse Überraschungen. Die Ampel bewertet Piloten, die im Local schreiben. Die Blutspur zeigt Rudel, die in deiner Nähe Schiffe abschießen, und warnt, wenn sie näher kommen.':
 'Two tools against nasty surprises. The traffic light rates pilots who talk in local. The Blood Trail shows packs that are killing ships near you, and warns you when they come closer.',
'Daten: deine Chatlogs auf diesem Rechner. Zu gefundenen Namen fragt Canary öffentliche Quellen: zKillboard und die EVE-Datenbank. Die Abschuss-Meldungen kommen von einem öffentlichen Killmail-Dienst. Über dich wird nichts gesendet.':
 'Data: your chat logs on this machine. For names it finds, Canary asks public sources: zKillboard and the EVE database. The kill reports come from a public killmail service. Nothing about you is sent anywhere.',
'Deine Missionen. Was du gerade bekämpfst, welche Mission es vermutlich ist, gegen welche Fraktion es geht und was am Ende dabei herauskam.':
 'Your missions. What you are fighting right now, which mission it probably is, which faction you are up against and what it paid in the end.',
'Daten: deine Logdateien für den Kampf. Mit EVE-Login zusätzlich das Wallet-Journal für die Belohnung, das ist bis zu eine Stunde alt. Wichtig: der Missionsname steht in keiner Datei. Canary erkennt ihn an den Gegnern und schreibt dazu, wie sicher es sich ist.':
 'Data: your log files for the combat part. With the EVE login also the wallet journal for the reward, which can be up to an hour old. Important: the mission name is in no file at all. Canary infers it from the enemies and tells you how sure it is.',
'Dein Tag als Zeitstrahl. Jeder Mining-Trip, jeder Kampf und jede Belohnung ist ein Eintrag, von jetzt nach hinten.':
 'Your day as a timeline. Every mining trip, every fight and every reward is one entry, from now backwards.',
'Daten: deine Logdateien und, wenn du den EVE-Login benutzt, die Belohnungen aus dem Wallet-Journal.':
 'Data: your log files and, if you use the EVE login, the rewards from the wallet journal.',
'Ein Steckbrief je Charakter: Bild, Corp, Schiff und Vermögen. Das Netz daneben zeigt, worin dieser Charakter stark ist, im Vergleich zu deinen anderen.':
 'A character sheet for each pilot: portrait, corp, ship and wealth. The web next to it shows what this character is strong at, compared to your others.',
'Daten: die Datenbank von Canary für das Netz. Mit EVE-Login Bild, Kontostand und Schiff. Corp und Sicherheitsstatus über öffentliche Quellen.':
 'Data: the Canary database for the web. With the EVE login portrait, wallet balance and ship. Corp and security status from public sources.',
'Deine Planeten-Fabriken. Wann läuft ein Extraktor ab, was liegt im Lager, was wird produziert und was ist es wert.':
 'Your planetary factories. When does an extractor run out, what is in storage, what is being produced and what is it worth.',
'Daten: nur über den EVE-Login. Achtung: die Lagerstände sind so aktuell, wie du die Kolonie zuletzt im Spiel geöffnet hast. Die Ablaufzeiten stimmen dagegen immer.':
 'Data: only through the EVE login. Careful: storage levels are only as fresh as the last time you opened the colony in game. The expiry times, however, are always correct.',
'Dein Erz in den Stationen, und der Rat, was sich mehr lohnt: roh verkaufen, komprimiert verkaufen oder einschmelzen.':
 'Your ore sitting in stations, plus advice on what pays more: selling it raw, selling it compressed or reprocessing it.',
'Daten: EVE-Login für den Bestand, Marktpreise von Fuzzwork. Der Einschmelz-Wert ist vorsichtig gerechnet, dein echter Erlös liegt eher darüber.':
 'Data: EVE login for the stock, market prices from Fuzzwork. The reprocessing value is calculated conservatively, your real return is likely higher.',
'Ein Preisrechner. Frachtraum im Spiel markieren, kopieren, hier einfügen, und du siehst sofort, was es an welchem Handelsplatz wert ist.':
 'A price calculator. Select your cargo hold in game, copy it, paste it here, and you immediately see what it is worth at which trade hub.',
'Daten: Marktpreise von Fuzzwork für die großen Handelsplätze. Der Text, den du einfügst, bleibt auf deinem Rechner.':
 'Data: market prices from Fuzzwork for the major trade hubs. The text you paste stays on your machine.',
'Anonym mitzählen lassen':'Let this install be counted anonymously',
'Einmal am Tag holt Canary eine leere Datei von GitHub, deren Name nur das Datum enthält. Gesendet wird dabei nichts: keine Kennung, keine Namen, keine Spieldaten. GitHub zählt nur, wie oft die Datei ausgeliefert wurde, und daraus wird sichtbar, wie viele Installationen es gibt. Ohne diese Zahl gibt es keinen Nachweis für die EVE-Partnerschaft.':
 'Once a day Canary fetches an empty file from GitHub whose name only contains the date. Nothing is sent: no identifier, no names, no game data. GitHub merely counts how often that file was served, which shows how many installations exist. Without that number there is no proof for the EVE partnership.',
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
 [/Mögliche Gank-Flotte im Local: ([0-9]+) geflaggte Piloten von (.+?), ([0-9]+) Miner-Kills/,
  'Possible gank fleet in local: $1 flagged pilots from $2, $3 miner kills'],
 // Blutspur-Alarme (Rudel-Radar). Klammern mit doppeltem Backslash escapen:
 // PAGE ist ein normaler Python-String, einfache Escapes gehen dort kaputt.
 [/Bekanntes Rudel im Local: (.+?) gehört zu Rudel \\[(.+?)\\] \\(([0-9]+) Piloten, zuletzt aktiv vor ([0-9]+) min in (.+?)\\)/,
  'Known pack in local: $1 belongs to pack [$2] ($3 pilots, last active $4 min ago in $5)'],
 [/Rudel \\[(.+?)\\] ist ([0-9]+) Sprünge entfernt aktiv \\((.+?), seit ([0-9]+) min, ([0-9]+) Piloten\\)/,
  'Pack [$1] active $2 jumps out ($3, for $4 min, $5 pilots)'],
 [/Rudel \\[(.+?)\\]: Kill in der Nähe \\((.+?)\\)/, 'Pack [$1]: kill nearby ($2)'],
 [/Rudel-Corp im Local: (.+?) ist in der Corp von Rudel \\[(.+?)\\]/,
  'Pack corp in local: $1 is in the corp of pack [$2]'],
 [/Rudel \\[(.+?)\\] nähert sich deinem System: noch ([0-9]+) Sprünge \\((.+?)\\)/,
  'Pack [$1] closing on your system: $2 jumps out ($3)'],
 [/Rudel \\[(.+?)\\] nähert sich: ([0-9]+) → ([0-9]+) Sprünge \\((.+?)\\)/,
  'Pack [$1] approaching: $2 to $3 jumps ($4)'],
 // Planetary-Industry-Ablauf-Alarm: distinkte Tokens, damit nichts anderes trifft.
 [/ · Extraktor abgelaufen/, ' · extractor expired'],
 [/ · Extraktor läuft in ([0-9]+) Std ab/, ' · extractor expires in $1 h'],
 [/ · Extraktor läuft in ([0-9]+) min ab/, ' · extractor expires in $1 min'],
 [/ · [+]([0-9]+) weitere/, ' · +$1 more'],
 [/ in 30 Tagen gefördert · Ø (.+?)[/]Tag · Skill-Bonus [+]([0-9]+)%/, ' mined in 30 days · avg $1/day · skill bonus +$2%'],
 [/ in 30 Tagen gefördert · Ø (.+?)[/]Tag/, ' mined in 30 days · avg $1/day'],
 [/[/]Tag/, '/day'],
 [/Ø letzte 7 Tage:/, 'Ø last 7 days:'], [/Bester Tag:/, 'Best day:'],
 [/Seit ([0-9]+) min kein Erz/, 'No ore for $1 min'],
 // Heavy-Water-Reichweite: "reicht bis ~22:47 Uhr" -> "lasts until ~22:47"
 [/reicht bis ~(.+?) Uhr/, 'lasts until ~$1'],
 // Schatzkammer: Erz im Erzladeraum/Fleet-Hangar des Mining-Schiffs
 [/· im Schiff/, '· on ship'],
 [/DPS ([0-9]+) raus [/] ([0-9]+) rein/, 'DPS $1 out / $2 in'],
 // PvP/Missionen-Ansicht: Zeitstempel, Salvage, EWAR
 [/Stand: vor ([0-9]+) min/, 'As of $1 min ago'], [/nächste in ([0-9]+) min/, 'next in $1 min'],
 [/aus EVE-Login/, 'from EVE login'],
 [/wird aktualisiert/, 'updating'],
 [/([0-9]+) Wracks geborgen/, '$1 wrecks salvaged'], [/([0-9]+) leer/, '$1 empty'],
 [/([0-9]+) Fehlversuch/, '$1 failed'], [/EWAR gegen dich:/, 'EWAR against you:'],
 [/gleiche Skala/, 'same scale'],
 [/Schaden ([0-9.]+) raus [/] ([0-9.]+) rein/, 'Damage $1 out / $2 in'],
 [/Trefferquote ([0-9]+)%/, 'Hit rate $1%'], [/([0-9]+) Kills/, '$1 kills'],
 [/Bekämpfte Gegner · ([0-9]+) Typen/, 'Enemies fought · $1 types'],
 [/~([0-9]+)% sicher/, '~$1% sure'],
 [/([0-9]+) Spieler komprimieren:/, '$1 pilots compressing:'],
 [/([0-9]+) Spieler komprimiert:/, '$1 pilot compressing:'],
 [/([0-9]+) Chars/, '$1 chars'], [/([0-9]+) Char\b/, '$1 char'],
 [/([0-9]+) Schiffe? · geschätzt aus Log/, '$1 ships · estimated from log'],
 [/([0-9]+) Schiffe? · ✅ ESI-verifiziert/, '$1 ships · ✅ ESI-verified'],
 [/([0-9]+) von ([0-9]+) ESI-verifiziert · Rest geschätzt/, '$1 of $2 ESI-verified · rest estimated'],
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
 // System-Gefahrenlage (Mining-Karte)
 [/Sicherheit /, 'Security '], [/Verluste letzte Stunde: /, 'Losses last hour: '],
 [/([0-9]+) Schiffe/, '$1 ships'], [/([0-9]+) Kapseln/, '$1 pods'],
 [/Verkehr /, 'Traffic '], [/([0-9.]+) Sprünge/, '$1 jumps'],
 // Markt / Item-Suche
 [/Item-Preis suchen/, 'Item price lookup'],
 [/Item-Namen tippen, Canary schlägt passende vor[.] Preise kommen aus dem aktuellen Orderbuch [(]ESI[)] über alle Handelsplätze[.]/,
  'Type an item name and Canary suggests matches. Prices come from the current order book (ESI) across all trade hubs.'],
 [/^Suchen$/, 'Search'], [/Suche Preise …/, 'Fetching prices …'],
 [/Marktabfrage fehlgeschlagen[.]/, 'Market lookup failed.'],
 [/Preisquelle: /, 'Price source: '], [/^Handelsplatz$/, 'Trade hub'],
 [/Sofortverkauf [(]Buy[)]/, 'Instant sell (buy)'], [/Kaufen [(]Sell[)]/, 'Buy (sell)'],
 [/Markt im Client öffnen/, 'Open market in client'], [/^Info öffnen$/, 'Open info'],
 [/Öffne im Client …/, 'Opening in client …'], [/Im Client geöffnet[.]/, 'Opened in client.'],
 [/Für „im Client öffnen“ zuerst einen Charakter über den EVE-Login verbinden[.]/,
  'To use “open in client”, first connect a character via the EVE login.'],
 [/(.*) muss einmal neu verbunden werden [(]neue Berechtigung 'Fenster oeffnen' noetig[)][.]/,
  '$1 needs to be reconnected once (new permission “open window” required).'],
 [/(.*): Client antwortet nicht [(]ist er offen und online[?][)][.]/,
  '$1: client not responding (is it open and online?).'],
 [/(.*): Client nicht erreichbar [(]offen und online[?][)][.]/,
  '$1: client unreachable (open and online?).'],
 [/(.*): Login abgelaufen, bitte neu verbinden[.]/, '$1: login expired, please reconnect.'],
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
  const d=await (await fetch('/data?view='+reqView,{cache:'no-store'})).json();
  if(reqView!==view)return;  // Nutzer hat inzwischen gewechselt -> Antwort verwerfen
  state=d.state;regionPills();handleAlerts();updateBadge();updateBanner();serverBadge();bootScreen();renderViewInfo();
  if(state.log_ok===false){renderSetup();return;}
  if(!$('#setup').hidden){$('#setup').hidden=true;$('#setup').dataset.built='';}
  if(view!=='live'&&view!=='month'&&view!=='total'&&view!=='analyse')$('#empty').hidden=true;
  // Der Mining/PvP-Umschalter gehört nur zur Live-Ansicht
  document.querySelectorAll('.modesel').forEach(b=>b.hidden=view!=='live');
  if(view==='live'){lastChars=d.chars;lastSummary=d.summary;renderLiveView();voiceWatch(d.chars);}
  else if(view==='missionen')renderMissions(d);
  else{
   $('#hero').innerHTML='';
   if(view==='month')renderMonth(d.days);
   else if(view==='analyse')renderAnalyse(d.analyse);
   else if(view==='intel')renderIntel(d.intel_auto,d.blutspur);
   else if(view==='vault')renderVault(d.vault);
   else if(view==='planeten')renderPlaneten(d.planeten);
   else if(view==='timeline')renderTimeline(d.timeline);
   else if(view==='profil')renderProfiles(d.profiles);
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
    serverstatus.start()
    danger.start()
    packintel.start()
    print(f"EVE Canary läuft:  http://localhost:{port}")
    if "--no-browser" not in sys.argv:
        # Browser erst jetzt öffnen, wo der Port sicher gebunden ist
        try:
            import webbrowser
            threading.Timer(0.5, lambda: webbrowser.open(f"http://localhost:{port}")).start()
        except Exception:
            pass
    srv.serve_forever()
