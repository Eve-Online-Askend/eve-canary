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
import socket
import sqlite3
import sys
import threading
import time
import urllib.error
import urllib.parse
import urllib.request

VERSION = "2.5.0"
UPDATE_FILES = ["eve_dashboard.py", "ore_types.json", "ore_refine.json",
                "eve_map.json", "npc_factions.json", "site_sigs.json",
                "mining_tools.json", "mission_sigs.json", "mission_items.json",
                "mission_fingerprints.json", "market_types.json",
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
    "CN-DATA-01": "Datendatei fehlt oder ist unbrauchbar und liess sich nicht nachladen",
    "CN-SET-01": "EVE-Einstellungen nicht lesbar oder nicht gefunden",
    "CN-SET-02": "EVE-Einstellungen nicht schreibbar",
    "CN-CFG-01": "Einstellungen nicht speicherbar",
    "CN-SRV-01": "Interner Serverfehler",
    "CN-SRV-02": "IPv6-Lauscher nicht startbar (localhost bleibt langsam, dann 127.0.0.1 nutzen)",
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


# Laufende Stoppuhr. Ueberlebt einen Neustart, weil sie in der meta-Tabelle
# liegt: wer Canary waehrend eines Trips aktualisiert, soll nicht von vorn
# anfangen muessen.
UHR = {"an": False, "pause": False, "label": "", "start": 0.0,
       "sek": 0.0, "snap_m3": 0.0, "snap_isk": 0.0}


def uhr_laufzeit():
    """Sekunden seit dem Start, Pausen abgezogen."""
    if not UHR["an"]:
        return UHR["sek"]
    if UHR["pause"]:
        return UHR["sek"]
    return UHR["sek"] + max(0.0, time.time() - UHR["start"])


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
# Missionserkennung über einzigartige FRACHT-Gegenstände. Dritter Weg neben
# Gegnernamen und Funk, und der einzige, der auch bei Missionen ohne Kampf und
# ohne Funk greift. Vergleich EXAKT, nicht als Teilwort: ein Frachtraum enthält
# gewöhnliche Ware, daran bliebe ein Teilwort-Vergleich sofort hängen.
MISSION_ITEMS = {k.lower(): v for k, v in load_json("mission_items.json", {}).items()
                 if not k.startswith("_")}
# Selbst vergebene Missionsnamen samt der Gegner-Zusammenstellung, an der sie
# haengen. Wird aus der Datenbank gefuellt (marken_laden), nicht ausgeliefert.
# Liste von {"name", "set", "ts"}.
MARKEN = []
# Dasselbe, aber von anderen gemeldet und mitgeliefert. Wer nie selbst etwas
# benennt, hat dadurch trotzdem Erkennung. Mehrere Vorlagen je Missionsname sind
# ausdruecklich erlaubt: dieselbe Mission hat je nach Auftraggeber andere Ratten.
MISSION_FP = [{"name": (v.get("m") or "").strip(),
               "set": {str(g).strip().lower() for g in (v.get("g") or []) if g},
               "n": int(v.get("n") or 1)}
              for v in (load_json("mission_fingerprints.json", {}).get("vorlagen") or [])
              if (v.get("m") or "").strip() and (v.get("g") or [])]
# Ab wann zwei Gegnerlisten dieselbe Mission sein duerfen. Beides muss stimmen.
# Die Zahlen sind am eigenen Bestand gewaehlt: dort gibt es genau ein Paar
# ueber der Schwelle, die zwei Aramachi-Laeufe mit 67% und 6 gemeinsamen
# Gegnern. Der zweite Wert ist der wichtigere. Ohne ihn wuerden zwei winzige
# Listen mit drei Namen schon bei einem Zufallstreffer gleichziehen.
FP_MIN_AEHNLICH = 0.65
FP_MIN_GEMEINSAM = 4
# Ab welchem Vielfachen der Normallieferung gilt Erz als Bonus, und bis wohin.
#
# Erst hiess die Regel "exaktes ganzes Vielfaches". Das war an einem einzigen
# Vormittag beobachtet und ist an 623.603 Lieferungen aus 8,5 Monaten
# durchgefallen: es gibt ZWEI scharfe Spitzen, 3,00 (15.330 Lieferungen) und
# 2,88 (5.531). Dazwischen liegt nichts, die naechsten Werte kommen 95 und 93
# mal vor. Die Ganzzahl-Pruefung verschluckte damit 28,6 Prozent aller
# Bonus-Lieferungen, im November und Dezember 2025 sogar restlos alle: dort
# hatte die Anzeige 108.924 Lieferungen ausgewertet und null gemeldet.
#
# Welcher Faktor gilt, wechselte je Charakter zu verschiedenen Zeitpunkten,
# nicht global. Deshalb keine feste Zahl mehr, sondern ein Fenster. Die
# Obergrenze faengt kaputte Basiswerte ab: am allerersten Logtag stand die
# Normalmenge bei 297 Einheiten und erzeugte Verhaeltnisse bis 21.
BONUS_AB = 2.5
BONUS_BIS = 5.0
# Ort-Erkennung. Fuer Kampfanomalien gibt es sowas NICHT und wird es nie geben:
# alle Anomalien einer Fraktion ziehen aus demselben Rattenpool, es gibt keinen
# site-eindeutigen Gegner. Fuer den Abyss dagegen fuehrt CCP zwei eigene Gruppen
# ("Abyssal Spaceship Entities", "Abyssal Drone Entities"), und was dort steht,
# kommt nirgendwo sonst vor. Die Liste wird aus dem SDE erzeugt
# (baue_npc_fraktionen.py), nicht von Hand gepflegt.
SITE_SIGS = {k.lower(): v for k, v in load_json("site_sigs.json", {}).items()
             if not k.startswith("_")}
# So heisst der Abyss bei uns. EVE selbst schreibt dort einen Platzhalter in
# den Local-Kanal ("Unknown" im englischen Client), der uebersetzt wird.
ABYSS_ORT = "Abyssal Deadspace"
_SYS_NAMES = None


def sys_names():
    """Alle Systemnamen der mitgelieferten Karte, einmal geladen.

    Dient als Gegenprobe fuer den Local-Kanal: der Abyss hat kein Local, EVE
    schreibt beim Eintritt einen Platzhalter statt eines Systemnamens. Statt
    das Wort zu vergleichen (das waere sprachabhaengig) wird gegen die Karte
    geprueft. An 65 echten Local-Namen aus einem Chatlog-Bestand standen 64
    in der Karte, nur der Abyss-Platzhalter nicht."""
    global _SYS_NAMES
    if _SYS_NAMES is None:
        m = load_json("eve_map.json", None) or {}
        _SYS_NAMES = {v[0] for v in (m.get("systems") or {}).values()
                      if isinstance(v, list) and v}
    return _SYS_NAMES
# Alle handelbaren Item-Namen -> typeID, fuer die Autovervollstaendigung der
# Marktpreis-Suche. Liegt als Datei bei; der Server haelt sie im Speicher und
# liefert nur die passenden Vorschlaege, damit die Oberflaeche leicht bleibt.
MARKET_TYPES = load_json("market_types.json", {})
# Vorsortiert nach Namenslaenge: kurze, exakte Treffer sollen oben stehen.
_MARKET_INDEX = sorted(((n.lower(), n) for n in MARKET_TYPES), key=lambda x: len(x[0]))
# Nur die Namen, klein geschrieben. Dient als Sperre fuer die Fracht-Erkennung:
# was handelbar ist, taugt nicht als Missions-Signatur. Siehe detect_mission.
MARKT_NAMEN = {str(n).lower() for n in MARKET_TYPES}


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


def loot_namen(text):
    """Gegenstandsnamen aus einem eingefuegten Frachtraum-Text.

    Bewusst NICHT ueber calc_loot: das wirft alles weg, was keine Markt-ID hat,
    und genau das sind Missionsgegenstaende. "Port Rolette Residents" steht in
    keiner der 19.119 Markt-Typen. Ueber calc_loot waere der Gegenstand, an dem
    die Mission haengt, immer der eine, der verschwindet."""
    namen = []
    for raw in (text or "").splitlines():
        n = raw.strip().split("\t")[0].strip()
        if n:
            namen.append(n)
    return namen


def beste_mission(*treffer):
    """Aus mehreren Erkennungen die mit der hoechsten Genauigkeit. None faellt raus."""
    best = None
    for t in treffer:
        if t and (best is None or int(t.get("conf", 0)) > int(best.get("conf", 0))):
            best = t
    return best


def detect_mission(enemies, dialogue="", items=None):
    """Missionsname + Genauigkeit (%) aus Gegnernamen, NPC-Funk (Local-Dialog)
    UND Fracht-Gegenstaenden.
    Der Funk ist die stärkere Quelle: er ist missions-spezifisch, kommt beim
    Reinwarpen und erkennt auch Missionen mit generischen Gegnern. Jede Signatur
    trägt eine Confidence; passt mehr als eine, gewinnt die mit der höchsten.

    Die Fracht ist der dritte Weg und deckt ab, woran die beiden anderen
    scheitern: Missionen mit gewoehnlichen Gegnern und ohne jeden Funk. Belegter
    Fall ist "Enemies Abound (1 von 5)" aus Aramachi, 13.08.2026: sieben Gegner,
    allesamt gewoehnliche Federation-Navy-Schiffe, kein Funk aufgezeichnet, also
    aus Kampf und Chat nicht ableitbar. Im Frachtraum lagen "Port Rolette
    Residents", und die gibt es nur in dieser Mission.

    Gibt {'name','conf'} oder None zurück (None = keine Mission erkannt)."""
    text = (" ".join(n for n, _ in (enemies or [])) + " " + (dialogue or "")).lower()
    best = None
    for sig, val in MISSION_SIGS.items():
        if sig and sig in text:
            name = val.get("m") if isinstance(val, dict) else val
            conf = int(val.get("c", 80)) if isinstance(val, dict) else 80
            if name and (best is None or conf > best["conf"]):
                best = {"name": name, "conf": conf}
    # Fracht: exakter Namensvergleich, wie bei den Site-Signaturen und aus
    # demselben Grund. Teilworte waeren hier fatal, weil im Laderaum ganz
    # normale Ware liegt.
    for nm in (items or []):
        schl = (nm or "").strip().lower()
        val = MISSION_ITEMS.get(schl)
        # Sperre: handelbare Ware taugt nie als Signatur, auch wenn sie in einer
        # Mission faellt. Belegt am eigenen Bestand: am 24.07. lagen "Tourists"
        # und "Kruul's DNA" aus einer frueheren Damsel-Mission noch im Laderaum,
        # waehrend in Anttiri Guristas bekaempft wurden. Als Signatur haetten die
        # beiden diesen Lauf falsch benannt. Beide stehen im Markt, echte
        # Missionsgegenstaende wie "Port Rolette Residents" oder "The Damsel"
        # dagegen nicht. Die Sperre greift also genau dort, wo sie muss, und
        # verhindert den Fehlgriff schon beim Eintragen.
        if not val or schl in MARKT_NAMEN:
            continue
        name = val.get("m") if isinstance(val, dict) else val
        conf = int(val.get("c", 90)) if isinstance(val, dict) else 90
        if name and (best is None or conf > best["conf"]):
            best = {"name": name, "conf": conf}
    return best


def fingerprint_mission(enemies):
    """Vierter Weg: der Gegner-Fingerabdruck aus deinen eigenen Benennungen.

    Missionen haben feste Gegner-Zusammenstellungen. Wer einen Lauf einmal
    benennt, hat damit eine Vorlage, an der jeder weitere Lauf derselben Mission
    wiedererkannt wird. Das braucht kein Wiki und keine gepflegte Signatur und
    greift genau da, wo alles andere versagt: gewoehnliche Gegner, kein Funk,
    nichts Einmaliges im Laderaum.

    Gemessen wird die Jaccard-Aehnlichkeit, also Schnittmenge geteilt durch
    Vereinigungsmenge. An den eigenen Daten liegt genau ein Paar darueber, und
    zwar das richtige: zwei Aramachi-Laeufe mit 6 von 9 gemeinsamen Gegnern.

    Die Genauigkeit ist die gemessene Aehnlichkeit, gedeckelt auf 88, damit ein
    einmaliger Gegnername oder Funk (90 bis 95) immer vorgeht. Das hier ist eine
    Aehnlichkeit, kein Beweis, und soll sich nie so anfuehlen.

    Verglichen wird gegen zwei Bestaende: die eigenen Benennungen und die
    mitgelieferten Vorlagen aus Meldungen anderer. Bei Gleichstand gewinnt die
    eigene, denn die stammt aus dem eigenen Spiel und ist damit die belastbarere.

    Gibt {'name','conf','quelle','wie'} oder None. 'quelle' ist 'eigen' oder
    'geteilt', 'wie' der Zeitstempel der eigenen Vorlage (sonst None), damit die
    Oberflaeche sagen kann, WORAN erinnert wurde."""
    hier = {(n or "").strip().lower() for n, _ in (enemies or []) if n}
    if len(hier) < FP_MIN_GEMEINSAM:
        return None
    best = None
    # Reihenfolge zaehlt: die eigenen zuerst, damit sie bei gleicher Genauigkeit
    # stehen bleiben (verglichen wird auf groesser, nicht groesser-gleich).
    for quelle, bestand in (("eigen", MARKEN), ("geteilt", MISSION_FP)):
        for m in bestand:
            gemeinsam = hier & m["set"]
            if len(gemeinsam) < FP_MIN_GEMEINSAM:
                continue
            alle = hier | m["set"]
            if not alle:
                continue
            j = len(gemeinsam) / len(alle)
            if j < FP_MIN_AEHNLICH:
                continue
            conf = min(88, int(round(j * 100)))
            if best is None or conf > best["conf"]:
                best = {"name": m["name"], "conf": conf, "quelle": quelle,
                        "wie": m.get("ts")}
    return best


def detect_site(enemies):
    """Wo war der Einsatz? Aktuell nur der Abyss, und zwar ueber EXAKTE
    Gegnernamen aus CCPs Abyssal-Gruppen.

    Bewusst kein Teilwort-Vergleich wie bei den Missionen: "Vila" sieht
    exklusiv aus, aber "Vila Allopoiesis Node" ist ein Spawn Container, und die
    EWAR-Praefixe (Harrowing, Starving, Tangling, Ghosting, Anchoring) gibt es
    auch ausserhalb des Abyss. An einem echten Logbestand haette ein
    Teilwort-Vergleich 1,3 Mio Zeilen falsch markiert.

    Ein einziger Treffer genuegt, denn diese Namen kann es woanders nicht
    geben. Gibt {'name','conf'} oder None."""
    for name, _cnt in (enemies or []):
        v = SITE_SIGS.get((name or "").strip().lower())
        if v:
            return {"name": v.get("m") if isinstance(v, dict) else v,
                    "conf": int(v.get("c", 90)) if isinstance(v, dict) else 90}
    return None


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
    # "shadow" allein war ein Fehlgriff: an 9.161 gespendeten Logs fing der Key
    # 125.380 Zeilen ein, die keine Serpentis sind. "Elder Corpum Shadow Sage"
    # und "Corpum Shadow Sage" tragen den Blood-Key "corpum", werden aber hier
    # zuerst geprueft. Echte Shadow-Serpentis-Treffer waren rund 700 Zeilen.
    # "pleasure hub"/"pleasure garden" ebenfalls raus: CCPs SDE kennt keinen NPC
    # dieses Namens (nur Strukturen), die 163.143 Zeilen waren also unbelegt.
    ("Serpentis",      ["serpenti", "coreli", "corelum", "corelior", "coretus",
                        "coreatis", "shadow serpentis", "core admiral",
                        "core lord"],
     ["therm", "kin"], ["kin", "therm"], "damp"),
    ("Blood Raiders",  ["corpus", "corpii", "corpior", "corpum", "corpatis",
                        "corpse", "blood raider", "blood clone", "dark blood"],
     ["em", "therm"], ["em", "therm"], "neut"),
    ("Sansha",         ["sansha", "centii", "centus", "centior", "centum",
                        "centatis", "true sansha"],
     ["em", "therm"], ["em", "therm"], "td"),
    # "angel cartel" verlangte beide Woerter und verfehlte damit "Tower Sentry
    # Angel III" (128.386 Zeilen), "Angel Viper", "Angel Assault Cruiser" und
    # weitere. Das kurze "angel" ist geprueft: ueber alle 115 NPC-Namen im SDE,
    # die "angel" enthalten, gehoert JEDER zum Angel Cartel.
    ("Angel Cartel",   ["gistii", "gistum", "gistatis", "gistior", "gist ",
                        "arch gist", "angel", "domination"],
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
    # --- Nachgetragen v1.71, weil sie in 1.021 fremden Logs die haeufigsten
    # Gegner ueberhaupt waren und Canary zu ihnen bisher geschwiegen hat.
    # Schadensprofile am EVE-University-Wiki geprueft, nicht geschaetzt.
    # Drifter: Schildwiderstaende 73-85%, EM ist das schwaechste Loch, sie
    # selbst schiessen EM/Therm.
    ("Drifter",        ["drifter", "lux kontos"],
     ["em", "therm"], ["em"], "neut"),
    # Sleeper: omni rein wie raus, es gibt KEINEN Schadensvorteil. Genau das
    # ist die nuetzliche Auskunft, sonst sucht man ewig nach der Schwaeche.
    # Dazu neuten sie den Kondensator leer.
    ("Sleeper",        ["sleeper", "sleepless", "awakened", "awoken",
                        "emergent "],
     ["omni"], ["omni"], "neut"),
    # Triglavianer: sie schiessen omni, sind aber gegen Explosiv und Thermal
    # am duennsten. Der Desintegrator dreht mit der Zeit hoch, deshalb Web.
    ("Triglavian",     ["leshak", "vedmak", "damavik", "rodiva", "kikimora",
                        "zirnitra", "drekavac", "ikitursa", "nergal",
                        "triglavian"],
     ["omni"], ["exp", "therm"], "web"),
    # EDENCOM und CONCORD tauchen in echten Logs auf (17.272 Zeilen bei einem
    # Spender), aber ein geprueftes Schadensprofil habe ich zu ihnen NICHT.
    # Deshalb nur der Name, ohne Empfehlung: leere Listen, die Oberflaeche
    # laesst die Zeilen "schiesse"/"tanke" dann weg. Lieber die Fraktion
    # benennen und zum Schaden schweigen als etwas zu behaupten.
    ("EDENCOM",        ["edencom"], [], [], None),
    ("CONCORD",        ["concord "], [], [], None),
]


# NPC-Name -> Fraktion, aus CCPs SDE erzeugt (Skript baue_npc_fraktionen.py).
# Quelle je Eintrag: invTypes.factionID, sonst der Gruppenname ("Deadspace
# Serpentis Battleship"). Was beides nicht hergab, steht NICHT drin.
# Der exakte Name schlaegt die Teilwort-Schluessel oben, denn die sind unscharf:
# an 9.161 gespendeten Logs lagen sie bei 42.026 Zeilen nachweislich daneben.
NPC_FACTIONS = load_json("npc_factions.json", {})


def faction_info(enemies):
    """Aus einer Gegnerliste [(Name, Anzahl), …] die dominante Fraktion ableiten,
    inkl. Schaden-tanken/-schiessen und typischer EWAR. None, wenn kein Name auf
    eine bekannte Fraktion passt (dann lieber nichts anzeigen als falsch raten)."""
    scores = {}
    for name, cnt in (enemies or []):
        low = (name or "").lower()
        # 1. exakter Name aus CCPs Tabelle, 2. die unscharfen Schluessel
        fac = NPC_FACTIONS.get(low)
        if fac:
            scores[fac] = scores.get(fac, 0) + (cnt or 1)
            continue
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
# Laengere Kompressions-Pause -> Kern gilt als aus (Verbrauch pausiert). An 27
# echten Logs gemessen (~13.000 Luecken): 99% der Pausen ohne Andocken liegen
# unter 4 min, Andock-Pausen dauern im Median 11 min. 10 min trennt beides und
# kostet nur 7 von 12.940 Luecken; das Andocken bremst zusaetzlich explizit.
HW_CORE_GAP = 600

TS_RE = re.compile(r"^\[ (\d{4})\.(\d{2})\.(\d{2}) (\d{2}):(\d{2}):(\d{2}) \] \((\w+)\) (.*)$")
HINT_RE = re.compile(r'hint="([^"]+)"')
STRIP_RE = re.compile(r"<[^>]+>")
# NBSP (\xa0) mit aufnehmen: manche Client-Sprachen (z.B. RU) nutzen ein
# geschuetztes Leerzeichen als Tausendertrenner — sonst wird "1<NBSP>234" zu "1".
# APOSTROPH ebenso: manche Clients schreiben "131'250 ISK". An 9.161 gespendeten
# Logs gemessen, dort betraf es 99,9% aller Bounty-Zeilen und machte aus
# 695 Mrd ISK ganze 79 Mio. Der Apostroph zaehlt NUR, wenn direkt eine Ziffer
# folgt, sonst frisst das Muster Namen wie "Tyrre'loh" an.
NUM_RE = re.compile("([\\d](?:[\\d.,\xa0 ]|['’](?=[\\d]))*)")
CHAR_FILE_RE = re.compile(r"^\d{8}_\d{6}_(\d+)\.txt$")
CHAT_LINE_RE = re.compile(r"^\[ [\d. :]+ \] ([^>]+?) > (.*)$")
CHAT_TS_RE = re.compile(r"^\[ (\d{4})\.(\d{2})\.(\d{2}) (\d{2}):(\d{2}):(\d{2}) \]")
OUT_COLOR = "0xff00ffff"
IN_COLOR = "0xffcc0000"
# Cap-Kriegsfuehrung hat eigene, blassere Varianten der beiden Schadensfarben.
# An 9.161 gespendeten Logs gemessen: 217.004 Zeilen rein, 4.494 raus, in jedem
# der acht Jahre. Bisher wurden sie nur ueber das WORT erkannt (EWAR_TEXTS, nur
# DE/EN), ein russischer Client verlor alle 217.004 still. Genau der Fehler,
# den es bei LOGI_COLOR schon einmal gab.
# Und die Richtung war falsch: die Gewinn-Zeile ("+43 GJ energy drained from X
# - Medium Rudimentary Energy Nosferatu") zaehlte als EWAR GEGEN dich, weil
# "Nosferatu" im Modulnamen steht. Es ist aber dein eigener Nosferatu.
NEUT_IN_COLOR = "0xffe57f7f"    # dein Kondensator wird geleert
NEUT_OUT_COLOR = "0xff7fffff"   # du saugst den Gegner leer
# Fernunterstuetzung (Logi): eigene Farbe, weder Schaden aus noch Schaden ein.
# "298 remote capacitor transmitted to Guardian [PR.BL] [C.H.P] [Jarrod Sands]
#  - - Large Inductive Compact Remote Capacitor Transmitter"
# An 12.252 echten Zeilen aus sechs Jahren geprueft, ausschliesslich dort.
LOGI_COLOR = "0xffccff66"
# Die ART der Hilfe kommt aus dem MODULNAMEN am Zeilenende, nicht aus dem Satz:
# Modulnamen sind nie lokalisiert, der Satz drumherum schon.
LOGI_ART = (("capacitor transmitter", "cap"), ("capacitor transporter", "cap"),
            ("armor repairer", "armor"), ("shield booster", "shield"),
            ("hull repairer", "hull"))
# Richtung laesst sich NICHT an der Farbe ablesen, die ist fuer beide gleich.
# Also doch am Wort. Englisch ist belegt, Deutsch ist begruendete Annahme.
# Passt keins, wird die Zeile trotzdem gezaehlt, nur ohne Richtung: die Farbe
# beweist ja, dass Hilfe geflossen ist.
LOGI_DIR = {"to": "out", "by": "in", "an": "out", "von": "in"}
# Wie lange nach der letzten Fernunterstuetzung gilt die Anzeige als aktuell.
# 15 Minuten: lang genug, dass eine Feuerpause im Einsatz sie nicht wegnimmt,
# kurz genug, dass nach dem Einsatz nichts Totes stehen bleibt.
LOGI_FRISCH = 900
# Mining-Zeilen: die Farbe vor der Zahl trennt Ertrag von Verlust, sprach-
# unabhaengig wie bei der Schadensrichtung. Gruen = normale Ausbeute,
# Gelb = "Kritischer Bergbauerfolg" (Bonus, zaehlt mit), ROT = Rueckstand
# ("Zusaetzliche N Einheiten aus X als Rueckstaende erschoepft"), also Abfall.
# An 60.000 echten Mining-Zeilen geprueft: Rot kommt AUSSCHLIESSLICH in
# Rueckstands-Zeilen vor. Ohne diese Pruefung zaehlt Canary den Abfall als
# Ertrag, sobald der Client den Namen in <localized hint=...> wrappt — beim
# GAS ist das der Fall ("Harvestable Cloud"), beim Erz steht dort nur der
# unverlinkte Klartext "Asteroid", weshalb es dort nie auffiel.
MINE_WASTE_COLOR = "#ffff454b"
# Spieler stehen im Kampflog IMMER als "Name[TICKER](Schiffstyp)", NPCs nie.
# Das gilt in jeder Client-Sprache und ist damit das verlaessliche Kriterium —
# eine Namensliste kann es nicht sein, weil Missionen ihre Rats frei umbenennen
# ("Shadow's Grunt", "Roden Shipyard Interceptor" stehen in keiner ESI-Kategorie).
PLAYER_RE = re.compile(r"\[[^\[\]]{1,10}\]\s*\([^()]+\)")
# Wurmloch-Systeme heissen J######, im Overview mit selbstgewaehltem Zusatz.
WH_SYS_RE = re.compile(r"^J\d{6}\b")


def not_a_pilot(name):
    """Traegt die Form "Name[TICKER](Typ)", ist aber kein Mensch.

    Drohnen, Wracks, Mobile Tractor Units, Kontrolltuerme und Zollbueros
    gehoeren einem Spieler und sehen im Log deshalb genauso aus wie ein Pilot.
    Erkennung ueber die schon mitgelieferte Typtabelle statt ueber eine
    Namensliste: was handelbar ist, ist ein Gegenstand und kein Pilot."""
    if not name:
        return True
    n = name.strip()
    if n in MARKET_TYPES or n.rstrip("*").strip() in MARKET_TYPES:
        return True
    if WH_SYS_RE.match(n):
        return True
    if " Wreck" in n or n.startswith("Customs Office"):
        return True
    # Besitzform "Askend's Warrior II": im Log steht der Eigentuemer vor dem
    # Geraet, in der Typtabelle steht nur der Typ. Ohne diesen Schritt zaehlt
    # jede Drohne als gegnerischer Pilot, und Ratten schiessen mit Drohnen
    # waere ploetzlich PvP. Ein echter Pilotenname faellt hier nicht durch: der
    # Rest hinter dem Apostroph steht dann in keiner Typtabelle.
    for trenn in ("'s ", "’s "):
        if trenn in n:
            rest = n.split(trenn, 1)[1].strip()
            if rest and (rest in MARKET_TYPES or rest.lower() in NPC_FACTIONS):
                return True
    return n.lower() in NPC_FACTIONS
# Fuehrende Schadenszahl (auch mit Tausender-Trennung) am Zeilenanfang
DMG_HEAD_RE = re.compile(r"^\d(?:[\d.,  ]|['’](?=\d))*")
# Sprachabhängige Signale. ALLES ANDERE (Erz, Schaden, Gegner, Bounties, Module)
# ist sprachunabhängig über hint-Tags, Farbcodes und Zahlen — nur diese vier
# Meldungen stehen als reiner Fließtext im Log und brauchen pro Sprache ein Muster.
# Erweitern ohne neue Version: in config.json unter "log_texts", z.B.
#   "log_texts": {"undock": ["Désamarrage", "Отстыковка"]}
# Die echten Sätze liefert die Diagnose eines Nutzers (Abschnitt "Unerkannte
# Meldungen"), damit hier nichts geraten werden muss.
CARGO_FULL_TEXTS = ["Frachtraum des Schiffs ist voll", "cargo hold is full",
                    "cargohold is full"]
# "mining drones must unload" stand hier sechs Versionen lang und hat NIE
# gegriffen: 0 Treffer in 9.267 Logdateien. Der echte englische Satz lautet
# "These mining drones need to deposit their current loads of ore before
# executing new mining commands." Dadurch fiel die Drohnen-Warnung bei jedem
# englischsprachigen Nutzer komplett aus. Der falsche Satz bleibt drin, er
# kostet nichts und faengt eine eventuelle aeltere Client-Fassung mit ab.
DRONE_UNLOAD_TEXTS = ["Bergbaudrohnen müssen ihre aktuellen Erzladungen verladen",
                      "mining drones need to deposit their current loads",
                      "mining drones must unload"]
UNDOCK_TEXTS = ["Abdocken", "Undocking"]      # (None)-Zeile beim Abdocken
TRADE_TEXTS = ["Handel mit", "Trade with"]    # Handel abgeschlossen -> Laderaum unklar
# Abgebrochener Handel. Nur diese Woerter heben den Laderaum-Reset wieder auf,
# alles andere bleibt wie bisher ein abgeschlossener Handel.
TRADE_CANCEL_TEXTS = ["canceled", "cancelled", "abgebrochen"]
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
# Die deutsche Fassung des Fehlschlags stand nicht drin und fiel damit aus der
# Bergungs-Statistik. Fuer die beiden anderen Faelle gibt es in den vorliegenden
# Logs keine deutsche Zeile, deshalb wird dort auch nichts geraten.
SALVAGE_FAIL = ["salvaging attempt failed", "bergungsversuch schlug"]
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


# ---------------------------------------------------------------------------
# Alltagslaerm: erkannt, aber stumm.
#
# An 9.161 gespendeten Logs (24 Mio Zeilen, sieben Jahre) gemessen: 1,16 Mio
# Zeilen fielen bisher durch, davon sind rund 98% Prozessgeplapper. Beispiele
# mit ihrer Haeufigkeit JE SITZUNG: "Drones engaging" 70,5, "Modul deaktiviert,
# Ziel weg" 71,0, "Nachladen" 22,6. Als Meldung waere das jedes Mal Laerm.
#
# Der Gewinn ist deshalb nicht die Quote, sondern die Diagnose: vorher
# ertranken die echt unbekannten Meldungen eines fremdsprachigen Clients in
# diesen 1,16 Mio Zeilen. Jetzt steht in UNKNOWN_NOTIFY nur noch, was Canary
# wirklich nicht kennt. Die Klassennamen sind absichtlich sprechend, damit ein
# spaeteres Feature eine Klasse einfach hochstufen kann.
#
# Muster haengen an Satzfragmenten ohne Eigennamen und Zahlen, damit sie ueber
# Client-Versionen stabil bleiben. Deutsche Entsprechungen stehen dort, wo sie
# belegt sind. Wo nicht, bleibt es beim englischen Muster: eine geratene
# Uebersetzung greift still nicht und taeuscht dann Abdeckung vor.
NOISE_PATTERNS = [
    # Module: Ziel weg, nicht gelockt, explodiert
    (r"deactivates as the item it was targeted at is no longer present", "modul_ziel_weg"),
    (r"deactivates because its target,.*is not locked", "modul_ziel_ungelockt"),
    (r"deactivates as .* begins to explode", "modul_ziel_explodiert"),
    (r"cannot activate that module as the target is no longer present", "modul_ziel_weg"),
    (r"deaktiviert.*Ziel.*nicht mehr (vorhanden|da)", "modul_ziel_weg"),
    # Module: leer, blockiert, keine Ziele
    (r"has run out of charges", "modul_leer"),
    (r"hat keine Ladungen mehr", "modul_leer"),
    (r"has no suitable targets within range", "modul_keine_ziele"),
    (r"External factors are preventing your .* from responding", "modul_blockiert"),
    (r"cannot load or unload .* while it is active", "modul_blockiert"),
    (r"cannot be manually deactivated in the middle of an operation", "modul_blockiert"),
    (r"requires [\d.,'’]+ units of charge\. The capacitor has only", "modul_kein_cap"),
    (r"cannot engage a tractor beam on that object as it is already", "modul_blockiert"),
    (r"You do not have the required skill", "modul_blockiert"),
    # Drohnen
    (r"^Drones engaging", "drohnen_angriff"),
    (r"^All drones returning to drone bay", "drohnen_rueckruf"),
    (r"^Regrouping", "drohnen_sammeln"),
    (r"don't have enough bandwidth to launch", "drohnen_bandbreite"),
    (r"cannot be commanded to work on a target that is no longer present", "drohnen_ziel_weg"),
    (r"drones fail to execute your commands", "drohnen_ziel_weg"),
    (r"because you are already controlling \d+ drones", "drohnen_limit"),
    (r"To give this command to a drone requires that you have an active target",
     "drohnen_kein_ziel"),
    (r"Drohnen.*(greifen an|kehren zurueck|kehren zurück)", "drohnen_angriff"),
    # Nachladen
    (r"^Loading the .* into the .*; this will take approximately", "nachladen"),
    (r"^Lade .* in .*; dies dauert", "nachladen"),
    # Zielerfassung
    (r"Targeting attempt failed", "ziel_fehlgeschlagen"),
    (r"Your attempt to target .* failed", "ziel_fehlgeschlagen"),
    (r"^Target lock unsuccessful", "ziel_fehlgeschlagen"),
    (r"Invalid target, the .* can only be activated on", "ziel_fehlgeschlagen"),
    (r"You are already managing \d+ targets", "ziel_limit"),
    (r"is too far away\. It must be within", "ziel_zu_weit"),
    (r"Interference from .* prevents your sensors from locking", "ziel_stoerung"),
    (r"Interference from .* preventing your sensors from getting a target lock", "ziel_stoerung"),
    (r"Interference from .* preventing your systems from functioning", "ziel_stoerung"),
    (r"Unknown local interference is preventing normal sensor operation", "ziel_stoerung"),
    (r"You have lost your target lock on", "ziel_verloren"),
    (r"^Target is invulnerable", "ziel_unverwundbar"),
    # Bewegung
    (r"^Ship stopping", "bewegung"),
    (r"^Speed changed to", "bewegung"),
    (r"You cannot do that while warping", "bewegung"),
    (r"is on automatic approach", "bewegung"),
    (r"unable to align or warp to the selected object", "bewegung"),
    (r"^Schiff haelt an|^Schiff hält an", "bewegung"),
    # Docking
    (r"docking request has been accepted", "docking"),
    (r"^Requested to dock at", "docking"),
    (r"station services processes your undocking request", "docking"),
    (r"^Docking operation already in progress", "docking"),
    (r"Can't do that while undocking", "docking"),
    (r"Andockanfrage", "docking"),
    # Reichweite und Fracht
    (r"is too far away to use your .* on, it needs to be closer", "zu_weit_weg"),
    (r"You must be within [\d.,'’]+ meters of the container", "zu_weit_weg"),
    (r"The item is no longer within your reach", "zu_weit_weg"),
    (r"^Cargo is too far away", "zu_weit_weg"),
    (r"Item was added to the hold but will not be included in the fitting", "fracht_hinweis"),
    (r"cargo units would be required to complete this operation", "fracht_hinweis"),
    (r"item(s)? (was|were) moved to your hangar", "fracht_hinweis"),
    (r"rigs in the saved fitting were not fitted", "fitting"),
    (r"These charges cannot be fitted", "fitting"),
    # Tarnung
    (r"[Cc]loak deactivates due to proximity", "tarnung_aus"),
    (r"Interference from the cloaking you are doing", "tarnung_stoerung"),
    (r"cloaking device .* recalibrat", "tarnung_stoerung"),
    # Bedienung
    (r"^Please wait\.\.\.", "bedienung"),
    (r"^Session change already in progress", "bedienung"),
    (r"^Attempting to join a channel", "bedienung"),
    (r"scanner is recalibrating", "bedienung"),
    (r"systems are still recalibrating", "bedienung"),
    (r"^Bitte warten", "bedienung"),
    # Flotten-Boost. Inhaltlich interessant (belegt Booster-Rolle und
    # Flottengroesse), aber 241 Zeilen je betroffener Sitzung. Erst einmal stumm.
    (r"has applied bonuses to \d+ fleet member", "flotten_boost"),
    # Sondieren, Sites, Markt, Kleinkram
    (r"^No scan signatures detected", "sondieren"),
    (r"You need \d+ probes to launch this formation", "sondieren"),
    (r"^This gate is locked", "tor_verschlossen"),
    (r"Local spatial phenomena may cause strange effects", "site_effekt"),
    (r"LP Store purchase completed", "markt"),
    (r"The price you have chosen is .* (above|below) regional average", "markt_warnung"),
    (r"You already have a license for this SKIN", "kleinkram"),
    (r"is inviting you to a conversation", "einladung"),
    (r"invites you to join|wants you to join their fleet", "einladung"),
    (r"You are about to throw away", "abfrage"),
    (r"^Starting clone jumping", "klonsprung"),
    (r"^Disembarking from ship", "schiffswechsel"),
    # --- Nachtrag aus einem echten DEUTSCHEN Client -----------------------
    # Alle Muster unten stammen woertlich aus vorliegenden Logzeilen, keins ist
    # geraten. Vorher fielen sie als "unbekannt" durch und ueberdeckten in der
    # Diagnose die Meldungen, um die es dort eigentlich geht. Auffaellig oft
    # war der Grund, dass die deutsche Fassung SIEZT, die Muster aber duzten.
    (r"Sie (verfolgen|managen) bereits [\d.,]+ Ziele", "ziel_limit"),
    (r"gewährt [\d.,]+ Flottenmitglied", "flotten_boost"),
    (r"^Versucht,? einen? Chatkanal", "bedienung"),
    (r"ist zu weit entfernt, um Ihr .* darauf anwenden zu können", "zu_weit_weg"),
    (r"ist zu weit entfernt\. Es muss sich innerhalb", "ziel_zu_weit"),
    (r"^Fracht ist zu weit entfernt", "zu_weit_weg"),
    (r"^Folge .* in den Warp", "bewegung"),
    (r"Sie können dies nicht tun, während Sie warpen", "bewegung"),
    (r"Sie können dies während des Andockvorgangs nicht tun", "docking"),
    (r"Die Drohnen können Ihre Befehle nicht ausführen", "drohnen_ziel_weg"),
    # Das alte Muster verlangte "greifen an" am Stueck, im Log steht aber
    # "Drohnen greifen <Ziel> an" — es hat deshalb nie gegriffen.
    (r"^Drohnen greifen .* an$", "drohnen_angriff"),
    (r"nicht verwenden, weil Sie schon [\d.,]+ Drohnen benutzen", "drohnen_limit"),
    (r"Um einer Drohne diesen Befehl zu geben", "drohnen_kein_ziel"),
    (r"erfordert, dass das Ziel von Ihnen aufgeschaltet ist", "drohnen_kein_ziel"),
    (r"Der Versuch der Zielerfassung ist gescheitert", "ziel_fehlgeschlagen"),
    (r"nicht als Ziel aufschalten, da Ihre Sensoren", "ziel_stoerung"),
    (r"^Lade .* in .*\. Dies (wird|dauert) ca", "nachladen"),
    (r"wird sich in .* selbst zerstören", "selbstzerstoerung"),
    (r"^Ihr Schiff richtet sein magnetisches Feld neu aus", "bedienung"),
    (r"^Bitte wählen Sie die zu transferierenden Güter", "bedienung"),
    (r"^Konnte nicht gelesen werden", "bedienung"),
    (r"Sie sind dabei, .* zu verschrotten", "abfrage"),
    (r"Sie verfügen bereits über eine Lizenz für diese SKIN", "kleinkram"),
    (r"Link wird in Ihrem Standardbrowser geöffnet", "kleinkram"),
    (r"Sie können das Aussehen Ihres Schiffs nicht verändern", "kleinkram"),
    (r"konnte aus folgendem Grund nicht als Ihre Heimatstation", "kleinkram"),
    (r"benötigt [\d.,]+ ISK in Unterteilung", "kleinkram"),
    (r"erfordert [\d.,]+ CPU-Einheiten", "modul_blockiert"),
    (r"Dieses System ist von einem Aufstand", "site_effekt"),
    (r"^Warnung! Dieses Sonnensystem wurde von EDENCOM", "site_effekt"),
    # Planetary Industry: Rueckfragen des Kolonie-Fensters.
    (r"Keine weitere Struktur vom Typ .* auf diesem Planeten möglich", "pi_hinweis"),
    (r"Sie können diese Schiffsroute nicht erstellen", "pi_hinweis"),
    (r"Diese Route kann nicht erstellt werden", "pi_hinweis"),
    # --- Nachtrag Englisch, ebenfalls aus echten Zeilen -------------------
    (r"^Autopilot\b", "autopilot"),
    (r"Some drones were unable to engage", "drohnen_gejammt"),
    (r"^Drone cannot be commanded", "drohnen_ziel_weg"),
    (r"^Drone cannot be activated as there is not enough bandwith", "drohnen_bandbreite"),
    (r"You can't set that as a waypoint", "bewegung"),
    (r"You cannot do that while docking", "docking"),
    (r"You cannot compress materials", "modul_blockiert"),
    (r"cannot be activated unless the ship has an active Industrial Core", "modul_blockiert"),
    (r"does not support .* compression", "modul_blockiert"),
    (r"will not activate because its .* is not calibrated", "modul_blockiert"),
    (r"You are attempting to activate a passive module", "modul_blockiert"),
    (r"is already active$", "modul_blockiert"),
    (r"interference prevents modules of that type from being used", "ziel_stoerung"),
    (r"open orders and your Trade skill level only allows", "markt"),
    (r"has rejected your invitation to join the fleet", "einladung"),
    (r"is either not a member of your fleet or not present", "einladung"),
    (r"You are too far from the facility to modify this job", "zu_weit_weg"),
    (r"A new cargo container is being moved into the jettison duct", "fracht_hinweis"),
    (r"You cannot place a Planck generator", "kleinkram"),
]
NOISE_RE = [(re.compile(p, re.I), k) for p, k in NOISE_PATTERNS]
# Ganze Tags, die strukturell immer dasselbe sind. Das ist keine Rateleistung:
# eine (question)-Zeile IST eine Rueckfrage des Clients, eine (slash)-Zeile IST
# die Quittung auf einen getippten Slash-Befehl.
TAG_NOISE = {"question": "abfrage", "slash": "slash_quittung"}
# Rueckstand beim Bergbau. Bis 2025 stand der Verschnitt im Ertragssatz, seither
# in einer eigenen Zeile. Echte Zahl, kein Laerm.
# Zweite Zeile ist die deutsche Fassung. Sie fehlte, wodurch in den eigenen Logs
# 2.005 Rueckstandszeilen still verworfen wurden, waehrend die englischen zaehlten.
RESIDUE_RE = re.compile(
    r"(?:Additional\s+([\d][\d.,\xa0 '’]*)\s+units depleted from asteroid as residue"
    r"|Zusätzliche\s+([\d][\d.,\xa0 '’]*)\s+Einheiten aus Asteroid als Rückstände erschöpft)",
    re.I)
# Erfolgreiches Hacken benennt den Behaelter und damit den Site-Typ.
HACK_RE = re.compile(r"You successfully access the\s+(.+?)\s*\.?\s*$", re.I)
# Flotten-Boost mit der Zahl der bebonusten Mitglieder. Bis v2.0.x landete das
# als Rauschen im Papierkorb, und zwar in erheblichem Umfang: an 1,07 Mio
# Zeilen waren es 67.478 Stueck in 220 Dateien, also 83 Prozent des gesamten
# verworfenen Materials.
#
# Das ist die einzige Quelle, die die FLOTTENGROESSE minutengenau aus dem Log
# belegt, ganz ohne ESI. Verteilung im Messbestand: 3 Mitglieder 39,4 Prozent,
# 4 Mitglieder 55,0 Prozent.
#
# Beide Sprachfassungen stehen schon als Rauschmuster im Projekt und sind dort
# an echten Logs belegt, hier werden sie nur zusaetzlich ausgewertet. Es kommt
# also keine neue Sprachabhaengigkeit hinzu.
BOOST_RE = re.compile(
    r"(?:has applied bonuses to\s+(\d+)\s+fleet member"
    r"|gewährt\s+([\d.,]+)\s+Flottenmitglied)", re.I)
# Das Boost-Modul steht davor und ist nie uebersetzt.
BOOST_MOD_RE = re.compile(r"(?:Your|Ihr|Ihre|Dein|Deine)\s+([A-Za-z' ]{4,40}?)\s+"
                          r"(?:has applied|gewährt)", re.I)
# Zusatz, den der englische Client seit 2022 an die Ertragszeile haengt. Muss
# vom Erznamen abgeschnitten werden, sonst ist der Schluessel unbrauchbar.
RESIDUE_SUFFIX_RE = re.compile(r"\s+with a lost residue of\b.*$", re.I)


def classify_rest(base, tag, text):
    """Faellt eine Zeile durch alle Regeln: kennen wir sie trotzdem?
    Liefert ein Ereignis oder None. None heisst echt unbekannt."""
    m = RESIDUE_RE.search(text)
    if m:
        return {**base, "kind": "residue", "key": "Rueckstand",
                "value": num(m.group(1) or m.group(2))}
    m = BOOST_RE.search(text)
    if m:
        mod = BOOST_MOD_RE.search(text)
        return {**base, "kind": "boost",
                "key": (mod.group(1).strip() if mod else "Boost"),
                "value": num(m.group(1) or m.group(2))}
    m = HACK_RE.search(text)
    if m and len(m.group(1)) < 60:
        return {**base, "kind": "hack", "key": m.group(1).strip(), "value": 1}
    for rx, klasse in NOISE_RE:
        if rx.search(text):
            return {**base, "kind": "noise", "key": klasse, "value": 1}
    k = TAG_NOISE.get(tag)
    if k:
        return {**base, "kind": "noise", "key": k, "value": 1}
    return None


def num(s):
    # Erst die eindeutigen Tausendertrenner weg: NBSP, Leerzeichen, Apostroph.
    t = re.sub("[\xa0 '’]", "", s)
    # Punkt und Komma sind zweideutig. Steht am ENDE einer davon mit ein oder
    # zwei Ziffern dahinter, ist es ein Dezimaltrenner und keine Tausenderstelle:
    # "3'384'375.00" sind 3.384.375 ISK und nicht 338.437.500. EVE hat bis 2020
    # Kopfgelder mit zwei Nachkommastellen geschrieben, danach nicht mehr.
    # Eine Tausendergruppe hat IMMER genau drei Ziffern, deshalb ist die
    # Unterscheidung eindeutig.
    t = re.sub(r"[.,]\d{1,2}$", "", t)
    return int(re.sub("[.,]", "", t) or 0)


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
        # Rueckstaende sind Verlust, kein Ertrag: nie als Ausbeute zaehlen.
        # Erkennung ueber die Farbe, damit es in jeder Sprache greift
        # (siehe MINE_WASTE_COLOR). Seit 2025 steht der Rueckstand in einer
        # EIGENEN Zeile ("Additional N units depleted from asteroid as
        # residue"), die traegt dieselbe Farbe. Die wird jetzt als kind
        # "residue" erkannt statt still verworfen, damit die Verschnittquote
        # eines Trips ausweisbar ist.
        if MINE_WASTE_COLOR in body:
            klar = STRIP_RE.sub("", body)
            ev = classify_rest(base, tag, klar)
            if ev:
                return ev
            # Die Farbe sagt schon sicher, dass es Abfall ist. Passt der
            # Wortlaut trotzdem nicht, reicht die fuehrende Zahl.
            #
            # Gemessen an 1,07 Mio Zeilen: RESIDUE_RE verlangt das Wort
            # "asteroid", deshalb fielen 96 Gaswolken-Zeilen durch
            # ("Additional 10 units depleted from Harvestable Cloud as
            # residue"), obwohl die Gas-Ertraege selbst sauber gezaehlt
            # wurden. Die Verschnittquote beim Gasernten war dadurch
            # strukturell falsch. Ueber die Farbe zu gehen ist ausserdem
            # sprachunabhaengig und ueberlebt jede kuenftige Umformulierung.
            n = NUM_RE.search(klar)
            if n:
                return {**base, "kind": "residue", "key": "Rueckstand",
                        "value": num(n.group(1))}
            return None
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
                # Seit 2022 haengt der englische Client " with a lost residue of
                # N units" an den Satz. Ohne diesen Schnitt wandert der Zusatz in
                # den Erznamen: an 9.161 gespendeten Logs waren dadurch 43.068 von
                # 175.440 Erz-Ereignissen (24,5%) falsch verschluesselt, aus 72
                # echten Sorten wurden 984, und 21 Sorten gab es NUR kaputt. Die
                # trafen ore_types.json nie und fehlten in Preis, Refine und
                # Fleet Power.
                ore = RESIDUE_SUFFIX_RE.split(ore)[0].strip()
        if ore and n:
            return {**base, "kind": "ore", "key": ore, "value": num(n.group(1))}
    elif tag == "combat":
        low = body.lower()
        # ---- Cap-Kriegsfuehrung: eigene Farben, sprachunabhaengig -----------
        if NEUT_IN_COLOR in low:
            return {**base, "kind": "ewar", "key": "neut", "value": 1}
        if NEUT_OUT_COLOR in low:
            # Eigener Nosferatu oder Neut. Kein Angriff gegen dich, deshalb
            # ausdruecklich KEIN ewar. Erkannt, aber vorerst stumm.
            return {**base, "kind": "noise", "key": "cap_gewinn", "value": 1}
        # ---- Fernunterstuetzung: eigene Farbe, kein Schaden -----------------
        if LOGI_COLOR in low:
            plain = STRIP_RE.sub("", body).strip()
            n = NUM_RE.search(plain)
            if not n:
                return None
            modul = plain.rsplit(" - ", 1)[-1].strip() if " - " in plain else ""
            ml = modul.lower()
            art = next((a for w, a in LOGI_ART if w in ml), "?")
            # Vor dem ersten Klammerblock steht "<Menge> <Satz> <Richtung> <Schiff>".
            # Von hinten nach dem Richtungswort suchen, alles danach ist das Schiff.
            kopf = plain.split("[", 1)[0] if "[" in plain else plain
            worte = kopf.split()
            richtung, schiff = "unklar", ""
            for i in range(len(worte) - 1, -1, -1):
                r = LOGI_DIR.get(worte[i].lower())
                if r:
                    richtung, schiff = r, " ".join(worte[i + 1:]).strip()
                    break
            # Reihenfolge der Klammern ist [Corp] [Allianz] [Pilot], die
            # Allianz fehlt manchmal. Der Pilot steht immer zuletzt.
            # ABER: das gilt nur fuer ein bestimmtes Overview-Layout. An zwei
            # fremden Log-Spenden geprueft: beim einen 10 echte Pilotennamen und
            # 100% Treffer, beim anderen 96,3% ohne jede Klammer und der Rest
            # ein ALLIANZKUERZEL ("LAWN", "ANGEL"), das dann als Pilot angezeigt
            # wurde. Kuerzel bestehen nur aus Grossbuchstaben, Ziffern und
            # Bindestrichen; ein Pilotenname hat immer Kleinbuchstaben. Sieht es
            # nach Kuerzel aus, lieber "?" als ein falscher Name.
            klammern = re.findall(r"\[([^\[\]]+)\]", plain)
            pilot = klammern[-1].strip() if klammern else ""
            if not pilot or not any(c.islower() for c in pilot):
                pilot = "?"
            # Das Schiff endet vor dem Modulnamen, sonst schleppt es ihn mit.
            if " - " in schiff:
                schiff = schiff.rsplit(" - ", 1)[0].strip()
            return {**base, "kind": "logi_" + richtung, "art": art,
                    "key": pilot, "ship": schiff, "weapon": modul,
                    "value": num(n.group(1))}
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
                m = re.match(r"^\d(?:[\d.,\xa0  ]|['’](?=\d))*\s+(?:from|to)\s+(.+)$",
                             plain)
                if m:
                    parts = [p.strip() for p in m.group(1).split(" - ")]
                    who = parts[0] or None
                    if len(parts) >= 3:
                        weapon = parts[1]
                # Spieler? Dann steht "[TICKER](Schiff)" drin — Pilotenname ist
                # alles davor, ohne Schadenszahl und Richtungswort.
                mp = PLAYER_RE.search(plain)
                spieler = bool(mp)
                if mp:
                    head = DMG_HEAD_RE.sub("", plain[:mp.start()]).strip()
                    who = (head.split(" ", 1)[1] if " " in head else head).strip() or who
                    # "[TICKER](Typ)" heisst nur "gehoert einem Spieler", nicht
                    # "ist ein Pilot". Drohnen, Wracks, Mobile Tractor Units,
                    # Kontrolltuerme und Zollbueros tragen dieselbe Form. An
                    # 9.161 gespendeten Logs standen dadurch Wracks, Warrior II
                    # und sogar Wurmloch-Systemnamen in der PvP-Liste.
                    if not_a_pilot(who):
                        spieler = False
                elif hints:
                    who = hints[0]   # lokalisierter Client: NPC-Name aus dem hint
                ev = {**base, "kind": direction, "key": who or "?",
                      "value": num(n.group(1)), "player": spieler}
                if direction == "dmg_out":
                    if len(hints) > 1:
                        ev["weapon"] = hints[1]
                    elif weapon:
                        ev["weapon"] = weapon
                return ev
        # Nicht-Schaden-Kampfzeilen fuer die PvP/Missions-Ansicht: Fehlschuesse
        # (eigene = Trefferquote, gegnerische = Ausweichen) und EWAR gegen dich.
        pl = STRIP_RE.sub("", body).strip().lower()
        # Der deutsche Client SIEZT: "Serpentis Initiate verfehlt Sie völlig".
        # Hier stand nur die geduzte Form, die es im Log gar nicht gibt — in den
        # eigenen Logs fielen dadurch 122 Fehlschuesse gegen den Spieler durch.
        # Zuerst klaeren, ob die Zeile vom EIGENEN Schiff handelt: sonst wuerde
        # "Ihre Drohne verfehlt sie" als Treffer GEGEN einen gezaehlt.
        eigen = bool(re.match(r"^(your|deine?|ihre?)\b", pl))
        rein = next((w for w in ("misses you", "verfehlt dich", "verfehlen dich",
                                 "verfehlt sie", "verfehlen sie") if w in pl), None)
        if not eigen and rein:
            # Der Gegnername steht VOR der Fehlschuss-Wendung. Er stand die
            # ganze Zeit in der Zeile und wurde verworfen: an 1,07 Mio Zeilen
            # gemessen betraf das ALLE 10.724 gegnerischen Fehlschuesse.
            # Ohne ihn ist keine Trefferquote je Gegner moeglich.
            #
            # Der Name wird aus dem UNGEKUERZTEN Text geschnitten, damit die
            # Gross- und Kleinschreibung erhalten bleibt. Die Wendung selbst
            # kommt aus derselben Liste wie die Erkennung, es kommt also keine
            # neue Sprachabhaengigkeit dazu.
            roh = STRIP_RE.sub("", body).strip()
            schnitt = pl.find(rein)
            wer = roh[:schnitt].strip() if schnitt > 0 else ""
            return {**base, "kind": "miss_in", "key": wer, "value": 1}
        if eigen and ("miss" in pl or "verfehl" in pl):
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
        mc = re.search(r"compressed (.+?) into (\d(?:[\d.,]|['’](?=\d))*) (Compressed .+?)\.?\s*$", text)
        if mc:
            return {**base, "kind": "compressed",
                    "key": mc.group(3).strip().rstrip("*").strip(),
                    "raw": mc.group(1).strip().rstrip("*").strip(),
                    "value": num(mc.group(2))}
        # Command Ship (Orca/Porpoise/Rorqual): das Log des Boosters nennt JEDEN
        # Flottenpiloten namentlich, der ueber den Kompressionsdienst komprimiert,
        # auch fremde Spieler. "FivaS compressed 1440 Plagioclase II-Grade using
        # your compression services." -> Flotten-Kompression je Pilot.
        mfc = re.search(r"^(.+?) compressed ([\d.,  '’]+?) (.+?) using your compression services",
                        text)
        if not mfc:   # deutscher Client: "<Name> hat <N> <Erz> mithilfe Ihrer Kompressionsanlage komprimiert."
            mfc = re.search(r"^(.+?) hat ([\d.,  '’]+?) (.+?) mithilfe .+? komprimiert", text)
        if mfc:
            raw = next((h for h in hints if not h.startswith("Compressed")), None) or mfc.group(3)
            return {**base, "kind": "fleet_compress",
                    "key": mfc.group(1).strip().rstrip("*").strip(),
                    "raw": raw.strip().rstrip("*").strip(),
                    "value": num(mfc.group(2))}
        if any(t in text for t in TRADE_TEXTS):
            # Ein ABGEBROCHENER Handel setzt den Laderaum nicht zurueck. Das
            # Muster "Trade with" nahm ihn bisher mit: an 1,07 Mio Zeilen zwar
            # nur 2 Faelle, aber sachlich falsch, und die Zeile beendet den
            # Trip in der Live-Karte. Sicherheitshalber nur abweisen, wenn das
            # Abbruchwort wirklich dasteht, sonst bleibt es beim alten
            # Verhalten. So kann die Regel in keiner Sprache etwas kaputt
            # machen, das heute funktioniert.
            if any(w in text.lower() for w in TRADE_CANCEL_TEXTS):
                return {**base, "kind": "noise", "key": "handel_abgebrochen",
                        "value": 1}
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
        # Derselbe Fall im ENGLISCHEN Client: der setzt keine hint-Tags, der
        # Erzname steht im Klartext. Deshalb feuerte die Regel oben an 24 Mio
        # Zeilen KEIN einziges Mal, und die Drohnen-Warnung ging bei englischen
        # Nutzern nie wieder auf. Gegen ORE_TYPES pruefen, damit Kampfdrohnen
        # ("Drones engaging Vila Swarmer") nicht mitzaehlen.
        mde = re.match(r"^Drones engaging\s+(.+?)\s*$", text)
        if mde:
            ziel = mde.group(1).strip().rstrip("*").strip()
            if ziel in ORE_TYPES and not ziel.startswith("Compressed"):
                return {**base, "kind": "drone_engage", "key": ziel, "value": 1}
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
        ev = classify_rest(base, tag, text)
        if ev:
            return ev
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
        ev = classify_rest(base, tag, text)
        if ev:
            return ev
        note_unknown(text)
        return None
    # question, hint, warning, info, slash und alles, was oben durchfaellt:
    # vielleicht kennen wir die Zeile trotzdem und sie ist nur nicht anzeigbar.
    return classify_rest(base, tag, STRIP_RE.sub("", body))


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
           # Karenzzeit fuer die Modul-Warnung, in Sekunden. 0 = sofort.
           "tool_warn_delay": 0,
           # Wie empfindlich soll die Meldung "Laser aus, neues Ziel erfassen"
           # sein? immer | rate | leer | aus. Die Stufen sind an echten Logs
           # gemessen, siehe laser_off_liste().
           "laser_off_mode": "rate",
           "clip_watch": False, "roles": {}, "log_texts": {},
           "count_me": True, "ping": {}, "share_ore": False,
           "update_url": "https://raw.githubusercontent.com/Eve-Online-Askend/eve-canary/main"}
    if CONFIG_PATH.exists():
        try:
            cfg.update(json.loads(CONFIG_PATH.read_text(encoding="utf-8")))
        except Exception:
            pass
    if not cfg.get("log_dir"):
        d = find_log_dir()
        cfg["log_dir"] = str(d) if d else ""
    # 1.98.2 hatte fuer die Laser-Meldung nur einen Ja/Nein-Schalter. Wer ihn
    # ausgeschaltet hatte, soll nach dem Update nicht ploetzlich wieder
    # Meldungen bekommen. Ein gesetztes Ja bedeutete den heutigen Standard.
    if "laser_off_msg" in cfg:
        if not cfg.pop("laser_off_msg"):
            cfg["laser_off_mode"] = "aus"
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
-- Wallet Buddy: eigene Tabellen, damit die Missions-Logik oben unberuehrt
-- bleibt (die speichert nur positive Betraege ausgewaehlter ref_types).
-- trades = jede Order-Ausfuehrung, wbook = das VOLLSTAENDIGE Journal inklusive
-- negativer Posten, denn genau dort stehen Broker-Gebuehr und Steuer.
CREATE TABLE IF NOT EXISTS trades(tx_id INTEGER, char TEXT, ts REAL,
    type_id INTEGER, qty INTEGER, price REAL, is_buy INTEGER, loc_id INTEGER,
    PRIMARY KEY(tx_id, char));
CREATE TABLE IF NOT EXISTS wbook(id INTEGER, char TEXT, ts REAL,
    ref_type TEXT, amount REAL, PRIMARY KEY(id, char));
CREATE TABLE IF NOT EXISTS item_ids(name TEXT PRIMARY KEY COLLATE NOCASE, type_id INTEGER);
-- Typnamen dauerhaft merken. Vorher lag der Cache nur im Arbeitsspeicher und war
-- nach jedem Start leer: das Wallet-Panel loeste dann 70 Typen einzeln bei ESI
-- auf und stand dabei gemessene 15,4 Sekunden. Namen von Item-Typen aendern
-- sich praktisch nie, sie duerfen also dauerhaft liegen bleiben.
CREATE TABLE IF NOT EXISTS type_names(type_id INTEGER PRIMARY KEY, name TEXT);
CREATE TABLE IF NOT EXISTS missions(mid TEXT PRIMARY KEY, char_id TEXT, char TEXT,
    start_ts REAL, end_ts REAL, system TEXT, dmg_out INTEGER, dmg_in INTEGER,
    kills INTEGER, bounty REAL, hits INTEGER, miss_out INTEGER, miss_in INTEGER,
    weapons TEXT, enemies TEXT, loot_isk REAL, loot_text TEXT);
    CREATE TABLE IF NOT EXISTS uhr(id INTEGER PRIMARY KEY AUTOINCREMENT,
    label TEXT, start_ts REAL, end_ts REAL, sek REAL, m3 REAL, isk REAL,
    unsicher INTEGER);
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
try:  # v1.95: selbst vergebener Missionsname. Grundlage des Gegner-Fingerabdrucks:
      # einmal benannt, erkennt Canary jeden weiteren Lauf derselben Mission an
      # der Gegner-Zusammenstellung. Bleibt rein lokal.
    DB.execute("ALTER TABLE missions ADD COLUMN label TEXT")
    DB.commit()
except sqlite3.OperationalError:
    pass
try:  # v1.71: Fernunterstuetzung je Einsatz. Ohne diese Spalten ist die
      # Leistung eines Logi-Piloten nach dem Andocken fuer immer weg.
    DB.execute("ALTER TABLE missions ADD COLUMN logi_out REAL")
    DB.execute("ALTER TABLE missions ADD COLUMN logi_in REAL")
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


def belohnung_seit(char, seit):
    """ESI-belegte Missionsbelohnungen dieses Charakters seit einem Zeitpunkt.

    Gebaut fuer die Flottensumme im OBS-Overlay. Eine ISK pro Stunde, die aus
    der laufenden Sitzung kommt, kennt bei einer Mission nur die Bounty, und
    die ist der kleinere Teil: an 10 ESI-belegten Missionen gemessen sind es
    31,8 Prozent, der Rest ist Belohnung und Loot. Ohne diese Zahl zeigt das
    Overlay einem Missionsflieger rund ein Drittel seines Verdienstes.

    Der Preis dafuer ist Ehrlichkeit an anderer Stelle: die Belohnung steht
    erst im Journal, wenn ESI sie liefert, also bis zu eine Stunde spaeter.
    Deshalb wird sie in der Anzeige gekennzeichnet."""
    if not char or not seit:
        return 0.0
    try:
        with DB_LOCK:
            r = DB.execute(
                "SELECT COALESCE(SUM(amount),0) FROM journal "
                "WHERE char=? AND ts>=? AND ref_type LIKE 'agent_mission%'",
                (char, seit)).fetchone()
        return float(r[0] or 0)
    except Exception:
        return 0.0


def marken_laden():
    """Die selbst benannten Laeufe als Vorlagen fuer den Fingerabdruck einlesen.

    Laeuft beim Start und nach jeder Benennung. Bewusst ein voller Neuaufbau:
    die Liste ist klein (so viele Eintraege, wie von Hand benannt wurden), und
    ein Neuaufbau kann nicht auseinanderlaufen wie ein fortgeschriebener Index.

    Gleiche Namen werden zusammengefasst: wer dieselbe Mission dreimal benennt,
    soll dadurch nicht dreimal verglichen werden. Es gewinnt die groesste
    Gegnerliste, denn die beschreibt die Mission am vollstaendigsten."""
    global MARKEN
    try:
        with DB_LOCK:
            rows = DB.execute(
                "SELECT label, enemies, start_ts FROM missions "
                "WHERE label IS NOT NULL AND label<>'' ORDER BY start_ts").fetchall()
    except Exception:
        return
    je_name = {}
    for label, ej, ts in rows:
        try:
            s = {(n or "").strip().lower() for n, _ in json.loads(ej or "[]") if n}
        except Exception:
            continue
        if len(s) < FP_MIN_GEMEINSAM:
            continue
        name = (label or "").strip()
        alt = je_name.get(name)
        if alt is None or len(s) > len(alt["set"]):
            je_name[name] = {"name": name, "set": s, "ts": ts}
    MARKEN = list(je_name.values())


def meta_get(key, default=None):
    with DB_LOCK:
        r = DB.execute("SELECT value FROM meta WHERE key=?", (key,)).fetchone()
    return r[0] if r else default


def zu_laden():
    """Von Hand abgeschlossene Missionen: Charakter-ID -> Zeitpunkt.

    Warum das dauerhaft sein muss: "Mission abschliessen" schiebt ein
    kuenstliches Abdock-Ereignis in die laufende Sitzung. Das lebt nur im
    Speicher. Beim Neustart baut der Ingest die Sitzung aus dem Logkopf neu
    auf und spielt dabei ALLE Kampfzeilen erneut ein, das kuenstliche
    Ereignis steht ja in keiner Logdatei. Die Mission stand danach wieder
    offen, obwohl der Charakter laengst offline war. Gemeldet von Nirahse."""
    try:
        return {str(k): float(v) for k, v in
                json.loads(meta_get("mission_zu") or "{}").items()}
    except Exception:
        return {}


def zu_merken(char_id, ts):
    d = zu_laden()
    d[str(char_id)] = float(ts)
    # Alte Eintraege wegwerfen, sonst waechst der Schluessel ewig mit. Aelter
    # als SESSION_MAX_AGE kann keine Sitzung mehr betreffen.
    grenze = time.time() - SESSION_MAX_AGE
    d = {k: v for k, v in d.items() if v >= grenze}
    try:
        with DB_LOCK:
            DB.execute("INSERT OR REPLACE INTO meta VALUES('mission_zu',?)",
                       (json.dumps(d),))
            DB.commit()
    except Exception as e:
        log_error("CN-DB-01", "zu_merken", e)


# Parser-Version: hochzaehlen, wenn eine Parser-Aenderung ein Neu-Einlesen aller
# Logs noetig macht. "2" = englischer Client (Mining/Kompr. ohne hint) wird erfasst.
# "3" = Gegnernamen im Kampflog des englischen Clients (standen vorher alle als "?")
# "4" = Missions-Historie an Undock-Grenzen rueckwirkend aus allen Logs aufbauen
# "5" = Missionsort aus dem Gamelog (Undock-Ziel/Sprung) rueckwirkend nachtragen
# "6" = EWAR-Profil je Mission rueckwirkend aus allen Logs mitschreiben
# "7" = Mining-Trip-Episoden (Verlauf/Zeitachse) der letzten 48h aus Logs rekonstruieren
# "8" = Gas (Mykoserocin/Cytoserocin/Fullerite) bekommt Volumen und Preis, und
#       Rueckstands-Zeilen zaehlen nicht mehr als Ertrag. Beides muss rueckwirkend
#       durch alle Logs, sonst bleiben Gas-Ausbeuten auf 0 m3 und der faelschlich
#       gebuchte Abfall ("Harvestable Cloud") stehen.
# "9" = Fernunterstuetzung (Logi) wird ueberhaupt erst erkannt, und ein reiner
#       Logi-Einsatz zaehlt als Einsatz. Ohne Neu-Einlesen fehlt jede Logi-Zeile
#       der Vergangenheit.
# "10" = mehrere Zahlen waren falsch und muessen rueckwirkend richtig werden:
#       Tausendertrenner Apostroph ("131'250 ISK" wurde als 131 gelesen),
#       Dezimalstellen bis 2020 ("3'384'375.00"), verunreinigte Erznamen
#       ("Veldspar with a lost residue of 0 units" war ein eigener Schluessel),
#       eigener Nosferatu zaehlte als EWAR gegen dich, Wracks und Drohnen
#       zaehlten als Spieler. Dazu die neue Art "residue" und die stummen
#       "noise"-Zeilen, die absichtlich NICHT in die Datenbank wandern.
# v11: der deutsche Client siezt. "verfehlt Sie völlig" (Fehlschuesse gegen
#      einen), "Zusätzliche N Einheiten ... als Rückstände erschöpft" und
#      "Ihr Bergungsversuch schlug fehl" wurden deshalb still verworfen, obwohl
#      die englischen Fassungen zaehlten. Dazu die englische Drohnen-Meldung
#      "need to deposit their current loads", die es sechs Versionen lang nur
#      in einer Fassung gab, die im Log gar nicht vorkommt.
PARSE_VER = "11"


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
         hits,miss_out,miss_in,weapons,enemies,loot_isk,loot_text,dialog,ewar,
         logi_out,logi_in)
        VALUES(?,?,?,?,?,?,?,?,?,?,?,?,?,?,?,?,?,?,?,?,?)
        ON CONFLICT(mid) DO UPDATE SET
         char=excluded.char, end_ts=excluded.end_ts, system=excluded.system,
         dmg_out=excluded.dmg_out, dmg_in=excluded.dmg_in, kills=excluded.kills,
         bounty=excluded.bounty, hits=excluded.hits, miss_out=excluded.miss_out,
         miss_in=excluded.miss_in, weapons=excluded.weapons, enemies=excluded.enemies,
         dialog=COALESCE(excluded.dialog, missions.dialog), ewar=excluded.ewar,
         logi_out=excluded.logi_out, logi_in=excluded.logi_in""",
        (mid, m["char_id"], m["char"], m["start_ts"], m["end_ts"], m["system"],
         m["dmg_out"], m["dmg_in"], m["kills"], m["bounty"], m["hits"],
         m["miss_out"], m["miss_in"], json.dumps(m["weapons"], ensure_ascii=False),
         json.dumps(m["enemies"], ensure_ascii=False), None, None, m.get("dialog"),
         json.dumps(m.get("ewar") or [], ensure_ascii=False),
         m.get("logi_out") or 0, m.get("logi_in") or 0))


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


AUTOSTART_OK = (os.name == "nt" or sys.platform.startswith("linux")
                or sys.platform == "darwin")
CLIPBOARD_OK = sys.platform in ("win32", "darwin")


def autostart_path():
    if os.name == "nt":
        return (Path(os.environ.get("APPDATA", "")) / "Microsoft" / "Windows"
                / "Start Menu" / "Programs" / "Startup" / "EVE-Canary-Autostart.vbs")
    if sys.platform == "darwin":
        # launchd liest beim Login alles aus diesem Ordner. Der Dateiname muss
        # zum Label im plist passen, sonst meckert launchctl.
        return Path.home() / "Library" / "LaunchAgents" / "io.evecanary.autostart.plist"
    base = os.environ.get("XDG_CONFIG_HOME") or (Path.home() / ".config")
    return Path(base) / "autostart" / "eve-canary.desktop"


def set_autostart(on):
    """Startet Canary beim Login still im Hintergrund.
    Windows: VBS im Autostart-Ordner (unterdrueckt das Konsolenfenster).
    Linux: .desktop-Datei nach XDG-Standard, greift in GNOME/KDE/XFCE gleich.
    macOS: LaunchAgent-plist, das launchd beim naechsten Login startet."""
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
    elif sys.platform == "darwin":
        # Pfade maskieren: ein & oder < im Benutzernamen wuerde die Datei sonst
        # zerlegen, und launchd meldet das nicht, es startet dann einfach nicht.
        def x(v):
            return (str(v).replace("&", "&amp;").replace("<", "&lt;")
                    .replace(">", "&gt;"))
        p.write_text(
            '<?xml version="1.0" encoding="UTF-8"?>\n'
            '<!DOCTYPE plist PUBLIC "-//Apple//DTD PLIST 1.0//EN" '
            '"http://www.apple.com/DTDs/PropertyList-1.0.dtd">\n'
            '<plist version="1.0"><dict>\n'
            '  <key>Label</key><string>io.evecanary.autostart</string>\n'
            '  <key>ProgramArguments</key><array>\n'
            f'    <string>{x(sys.executable)}</string>\n'
            f'    <string>{x(script)}</string>\n'
            '    <string>--no-browser</string>\n'
            '  </array>\n'
            '  <key>RunAtLoad</key><true/>\n'
            '</dict></plist>\n', encoding="utf-8")
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

# Groessenklassen fuer die freiwillige Ertrags-Statistik (share_ore).
# Bewusst dieselbe Mechanik wie die Zaehlmarken: es wird NICHTS gesendet, die
# Installation holt lediglich EINE vorbereitete leere Datei, deren Name die
# Klasse traegt. Aus GitHubs Download-Zaehler wird daraus ein Histogramm.
# Halb-dekadisch (1, 3, 10, ...), damit wenige Klassen einen sehr weiten
# Bereich abdecken. Veroeffentlicht wird spaeter die UNTERGRENZE je Klasse,
# die Gesamtzahl ist damit ein belegbares Minimum und niemals geschoent.
ORE_M3_BUCKETS = [10_000, 30_000, 100_000, 300_000, 1_000_000, 3_000_000,
                  10_000_000, 30_000_000, 100_000_000, 300_000_000, 1_000_000_000]
ORE_ISK_BUCKETS = [10_000_000, 30_000_000, 100_000_000, 300_000_000,
                   1_000_000_000, 3_000_000_000, 10_000_000_000,
                   30_000_000_000, 100_000_000_000]


def ore_bucket(wert, klassen):
    """Groesste Klasse, die 'wert' noch erreicht, sonst None (zu wenig)."""
    treffer = None
    for k in klassen:
        if wert >= k:
            treffer = k
        else:
            break
    return treffer


def ore_month_totals(stamp):
    """m3 und ISK-Wert des angegebenen Monats ('2026-07') aus der Datenbank.

    Bewertet wird wie ueberall sonst ueber ore_value(), also zum Preis der
    komprimierten Variante. Ohne Preisdaten bleibt der ISK-Wert 0 und wird
    dann auch nicht gemeldet, statt eine Zahl zu erfinden."""
    with DB_LOCK:
        rows = DB.execute("SELECT key, SUM(value) FROM daily "
                          "WHERE kind='ore' AND substr(day,1,7)=? GROUP BY key",
                          (stamp,)).fetchall()
    if not rows:
        return 0.0, 0.0
    ids = set()
    for ore, _ in rows:
        t = ORE_TYPES.get(ore)
        if t:
            ids.add(t["typeID"])
        comp = ORE_TYPES.get("Compressed " + ore)
        if comp:
            ids.add(comp["typeID"])
    pm = {}
    if ids:
        try:
            roh = hub_prices(str(CONFIG.get("region") or "10000002"), ids)
            pm = {t: p[0] for t, p in roh.items()}   # Buy-Preis, wie in der Gesamt-Ansicht
        except Exception:
            pm = {}
    m3 = isk = 0.0
    for ore, units in rows:
        i, v = ore_value(ore, units or 0.0, pm)
        isk += i
        m3 += v
    return m3, isk


def share_ore_ping():
    """Freiwillige Ertrags-Statistik (Opt-in, Standard AUS).

    Meldet EINMAL pro Monat, in welche Groessenklasse die Foerdermenge des
    VORMONATS faellt, indem genau eine vorbereitete leere Datei geholt wird.
    Gesendet wird dabei nichts: kein Wert, keine Kennung, keine Namen. Allein
    die Wahl der Datei traegt die Groessenordnung, und GitHub zaehlt nur, wie
    oft sie ausgeliefert wurde.

    Bewusst der VORMONAT: nur der ist vollstaendig, der laufende waere je nach
    Meldezeitpunkt beliebig unfertig und wuerde die Statistik nach unten
    verzerren."""
    if not CONFIG.get("share_ore", False):
        return
    now = time.time()
    vor = time.gmtime(now - 15 * 86400)         # sicher im Vormonat gelandet
    stamp = time.strftime("%Y-%m", vor) if time.gmtime(now).tm_mday >= 2 \
        else time.strftime("%Y-%m", time.gmtime(now - 40 * 86400))
    if (CONFIG.get("ping") or {}).get("ore") == stamp:
        return
    try:
        m3, isk = ore_month_totals(stamp)
    except Exception as e:
        log_error("CN-UPD-01", "share_ore_ping(db)", e)
        return
    marken = []
    b = ore_bucket(m3, ORE_M3_BUCKETS)
    if b:
        marken.append(f"ore-{stamp}-m3-{b}.json")
    b = ore_bucket(isk, ORE_ISK_BUCKETS)
    if b:
        marken.append(f"ore-{stamp}-isk-{b}.json")
    for name in marken:
        try:
            fetch_url(f"https://github.com/{PING_REPO}/releases/download/"
                      f"stats-{stamp}/{name}", timeout=20)
        except urllib.error.HTTPError as e:
            if e.code != 404:      # 404 = Klasse nicht angelegt, gilt als erledigt
                log_error("CN-UPD-01", "share_ore_ping", e)
                return
        except Exception as e:
            log_error("CN-UPD-01", "share_ore_ping", e)
            return
    # Auch ohne Marken (zu wenig gefoerdert) als erledigt vermerken, sonst
    # rechnet die Installation den Monat immer wieder neu durch.
    with CONFIG_LOCK:
        p = dict(CONFIG.get("ping") or {})
        p["ore"] = stamp
        CONFIG["ping"] = p
        save_config()


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


# ------------------------------------------------------- Selbstpruefung Daten
# Was eine vollstaendige Installation haben MUSS, mit einer Mindestpruefung je
# Datei. Geprueft wird nicht nur "existiert", sondern auch "ist brauchbar": ein
# abgebrochener Download hinterlaesst eine Datei, die es zwar gibt, die aber
# kein gueltiges JSON enthaelt, und ein leeres {} sieht fuer load_json genauso
# aus wie eine fehlende Datei.
#
# Die Schwellen sind bewusst niedrig angesetzt. Sie sollen "kaputt oder leer"
# von "da" trennen, nicht den Inhalt bewerten: sonst schlaegt die Pruefung an,
# sobald eine Liste mal kuerzer wird.
DATEN_PRUEFUNG = {
    "ore_types.json": lambda d: isinstance(d, dict) and len(d) > 100,
    "ore_refine.json": lambda d: isinstance(d, dict) and bool(d.get("refine")),
    "eve_map.json": lambda d: isinstance(d, dict) and len(d.get("systems") or {}) > 1000,
    "npc_factions.json": lambda d: isinstance(d, dict) and len(d) > 20,
    "site_sigs.json": lambda d: isinstance(d, dict) and len(d) > 2,
    "mining_tools.json": lambda d: isinstance(d, list) and len(d) > 5,
    "mission_sigs.json": lambda d: isinstance(d, dict) and len(d) > 5,
    "mission_items.json": lambda d: isinstance(d, dict) and len(d) > 1,
    "mission_fingerprints.json": lambda d: isinstance(d, dict)
    and isinstance(d.get("vorlagen"), list) and len(d["vorlagen"]) > 0,
    "market_types.json": lambda d: isinstance(d, dict) and len(d) > 100,
    "gank_groups.json": lambda d: isinstance(d, dict)
    and bool((d.get("highsec") or {}).get("allianzen")),
}
DATEN_STATUS = {"geprueft": False, "repariert": [], "offen": []}


def daten_uebernehmen(name):
    """Abgeleitete Strukturen nach einer Reparatur neu bauen.

    Ohne das laege die frisch geholte Datei zwar auf der Platte, wuerde aber
    erst nach einem Neustart wirken. Die Ableitungen stehen hier absichtlich
    ausgeschrieben und nicht ueber eine Automatik: das ist die eine Stelle, die
    mitgezogen werden muss, wenn oben eine neue Datei dazukommt."""
    global ORE_TYPES, ORE_BY_TID, ORE_REFINE, MINING_TOOLS, GANK_GROUPS
    global GANK_IDX, MISSION_SIGS, MISSION_ITEMS, MISSION_FP, SITE_SIGS
    global MARKET_TYPES, _MARKET_INDEX, MARKT_NAMEN, NPC_FACTIONS, _SYS_NAMES
    if name == "ore_types.json":
        ORE_TYPES = load_json(name, {})
        ORE_BY_TID = {v["typeID"]: (n, v.get("volume", 0.0))
                      for n, v in ORE_TYPES.items()}
    elif name == "ore_refine.json":
        ORE_REFINE = load_json(name, {"refine": {}, "minerals": {}})
    elif name == "mining_tools.json":
        MINING_TOOLS = sorted(load_json(name, []), key=len, reverse=True)
    elif name == "gank_groups.json":
        GANK_GROUPS = load_json(name, {})
        GANK_IDX = gank_index(GANK_GROUPS)
    elif name == "mission_sigs.json":
        MISSION_SIGS = {k.lower(): v for k, v in load_json(name, {}).items()
                        if not k.startswith("_")}
    elif name == "mission_items.json":
        MISSION_ITEMS = {k.lower(): v for k, v in load_json(name, {}).items()
                         if not k.startswith("_")}
    elif name == "mission_fingerprints.json":
        MISSION_FP = [{"name": (v.get("m") or "").strip(),
                       "set": {str(g).strip().lower() for g in (v.get("g") or []) if g},
                       "n": int(v.get("n") or 1)}
                      for v in (load_json(name, {}).get("vorlagen") or [])
                      if (v.get("m") or "").strip() and (v.get("g") or [])]
    elif name == "site_sigs.json":
        SITE_SIGS = {k.lower(): v for k, v in load_json(name, {}).items()
                     if not k.startswith("_")}
    elif name == "market_types.json":
        MARKET_TYPES = load_json(name, {})
        _MARKET_INDEX = sorted(((n.lower(), n) for n in MARKET_TYPES),
                               key=lambda x: len(x[0]))
        MARKT_NAMEN = {str(n).lower() for n in MARKET_TYPES}
    elif name == "npc_factions.json":
        NPC_FACTIONS = load_json(name, {})
    elif name == "eve_map.json":
        _SYS_NAMES = None          # wird beim naechsten Zugriff neu geladen


def pruefe_daten():
    """Fehlende oder unbrauchbare Datendateien einmalig nachladen.

    Laeuft beim Start in einem eigenen Thread, damit das Dashboard sofort da
    ist. Ohne Netz passiert nichts Schlimmes: es bleibt beim bisherigen Stand,
    und die Diagnose sagt, welche Datei fehlt."""
    # Erst pruefen, dann erst ans Netz. Bei einer vollstaendigen Installation
    # ist das der Normalfall, und die soll nicht bei jedem Start eine Abfrage
    # ausloesen, die nichts findet.
    kaputt = []
    for name, ok in DATEN_PRUEFUNG.items():
        try:
            if ok(load_json(name, None)):
                continue
        except Exception:
            pass                   # unbrauchbar zaehlt wie fehlend
        kaputt.append(name)
    DATEN_STATUS["geprueft"] = True
    if not kaputt:
        print("Selbstpruefung: alle Datendateien vollstaendig.", flush=True)
        return

    base = (CONFIG.get("update_url") or "").rstrip("/")
    if not base.startswith("https://"):
        DATEN_STATUS["offen"] = list(kaputt)
        return
    rel = None
    try:
        info = json.loads(fetch_url(f"{base}/version.json", timeout=20).decode("utf-8"))
        repo, tag = info.get("repo"), info.get("tag")
        if repo and tag and re.fullmatch(r"[\w.-]+/[\w.-]+", repo) \
                and re.fullmatch(r"[\w.-]+", tag):
            rel = f"https://github.com/{repo}/releases/download/{tag}"
    except Exception:
        pass                       # dann eben ueber raw, siehe unten
    for name in kaputt:
        ok = DATEN_PRUEFUNG[name]
        daten = None
        for url in ([f"{rel}/{name}"] if rel else []) + [f"{base}/{name}"]:
            try:
                roh = fetch_url(url, timeout=60)
                geprueft = json.loads(roh.decode("utf-8"))
                if not ok(geprueft):
                    continue       # kaputte Quelle darf nichts ueberschreiben
                daten = roh
                break
            except Exception:
                continue
        if daten is None:
            DATEN_STATUS["offen"].append(name)
            log_error("CN-DATA-01", "pruefe_daten", Exception(name))
            continue
        try:
            (APP_DIR / (name + ".neu")).write_bytes(daten)
            os.replace(APP_DIR / (name + ".neu"), APP_DIR / name)
        except Exception as e:
            DATEN_STATUS["offen"].append(name)
            log_error("CN-DATA-01", "pruefe_daten/schreiben", e)
            continue
        daten_uebernehmen(name)
        DATEN_STATUS["repariert"].append(name)
        print(f"Selbstpruefung: {name} fehlte und wurde nachgeladen.", flush=True)


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


NOTFALL_CSS = (
    "font:14px/1.45 'Segoe UI',system-ui,sans-serif;background:#101418;"
    "color:#dfe7ef;margin:0;padding:40px 20px;text-align:center")
NOTFALL_KNOPF = (
    "display:inline-block;margin-top:14px;padding:10px 22px;border:0;"
    "border-radius:9px;background:#e8c645;color:#101418;font:inherit;"
    "font-weight:700;cursor:pointer")


def notfall_banner():
    """Update-Hinweis, den PYTHON in die Seite schreibt, nicht das Skript.

    Der Grund steht in der Versionsgeschichte zu 1.96.0: ein einziger
    Syntaxfehler im grossen Skriptblock legt diesen Block komplett still, und
    zwar bevor die erste Zeile laeuft. Das bisherige Update-Banner wurde vom
    Skript gebaut, war damit ebenfalls tot, und die Betroffenen kamen aus dem
    Dashboard nicht mehr an das rettende Update. Sie mussten den Installer von
    Hand nachziehen.

    Dieses Banner haengt an gar keinem Skript. Sein Knopf ist ein gewoehnliches
    Formular, das der Server selbst beantwortet. Es ueberlebt damit auch einen
    Totalausfall der Oberflaeche, und genau dafuer ist es da.

    Die Position ganz oben im Body ist Absicht, aber sie ist NICHT der Grund,
    warum es funktioniert. Entscheidend ist, dass hier kein JavaScript
    beteiligt ist."""
    if not UPDATE_INFO.get("available"):
        return ""
    neu = html_escape(str(UPDATE_INFO.get("latest") or "?"))
    return (
        '<form method="post" action="/reparieren" '
        'style="margin:0;padding:9px 14px;background:#e8c645;color:#101418;'
        'font:600 13px/1.4 \'Segoe UI\',system-ui,sans-serif;display:flex;'
        'gap:12px;align-items:center;flex-wrap:wrap">'
        '<span>Neue Version <b>' + neu + '</b> verfuegbar '
        '(installiert: ' + html_escape(VERSION) + ').</span>'
        '<button type="submit" style="padding:5px 14px;border:0;border-radius:7px;'
        'background:#101418;color:#e8c645;font:inherit;cursor:pointer">'
        'Jetzt aktualisieren</button>'
        '<span style="opacity:.75;font-weight:400">Dieser Hinweis kommt vom '
        'Server und funktioniert auch, wenn die Oberflaeche streikt.</span>'
        '</form>')


def html_escape(t):
    return (str(t).replace("&", "&amp;").replace("<", "&lt;")
            .replace(">", "&gt;").replace('"', "&quot;"))


def notfall_seite(inhalt):
    return ("<!DOCTYPE html><html lang=\"de\"><head><meta charset=\"utf-8\">"
            "<title>EVE Canary reparieren</title></head>"
            "<body style=\"" + NOTFALL_CSS + "\">"
            "<div style=\"font-size:46px\">🐤</div>" + inhalt + "</body></html>")


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

    def push(self, kind, char, text, logo=None):
        """logo: optionaler Pfad beim offiziellen Bilddienst, z.B.
        "corporations/98679090" oder "alliances/1354830081". Nur Pfad, keine
        volle Adresse: die baut das Frontend und prueft sie vorher gegen ein
        festes Muster, damit ueber diesen Weg keine fremde URL ins Bild kommt."""
        with self.lock:
            self.items.append({"id": self.next_id, "ts": time.time(),
                               "kind": kind, "char": char, "text": text,
                               "logo": logo})
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
        # Erz -> {Liefermenge: Anzahl}. Grundlage der Bonus-Zaehlung, siehe
        # bonus_roh(). Winzig: an 3.074 echten Lieferungen kamen je Erz nur
        # rund 60 verschiedene Mengen vor.
        self.ore_amounts = {}
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
        self.core_break = None   # letztes An-/Abdocken: davor und danach nicht ueberbruecken
        self.cargo_full = False
        self.cargo_ts = 0
        # Belegte Flottengroesse aus den Boost-Zeilen: (Zeitpunkt, Anzahl).
        # Nur der letzte Stand, mehr braucht die Anzeige nicht.
        self.boost = None
        self.last_ore_ts = None   # fuer Stillstand-Erkennung
        self.last_event_ts = None # letztes Log-Ereignis (Aktivitaets-/Online-Heuristik)
        self.idle_alerted = False
        self.low_since = None     # Raten-Waechter (Teilausfall-Erkennung)
        self.low_alerted = False
        self.lost_m3 = 0.0        # in dieser Session durch Stillstand/Drosselung entgangenes Erz-Volumen
        self._lost_ts = None      # letzter Verrechnungs-Zeitpunkt des Verlustzaehlers
        self.traveling = None     # ts des letzten Dock-/Warp-Signals -> Verlust pausiert
        self.dock_ts = None       # ts des letzten Anflugs zur Station (siehe feed)
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
        # Nur der Anteil gegen echte Spieler. Trennt PvP von Ratten und
        # Missionsgegnern, ohne dass jemand die Rolle von Hand setzen muss.
        self.pvp_out = self.pvp_in = 0
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
        # Fernunterstuetzung: was ich gegeben und was ich bekommen habe, je Art
        # (cap/armor/shield/hull), dazu die Partner. Ein Logi-Pilot teilt keinen
        # Schaden aus und bekommt keine Bounty, seine ganze Leistung steckt hier.
        self.logi_out = {}      # Art -> Menge gegeben
        self.logi_in = {}       # Art -> Menge bekommen
        self.logi_partner = {}  # Pilot -> {"out": Menge, "in": Menge, "ship": Typ}
        self.logi_unklar = 0    # Menge ohne erkennbare Richtung
        self.logi_last = 0      # Zeitstempel der letzten Fernunterstuetzung
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
            if ev["key"] == "dock":
                self.core_break = ev["ts"]   # an der Station laeuft kein Kern
                # Anflug zur Station gemerkt. Das ist das EINZIGE Andock-Signal,
                # das in beiden Sprachen belegt ist: "Setting course to docking
                # perimeter" bzw. "Setze Kurs zum Andock-Perimeter". Die
                # eigentliche Bestaetigung ("docking request has been accepted")
                # schreibt nur der englische Client, in 13 deutschen Logdateien
                # kommt sie kein einziges Mal vor. Daran haengt die Unterscheidung,
                # ob eine Mission an der Station oder aus der Ferne abgeschlossen
                # wurde.
                self.dock_ts = ev["ts"]
            return
        if k == "ore":
            self.cargo_full = False
            self.traveling = None   # es kommt Erz -> wieder aktiv am Guertel
            self.dock_ts = None     # und damit nachweislich nicht in der Station
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
            # Liefermengen mitzaehlen, fuer die Bonus-Erkennung (bonus_roh).
            mengen = self.ore_amounts.setdefault(ev["key"], {})
            menge = int(ev["value"])
            mengen[menge] = mengen.get(menge, 0) + 1
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
            if ev.get("player"):
                self.pvp_out += ev["value"]
            self.hits_out += 1
            # Wer schiesst, steht nicht in der Station: ein zuvor begonnener
            # Anflug wurde also abgebrochen.
            self.dock_ts = None
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
            if ev.get("player"):
                self.pvp_in += ev["value"]
            self.attackers[ev["key"]] = self.attackers.get(ev["key"], 0) + ev["value"]
            self._dmg_bucket(ev["ts"], "in", ev["value"])
            if live:
                self.win_in.append((now, ev["value"]))
        elif k == "miss_out":
            self.miss_out += 1
        elif k == "miss_in":
            self.miss_in += 1
        elif k in ("logi_out", "logi_in", "logi_unklar"):
            self.logi_last = ev["ts"]
            art = ev.get("art") or "?"
            # Ohne erkannte Richtung trotzdem zaehlen, aber getrennt fuehren:
            # lieber eine Zeile "Richtung unbekannt" als eine falsche Summe.
            ziel = self.logi_out if k == "logi_out" else (
                self.logi_in if k == "logi_in" else None)
            if ziel is None:
                self.logi_unklar += ev["value"]
            else:
                ziel[art] = ziel.get(art, 0) + ev["value"]
            p = self.logi_partner.setdefault(
                ev["key"], {"out": 0, "in": 0, "ship": ev.get("ship") or ""})
            if k == "logi_out":
                p["out"] += ev["value"]
            elif k == "logi_in":
                p["in"] += ev["value"]
            if ev.get("ship"):
                p["ship"] = ev["ship"]
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
            # Auch fremde Piloten koennen nur ueber den Kompressionsdienst
            # komprimieren, wenn der Kern laeuft: derselbe Beleg wie eigene
            # Kompression, oft aber haeufiger (mehrere Miner liefern laufend).
            self._core_heartbeat(ev["ts"])
        elif k == "compressed":
            self.cargo_full = False  # Kompression schafft Platz
            self._core_heartbeat(ev["ts"])
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
            self.dock_ts = None      # abgedockt: ab jetzt wieder draussen
            if ev["key"] == "dock":
                # Station-Stopp: Karte beginnt einen neuen Trip, sonst zeigen
                # ISK/Erz-Werte laengst abgeladene Ladung an. Historie (DB)
                # bleibt davon unberuehrt.
                self.core_break = ev["ts"]   # Abdocken: davor war der Kern aus
                self.trips += 1
                self.mining = {}
                self.ore_amounts = {}
                self.compressed = {}
                self.fleet_compress = {}
                self.weapons = {}
                self.targets = {}
                self.attackers = {}
                self.bounty = 0
                self.kills = 0
                self.dmg_out = self.dmg_in = 0
                self.pvp_out = self.pvp_in = 0
                self.hits_out = self.miss_out = self.miss_in = 0
                self.ewar = {}
                self.logi_out = {}
                self.logi_in = {}
                self.logi_partner = {}
                self.logi_unklar = 0
                self.logi_last = 0
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
        elif k == "boost":
            # Die Zahl im Log ist die Zahl der BEBONUSTEN Mitglieder, der
            # Booster selbst zaehlt nicht mit. Fuer die angezeigte
            # Flottengroesse gehoert er dazu.
            self.boost = {"ts": ev["ts"], "n": int(ev["value"]) + 1,
                          "modul": ev["key"]}
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
        """Aktive Modul-Warnungen (letzte 60s), mit Werkzeugname.

        Zwei Daempfer, beide aus der Praxis eines Flotten-Miners (gemeldet von
        Eron Solette, 4 Hulks und eine Orca an kleinen Brocken):

        1. Ist seit dem Abschalten wieder Erz geflossen, war es kein Ausfall,
           sondern ganz gewoehnliches Mining: der Brocken war leer, der Laser
           haengt laengst am naechsten. Die Meldung war dort schlicht falsch.
        2. Zusaetzlich eine einstellbare Karenzzeit (Optionen, tool_warn_delay),
           fuer alle, denen auch die verbleibenden Meldungen zu haeufig sind.
           Standard 0, damit sich ungefragt bei niemandem etwas aendert.

        Die echte Ausfallerkennung haengt NICHT hier dran. Die laeuft ueber
        lasers_off und den Ratenwaechter (rate_status) und schlaegt weiter an,
        sobald die Foerderrate wirklich einbricht. Hier faellt nur der Laerm weg.

        Warum ueberhaupt: an echten Logs gezaehlt kommt die Meldung schon bei
        EINEM Miner in der Spitze alle 77 Sekunden, bei 60 Sekunden Standzeit.
        Bei einer Flotte steht sie damit dauerhaft im Bild und wird zu Tapete."""
        now = time.time()
        cutoff = now - 60
        try:
            puffer = max(0, int(CONFIG.get("tool_warn_delay", 0) or 0))
        except (TypeError, ValueError):
            puffer = 0
        out = []
        for tool, (cnt, ts) in list(self.tool_off.items()):
            if ts < cutoff:
                del self.tool_off[tool]
                continue
            if self.last_ore_ts and self.last_ore_ts > ts:
                continue          # es floss wieder Erz, also laeuft das Ding
            if puffer and now - ts < puffer:
                continue          # Karenzzeit laeuft noch
            out.append({"tool": tool, "count": cnt, "drone": "Drone" in tool})
        return out

    def bonus_roh(self):
        """Lieferungen mit vervielfachtem Ertrag zaehlen. Gibt {Erz: (Anzahl,
        Zusatz-Einheiten)}.

        Je Charakter und Erz gibt es eine klare Normalmenge. Ein kleiner Teil
        der Lieferungen ist ein Vielfaches davon, rund 3,4 Prozent.

        Nachgemessen an 623.603 Lieferungen aus 8,5 Monaten: es gibt ZWEI
        scharfe Spitzen, 3,00 und 2,88, dazwischen praktisch nichts.
        Zweifache und Vierfache gibt es nicht. Welcher der beiden Faktoren
        gilt, wechselte je Charakter zu unterschiedlichen Zeitpunkten, das
        sieht nach Schiff oder Ausruestung aus und nicht nach einem Patch.
        Deshalb wird hier ein FENSTER geprueft (BONUS_AB bis BONUS_BIS) und
        nicht auf ganze Vielfache. Die erste Fassung tat Letzteres und meldete
        fuer die Daten von Dezember 2025 stur null.

        Alles UNTER der Normalmenge sind Restbestaende eines leerlaufenden
        Brockens und zaehlen selbstverstaendlich nicht als Bonus.

        Erkannt wird allein an ZAHLEN, nicht an Text. Damit funktioniert es in
        jeder Client-Sprache, so wie fast alles in Canary.

        Die Normalmenge ist die haeufigste Menge. Sie steht nach wenigen
        Zyklen fest, und weil hier jedes Mal neu ueber alle Lieferungen der
        Sitzung gerechnet wird, korrigieren sich die ersten Zyklen von selbst,
        sobald genug Daten da sind.

        Der Orca-Pilot hat in den Messdaten null Bonus: mit Drohnen gibt es ihn
        offenbar nicht, nur mit Strip Minern. Das faellt hier automatisch raus,
        es braucht keine Sonderregel."""
        out = {}
        for erz, mengen in self.ore_amounts.items():
            if not mengen:
                continue
            # Haeufigste Menge = Normallieferung. Bei Gleichstand die groessere,
            # damit eine einzelne Restmenge nicht zur Normalmenge wird.
            basis = max(mengen.items(), key=lambda x: (x[1], x[0]))[0]
            if basis <= 0:
                continue
            anzahl = extra = 0
            for menge, n in mengen.items():
                v = menge / basis
                if BONUS_AB <= v <= BONUS_BIS:
                    anzahl += n
                    extra += (menge - basis) * n
            if anzahl:
                out[erz] = (anzahl, extra)
        return out

    def laser_off_liste(self):
        """Die Dauer-Meldung "Laser aus, neues Ziel erfassen" fuers Frontend.

        Wichtig: das hier ist ein ANDERER Mechanismus als tool_warns. Der
        Zustand bleibt absichtlich stehen, bis die Rate sich erholt hat, bis
        angedockt wird oder bis man ihn abhakt. Genau das ist der Sinn: ein
        wirklich toter Laser soll nicht nach 60 Sekunden aus dem Blick fallen.

        Nur greift die Erholung erst beim naechsten vollen Minutenwechsel. Wer
        an kleinen Brocken foerdert, sieht die Meldung deshalb nach JEDEM
        Asteroiden aufblitzen, obwohl der Laser laengst weiterarbeitet.

        Der Ausweg ist dieselbe Karenzzeit wie bei tool_warns, und sie wirkt
        hier sogar praeziser: jede neue Abschaltung DESSELBEN Moduls setzt
        'since' zurueck. Ein Laser, der brav von Brocken zu Brocken springt,
        meldet sich also im Sekundentakt neu und kommt nie ueber die Karenz.
        Einer, der wirklich steht, meldet gar nichts mehr, altert durch und
        wird angezeigt. Genau die Unterscheidung, um die es geht.

        Bewusst NICHT die 'seit dem Abschalten floss wieder Erz'-Regel aus
        tool_warns: hier faellt das Erz der ANDEREN Laser und der Drohnen mit
        an, und damit wuerde ein tatsaechlich ausgefallenes Modul sofort
        stillgelegt. Das ist der eine Fall, den diese Meldung finden soll.

        Die Karenzzeit allein reicht hier NICHT, das ist gemessen: zwischen
        zwei Abschaltungen desselben Moduls liegen im Median 204 Sekunden (985
        echte Abstaende). Ein Strip-Miner-Zyklus dauert eben Minuten. Das
        gefuehlte "alle paar Sekunden" entsteht erst durch viele Laser
        gleichzeitig. Eine Karenz von 30 Sekunden deckt darum nur 9,7% der
        Abstaende ab, der Zustand altert fast immer durch.

        Deshalb gibt es vier Stufen (laser_off_mode), alle an den Logs eines
        Flotten-Miners mit 5 Rechnern gemessen. Angegeben ist, wie oft dort
        MINDESTENS EINE der fuenf Karten die Meldung zeigte:

          immer  41,1% der Foerderzeit. Jede Abschaltung meldet, bis die
                 Erholung greift. Das war das Verhalten bis 1.98.1.
          rate   24,7%. Nur wenn die Ausbeute auch wirklich eingebrochen ist.
                 Trennt sauber: sofort nachgezielt sind ~100% und still,
                 vergessen sind ~67% und meldet. Der Rest sind echte
                 Schwankungen (Warp, voller Frachtraum, Wechsel der
                 Guteklasse). Standard.
          leer    7,3%. Zusaetzlich still, sobald ueberhaupt wieder Erz kommt.
                 ACHTUNG, das verschweigt den Ausfall EINES von mehreren
                 Lasern: die anderen liefern weiter, und der Ratenwaechter
                 schlaegt erst unter 55% an, waehrend einer von drei Lasern
                 67% bedeutet. Wer ganz Ruhe will, zahlt hier dafuer.
          aus    gar nichts.

        Die Schwelle 0.85 ist dieselbe wie in der schon vorhandenen
        Erholungsregel, damit Anzeige und Erholung nicht auseinanderlaufen."""
        modus = str(CONFIG.get("laser_off_mode", "rate") or "rate")
        if modus == "aus":
            return []
        try:
            puffer = max(0, int(CONFIG.get("tool_warn_delay", 0) or 0))
        except (TypeError, ValueError):
            puffer = 0
        now = time.time()
        if modus in ("rate", "leer"):
            # Rate in Ordnung? Dann fehlt nichts, egal was ein einzelnes Modul
            # meldet. Ohne genug Messwerte (erste Minuten einer Sitzung) bleibt
            # es beim Melden, sonst waere ein echter Ausfall ausgerechnet am
            # Anfang stumm.
            rs = self.rate_status()
            if rs and rs[0] > 0 and rs[1] >= 0.85 * rs[0]:
                return []
        out = []
        for t, i in sorted(self.lasers_off.items()):
            if puffer and now - i["since"] < puffer:
                continue
            # Stufe "leer": kam nach der Abschaltung wieder Erz, ist Ruhe.
            # Die 15 Sekunden Beruhigung verhindern, dass eine Lieferung aus
            # dem noch laufenden alten Zyklus faelschlich als Entwarnung zaehlt.
            if modus == "leer" and self.last_ore_ts \
                    and self.last_ore_ts >= i["since"] + 15:
                continue
            out.append({"tool": t, "since": int(i["since"]),
                        "before": round(i["before"] or 0, 1)})  # m³/min vorher
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

    def _core_heartbeat(self, ts):
        """Ein Kompressions-Ereignis (eigenes oder eines Flottenmitglieds ueber
        den Dienst) ist der einzige Log-Beleg, dass der Industriekern in diesem
        Moment lief: ohne aktiven Kern lehnt EVE die Kompression rundweg ab.

        Zwei Bremsen gegen Ueberzaehlung: Luecken > HW_CORE_GAP zaehlen nicht,
        und ueber ein An-/Abdocken hinweg wird nie ueberbrueckt (an der Station
        laeuft garantiert kein Kern). An echten Logs gemessen liegen 99% der
        Luecken ohne Andocken unter 4 Minuten, waehrend Andock-Pausen im Median
        11 Minuten dauern, deshalb trennt HW_CORE_GAP beides zuverlaessig."""
        tl = self.core_timeline
        cum = tl[-1][1] if tl else 0.0
        if tl:
            gap = ts - tl[-1][0]
            docked = self.core_break is not None and self.core_break > tl[-1][0]
            if 0 < gap < HW_CORE_GAP and not docked:
                cum += gap
        tl.append((ts, cum))
        if len(tl) > 6000:
            del tl[:1000]

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

    def wieder_aufnehmen(self, m):
        """Eine bereits abgeschlossene Mission fortsetzen.

        Nirahses Fall: mitten in der Mission raus, andocken, reparieren,
        weiter. Das Andocken ist kein sicherer Abschluss, und im Gamelog gibt
        es dafuer kein Signal. An 1.010 Logdateien gesucht: kein Reparatur-
        Eintrag, keine Abgabe-Meldung, kein Schiffswechsel. Also wird nicht
        geraten, sondern zurueckgenommen, sobald sich zeigt, dass es weiterging.

        Die Werte der gespeicherten Mission wandern zurueck in die Sitzung, der
        weitere Kampf zaehlt oben drauf. Der Datenbank-Eintrag wird geloescht,
        damit beim naechsten Abschluss ein einziger daraus wird."""
        self.dmg_out = m.get("dmg_out") or 0
        self.dmg_in = m.get("dmg_in") or 0
        self.pvp_out = self.pvp_in = 0
        self.kills = m.get("kills") or 0
        self.bounty = m.get("bounty") or 0
        self.hits_out = m.get("hits") or 0
        self.miss_out = m.get("miss_out") or 0
        self.miss_in = m.get("miss_in") or 0
        self.weapons = dict(m.get("weapons") or [])
        self.targets = dict(m.get("enemies") or [])
        self.mission_system = m.get("system") or self.mission_system
        self.first_ts = m.get("start_ts") or self.first_ts
        self.dock_ts = None

    def reset_combat(self, ts=None):
        """Kampfzaehler auf null und einen neuen Einsatz beginnen.

        Wird beim Anflug zur Station und bei der Rueckkehr aus dem Abyss
        gebraucht. Ohne das Zuruecksetzen wuerde der naechste Einsatz die Werte
        des vorigen mitschleppen.

        ts ist der Zeitstempel AUS DEM LOG, nicht die aktuelle Uhrzeit. Beim
        einmaligen Neueinlesen alter Logs wuerde sonst jeder Einsatz auf heute
        datiert."""
        self.weapons = {}
        self.targets = {}
        self.attackers = {}
        self.bounty = 0
        self.kills = 0
        self.dmg_out = self.dmg_in = 0
        self.pvp_out = self.pvp_in = 0
        self.hits_out = self.miss_out = self.miss_in = 0
        self.ewar = {}
        self.logi_out = {}
        self.logi_in = {}
        self.mission_system = None
        self.first_ts = ts if ts is not None else time.time()

    def mission_dict(self, end_ts):
        """Die gerade abgeschlossene Mission als Datensatz — oder None, wenn
        seit dem letzten Undock kein Kampf stattfand (z.B. reiner Mining-Trip).
        Ort = wo der Kampf begann (aus dem Gamelog, zuverlaessig)."""
        # Auch ein reiner Logi-Einsatz zaehlt: kein Schaden, keine Bounty,
        # trotzdem stundenlange Arbeit. Seit v1.71 hat die Tabelle Spalten
        # dafuer, vorher waere der Datensatz leer gewesen.
        if not (self.bounty or self.kills or self.dmg_out
                or self.logi_out or self.logi_in):
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
                "ewar": sorted(self.ewar.items(), key=lambda x: -x[1]),
                "logi_out": sum(self.logi_out.values()),
                "logi_in": sum(self.logi_in.values())}


def mission_hinweis(cname, md):
    """Text des Hinweises, wenn ein Einsatz von selbst abgeschlossen wurde.

    Ohne ihn saehe man nur, dass die Live-Zahlen ploetzlich auf null stehen,
    und wuesste nicht, dass sie im Verlauf gelandet sind."""
    isk = f"{round(md['bounty']):,}".replace(",", ".")
    k = md["kills"]
    return (f"{cname}: Einsatz abgeschlossen ({k} Kill{'' if k == 1 else 's'}, "
            f"{isk} ISK Kopfgeld). Loot lässt sich jetzt eintragen.")


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
                share_ore_ping()
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
                if active <= 0 and e.get("burn_on"):
                    # Kein Kompressions-Beleg, aber ESI hat echten Verbrauch
                    # gemessen: der Kern laeuft nachweislich, also die Zeit voll
                    # anrechnen statt die Anzeige einfrieren zu lassen.
                    active = max(0.0, now - e.get("ts", now))
                if active > 0:
                    e["units"] = max(0.0, e.get("units", 0.0) - active * rate)
                    e["ts"] = now
                    changed = True
                if ((s.core_on() or e.get("burn_on")) and not e.get("warned")
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
        # Rueckkehr aus dem Abyss abarbeiten, die der Chat-Thread vorgemerkt hat.
        # Hier ist der richtige Ort: dieser Thread haelt die Sperren ohnehin in
        # fester Reihenfolge, und er laeuft im selben Takt wie die Kampfzeilen.
        # Der Abyss endet nicht mit einem Andocken, sondern mit dem Ruecksprung
        # ins normale All, deshalb gaebe es sonst nie einen Abschluss.
        with chatwatch.lock:
            abyss_fertig, chatwatch.abyss_ende = chatwatch.abyss_ende, []
        for a_cid, a_ts, a_ein in abyss_fertig:
            with self.lock:
                a_sess = self.sessions.get(a_cid)
            if not a_sess:
                continue
            a_md = a_sess.mission_dict(a_ts)
            if a_md:
                # Der Durchgang beginnt mit dem EINTRITT in den Abyss, nicht
                # mit der ersten Logzeile seit dem Abdocken. Sonst zaehlt der
                # Anflug mit: gemeldet wurden 10 Minuten, obwohl die
                # Local-Uebergaenge 5:05 sagen. Im Abyss selbst laeuft eine
                # harte 20-Minuten-Grenze, die Zahl muss also stimmen.
                # Nur nach vorn korrigieren, nie nach hinten.
                if a_ein and a_ein > a_md["start_ts"]:
                    a_md["start_ts"] = a_ein
                a_md["dialog"] = " ".join(chatwatch.dialogue(
                    a_cid, a_md["start_ts"], a_ts))[:2000] or None
                save_mission(a_md)
                a_sess.reset_combat(a_ts)
                # Nur bei frischer Rueckkehr melden, nicht beim einmaligen
                # Nachlesen alter Logs: sonst prasseln beim Neuaufbau hunderte
                # Hinweise auf einmal herein.
                if time.time() - a_ts < 300 and (a_md["bounty"] or a_md["kills"]):
                    alerts.push("mission", a_sess.name,
                                mission_hinweis(a_sess.name, a_md))

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
                            #
                            # Ein von Hand abgeschlossener Lauf muss dabei
                            # erhalten bleiben. Sonst spielt der Neuaufbau alle
                            # Kampfzeilen davor erneut ein und die Mission steht
                            # wieder offen. Siehe zu_laden().
                            zu_ts = zu_laden().get(cid)
                            zu_getan = False
                            try:
                                with open(f, "rb") as fh0:
                                    head = fh0.read(offset)
                                for bline in head.split(b"\n"):
                                    ev = parse_line(bline.decode("utf-8", "replace").lstrip("﻿"))
                                    # "noise" ist verstanden, aber kein Ereignis:
                                    # sonst zoege "Please wait..." den Zeitstempel
                                    # der letzten Aktivitaet hoch und ein
                                    # angedockter Client sae aktiv aus.
                                    if ev and ev["kind"] != "noise":
                                        if zu_ts and not zu_getan and ev["ts"] >= zu_ts:
                                            sess.feed({"kind": "hold_reset", "key": "dock",
                                                       "ts": zu_ts, "char_id": cid,
                                                       "day": time.strftime(
                                                           "%Y-%m-%d", time.gmtime(zu_ts)),
                                                       "value": 1}, live=False)
                                            zu_getan = True
                                        sess.feed(ev, live=False)
                                # Abschluss NACH dem letzten eingelesenen
                                # Ereignis: dann steht er am Ende, nicht mittendrin.
                                if zu_ts and not zu_getan:
                                    sess.feed({"kind": "hold_reset", "key": "dock",
                                               "ts": zu_ts, "char_id": cid,
                                               "day": time.strftime(
                                                   "%Y-%m-%d", time.gmtime(zu_ts)),
                                               "value": 1}, live=False)
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
                drop_mid = []        # zurueckgenommene Abschluesse (Zwischenstopp)
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
                        # "noise" heisst: die Zeile ist verstanden, aber sie ist
                        # Alltagsgeplapper (Drohnenmeldungen, Modul-Deaktivierungen,
                        # Nachladen). Sie darf weder in die Datenbank noch in eine
                        # Sitzung noch in einen Alarm. Sie zaehlt nur als "erkannt",
                        # damit die Diagnose nur noch echte Unbekannte zeigt.
                        if ev and ev["kind"] == "noise":
                            continue
                        if ev:
                            batch.append(ev)
                            if sess:
                                # Geht der Kampf kurz nach dem Anflug im selben
                                # System weiter, war das Andocken kein Abschluss
                                # sondern ein Zwischenstopp, etwa zum Reparieren.
                                # Dann wird der Eintrag zurueckgeholt statt ein
                                # zweiter angelegt.
                                #
                                # FUENF Minuten, nicht zehn. Der einzige echte
                                # Reparatur-Fall in 2.142 gemessenen Anfluegen
                                # ging nach 3,2 Minuten weiter. Mit zehn
                                # Minuten verschluckte die Regel dagegen einen
                                # echten Missionswechsel im Prueflauf: dort
                                # lagen zwischen Anflug und neuem Kampf genau
                                # 600 Sekunden. Wer eine neue Mission annimmt
                                # und hinfliegt, braucht laenger als wer nur
                                # das Schild flickt.
                                if (ev["kind"] in ("dmg_out", "dmg_in", "bounty")
                                        and getattr(sess, "zuletzt_zu", None)):
                                    a_md, a_ts = sess.zuletzt_zu
                                    gleich = (a_md.get("system") in (None, "?", sess.system)
                                              or sess.system in (None, "?"))
                                    if ev["ts"] - a_ts <= 300 and gleich:
                                        sess.wieder_aufnehmen(a_md)
                                        drop_mid.append(
                                            f"{a_md['char_id']}:{int(a_md['start_ts'])}")
                                        missions_done[:] = [
                                            x for x in missions_done
                                            if x is not a_md]
                                    sess.zuletzt_zu = None
                                # Anflug zur Station beendet den Einsatz, ohne dass
                                # man erst wieder abdocken muss. Damit steht die
                                # Mission sofort in der Liste und der Loot laesst
                                # sich eintragen, solange man noch drin steht.
                                # An echten Logs geprueft: nach 53 von 53 eigenen
                                # und 1.740 von 1.743 fremden Anfluegen kam kein
                                # Kampf mehr. Die drei Ausnahmen lagen alle mehr
                                # als zwei Minuten spaeter.
                                if ev["kind"] == "travel" and ev["key"] == "dock":
                                    md = sess.mission_dict(ev["ts"])
                                    if md:
                                        md["dialog"] = " ".join(chatwatch.dialogue(
                                            cid, md["start_ts"], ev["ts"]))[:2000] or None
                                        missions_done.append(md)
                                        sess.reset_combat(ev["ts"])
                                        # Fuer eine mögliche Ruecknahme merken
                                        sess.zuletzt_zu = (md, ev["ts"])
                                        # Ohne Hinweis waere nur zu sehen, dass die
                                        # Live-Zahlen ploetzlich auf null stehen.
                                        # Der Hinweis sagt, wohin sie gewandert sind
                                        # und dass jetzt der Loot dazu passt.
                                        # Nicht beim Nachlesen alter Logs melden:
                                        # sonst prasseln beim einmaligen Neuaufbau
                                        # hunderte Hinweise auf einmal herein.
                                        if (not catch_up and now - ev["ts"] < 600
                                                and (md["bounty"] or md["kills"])):
                                            alerts.push("mission", cname,
                                                        mission_hinweis(cname, md))
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
                        # Erst die zurueckgenommenen loeschen, dann speichern:
                        # sonst schriebe ein spaeterer Abschluss denselben
                        # Eintrag neu und der geloeschte waere wieder da.
                        for mid_weg in drop_mid:
                            DB.execute("DELETE FROM missions WHERE mid=?", (mid_weg,))
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
        # char_id -> Zeitstempel des Abyss-Eintritts. Der Abyss hat eine harte
        # Zeitgrenze (20 min), danach stirbt das Schiff. Die verstrichene Zeit
        # ist damit die nuetzlichste Zahl, die sich aus dem Eintritt ableiten
        # laesst. Steht der Charakter wieder in einem echten System, fliegt der
        # Eintrag raus.
        self.abyss_seit = {}
        # Rueckkehr aus dem Abyss, vorgemerkt fuer den Log-Thread: [(char_id, ts)].
        # Der arbeitet die Liste ab und schliesst den Durchgang als Einsatz ab.
        self.abyss_ende = []
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

    def setz_ort(self, cid, roh, line):
        """Systemwechsel aus dem Local-Kanal verbuchen.

        Der Abyss hat KEIN Local. Beim Eintritt schreibt EVE deshalb einen
        Platzhalter statt eines Systemnamens ("Channel changed to Local :
        Unknown"). Erkannt wird das nicht am Wort, sondern daran, dass die
        mitgelieferte Karte den Namen nicht kennt: an 65 echten Local-Namen
        standen 64 in der Karte, nur der Platzhalter nicht. So greift es auch
        im deutschen oder russischen Client.

        Wurmloch-Systeme (J######) stehen ebenfalls nicht in der Karte, die
        sind aber echte Systeme und werden am Namensmuster durchgelassen."""
        nm = (roh or "").strip().rstrip("*").strip()
        if not nm:
            return
        if nm in sys_names() or WH_SYS_RE.match(nm):
            self.systems[cid] = nm
            # Rueckkehr aus dem Abyss: das ist das Ende des Durchgangs. Der Lauf
            # wird hier NICHT selbst abgeschlossen, sondern nur vorgemerkt. Grund
            # ist die Sperrenreihenfolge: der Log-Thread haelt beim Verarbeiten
            # seine eigene Sperre und greift dabei auf die Chat-Daten zu. Wuerde
            # dieser Thread umgekehrt nach der Log-Sperre greifen, koennten sich
            # beide gegenseitig blockieren, ausgerechnet im Moment der Rueckkehr.
            eintritt = self.abyss_seit.pop(cid, None)
            if eintritt is not None:
                # Ausstieg aus DEM ZEITSTEMPEL der Chatzeile nehmen, nicht aus
                # der Uhr: beim Nachlesen aelterer Zeilen laege die Uhr sonst
                # Minuten daneben. Und den Eintritt mitgeben, sonst ist er hier
                # weg und der Durchgang bekommt die Laenge des ganzen
                # Kampfblocks statt der Zeit im Abyss. Gemeldet von Nirahse:
                # Canary zeigte 10 Minuten, die Local-Uebergaenge sagen 5:05.
                m = CHAT_TS_RE.match(line or "")
                raus = time.time()
                if m:
                    try:
                        raus = datetime(*(int(x) for x in m.groups()),
                                        tzinfo=timezone.utc).timestamp()
                    except (ValueError, OverflowError):
                        pass
                with self.lock:
                    self.abyss_ende.append((cid, raus, eintritt))
            return
        self.systems[cid] = ABYSS_ORT
        if cid not in self.abyss_seit:
            m = CHAT_TS_RE.match(line or "")
            if m:
                try:
                    self.abyss_seit[cid] = datetime(
                        *(int(x) for x in m.groups()), tzinfo=timezone.utc).timestamp()
                except (ValueError, OverflowError):
                    self.abyss_seit[cid] = time.time()
            else:
                self.abyss_seit[cid] = time.time()

    # Harte Zeitgrenze im Abyss. Wer sie reisst, verliert das Schiff.
    ABYSS_LIMIT_MIN = 20

    def abyss_minuten(self, cid):
        """Wie lange laeuft der Abyss-Durchgang schon? None, wenn nicht drin.

        Wer im Abyss ausloggt oder stirbt, hinterlaesst einen Eintritt ohne
        Ausstieg: dann steht im Local nie wieder ein echtes System und der
        Zaehler liefe ewig weiter. Alles jenseits der Zeitgrenze plus etwas
        Luft gilt deshalb als veraltet und wird verworfen."""
        t = self.abyss_seit.get(cid)
        if t is None:
            return None
        min_ = max(0, (time.time() - t) / 60.0)
        if min_ > self.ABYSS_LIMIT_MIN + 5:
            self.abyss_seit.pop(cid, None)
            return None
        return min_

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
                    self.setz_ort(cid, msg.rsplit(":", 1)[1], line)
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
                        self.setz_ort(cid, msg.rsplit(":", 1)[1], line)
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
              "esi-industry.read_character_mining.v1 esi-planets.manage_planets.v1 "
              "esi-markets.read_character_orders.v1")
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


def extractor_total(install, expiry, cycle, qty, ab=None):
    """Extraktionsmenge eines Extractor-Programms in Einheiten.

    Nach der offiziellen EVE-Formel (developers.eveonline.com, PI-Guide):
    abklingender Grundwert mal Rausch-Oszillation, je Zyklus aufsummiert.
    Gegen CCPs eigenen Referenzvektor geprueft: qty 6965, Zyklus 1800 s,
    Dauer 171.000 s ergibt 789.314, und genau das liefert diese Funktion.

    Die Konstanten decay und noise stehen in EVE als Dogma-Attribute (1683
    und 1687) und koennten sich mit einem Patch aendern. Hier sind sie fest.

    ab: Zeitpunkt, ab dem gezaehlt wird. Ohne Angabe das ganze Programm ab
    install. Mit ab=jetzt bekommt man den RESTertrag, also das, was noch
    kommt. Genau den will man neben einem Countdown sehen, denn die
    Gesamtmenge liest sich dort faelschlich als "so viel kommt noch"."""
    if not (install and expiry and cycle and qty) or expiry <= install:
        return 0
    decay, noise = 0.012, 0.8
    bar_width = cycle / 900.0
    # Erster Zyklus, der noch KOMPLETT aussteht. Zyklus c startet bei
    # install + c*cycle, gesucht ist also das kleinste c mit Start >= ab.
    # Ein bereits angebrochener Zyklus zaehlt nicht mit, das entspricht der
    # Ganzzahl-Zyklenzahl der Originalformel.
    erst = 0 if ab is None else max(0, math.ceil((ab - install) / cycle))
    total = 0
    for c in range(erst, int((expiry - install) // cycle)):
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
        self.type_miss = {}   # type_id -> ts des letzten Fehlschlags (Negativ-Cache)
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
        # Negativ-Cache: ohne ihn kostete ein nicht aufloesbarer Typ bei JEDEM
        # Aufruf erneut bis zu 15 Sekunden Timeout, also bei jedem 2s-Tick.
        if time.time() - self.type_miss.get(tid, 0) < 600:
            return None
        try:
            req = urllib.request.Request(f"{ESI_BASE}/universe/types/{tid}/",
                                         headers={"User-Agent": ESI_UA})
            with urllib.request.urlopen(req, timeout=15) as r:
                n = json.loads(r.read()).get("name")
        except Exception:
            self.type_miss[tid] = time.time()
            return None
        if n:
            self.remember_type(tid, n)
        else:
            self.type_miss[tid] = time.time()
        return n

    def remember_type(self, tid, name):
        """Typnamen im Speicher und dauerhaft in der Datenbank ablegen."""
        self.type_cache[int(tid)] = name
        try:
            with DB_LOCK:
                DB.execute("INSERT OR REPLACE INTO type_names VALUES(?,?)", (int(tid), name))
                DB.commit()
        except Exception as e:
            log_error("CN-DB-01", "remember_type", e)

    def load_type_cache(self):
        """Beim Start die gemerkten Typnamen einlesen, damit das Wallet- und das
        Intel-Panel nicht wieder bei null anfangen."""
        try:
            with DB_LOCK:
                rows = DB.execute("SELECT type_id, name FROM type_names").fetchall()
            self.type_cache.update({int(t): n for t, n in rows if n})
        except Exception as e:
            log_error("CN-DB-01", "load_type_cache", e)

    def type_names_bulk(self, tids):
        """Mehrere Typnamen in EINEM Abruf holen (/universe/names/, bis 1000 IDs).

        Vorher loeste jede Ansicht ihre Namen einzeln auf: das Wallet-Panel
        brauchte fuer 70 Typen gemessene 15,4 Sekunden, waehrend derer die
        gesamte Antwort stand. Ein Sammelabruf kostet einen Bruchteil davon.
        Fehler sind hier ungefaehrlich: was fehlt, holt type_name spaeter
        einzeln nach, und die Anzeige faellt auf die reine Typnummer zurueck."""
        offen = [int(t) for t in {int(x) for x in tids if x}
                 if int(t) not in self.type_cache
                 and time.time() - self.type_miss.get(int(t), 0) >= 600]
        if not offen:
            return
        for i in range(0, len(offen), 1000):
            block = offen[i:i + 1000]
            try:
                req = urllib.request.Request(
                    ESI_BASE + "/universe/names/", data=json.dumps(block).encode(),
                    headers={"Content-Type": "application/json", "User-Agent": ESI_UA})
                with urllib.request.urlopen(req, timeout=20) as r:
                    gefunden = {e["id"]: e["name"] for e in json.loads(r.read())
                                if e.get("category") == "inventory_type"}
            except Exception:
                # Ein einziger unbekannter Typ laesst ESI den GANZEN Block mit 404
                # abweisen. Dann nichts merken, die Einzelabfrage klaert es spaeter.
                continue
            for tid, name in gefunden.items():
                self.remember_type(tid, name)
            for tid in block:
                if tid not in gefunden:
                    self.type_miss[tid] = time.time()

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
                        # qty_per_cycle mitnehmen, sonst laesst sich der
                        # RESTertrag spaeter nicht mehr rechnen. Der muss bei
                        # jeder Abfrage neu bestimmt werden, weil er mit der
                        # Zeit faellt, waehrend "total" konstant bleibt.
                        "qty": qty,
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
                # Wann EVE diese Kolonie zuletzt wirklich gerechnet hat. NICHT
                # dasselbe wie der Cache-Zeitstempel der ESI-Antwort: EVE
                # simuliert eine Kolonie erst, wenn sie im Client geoeffnet
                # wird. An echten Daten gemessen lag der Cache-Header bei
                # 3 Minuten, waehrend die Lagerstaende 4,5 STUNDEN alt waren.
                # Nur dieser Wert taugt als Altersangabe fuer Lager und Wert.
                "updated": _ts(col.get("last_update")),
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
            # Stueckpreis je Extraktor merken. Der Restertrag wird erst bei der
            # Abfrage gerechnet (er faellt mit der Zeit), und ohne Stueckpreis
            # muesste man ihn anteilig schaetzen statt exakt zu bewerten.
            for e in col["extractors"]:
                e["px"] = pm.get(e.get("product_id"), (0, 0))[0]
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
                ctype = core or prev.get("core", "t1")
                # HARTER BELEG statt Heuristik: Heavy Water verbraucht NUR der
                # Industriekern. Zwei aufeinanderfolgende ESI-Messungen zeigen
                # den echten Schwund, daraus folgt direkt, ob der Kern lief.
                # Gemessen wird gegen "esi_units"/"esi_ts" (die ROHEN Werte der
                # letzten Messung), nicht gegen "units": das wird zwischendurch
                # von hw_tick lokal heruntergerechnet und waere als Basis falsch.
                # Zeitbasis ist Last-Modified, nicht jetzt: ESI-Assets sind bis
                # zu eine Stunde alt, sonst waere die Spanne zu gross gemessen.
                rate = HW_RATE.get(ctype, HW_RATE["t1"])
                burn_on, burn = bool(prev.get("burn_on")), None
                used = float(prev.get("used") or 0.0)
                fill = max(float(units), float(prev.get("fill") or 0))
                p_units, p_ts = prev.get("esi_units"), prev.get("esi_ts")
                if p_units is not None and p_ts is not None:
                    span = asof - p_ts
                    drop = float(p_units) - float(units)
                    if span > 0:
                        if drop > 0:
                            # Gemessener Schwund: exakt der Verbrauch dieses
                            # Intervalls, keine Schaetzung. Summiert ergibt das
                            # den echten Verbrauch seit dem letzten Nachfuellen.
                            used += drop
                            secs = min(drop / rate, span)
                            burn = {"secs": round(secs), "span": round(span),
                                    "at": int(asof)}
                            # Mindestens die halbe Spanne verbrannt -> Kern lief
                            # durch. Weniger kann ein kurzes Anschalten sein,
                            # das reicht als Beleg nicht.
                            burn_on = secs >= 0.5 * span
                        elif drop < 0:
                            # Bestand gestiegen -> nachgefuellt. Neuer Tank,
                            # Verbrauchszaehler beginnt von vorn; ueber das
                            # Intervall selbst laesst sich nichts sagen.
                            used, fill = 0.0, float(units)
                        else:
                            burn_on = False      # unveraendert -> kein Verbrauch
                hw[name] = {"units": float(units), "fill": fill, "core": ctype,
                            "ts": time.time(), "ck": 0, "esi": True,
                            "esi_units": float(units), "esi_ts": asof,
                            "burn_on": burn_on, "burn": burn, "used": used,
                            "warned": bool(prev.get("warned")) and units <= prev.get("units", 0)}

    def value_cargo(self, name, c, items, ship_item_id, asof, nxt):
        """Frachtraum des aktiven Schiffs bewerten (Jita), fuer die Loot-Anzeige."""
        cargo = [i for i in items if i.get("location_flag") == "Cargo"
                 and i.get("location_id") == ship_item_id]
        # Behaelter im Frachtraum mitnehmen. Ihr Inhalt haengt fuer ESI nicht
        # am Schiff, sondern am Behaelter, und fiel deshalb komplett raus: eine
        # randvolle Kiste sah aus wie leerer Laderaum. Gemeldet von Dune2Man,
        # der seinen Loot immer in eine Kiste packt, weil dann mehr reingeht.
        #
        # Die Schleife deckt Kiste-in-Kiste ab. Sie laeuft hoechstens fuenf
        # Runden, damit ein widerspruechlicher Datensatz sie nicht ewig dreht.
        # Der Behaelter selbst bleibt in der Liste, der hat ja auch einen Wert,
        # und doppelt gezaehlt wird nichts: Inhalt sind eigene Eintraege.
        drin = list(cargo)
        for _ in range(5):
            ids = {i["item_id"] for i in drin if "item_id" in i}
            neu = [i for i in items
                   if i.get("location_id") in ids and i not in drin]
            if not neu:
                break
            cargo += neu
            drin = neu
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
        # Liegt ein Missionsgegenstand an Bord? Das muss ueber die VOLLE Liste
        # laufen und nicht ueber die gekuerzte Anzeige unten: ein
        # Missionsgegenstand ist nicht handelbar, steht deshalb mit 0 ISK ganz
        # am Ende und faellt aus rows[:12] praktisch immer heraus.
        fracht = detect_mission([], "", [r["name"] for r in rows])
        with CONFIG_LOCK:
            c["cargo"] = {
                "buy": round(sum(q * pm.get(t, (0, 0))[0] for t, q in qty.items())),
                "sell": round(sum(q * pm.get(t, (0, 0))[1] for t, q in qty.items())),
                "as_of": int(asof), "next": int(nxt), "mission": fracht,
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
            # Wallet Buddy: das VOLLSTAENDIGE Journal mitschreiben, ungefiltert
            # und mit Vorzeichen. Nur so sind Broker-Gebuehr und Steuer sichtbar.
            for e in data:
                ts = datetime.fromisoformat(
                    e["date"].replace("Z", "+00:00")).timestamp()
                DB.execute("INSERT OR IGNORE INTO wbook VALUES(?,?,?,?,?)",
                           (e["id"], name, ts, e.get("ref_type") or "?",
                            e.get("amount") or 0.0))
            DB.commit()
        try:
            self.sync_trades(name, c)
        except Exception as e:
            log_error("CN-ESI-01", "sync_trades", e)

    def sync_trades(self, name, c):
        """Markt-Transaktionen einlesen (Wallet Buddy).

        Braucht KEINEN neuen Scope: /wallet/transactions/ haengt am selben
        esi-wallet.read_character_wallet.v1 wie das Journal. ESI liefert die
        letzten ~1000 Ausfuehrungen, die lokale Historie waechst darueber
        hinaus, weil jede Zeile eine feste transaction_id hat."""
        data, _ = self._get(c, f"/characters/{c['char_id']}/wallet/transactions/")
        with DB_LOCK:
            for t in data:
                ts = datetime.fromisoformat(
                    t["date"].replace("Z", "+00:00")).timestamp()
                DB.execute("INSERT OR IGNORE INTO trades VALUES(?,?,?,?,?,?,?,?)",
                           (t["transaction_id"], name, ts, t["type_id"],
                            t["quantity"], t["unit_price"],
                            1 if t["is_buy"] else 0, t.get("location_id") or 0))
            DB.commit()
        # Offene Orders sind optional: sie haengen an einem ZUSAETZLICHEN Scope.
        # Fehlt er (Char noch nicht neu verbunden), bleibt der Rest nutzbar.
        try:
            orders, _ = self._get(c, f"/characters/{c['char_id']}/orders/")
            c["orders"] = [{"type_id": o["type_id"], "buy": bool(o.get("is_buy_order")),
                            "price": o["price"], "rest": o.get("volume_remain") or 0,
                            "total": o.get("volume_total") or 0,
                            "loc_id": o.get("location_id") or 0,
                            "issued": o.get("issued")} for o in orders]
            c["orders_scope"] = True
        except Exception:
            c.pop("orders", None)
            c["orders_scope"] = False

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
                # Die *_next-Marke wird erst NACH einem Erfolg gesetzt. Ohne eine
                # eigene Pause im Fehlerfall fragte Canary bei fehlendem Scope
                # alle 120 s erneut und erzeugte dauerhaft 403er bei CCP. Wie bei
                # den Planeten daher eine halbe Stunde Ruhe.
                try:
                    if time.time() >= c.get("skills_next", 0):
                        self.sync_skills(name, c)
                except Exception:
                    c.pop("skill_bonus", None)
                    c["skills_next"] = time.time() + 1800
                try:
                    if time.time() >= c.get("mining_next", 0):
                        self.sync_mining(name, c)
                except Exception:
                    c.pop("esi_mining", None)
                    c.pop("mined_30d", None)
                    c["mining_next"] = time.time() + 1800
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
        if sys.platform == "darwin":
            # pbpaste liegt auf jedem Mac. Als Liste aufgerufen, ohne Shell,
            # mit Zeitgrenze: haengt das Programm, haengt Canary nicht mit.
            # Import lokal wie beim Neustart weiter oben: subprocess steht
            # nicht oben in der Datei, und auf Windows wird der Zweig nie
            # betreten.
            import subprocess
            try:
                r = subprocess.run(["pbpaste"], capture_output=True, timeout=2)
            except (OSError, subprocess.SubprocessError):
                return None
            if r.returncode != 0:
                return None
            return r.stdout.decode("utf-8", errors="replace")
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
        while CLIPBOARD_OK:
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
                    self._resolve_ids([self._top_corp(p)])   # Name vor dem Alarm
                    if flag:
                        alerts.push("pack" if d <= 5 else "packinfo", self._label(p),
                                    f"🩸 Achtung, {flag['name']}: Rudel nähert sich, "
                                    f"{prevd} → {d} Sprünge ({sysn}). "
                                    f"{flag['miner']} Miner-Kills zuletzt.",
                                    self._logo(p, flag))
                    elif d <= 3:
                        alerts.push("pack", self._label(p),
                                    f"🩸 Rudel [{self._label(p)}] nähert sich deinem "
                                    f"System: noch {d} Sprünge ({sysn})",
                                    self._logo(p))
                    else:
                        alerts.push("packinfo", self._label(p),
                                    f"🩸 Rudel [{self._label(p)}] nähert sich: "
                                    f"{prevd} → {d} Sprünge ({sysn})",
                                    self._logo(p))

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
        # Die getroffene ID MUSS mit zurueck: das Wappen muss dieselbe Gruppe
        # zeigen, die im Text steht. Vorher nahm das Bild die haeufigste Allianz
        # des Rudels, und bei gemischten Rudeln stand dann "Goonswarm" im Text,
        # waehrend das Wappen von Shadow Cartel danebenhing.
        for aid in (p.get("allis") or {}):
            if aid in allis:
                return dict(allis[aid], art="alliance", id=aid)
        for cid in (p.get("corps") or {}):
            if cid in corps:
                return dict(corps[cid], art="corp", id=cid)
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

    def _logo(self, p, flag=None):
        """Bildpfad fuers Rudel. Ist die Gruppe gelistet, zeigt das Wappen GENAU
        die getroffene Gruppe (sonst widersprechen sich Bild und Text), sonst
        das Logo der dominanten Corp. Der Alarm-Balken ist eine eigene
        Oberflaeche, die Bilder aus der Karte tauchen dort nicht auf."""
        if flag and flag.get("id"):
            return ("alliances/" if flag.get("art") == "alliance"
                    else "corporations/") + str(flag["id"])
        c = self._top_corp(p)
        return f"corporations/{c}" if c else None

    def _top_corp(self, p):
        return max(p["corps"], key=p["corps"].get) if p["corps"] else None

    def _top_alli(self, p):
        a = p.get("allis") or {}
        return max(a, key=a.get) if a else None

    def _label(self, p):
        top = self._top_corp(p)
        nm = self.names.get(top) or (f"Corp #{top}" if top else "Unbekannt")
        return nm

    def _resolve_ids(self, ids):
        """Einzelne Namen sofort nachschlagen. Die Runden-Aufloesung haengt bis
        zu 70s im Long-Poll fest; ein Alarm, der in dieser Luecke entsteht,
        traegt sonst dauerhaft "Corp #98679090" statt des Namens, denn die
        Alarmzeile wird nie neu gezeichnet."""
        ids = [i for i in ids if isinstance(i, int) and i not in self.names]
        if not ids:
            return
        try:
            req = urllib.request.Request(
                ESI_BASE + "/universe/names/", data=json.dumps(ids[:100]).encode(),
                headers={"Content-Type": "application/json", "User-Agent": ESI_UA})
            with urllib.request.urlopen(req, timeout=10) as r:
                for x in json.loads(r.read()):
                    self.names[x["id"]] = x["name"]
        except Exception:
            pass

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
                        f"Rudel [{label}] ({n} Piloten, zuletzt aktiv vor {mins} min in {sysn})",
                        self._logo(p) if p else None)
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
                                    f"🩸 Rudel [{self._label(p)}]: Kill in der Nähe ({sysn})",
                                    self._logo(p))

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
                self._resolve_ids([self._top_corp(p)])   # Name vor dem Alarm
                mins = max(1, int((now - p["first"]) // 60))
                sysn = (self.sysrow.get(p["systems"][-1][0]) or (None, "?"))[1] \
                    if p["systems"] else "?"
                alerts.push("packinfo", self._label(p),
                            f"🩸 Rudel [{self._label(p)}] ist {d} Sprünge entfernt aktiv "
                            f"({sysn}, seit {mins} min, {len(p['members'])} Piloten)",
                            self._logo(p))

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
        # Schiffsnamen vorab in EINEM Abruf holen. Einzeln aufgeloest kostete das
        # Intel-Panel nach einem Neustart gemessene 3,9 Sekunden, weil jeder
        # unbekannte Typ eine eigene ESI-Anfrage im Antwortpfad ausloeste.
        with self.lock:
            vorab = {t for p in self.packs.values() for t in (p.get("ships") or [])}
            vorab |= {v for _, _, v, _, _ in self.recent if v}
        esi.type_names_bulk(vorab)
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
                    # IDs fuer die offiziellen Logos (images.evetech.net)
                    "corp_id": self._top_corp(p), "alli_id": self._top_alli(p),
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
esi.load_type_cache()   # gemerkte Typnamen: sonst faengt jede Ansicht bei null an
threat = ThreatIntel()
clipwatch = ClipWatch()
serverstatus = ServerStatus()
danger = SystemDanger()
packintel = PackIntel()


# ---------------------------------------------------------------- Abfragen

# ----------------------------------------------------------------- OBS-Seite
# Eigene, schlanke Seite fuer OBS als Browser-Quelle. Bewusst getrennt vom
# grossen Dashboard: hier zaehlt nur, was auf einem Stream in einer Sekunde
# lesbar ist. Alles wird ueber die Adresse gesteuert, damit in OBS niemand
# etwas einstellen oder gar programmieren muss.
#
# Der Standort ist standardmaessig AUS. Wer streamt, verraet sonst im Bild,
# wo er steht, und im Wurmloch ist das eine Einladung.
OBS_PAGE = """<!DOCTYPE html><html lang="de"><head><meta charset="utf-8">
<title>Canary OBS</title><style>
*{margin:0;box-sizing:border-box;font-family:'Bahnschrift','Segoe UI',system-ui,sans-serif}
html,body{background:transparent}
/* Ohne das gewinnt jede display-Regel gegen das hidden-Attribut, und eine
   abgeschaltete Zeile bleibt als leerer Balken im Bild stehen. */
[hidden]{display:none !important}
body{padding:6px;color:#fff;font-variant-numeric:tabular-nums}
body.grund{background:#0b0e14}
#w{display:flex;flex-direction:column;gap:5px}
body.quer #w{flex-direction:row;flex-wrap:wrap;align-items:stretch}
/* Taetigkeits-Modus: ein Kasten je Taetigkeit statt einer Zeile je Charakter. */
.tk{display:flex;align-items:center;gap:11px;padding:7px 12px;border-radius:9px;
 background:rgba(8,11,16,.78);border:1px solid rgba(255,255,255,.12);
 box-shadow:0 1px 3px rgba(0,0,0,.75)}
body.klar .tk{background:rgba(10,14,20,.55)}
body.grund .tk{background:#121722;border-color:#1e2636;box-shadow:none}
body.quer .tk{flex-direction:column;align-items:flex-start;gap:2px;min-width:150px}
.tk .kopf{font-size:11px;font-weight:700;letter-spacing:1.4px;
 text-shadow:0 1px 3px rgba(0,0,0,.95)}
.tk.k-mining .kopf{color:#7fe3ff}
.tk.k-pve .kopf{color:#f5d873}
.tk.k-pvp .kopf{color:#ff9a94}
.tk .unter{font-size:9.5px;color:#b6c2d2;text-shadow:0 1px 3px rgba(0,0,0,.9)}
.tk .zahl{margin-left:auto;text-align:right;font-size:14px;font-weight:700;
 color:#e8c645;line-height:1.2;text-shadow:0 1px 3px rgba(0,0,0,.95)}
body.quer .tk .zahl{margin-left:0;text-align:left}
.tk .zahl small{display:block;font-size:9.5px;color:#9fb0c4;font-weight:600}
.z{display:flex;align-items:center;gap:9px;padding:6px 11px;border-radius:9px;
 background:rgba(10,14,20,.62);border:1px solid rgba(255,255,255,.10);
 box-shadow:0 1px 2px rgba(0,0,0,.5)}
body.klar .z{background:rgba(10,14,20,.55)}
body.grund .z{background:#121722;border-color:#1e2636;box-shadow:none}
body.quer .z{flex-direction:column;align-items:flex-start;gap:2px;min-width:150px}
.pkt{width:9px;height:9px;border-radius:50%;flex:none}
.ok{background:#4fd47f}.warn{background:#e8c645}
.bad{background:#e8564f;animation:p .9s infinite}
@keyframes p{50%{opacity:.25}}
.nm{font-weight:700;font-size:13px;line-height:1.2;
 text-shadow:0 1px 3px rgba(0,0,0,.9)}
.sub{font-size:9.5px;color:#b6c2d2;line-height:1.35;text-shadow:0 1px 3px rgba(0,0,0,.9)}
.tag{display:inline-block;font-size:8.5px;font-weight:700;letter-spacing:.9px;
 padding:1px 5px;border-radius:4px;vertical-align:middle;margin-right:5px}
.t-mining{background:rgba(53,200,232,.22);color:#7fe3ff}
.t-pve{background:rgba(232,198,69,.22);color:#f5d873}
.t-pvp{background:rgba(232,86,79,.24);color:#ff9a94}
.wert{margin-left:auto;text-align:right;font-size:13px;font-weight:700;color:#e8c645;
 line-height:1.2;text-shadow:0 1px 3px rgba(0,0,0,.9)}
body.quer .wert{margin-left:0;text-align:left}
.wert small{display:block;font-size:9.5px;color:#9fb0c4;font-weight:600}
.st{font-size:9px;color:#e8c645;font-weight:700;letter-spacing:.5px;\n text-shadow:0 1px 3px rgba(0,0,0,.95)}
.st.bad{color:#ff8b80}\n.z.leer{opacity:.72}
#cfg{background:#0f1620;border:1px solid #22304a;border-radius:11px;padding:13px 15px;
 margin-bottom:9px;max-width:520px}
.ct{font-size:11px;letter-spacing:1.6px;text-transform:uppercase;color:#93a3bd;
 font-weight:700;margin-bottom:10px}
/* 132px zwangen "Chars hoechstens" in zwei Zeilen und machten die Reihen
   ungleich hoch. Breitere Spalten, mehr Luft dazwischen. */
.cg{display:grid;grid-template-columns:repeat(auto-fit,minmax(168px,1fr));gap:10px 16px}
.cg label{display:flex;align-items:center;gap:7px;font-size:12px;color:#c9d4e3;
 cursor:pointer;min-height:22px}
.cg select,.cg input[type=number]{background:#0b111a;color:#e6edf7;border:1px solid #22304a;
 border-radius:6px;padding:3px 6px;font:inherit;font-size:12px;width:72px}
/* Feste 72px schnitten "halb durchsichtig" mitten im Wort ab. In einer
   132px-Spalte bleibt neben der Beschriftung zu wenig uebrig, also bekommen
   die beiden Auswahlfelder eine ganze Zeile und das Feld seine Wunschbreite. */
/* Felder mit Wert bekommen eine ganze Zeile, die Haken bleiben im Raster.
   Sonst quetscht sich "Chars hoechstens" neben sein Eingabefeld und bricht um,
   was die Reihe hoeher macht als alle anderen. */
.cg label:has(select),.cg label:has(input[type=number]){grid-column:1/-1}
.cg label:has(input[type=number]) input{margin-left:auto}
.cg select{width:auto;min-width:0;max-width:100%}
.cu{display:flex;gap:7px;margin-top:11px}
.cu input{flex:1;background:#0b111a;color:#7fe3ff;border:1px solid #22304a;border-radius:7px;
 padding:7px 9px;font-family:Consolas,monospace;font-size:11.5px}
.cu button{background:#35c8e8;color:#06222a;border:none;border-radius:7px;padding:7px 14px;
 font:inherit;font-weight:700;font-size:12px;cursor:pointer}
.ch{font-size:11.5px;color:#8c99ab;margin-top:13px;line-height:1.65;
 border-top:1px solid #1b2740;padding-top:12px}
.ch b{color:#c9d4e3}
.ch ol{margin:7px 0 0 17px;padding:0}
.ch li{margin-bottom:5px}
.ch code{background:#0b111a;border:1px solid #22304a;border-radius:4px;
 padding:1px 5px;color:#7fe3ff;font-family:Consolas,monospace;font-size:11px}
.ch .warnung{color:#f5d873}
/* Im Dialog des Dashboards: kein zweiter Kasten und keine zweite
   Ueberschrift, der Dialog bringt beides schon mit. */
body.imrahmen{padding:18px 20px}
body.imrahmen #cfg{background:none;border:none;border-radius:0;padding:0;
 max-width:none;margin-bottom:16px}
body.imrahmen>#cfg>.ct{display:none}
#uhr{display:flex;align-items:center;justify-content:center;gap:9px;
 padding:5px 12px;margin-bottom:5px;border-radius:9px;
 background:rgba(8,11,16,.78);border:1px solid rgba(53,200,232,.35);
 box-shadow:0 1px 3px rgba(0,0,0,.75)}
body.klar #uhr{background:rgba(10,14,20,.55)}
body.grund #uhr{background:#121722;box-shadow:none}
#uhr b{font-size:17px;color:#35c8e8;font-variant-numeric:tabular-nums;
 text-shadow:0 1px 3px rgba(0,0,0,.95)}
#uhr span{font-size:10px;letter-spacing:1.2px;text-transform:uppercase;
 color:#9fb0c4;text-shadow:0 1px 3px rgba(0,0,0,.95)}
#uhr.pause b{color:#e8c645}
#dt{display:flex;align-items:center;justify-content:center;gap:8px;
 padding:4px 11px;margin-bottom:5px;border-radius:9px;font-size:10px;
 letter-spacing:1.2px;text-transform:uppercase;font-weight:700;
 background:rgba(232,198,69,.16);color:#f5d873;border:1px solid rgba(232,198,69,.35)}
#dt.nah{background:rgba(232,86,79,.20);color:#ff9a94;border-color:rgba(232,86,79,.45)}
#dt b{font-size:13px;letter-spacing:0}
#sum{display:flex;align-items:center;justify-content:space-between;gap:12px;
 padding:5px 11px;border-radius:9px;background:rgba(10,14,20,.62);
 border:1px solid rgba(255,255,255,.10);font-size:9px;letter-spacing:1.2px;
 color:#9fb0c4;text-transform:uppercase}
body.grund #sum{background:#121722;border-color:#1e2636}
#sum b{font-size:13px;color:#35c8e8;letter-spacing:0;text-transform:none;\n text-shadow:0 1px 3px rgba(0,0,0,.95)}
#sum i{font-style:normal;font-size:10px;color:#e8c645}
#mk{display:flex;align-items:center;gap:7px;padding:4px 10px;border-radius:9px;
 background:rgba(8,11,16,.78);border:1px solid rgba(255,255,255,.12);
 box-shadow:0 1px 3px rgba(0,0,0,.75)}
body.klar #mk{background:rgba(10,14,20,.55)}
body.grund #mk{background:#121722;border-color:#1e2636;box-shadow:none}
#mk img{width:16px;height:16px;flex:none;display:block}
#mk span{font-size:10px;font-weight:700;letter-spacing:1.7px;color:#f2d24a;
 text-shadow:0 1px 3px rgba(0,0,0,.95)}
#mk em{font-style:normal;font-size:8.5px;color:#a8b8cc;margin-left:auto;
 padding-left:10px;letter-spacing:.3px;text-shadow:0 1px 3px rgba(0,0,0,.95)}
body.quer #mk{flex:none;align-self:flex-start}
body.quer #mk em{display:none}
/* Kompakt. Nicht alles gleichmaessig kleiner, das waere nur unleserlich:
   zuerst geht die Luft raus (Innenabstaende, Luecken, Raender), und erst
   danach schrumpfen die Beschriftungen. Die grossen Zahlen bleiben fast
   unangetastet, denn genau die soll man im Stream noch lesen koennen.
   Gedacht fuer eine schmale Browser-Quelle ab etwa 300 mal 180. */
body.eng{padding:3px}
body.eng #w{gap:3px}
body.eng .z,body.eng .tk{padding:3px 7px;gap:6px;border-radius:7px}
body.eng .pkt{width:7px;height:7px}
body.eng .nm{font-size:12px}
body.eng .sub{font-size:8.5px;line-height:1.2}
body.eng .st{font-size:8px}
body.eng .tag{font-size:8px;padding:0 4px;margin-right:4px}
body.eng .wert,body.eng .tk .zahl{font-size:12.5px}
body.eng .wert small,body.eng .tk .zahl small{font-size:8.5px}
body.eng .tk .kopf{font-size:10px;letter-spacing:1.1px}
body.eng .tk .unter{font-size:8.5px}
body.eng #sum{padding:3px 7px;gap:7px;font-size:8px;border-radius:7px}
body.eng #sum b{font-size:11.5px}
body.eng #sum i{font-size:9px}
body.eng #mk{padding:2px 7px;border-radius:7px}
body.eng #mk img{width:13px;height:13px}
body.eng #mk span{font-size:8.5px;letter-spacing:1.2px}
body.eng #mk em{display:none}
body.eng #uhr{padding:3px 8px;margin-bottom:3px;border-radius:7px}
body.eng #uhr b{font-size:14px}
body.eng #uhr span{font-size:8.5px}
body.eng #dt{padding:2px 8px;margin-bottom:3px;font-size:8.5px;border-radius:7px}
body.eng #dt b{font-size:11px}
</style></head><body><div id="cfg" hidden>
<div class="ct">OBS-Einrichtung</div>
<div class="cg" id="cg"></div>
<div class="cu"><input id="url" readonly><button id="cp">Kopieren</button></div>
<div class="ch"><b>So kommt es in OBS</b>
<ol>
<li>Oben einstellen, was im Bild stehen soll. Was du aenderst, siehst du sofort
darunter.</li>
<li><b>Kopieren</b> druecken.</li>
<li>In OBS unter <b>Quellen</b> auf <b>+</b>, dann <b>Browser</b>.</li>
<li>Die Adresse in das Feld <b>URL</b> einfuegen. Breite <code>380</code>,
Hoehe <code>220</code> passen fuer senkrecht, fuer waagerecht eher
<code>900</code> mal <code>130</code>. Mit <b>Kompakt</b> reichen
<code>300</code> mal <code>180</code>.</li>
<li>Den Haken bei <b>Quelle abschalten, wenn nicht sichtbar</b> herausnehmen.
Sonst faengt das Overlay bei jedem Szenenwechsel von vorn an.</li>
</ol>
<p style="margin:9px 0 0"><b>Gut zu wissen</b></p>
<ol>
<li>Es laeuft nur auf deinem Rechner. OBS holt das Bild von
<code>localhost</code>, von aussen kommt niemand an die Adresse.</li>
<li>Der <b>Standort ist absichtlich aus</b>. Wer ihn einschaltet, verraet im
Stream, in welchem System er steht.</li>
<li>Zum Einrichten ohne laufendes EVE den Haken bei <b>Beispielwerte</b>
setzen. Eine Zeile im Bild sagt dann deutlich, dass es keine echten Zahlen
sind. <span class="warnung">Vor dem Stream wieder herausnehmen.</span></li>
<li>Jeder Charakter bekommt seine eigene Marke: <b>MINING</b>, <b>MISSION</b>
oder <b>PVP</b>. Wer foerdert, bleibt beim Erz, auch wenn er nebenbei eine
Ratte wegschiesst.</li>
<li>Steht hinter der Stundenrate ein <b>+ESI</b>, dann stecken
Missionsbelohnungen aus dem Wallet-Journal mit drin. Die Zahl stimmt, kommt
aber bis zu eine Stunde spaeter, denn so lange braucht ESI. Ohne sie waere
die Rate eines Missionsfliegers nur seine Bounty, und das ist knapp ein
Drittel des Einkommens.</li>
<li>Wirkt das Bild <b>unscharf</b>, dann zieh die Quelle nicht in der Szene
groesser. Setz stattdessen in den Eigenschaften der Browser-Quelle
<b>Breite und Hoehe</b> hoeher und dreh hier die <b>Groesse</b> auf. Dann
rendert der Browser gleich gross und es bleibt scharf.</li>
<li>Soll es <b>wenig Platz</b> wegnehmen, nimm <b>Kompakt</b>. Das raeumt
zuerst die Abstaende weg und schrumpft erst danach die Beschriftungen, die
grossen Zahlen bleiben lesbar. Wer es klein UND scharf will, kombiniert
Kompakt mit doppelter Quellengroesse und <b>Groesse 2</b>.</li>
</ol>
<p style="margin:9px 0 0">Diese Leiste erscheint nur hier. In OBS haengen
Parameter an der Adresse, dort ist sie nie zu sehen.</p></div>
</div><div id="uhr" hidden></div><div id="dt" hidden></div><div id="w"></div><div id="sum" hidden></div><div id="mk" hidden><img alt="" src="data:image/png;base64,iVBORw0KGgoAAAANSUhEUgAAADAAAAAwCAYAAABXAvmHAAAJA0lEQVR42u1ZCVCTZxqmo3ZROzu729HdlSCChoCAeCvhSALkwl7WKq3b7ro7u6PW7a7TqlPHqrVbzwqiqIgBBA8iHggi9xGhRK4kgqwiSAghd8JNwHZbfff9/xwiQl2peOzwzTzz//zfn8zzfO/7Pt+bDweH0TE6Rsfo+L8YoWkVv+GVtfyBJ9HF8KWG0jCpUcmXGrvwvjtMZmzB6zWci+WVq/7Iyaia9MIQ51xtCOBJ9Klh1a3fcyX6Cm6VdjevvCWcV9K4mFtUR+OJbrvzi+8s4JYp38O5r/kyQym/uvU7rkSXHlYqD3luxPnFjV5IPG9JTZueW6nZysmpofzP0cqp+X2YRLuZJzOpULQorLTJ95kRd13xsQOvTLUeV7wbie8IviCeMNzvYl8U/yKsUrOFe93Uw8cr61DyKyNKnnW6YByvSneSV93aFPqtfO7T+l5uSaM3r9pUh2mVEpZRNW5kilQoGsuTGVK5WKDcgpuvD/3mqw7yZL8PTemBzZ3ZrNqOLGZheyZT2JbJOmDKYG02pDP+ornEfKP+bMjrD4uQz+XfaP+RX6V7Z0QEYAEe58qMZayzJROHeqcwiu6oPkePb03zg9ZLftCby4C+PBb05VuRF2z/uzubqVNdZPLIehLVUzCqap7UsGFknOZayypeTauWXXT7d0O9U3eSTtNd9KsmyZMC6NCWRgczIYIkz3pwtaI3j3XPeJmx7+uI1Y48seLtESGPNkjhXDd1sMWK4KHewZRZZUz162lNWwzGC/NBl+wLygQPKN3lDPlfOsG1va5Qc8QD5Em+oDu/EHqyg6AnKwA6Li0EU8ocaDox69jI+bxEn8CT6uMGmxMfob/WIlyYZEiZC9pTXqBKcAdVHBXkMdOh+CsKFGx3smDbFEj7fGrtuQ0uublfOJlFKEp+bDr5LgFlrLeped9GytNf/YJbU3H1e4Kzb0wZdOUFnldJEgILEVU8FRqOusHVHU5QuH2KXUDuVkrHrFmL38w9FBJ9dB01umCbE5TvdiY/o0bc3f0R/HBwk7k7YsPWa1vXOT41AexKzS50ncTB5iRRM71aBNT7qjhi1RHx7qAQuENHBh3hT8KUuhCaUdzNw1SlCy1wya+cAwJ3/9VnZ/FXKBCjUntwGrTv8YP7a1bA/U9Wwv0da+E/EZ8q27/57IOfTd6Zt9IBXUcZWtLEGmz+zjFahI24GlPn1iFX0J6bj4XJIN2HBN53pi8GzQkaVETOLMjb6X2iMdbdoE6gguL4dGiM8IQf/r4UBYRbsDoc7q37AO5tX3O/fff68J/n+zm1XrhDdvlHCccOnDu50Wec4jjNQJKPt5C/Ee3+gPgAdKYvAt2pmSiEEEslYTwwD4yr+FC3NBikYQFQ+xYDGt4NgeZwLuhXhkHHx+Hm+rXvzx5+8Zar/4YFnD3Y3M0jnssJ8kQECPIl/6JA15UAcsX7rBHos4F8xsR7Aug+V+igT/ICzfqF0P5eMPQuD4W7K6wID4XeFex7xmUhmdVvMgKWzKCOGf7GJdEe4FRp9w021xhLK1DF08j0kX4zFRRJsx8Qzh0goB+6Li8G3UlPUBOROEGF7jUBcPd9NiIU+sJDf2xbHiJseCfY+yntvLrznHLVPwY+r4j0mq6Ko91TowAifRTHqdCR7gd9OVaiOY+iNysQTGd9ydTRWFOoWTADrqJDiTe7gOyftJbbbzPdB82E3Npfc0rkvCe3UJkpi1um+vPA5w0xtL324o23XCv3TgV18rwBxIMQgdCROh+0STSy0DUEcOVVKEC8k0I6EYHMLZRPhuRR2szExbw+jBQyZGEdPCRA+LnPq80CmtFG3iag7rAr6fs3YzzBnB1Iku+54gf6015kqlhSxt1+L93vAkX4fhFuaPnbnAxH17qNH7IWSxUsjkQnHYYAfTIK+Kz/s1tHPZeRqZNgSR9iVYl0IDYwYuclRFTudwO90NfiOARh68oT98SzW9GuFvKYPgSyt1C2/3QfplyGXAqf3IUqNHs4ldoj9sIVMl26MgNVXWiJRD5rEmlWS7QIqY50QQFOJES4E9cedLVbpk0E0T4QbYSNPO7I5uRPXSc9hscGFJD45LuwWBnOqdKdI1f+FGNSVyajvrdfkfZimnRcWgCGM95kWhBFaSdnvYp3OoM8djopQoktA2G3Rf0EZH/hHPXYhazUnkYRG588AhmSyaH5/54kTWC+huQre/vZo90mrWLMmf7QdmEu1BycAWXYeZLYY7mWIxqOUS15/yXFjsLtlO9TNk1z/ikO0976kwNHZlCxi+/4D8tKM/YHjeu4wsh62B6DoPuyH7SdnwftF+aRkeglI2Ldea3RsT0jPtON/m8440U2b00YEaLhqzngVvDYbkDUsIgtNZjoEafHPjH5DR/6vNJ2mXGK2EHNmdi7py4AY/IszGUPcgcm6qCvH3FbZOxCrPfEc9PZ2dB2bg62E172FloeS6t7bBZUaePYldpDw1p9hTDgI0PKPJkq0VuGfY9MIbAC73XJc2RdWUEIhhVBsm7imhnU8kgvhNEgmjk9kjdn+WO9eJAOhnb83eolbkO2Cmw8egmRGsyh+bdoz+zIpehw0MTWy0EiMoVsjRz+6rLtGWb8FdaVtggIKyaiWLrPx23o4tXEYgQSHZ71KIjyn4h1I7KlkOGMj1UAjRRDiGvFdCIE1EbPHLRF4H4rD8Tcbw3JufHb53JqVy5gTOi8ElRIrLilZ7KAqBtbWulOekF9jMcjLURobu1krszQwilTrnquZ6bXk0LG64Rzc/sL0CZ62gu/B623KW7m4f6feaPkzi/xaKUST/xiXoiDX3GE7/hmgWd+fxHd+JPTll6t6YFCe9OWVzuJJzFU8CW65EW74sY4vCjjWuSs8QqBR546nnAfD3L/sAnQpjJXkgVbfIcedt3YzEfbDIhOeXHI20ZZpK8jRiKHiID+lA/566wnh9UtOsKYwCuVs5ZUGzrx+H315OB3X9x/gJRFzSFE5GkwCr3ZmD4ZTNIi2aL6peyCmxSHl2GII+c4KgSeuZ14gqdODWa/lP+KEu2b7dhyZkFCzCb6GIfRMTpGx+h46cd/AeoX1FMbXGL0AAAAAElFTkSuQmCC"><span>EVE CANARY</span><em>eve-online-askend.github.io/eve-canary</em></div>
<script>
const P = new URLSearchParams(location.search);
// Steckt die Seite im Dashboard-Dialog? Dann traegt der Dialog den Rahmen.
if (window.self !== window.top) document.body.classList.add('imrahmen');
const an = (k, vor) => { const v = P.get(k); return v === null ? vor : v !== '0'; };
const ZEIG = {
  sys:    an('sys', false),      // Standort standardmaessig AUS
  ship:   an('ship', true),
  status: an('status', true),
  sum:    an('sum', true),
  warn:   an('warn', true),\n  iskh:   an('iskh', true)
};
const MAX = parseInt(P.get('max') || '0', 10) || 99;
// Zwei Ansichten: je Charakter (wie bisher) oder je Taetigkeit.
const NACH_ART = (P.get('modus') || '') === 'art';
document.getElementById('mk').hidden = !an('brand', true);
document.body.classList.toggle('grund', P.get('bg') === 'dark');
document.body.classList.toggle('klar', P.get('bg') === 'clear');
document.body.classList.toggle('quer', (P.get('dir') || 'v')[0] === 'h');
document.body.classList.toggle('eng', an('kompakt', false));
const SKALA = parseFloat(P.get('scale') || '1') || 1;
if (SKALA !== 1) document.body.style.zoom = SKALA;

const esc = (t) => String(t == null ? '' : t).replace(/[&<>"]/g,
  (c) => ({ '&': '&amp;', '<': '&lt;', '>': '&gt;', '"': '&quot;' }[c]));
const fmt = (n) => Math.round(n || 0).toLocaleString('de-DE');
const fmtM = (n) => { n = n || 0; const a = Math.abs(n);
  return a >= 1e9 ? (n / 1e9).toFixed(2) + ' Mrd'
       : a >= 1e6 ? (n / 1e6).toFixed(1) + ' M'
       : a >= 1e3 ? (n / 1e3).toFixed(1) + ' K' : String(Math.round(n)); };
const fmtC = (n) => { n = n || 0;
  return n >= 1e6 ? (n / 1e6).toFixed(2) + ' M' : n >= 1e3 ? (n / 1e3).toFixed(1) + ' K'
       : String(Math.round(n)); };

// Rolle je Charakter, aus dem, was wirklich im Log stand.
//
// Foerdern gewinnt vor Kampf. Ein Hulk schiesst zwischendurch eine Ratte weg,
// das macht ihn nicht zum Kampfschiff, und im Stream soll seine Rate stehen
// bleiben statt auf Schadenszahlen umzuspringen. Kommt ein Ganker, sagt das
// rote UNTER BESCHUSS in derselben Zeile deutlich genug Bescheid.
//
// PvP nur, wenn wirklich ein Spieler beteiligt war. Der Parser erkennt das am
// "[TICKER](Schiff)" im Kampflog, das steht bei NPCs nie, und Drohnen, Wracks
// und Tuerme sind dort schon aussortiert. Ohne diese Pruefung waere jede
// Mission ein Gefecht gegen Mitspieler.
function rolle(c) {
  if ((c.m3 || 0) > 0) return ['mining', 'MINING'];
  if (!((c.dmg_out || 0) > 0 || (c.dmg_in || 0) > 0)) return null;
  if ((c.pvp_out || 0) > 0 || (c.pvp_in || 0) > 0) return ['pvp', 'PVP'];
  if (c.mission && c.mission.name) return ['pve', 'MISSION'];
  return ['pve', 'PVE'];
}

// ISK je Stunde: Rate mal Wert je m3 dieser Sitzung. Nicht der Kontostand
// geteilt durch Zeit, denn der enthaelt auch Verkaeufe von gestern.
// Alles, was dieser Charakter in der Sitzung verdient hat: Erz und Bounty aus
// dem Log, dazu die Missionsbelohnung aus dem Wallet-Journal. Ohne die
// Belohnung sieht ein Missionsflieger nur seine Bounty, und die ist an echten
// Daten gemessen nur ein knappes Drittel des Missionseinkommens.
function gesamtIsk(c) {
  return (c.total_isk || 0) + (c.reward_session || 0);
}

function iskH(c) {
  if (!ZEIG.iskh) return 0;
  const m3 = c.m3 || 0, isk = c.ore_isk || 0, rate = c.m3h || 0;
  // Beim Foerdern bleibt es bei der gemessenen Rate mal Wert je m3. Die
  // reagiert sofort, waehrend eine Rechnung ueber die ganze Sitzungsdauer
  // erst traege nachzieht. Diese Zahl ist erprobt, die wird nicht angefasst.
  if (m3 && rate) return rate * (isk / m3);
  // Alle anderen ueber die Sitzungsdauer. Unter fuenf Minuten bleibt es aus:
  // eine einzelne Bounty geteilt durch zwei Minuten ergaebe eine Fantasiezahl,
  // die im Stream schlimmer ist als gar keine.
  const min = c.session_min || 0;
  const ges = gesamtIsk(c);
  if (min < 5 || ges <= 0) return 0;
  return ges / (min / 60);
}

// Die rechte Spalte richtet sich danach, was der Charakter gerade tut. Beim
// Foerdern zaehlt die Rate, beim Kaempfen der Schaden. Frueher stand dort
// stur die Foerderrate, sodass eine PvP-Flotte nur Nullen anzeigte.
function rechts(c) {
  const rate = c.m3h || 0, isk = gesamtIsk(c);
  const raus = c.dmg_out || 0, rein = c.dmg_in || 0;
  // Gleiche Grenze wie bei der Rolle: wer foerdert, bleibt beim Erz, auch
  // wenn er nebenbei Ratten wegschiesst.
  const kampf = (c.m3 || 0) <= 0 && (raus > 0 || rein > 0);
  const unten = [];
  if (rate > 0) {
    unten.push(fmt(rate) + ' m³/h');
    if (iskH(c)) unten.push(fmtM(iskH(c)) + '/h');
  } else if (kampf) {
    // Ohne ISK traegt der Schaden die grosse Zahl, sonst stuende sie doppelt.
    if (isk > 0 && raus > 0) unten.push(fmtC(raus) + ' Schaden');
    else if (raus > 0) unten.push('Schaden');
    if (rein > 0) unten.push(fmtC(rein) + ' rein');
    // Bis v1.95 gab es hier nie eine Stundenrate: sie wurde ausschliesslich
    // aus dem Erz gerechnet. Ein Missionsflieger sah also immer nichts.
    if (iskH(c)) unten.push(fmtM(iskH(c)) + '/h');
  }
  let gross = '';
  if (isk > 0) gross = fmtM(isk);
  else if (kampf && raus > 0) gross = fmtC(raus);
  if (!gross && !unten.length) return '';
  return '<span class="wert">' + gross
    + (unten.length ? '<small>' + unten.join(' &middot; ') + '</small>' : '')
    + '</span>';
}

function zustand(c) {
  if (c.dps_in > 0) return ['bad', 'UNTER BESCHUSS'];
  if (c.cargo_full) return ['bad', 'FRACHTRAUM VOLL'];
  const tw = c.tool_warns || [];
  if (tw.length) return ['warn', String(tw[0].tool).toUpperCase() + ' AUS'];
  if (c.drones_idle) return ['warn', 'DROHNEN OHNE ERZ'];
  return ['ok', ''];
}


// Ohne Parameter ist das hier die Einrichtung, mit Parametern das fertige
// Overlay. Eine Adresse, kein zweites Menue, und in OBS taucht die Leiste
// nie auf, weil dort immer Parameter dranhaengen.
if (!location.search) {
  const F = [
    ['dir', 'Ausrichtung', 'wahl', [['v', 'senkrecht'], ['h', 'waagerecht']]],
    ['modus', 'Aufteilung', 'wahl', [['', 'je Charakter'], ['art', 'je Tätigkeit']]],
    ['bg', 'Hintergrund', 'wahl', [['', 'halb durchsichtig'], ['clear', 'sehr dezent'], ['dark', 'voll']]],
    ['scale', 'Groesse', 'zahl', [1, 0.6, 3, 0.1]],
    ['kompakt', 'Kompakt (schmale Quelle)', 'ja', 0],
    ['max', 'Chars hoechstens', 'zahl', [0, 0, 20, 1]],
    ['status', 'Status PvE/PvP/Mining', 'ja', 1],
    ['ship', 'Schiff', 'ja', 1],
    ['iskh', 'ISK pro Stunde', 'ja', 1],
    ['sum', 'Flottensumme', 'ja', 1],
    ['warn', 'Warnungen', 'ja', 1],
    ['brand', 'Markenzeile Eve Canary', 'ja', 1],
    ['dt', 'Downtime-Countdown', 'ja', 1],
    ['uhr', 'Stoppuhr zeigen', 'ja', 1],
    ['sys', 'Standort zeigen', 'ja', 0],\n    ['idle', 'Hinweis wenn niemand fliegt', 'ja', 1],\n    ['demo', 'Beispielwerte zeigen', 'ja', 0]
  ];
  const box = document.getElementById('cg');
  box.innerHTML = F.map(([k, txt, art, v]) => {
    if (art === 'ja') return '<label><input type=checkbox data-k=' + k
      + (v ? ' checked' : '') + '> ' + txt + '</label>';
    if (art === 'wahl') return '<label>' + txt + ' <select data-k=' + k + '>'
      + v.map(([w, t]) => '<option value="' + w + '">' + t + '</option>').join('') + '</select></label>';
    return '<label>' + txt + ' <input type=number data-k=' + k + ' value=' + v[0]
      + ' min=' + v[1] + ' max=' + v[2] + ' step=' + v[3] + '></label>';
  }).join('');
  function bau() {
    const q = [];
    for (const el of box.querySelectorAll('[data-k]')) {
      const k = el.dataset.k;
      if (el.type === 'checkbox') { const vor = F.find((f) => f[0] === k)[3];
        if (el.checked !== !!vor) q.push(k + '=' + (el.checked ? 1 : 0)); }
      else if (el.value && el.value !== '0' && el.value !== '1') q.push(k + '=' + el.value);
      else if (el.tagName === 'SELECT' && el.value) q.push(k + '=' + el.value);
    }
    document.getElementById('url').value = location.origin + '/obs'
      + (q.length ? '?' + q.join('&') : '?v=1');
  }
  box.addEventListener('input', bau);
  document.getElementById('cp').onclick = async () => {
    const f = document.getElementById('url');
    try { await navigator.clipboard.writeText(f.value);
      document.getElementById('cp').textContent = 'kopiert'; }
    catch (e) { f.select(); }
    setTimeout(() => { document.getElementById('cp').textContent = 'Kopieren'; }, 1800);
  };
  document.getElementById('cfg').hidden = false;
  bau();
}

const DT_MIN = parseInt(P.get('dtwarn') || '60', 10);
function downtime() {
  const jetzt = new Date();
  const dt = new Date(Date.UTC(jetzt.getUTCFullYear(), jetzt.getUTCMonth(),
    jetzt.getUTCDate(), 11, 0, 0));
  if (dt - jetzt < 0) dt.setUTCDate(dt.getUTCDate() + 1);
  const min = Math.floor((dt - jetzt) / 60000);
  const box = document.getElementById('dt');
  if (!an('dt', true) || min > DT_MIN) { box.hidden = true; return; }
  box.hidden = false;
  box.classList.toggle('nah', min <= 15);
  const h = Math.floor(min / 60), m = min % 60;
  box.innerHTML = 'Downtime in <b>' + (h ? h + ' Std ' : '') + m + ' min</b>';
}

// Beispielwerte fuer die Einrichtung in OBS. Damit laesst sich Groesse und
// Platz einstellen, ohne dafuer ins Spiel zu muessen. Rein oertlich, es wird
// nichts geladen, und die Zeile darunter sagt deutlich, dass es Beispiele
// sind: sonst steht so etwas irgendwann versehentlich im Stream.
// session_min gehoert dazu, sonst zeigt die Vorschau die Stundenrate nicht:
// unter fuenf Minuten bleibt sie absichtlich aus. Und genau beim Einrichten
// will man sehen, wo die Zahl landet.
const DEMO = [
  { name: 'Darius Ward', active: true, system: 'J152827', ship: 'Hulk',
    m3: 297699, m3h: 294159, ore_isk: 159300000, total_isk: 159300000,
    session_min: 62, dmg_out: 0 },
  { name: 'Jessedaika Law', active: true, system: 'J152827', ship: 'Hulk',
    m3: 241113, m3h: 241113, ore_isk: 131300000, total_isk: 131300000,
    session_min: 62, dmg_out: 0 },
  // Foerdert und schiesst nebenbei Ratten weg. Muss MINING bleiben und die
  // Rate zeigen, nicht auf Schadenszahlen umspringen.
  { name: 'Lea o Connor', active: true, system: 'Vullat', ship: 'Covetor',
    m3: 209318, m3h: 209318, ore_isk: 145500000, total_isk: 145500000,
    session_min: 58, dmg_out: 6400, dmg_in: 900,
    tool_warns: [{ tool: 'Strip Miner II' }] },
  // Missionsflieger MIT Belohnung aus dem Journal, damit in der Vorschau das
  // Kuerzel +ESI auftaucht und man es beim Einrichten schon erklaert bekommt.
  { name: 'Askend', active: true, system: 'Gisleres', ship: 'Megathron',
    m3: 0, m3h: 0, ore_isk: 0, total_isk: 42800000, reward_session: 21500000,
    session_min: 95, dmg_out: 184000, dmg_in: 41000,
    mission: { name: 'Recon 2 of 3 (Mercenaries)', conf: 92 }, dps_in: 0 },
  { name: 'FivaS', active: true, system: 'Amarr', ship: 'Vexor',
    m3: 0, m3h: 0, ore_isk: 0, total_isk: 8100000, session_min: 41,
    dmg_out: 22000, dmg_in: 31000,
    pvp_out: 22000, pvp_in: 31000, dps_in: 340 }
];

/* Nach Taetigkeit zusammenfassen. Die Rolle je Charakter steht schon fest,
   hier wird nur addiert. ISK pro Stunde ist die Summe der Einzelraten, nicht
   die Gesamtsumme geteilt durch eine Laufzeit: die Charaktere fliegen
   unterschiedlich lange, eine gemeinsame Laufzeit gibt es gar nicht. */
function nachArt(chars) {
  const arten = {mining: {}, pve: {}, pvp: {}};
  for (const k of Object.keys(arten))
    arten[k] = {n: 0, isk: 0, rate: 0, m3: 0, m3h: 0, schaden: 0};
  for (const c of chars) {
    const r = rolle(c);
    if (!r) continue;
    const a = arten[r[0]];
    a.n += 1;
    a.isk += gesamtIsk(c);
    a.m3 += c.m3 || 0;
    a.m3h += c.m3h || 0;
    a.rate += iskH(c) || 0;
    a.schaden += c.dmg_out || 0;
  }
  return arten;
}

function kaesten(chars) {
  const a = nachArt(chars);
  const namen = {mining: 'MINING', pve: 'PVE', pvp: 'PVP'};
  const teile = [];
  let summe = 0, rate = 0;
  for (const k of ['mining', 'pve', 'pvp']) {
    const d = a[k];
    if (!d.n) continue;                       // leere Kaesten sind nur Hoehe
    summe += d.isk; rate += d.rate;
    const unten = [d.n + (d.n === 1 ? ' Pilot' : ' Piloten')];
    if (k === 'mining' && d.m3h) unten.push(fmt(d.m3h) + ' m³/h');
    if (k !== 'mining' && d.schaden) unten.push(fmtC(d.schaden) + ' Schaden');
    teile.push('<div class="tk k-' + k + '"><span>'
      + '<div class="kopf">' + namen[k] + '</div>'
      + '<div class="unter">' + unten.join(' &middot; ') + '</div></span>'
      + '<span class="zahl">' + fmtM(d.isk)
      + (d.rate ? '<small>' + fmtM(d.rate) + '/h</small>' : '')
      + '</span></div>');
  }
  if (teile.length > 1 && ZEIG.sum)
    teile.push('<div class="tk"><span><div class="kopf" style="color:#9fb0c4">GESAMT</div>'
      + '<div class="unter">' + chars.length
      + (chars.length === 1 ? ' Charakter' : ' Charaktere') + '</div></span>'
      + '<span class="zahl">' + fmtM(summe)
      + (rate ? '<small>' + fmtM(rate) + '/h</small>' : '') + '</span></div>');
  return teile.join('');
}

function zeigUhr(u) {
  const box = document.getElementById('uhr');
  if (!an('uhr', true) || !u || !u.an) { box.hidden = true; return; }
  box.hidden = false;
  box.classList.toggle('pause', !!u.pause);
  const h = Math.floor(u.sek / 3600), m = Math.floor(u.sek % 3600 / 60),
        k = Math.floor(u.sek % 60), zz = (n) => String(n).padStart(2, '0');
  box.innerHTML = '<b>' + (h ? h + ':' : '') + zz(m) + ':' + zz(k) + '</b>'
    + '<span>' + esc(u.label || 'Trip') + (u.pause ? ' &middot; Pause' : '') + '</span>';
}

async function tick() {
  downtime();
  if (an('demo', false)) {
    // Beispielwerte fuer die Charaktere, aber der ZUSTAND kommt echt: sonst
    // fehlt beim Einrichten die Stoppuhr, und genau dabei will man sehen, wo
    // sie landet. Geht der Abruf schief, laeuft der Demo-Modus trotzdem.
    let st = {};
    try {
      st = (await (await fetch('/data?view=live', { cache: 'no-store' })).json()).state || {};
    } catch (e) {}
    zeichne({ chars: DEMO, state: st });
    return;
  }
  let d;
  try { d = await (await fetch('/data?view=live', { cache: 'no-store' })).json(); }
  catch (e) { return; }
  zeichne(d);
}

function zeichne(d) {
  zeigUhr((d.state || {}).uhr);
  const chars = (d.chars || []).filter((c) => c.active).slice(0, MAX);
  // Niemand aktiv? Fuer OBS ist ein leeres Bild richtig, beim Einrichten
  // sieht es aber aus wie kaputt. Deshalb eine stille Bereitschaftszeile,
  // die verschwindet, sobald jemand fliegt. Mit idle=0 ganz abschaltbar.
  if (!chars.length) {
    document.getElementById('w').innerHTML = an('idle', true)
      ? '<div class="z leer"><span class="pkt warn"></span><span>'
        + '<div class="nm">Canary bereit</div>'
        + '<div class="sub">' + ((d.chars || []).length
            ? 'kein Charakter aktiv, sobald du fliegst erscheint er hier'
            : 'noch kein Charakter erkannt, EVE starten') + '</div></span></div>'
      : '';
    document.getElementById('sum').hidden = true;
    return;
  }
  if (NACH_ART) {
    document.getElementById('w').innerHTML = kaesten(chars);
    document.getElementById('sum').hidden = true;    // steckt im GESAMT-Kasten
    if (an('demo', false)) {
      document.getElementById('w').insertAdjacentHTML('beforeend',
        '<div class="z leer"><span class="pkt warn"></span><span>'
        + '<div class="sub">Beispielwerte zum Einrichten, nicht aus dem Spiel. '
        + 'Zum Beenden demo aus der Adresse entfernen.</div></span></div>');
    }
    return;
  }
  document.getElementById('w').innerHTML = chars.map((c) => {
    const [cls, txt] = zustand(c);
    const r = ZEIG.status ? rolle(c) : null;
    const unten = [];
    if (r) unten.push('<span class="tag t-' + r[0] + '">' + r[1] + '</span>');
    // Bei einer erkannten Mission steht ihr Name da, nicht nur die Rolle: das
    // ist die eine Angabe, nach der im Chat wirklich gefragt wird.
    if (r && r[1] === 'MISSION') unten.push(esc(c.mission.name));
    if (ZEIG.sys && c.system) unten.push(esc(c.system));
    if (ZEIG.ship && c.ship) unten.push(esc(c.ship));
    return '<div class="z"><span class="pkt ' + cls + '"></span><span>'
      + '<div class="nm">' + esc(c.name) + '</div>'
      + (unten.length ? '<div class="sub">' + unten.join(' &middot; ') + '</div>' : '')
      + (ZEIG.warn && txt ? '<div class="st ' + (cls === 'bad' ? 'bad' : '') + '">' + txt + '</div>' : '')
      + '</span>' + rechts(c) + '</div>';
  }).join('');

  const m3 = chars.reduce((s, c) => s + (c.m3 || 0), 0);
  const isk = chars.reduce((s, c) => s + gesamtIsk(c), 0);
  const rate = chars.reduce((s, c) => s + iskH(c), 0);
  // Steckt eine ESI-Belohnung mit drin? Dann wird die Zahl gekennzeichnet.
  // Sie ist richtig, kommt aber bis zu eine Stunde spaeter, und ohne Hinweis
  // wundert man sich im Stream ueber einen Sprung nach oben.
  const mitEsi = chars.some((c) => (c.reward_session || 0) > 0);
  if (an('demo', false)) {
    document.getElementById('w').insertAdjacentHTML('beforeend',
      '<div class="z leer"><span class="pkt warn"></span><span>'
      + '<div class="sub">Beispielwerte zum Einrichten, nicht aus dem Spiel. '
      + 'Zum Beenden demo aus der Adresse entfernen.</div></span></div>');
  }
  const box = document.getElementById('sum');
  // Frueher hing die ganze Zeile an m3 > 0. Wer Missionen flog oder PvP,
  // hatte "Flottensumme" eingeschaltet und sah trotzdem nie etwas.
  box.hidden = !(ZEIG.sum && (m3 > 0 || isk > 0));
  if (!box.hidden) {
    box.innerHTML = '<span>' + chars.length + ' Chars</span>'
      + '<span>' + (m3 > 0 ? '<b>' + fmtC(m3) + ' m³</b> ' : '')
      + '<i>' + fmtM(isk) + ' ISK</i>'
      + (rate ? ' <i>' + fmtM(rate) + '/h' + (mitEsi ? ' +ESI' : '') + '</i>' : '')
      + '</span>';
  }
}
tick();
setInterval(tick, 2000);
</script></body></html>"""

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
    pm = hub_prices_bg(str(region), tids) if tids else {}
    # Erst rechnen, wenn JEDER benoetigte Preis da ist. Mit halbem Cache stand
    # sonst kurzzeitig "Raffinieren: 0 ISK" auf dem Schirm, weil die Mineralpreise
    # noch fehlten — eine falsche Zahl ist schlimmer als eine fehlende Anzeige.
    if not tids <= set(pm):
        return None
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
        # Lieferungen mit vervielfachtem Ertrag. Bewertet wie das uebrige Erz,
        # damit die Zahl direkt mit dem Sitzungs-Ertrag vergleichbar ist.
        b_n = b_m3 = b_isk = 0
        b_alle = 0
        for erz, (anzahl, extra) in s.bonus_roh().items():
            i, v = ore_value(erz, extra, pm)
            b_n += anzahl
            b_m3 += v
            b_isk += i
        for mengen in s.ore_amounts.values():
            b_alle += sum(mengen.values())
        bonus = {"n": b_n, "von": b_alle, "m3": round(b_m3), "isk": round(b_isk),
                 "quote": round(100 * b_n / b_alle, 1) if b_alle else 0}
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
            # Zwei unabhaengige Belege, dass der Kern laeuft: eine Kompression
            # (sofort sichtbar, aber nur wenn jemand komprimiert) und gemessener
            # ESI-Verbrauch (hart, aber bis zu eine Stunde alt). Keiner von
            # beiden ist geraten. Fehlen beide, behaupten wir nichts.
            burned = bool(hw_cfg.get("burn_on"))
            on = s.core_on() or burned
            # Verbrauch seit dem letzten Nachfuellen: die Summe der gemessenen
            # ESI-Rueckgaenge (hart) plus das, was seit der letzten Messung
            # lokal dazugekommen ist. Ohne ESI gibt es keine Messung, dann
            # bleibt nur die Differenz zum gesetzten Anfangsbestand.
            e_units = hw_cfg.get("esi_units")
            if hw_cfg.get("esi") and e_units is not None:
                used = float(hw_cfg.get("used") or 0.0) + max(0.0, float(e_units) - rem)
            else:
                used = max(0.0, float(hw_cfg.get("fill") or 0) - rem)
            hw = {"units": round(rem), "core": hw_cfg.get("core", "t1"), "on": on,
                  "fill": round(hw_cfg.get("fill") or 0), "esi": bool(hw_cfg.get("esi")),
                  "min_left": round(rem / rate / 60), "used": round(used),
                  "src": "log" if s.core_on() else ("esi" if burned else None),
                  "quiet": (round(time.time() - s.core_timeline[-1][0])
                            if s.core_timeline else None),
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
            "lasers_off": [] if drone_only else s.laser_off_liste(),
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
            # Abyss laeuft gegen eine harte Zeitgrenze von 20 Minuten. Steht
            # hier eine Zahl, ist der Charakter gerade drin.
            "abyss_min": chatwatch.abyss_minuten(s.char_id),
            "danger": danger.for_system(s.system or chatwatch.systems.get(s.char_id)),
            "ores": ores, "m3": round(m3), "ore_isk": round(ore_isk),
            "bonus": bonus,
            # Flottengroesse aus den Boost-Zeilen. Nur zeigen, solange sie
            # frisch ist: ein Boost von vor einer halben Stunde sagt nichts
            # mehr ueber die Flotte von jetzt.
            "boost": (s.boost if s.boost and time.time() - s.boost["ts"] < 600
                      else None),
            # Tatsaechlicher Stillstand-Verlust dieser Session (kumuliert), zum
            # ISK/m³-Schnitt der Session bewertet.
            "lost_isk": round(s.lost_m3 * (ore_isk / m3)) if m3 > 0 else 0,
            # Pausiert der Verlustzaehler gerade? (angedockt/Warp oder kein Erz in 3 min)
            # Dann ist die Zahl eingefroren, nicht steigend -> in der UI so kennzeichnen.
            "lost_paused": bool(s.traveling) or s.last_ore_ts is None
                           or (time.time() - s.last_ore_ts) > 180,
            "m3h": round(m3 / mins * 60), "bounty": s.bounty, "kills": s.kills,
            "total_isk": round(ore_isk + s.bounty),
            # Missionsbelohnungen dieser Sitzung, aus dem Wallet-Journal. Ohne
            # sie waere jede ISK/h fuer einen Missionsflieger nur die Bounty.
            "reward_session": round(belohnung_seit(s.name, s.first_ts)),
            "dmg_out": s.dmg_out, "dmg_in": s.dmg_in,
            "pvp_out": s.pvp_out, "pvp_in": s.pvp_in,
            "dps_out": s.dps(s.win_out), "dps_in": s.dps(s.win_in),
            "depleted": s.depleted,
            "weapons": sorted(s.weapons.items(), key=lambda x: -x[1])[:6],
            # Volle Gegnerliste (bis 60), damit z. B. Abyss-Runs ohne Bounty alle
            # bekaempften Typen zeigen. enemy_types = Anzahl verschiedener Gegner,
            # die einzige ehrlich belegbare "Kill"-naehe Zahl (EVE loggt keine Tode).
            "top_targets": sorted(s.targets.items(), key=lambda x: -x[1])[:60],
            "enemy_types": len(s.targets),
            "top_attackers": sorted(s.attackers.items(), key=lambda x: -x[1])[:12],
            # Kampf und Funk aus dieser Session, dazu der Fracht-Treffer aus der
            # letzten ESI-Runde. Es gewinnt die genauere der beiden Erkennungen.
            "mission": beste_mission(
                detect_mission(sorted(s.targets.items(), key=lambda x: -x[1]),
                               " ".join(chatwatch.dialogue(s.char_id, s.first_ts))),
                ((esi_char or {}).get("cargo") or {}).get("mission"),
                fingerprint_mission(sorted(s.targets.items(), key=lambda x: -x[1]))),
            "site": detect_site(sorted(s.targets.items(), key=lambda x: -x[1])),
            "faction": faction_info(sorted(s.targets.items(), key=lambda x: -x[1])),
            "npc": chatwatch.dialogue(s.char_id, s.first_ts)[-3:],
            "hits_out": s.hits_out, "miss_out": s.miss_out, "miss_in": s.miss_in,
            "ewar": sorted(s.ewar.items(), key=lambda x: -x[1]),
            # Fernunterstuetzung. Summen je Art plus die Partner, absteigend
            # nach dem, was insgesamt zwischen euch geflossen ist.
            # Nur zeigen, solange gerade wirklich Logi geflogen wird. Erkannt
            # und gezaehlt wird immer, aber eine Karte, auf der seit Stunden
            # dieselben Reparaturzahlen stehen, sagt nichts mehr. Faellt der
            # letzte Eintrag aus dem Fenster, verschwindet der Block von selbst.
            "logi": ({"out": s.logi_out, "in": s.logi_in,
                      "unklar": s.logi_unklar,
                      "partner": sorted(
                          [{"name": n, **d} for n, d in s.logi_partner.items()],
                          key=lambda x: -(x["out"] + x["in"]))[:10]}
                     if s.logi_last and (time.time() - s.logi_last) < LOGI_FRISCH
                     else None),
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
# Regionen, fuer die gerade im Hintergrund Preise geholt werden (siehe hub_prices_bg).
BG_PRICE_RUNS = set()
BG_PRICE_LOCK = threading.Lock()
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


def hub_prices_bg(region, ids):
    """Preise ohne Wartezeit: liefert sofort, was im Cache liegt (auch wenn es
    alt ist), und holt den Rest im Hintergrund.

    Grund: esi_orderbook fragt JEDEN Typ einzeln ab, mit bis zu zehn Seiten. Fuer
    den Verwertungs-Berater sind das rund vierzig Abrufe hintereinander, gemessene
    10,4 Sekunden, in denen die gesamte Erz-Schatzkammer stand. Und weil der
    ESI-Preis-Cache nur fuenf Minuten haelt, waere das im Betrieb immer wieder
    passiert. Beim allerersten Mal kommt hier nichts zurueck, dann zeigt die
    Oberflaeche den Berater einfach noch nicht an und holt ihn beim naechsten
    Durchlauf nach."""
    with CALC_LOCK:
        e = CALC_CACHE.get(region)
        vorhanden = dict(e["prices"]) if e else {}
    frisch = bool(e) and time.time() - e["ts"] < PRICE_REFRESH and ids <= set(vorhanden)
    if not frisch:
        with BG_PRICE_LOCK:
            starten = region not in BG_PRICE_RUNS
            if starten:
                BG_PRICE_RUNS.add(region)
        if starten:
            def lauf():
                try:
                    hub_prices(region, ids, prefer_esi=True)
                except Exception as ex:
                    log_error("CN-NET-01", f"hub_prices_bg(region={region})", ex)
                finally:
                    with BG_PRICE_LOCK:
                        BG_PRICE_RUNS.discard(region)
            threading.Thread(target=lauf, daemon=True).start()
    return vorhanden


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
            # Der Cache merkt sich JE TYP, woher der Preis stammt. Ohne das bekam
            # ein Aufruf mit prefer_esi stillschweigend Fuzzwork-Werte, sobald ein
            # frueherer Aufruf denselben Typ ohne prefer_esi geholt hatte. Das ist
            # nicht dasselbe: Fuzzwork mittelt ueber die GANZE Region, ESI filtert
            # auf das Hub-System. An Tritanium sichtbar geworden, wo der regionale
            # Verkaufspreis (3,79) UNTER dem Jita-Ankaufsgebot (3,85) lag.
            quellen = e.get("src") or {}
            if not prefer_esi or all(quellen.get(t) == "esi" for t in ids):
                PRICE_SOURCE[str(region)] = ("esi" if all(quellen.get(t) == "esi" for t in ids)
                                             else "fuzzwork")
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
        alt = CALC_CACHE.get(region, {})
        merged = alt.get("prices", {})
        merged.update(result)
        # Als "esi" gilt ein Typ nur, wenn das Orderbuch BEIDE Seiten geliefert
        # hat. Wurde eine Seite aus Fuzzwork ergaenzt, ist der Eintrag gemischt
        # und darf beim naechsten prefer_esi-Aufruf nicht als frisch durchgehen.
        quellen = alt.get("src", {})
        for t in result:
            eb, es = fetched.get(t, (0.0, 0.0))
            quellen[t] = "esi" if (eb and es) else "fuzzwork"
        CALC_CACHE[region] = {"ts": time.time(), "prices": merged, "src": quellen}
        return dict(merged)


# Spalten trennen: an Tabulatoren ODER an zwei und mehr Leerzeichen. Ein
# EINZELNES Leerzeichen bleibt drin, denn manche Clients setzen es als
# Tausendertrenner ("1 234 567").
SPALTEN_RE = re.compile(r"\t+| {2,}")
# Spalten, die eine Einheit tragen, sind niemals die Stueckzahl. Ohne diese
# Pruefung las der Rechner aus einer Bergbauvermesser-Kopie, deren Tabulatoren
# unterwegs zu Leerzeichen geworden waren, "2.870    861 m3" als 2.870.861
# Einheiten: Faktor 9.404 zu viel, ohne jede Warnung.
# Das einzelne "m" (Entfernung: "2.352 m") braucht das Leerzeichen davor, sonst
# wuerde eine blosse Zahl mitgefangen.
EINHEIT_RE = re.compile(r"(m3|m³|ISK|km|%|\sm)\s*$", re.I)


def parse_calc_text(text):
    """Zeilen wie 'Compressed Veldspar<TAB>49.105' (Frachtraum-Kopie),
    'Compressed Scordite 42000' oder eine Zeile aus der Bergbauvermessung
    ('Pyroxeres II-Grade*<TAB>2.870<TAB>861 m3<TAB>69.800,00 ISK<TAB>2.352 m')
    in (Typname, Menge) uebersetzen. Genommen wird die erste Spalte OHNE
    Einheit, alles mit m3, ISK, km oder Prozent wird uebersprungen."""
    names = sorted(ORE_TYPES, key=len, reverse=True)
    items, unknown = {}, []
    for raw in (text or "").splitlines():
        line = raw.strip()
        if not line:
            continue
        low = line.lower()
        match = next((n for n in names if low.startswith(n.lower())), None)
        if not match:
            unknown.append(SPALTEN_RE.split(line)[0][:40])
            continue
        rest = SPALTEN_RE.split(line[len(match):].lstrip("*"))
        qty = 1
        for part in rest:
            sauber = STRIP_RE.sub("", part).strip()
            if not sauber or EINHEIT_RE.search(sauber):
                continue          # Volumen, Wert, Entfernung: keine Stueckzahl
            m = NUM_RE.search(sauber)
            if m and num(m.group(1)) > 0:
                qty = num(m.group(1))
                break
        items[match] = items.get(match, 0) + qty
    return items, unknown


def calc_hubs(text):
    """Belt-Auswertung, roh und komprimiert nebeneinander.

    Komprimieren ist in STUECK 1:1, der Gewinn steckt allein im Stueckvolumen.
    An 92 Tagespaaren aus echten Daten nachgemessen: alle 92 lagen bei 1:1.
    Der Faktor beim Volumen ist aber NICHT ueberall 100, 39 Sorten schrumpfen
    nur auf ein Zehntel. Deshalb wird das echte Volumen des komprimierten Typs
    genommen und nicht durch eine feste Zahl geteilt.

    26 Sorten (Eis, Mutanite, Polygypsum) haben gar keine komprimierte Form.
    Fuer die gelten weiter die Rohwerte, gekennzeichnet mit comp=False."""
    items, unknown = parse_calc_text(text)
    if not items:
        return {"ok": True, "items": [], "unknown": unknown}

    def comp_of(n):
        return ORE_TYPES.get("Compressed " + n)

    ids = {ORE_TYPES[n]["typeID"] for n in items}
    ids |= {c["typeID"] for c in (comp_of(n) for n in items) if c}

    def preis(pm, n, idx, komprimiert):
        """Preis je Stueck. Fehlt der komprimierte Preis, gilt der rohe: lieber
        die zweitbeste belegte Zahl als eine erfundene."""
        c = comp_of(n) if komprimiert else None
        if c:
            p = pm.get(c["typeID"])
            if p and p[idx]:
                return p[idx]
        return pm.get(ORE_TYPES[n]["typeID"], (0, 0))[idx]

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
                     "buy": round(sum(q * preis(pm, n, 0, False)
                                      for n, q in items.items())),
                     "sell": round(sum(q * preis(pm, n, 1, False)
                                       for n, q in items.items())),
                     "cbuy": round(sum(q * preis(pm, n, 0, True)
                                       for n, q in items.items())),
                     "csell": round(sum(q * preis(pm, n, 1, True)
                                        for n, q in items.items()))}
    rows = []
    for n, q in items.items():
        c = comp_of(n)
        vol = ORE_TYPES[n].get("volume", 0)
        cvol = c.get("volume", 0) if c else vol
        rows.append({"name": n, "qty": q,
                     "m3": round(q * vol),
                     "cm3": round(q * cvol, 1),
                     "isk": round(q * preis(jita, n, 0, False)),
                     "cisk": round(q * preis(jita, n, 0, True)),
                     "comp": bool(c)})
    rows.sort(key=lambda r: -r["cisk"])
    return {"ok": True, "items": rows, "hubs": hubs, "unknown": unknown,
            "m3": round(sum(r["m3"] for r in rows)),
            "cm3": round(sum(r["cm3"] for r in rows), 1),
            "ohne_comp": [r["name"] for r in rows if not r["comp"]]}


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


# Eine reine Zahl, nichts sonst: so sieht die Mengenspalte einer
# Frachtraum-Kopie aus. Trennzeichen sind erlaubt, ein Buchstabe nicht.
NUR_ZAHL_RE = re.compile(r"^\d[\d.,\xa0 '’]*$")
# Nur fuer Zeilen OHNE Tabulator: Menge am Zeilenende abschneiden. Kommt vor,
# wenn der Text unterwegs durch ein Feld ging, das Tabulatoren frisst.
ENDZAHL_RE = re.compile(r"\s(\d[\d.,\xa0 '’]*)$")


def parse_inventar_text(text):
    """Eine Frachtraum-Kopie in {Name: Menge} uebersetzen.

    Anders als parse_calc_text braucht das hier KEINE Item-Erkennung. Fuer eine
    Differenz genuegt der Text mit sich selbst verglichen, deshalb funktioniert
    es in jeder Client-Sprache und auch mit Items, die Canary nicht kennt.
    Ueberschriften wie "Munition und Ladungen" stoeren nicht: sie stehen in
    beiden Kopien und kuerzen sich beim Abziehen von selbst weg.

    Die Menge wird POSITIONSTREU aus der zweiten Spalte gelesen, nicht als
    "erste Zahl in der Zeile". Grund: bei einem einzelnen Modul laesst EVE die
    Mengenspalte leer, und die naechste Zahl in der Zeile waere dann das
    Meta-Level. Eine Zeile "Small Shield Booster II<TAB><TAB>Schildverstaerker
    <TAB>Modul<TAB>Mid<TAB>5<TAB>2" haette so 5 Stueck ergeben statt einem.
    Steht in Spalte zwei keine reine Zahl, gilt die erste reine Zahl weiter
    hinten, und wenn es auch die nicht gibt, ist es ein Stueck."""
    out = {}
    for raw in (text or "").splitlines():
        line = raw.rstrip()
        if not line.strip():
            continue
        if "\t" in line:
            cols = [c.strip() for c in line.split("\t")]
        else:
            # Ohne Tabulatoren: an zwei und mehr Leerzeichen trennen, ein
            # einzelnes bleibt drin (Item-Namen haben Leerzeichen).
            cols = [c.strip() for c in SPALTEN_RE.split(line.strip())]
        name = cols[0]
        if not name:
            continue
        menge = 0
        if len(cols) > 1:
            if NUR_ZAHL_RE.match(cols[1]):
                menge = num(cols[1])
            elif not cols[1]:
                # Leere Mengenspalte heisst EIN Stueck. Hier darf nicht weiter
                # hinten gesucht werden, sonst wird das Meta-Level zur Menge.
                menge = 1
            else:
                # Spalte zwei ist Text: dann hat der Nutzer die Mengenspalte
                # ausgeblendet oder verschoben, also die erste reine Zahl nehmen.
                for part in cols[1:]:
                    if NUR_ZAHL_RE.match(part):
                        menge = num(part)
                        break
        if not menge and len(cols) == 1:
            m = ENDZAHL_RE.search(name)
            if m:
                name, menge = name[:m.start()].strip(), num(m.group(1))
        if not name:
            continue
        out[name] = out.get(name, 0) + (menge or 1)
    return out


def cargo_diff(vorher, nachher):
    """Zwei Frachtraum-Kopien vergleichen: was ist dazugekommen, was ist weg.

    Rein oertliche Rechnerei, kein Netz. Der Text unter "plus_text" ist so
    gebaut, dass calc_loot ihn wieder lesen kann (Name, Tabulator, Menge),
    damit er direkt in das Loot-Feld einer Mission passt."""
    a, b = parse_inventar_text(vorher), parse_inventar_text(nachher)
    plus, minus = [], []
    for name in set(a) | set(b):
        vor, nach = a.get(name, 0), b.get(name, 0)
        d = nach - vor
        if d:
            zeile = {"name": name, "vor": vor, "nach": nach, "qty": abs(d)}
            (plus if d > 0 else minus).append(zeile)

    def zahl(x):
        return str(int(x)) if float(x).is_integer() else str(x)

    for liste in (plus, minus):
        liste.sort(key=lambda r: (-r["qty"], r["name"].lower()))
    return {"ok": True, "plus": plus, "minus": minus,
            "gleich": len(set(a) & set(b)) - len([r for r in plus + minus
                                                  if r["vor"] and r["nach"]]),
            "plus_text": "\n".join(r["name"] + "\t" + zahl(r["qty"]) for r in plus),
            "minus_text": "\n".join(r["name"] + "\t" + zahl(r["qty"]) for r in minus)}


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
            "tool_warn_delay": int(CONFIG.get("tool_warn_delay", 0) or 0),
            "laser_off_mode": str(CONFIG.get("laser_off_mode", "rate") or "rate"),
            "clip_watch": bool(CONFIG.get("clip_watch")),
            "count_me": bool(CONFIG.get("count_me", True)),
            "share_ore": bool(CONFIG.get("share_ore", False)),
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
            # Handgesetzte Stoppuhr. Dashboard und Overlay lesen denselben
            # Wert, damit im Stream nicht zwei verschiedene Zeiten stehen.
            "uhr": uhr_json(),
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
                      char_id,ewar,logi_out,logi_in,label
               FROM missions ORDER BY start_ts DESC LIMIT ?""", (limit * 5,)).fetchall()
        # Verifizierte Missions-Belohnungen aus dem Wallet-Journal (Server-Wahrheit).
        # Jede wird gleich der Mission zugeordnet, die kurz davor endete.
        jrows = DB.execute(
            "SELECT char, ts, ref_type, amount FROM journal "
            "WHERE ref_type LIKE 'agent_mission%'").fetchall()
    # (mid, char, start, end) je Missionszeile fuer die Zuordnung unten.
    cand = [(x[0], x[1], x[2] or 0, x[3] or 0) for x in rows]
    verified = {}
    # Belohnungen, zu denen es keine Mission gibt. Die entstehen bei Auftraegen
    # ganz OHNE Kampf (Kurier, Transport, reine Dialog-Missionen, viele Schritte
    # der Epic Arcs): im Gamelog steht dann nichts, also kennt Canary die Mission
    # nicht. An echten Daten gemessen lagen solche Buchungen 11 bis 23 Stunden von
    # jeder erfassten Mission entfernt, eine groessere Zeittoleranz wuerde davon
    # KEINE EINZIGE retten. Statt sie stumm zu verschlucken, werden sie unten
    # ausgewiesen: dann sieht man, dass die ISK da sind und nur kein Kampf dazu.
    offen = []
    for jchar, jts, jref, jamt in jrows:
        best_mid, best_gap = None, None
        for mid_, mchar, mst, met in cand:
            if mchar != jchar or jts < mst - 300:
                continue
            gap = jts - (met or mst)           # Belohnung faellt nach Kampfende
            if -300 <= gap <= 3600 and (best_gap is None or abs(gap) < best_gap):
                best_gap, best_mid = abs(gap), mid_
        if best_mid is None:
            offen.append({"char": jchar, "ts": int(jts), "isk": jamt or 0})
            continue
        v = verified.setdefault(best_mid, {"reward": 0, "bonus": 0})
        if jref == "agent_mission_reward":
            v["reward"] += jamt or 0
        else:
            v["bonus"] += jamt or 0
    # Buchungen desselben Augenblicks zusammenfassen (Belohnung + Zeitbonus).
    zus = {}
    for o in offen:
        k = (o["char"], o["ts"])
        zus[k] = zus.get(k, 0) + o["isk"]
    ohne_mission = sorted(({"char": c, "ts": t, "isk": round(i)}
                           for (c, t), i in zus.items()), key=lambda x: -x["ts"])[:10]
    ohne_summe = round(sum(o["isk"] for o in offen))
    out = []
    for r in rows:
        if len(out) >= limit:
            break
        (mid, char, st, et, sysn, do, di, kills, bounty, hits, mo, mi,
         wj, ej, loot, loot_text, dialog, char_id, ewj, lo, li, label) = r
        shots = (hits or 0) + (mo or 0)
        enemies = json.loads(ej or "[]")
        # Fehlt der gespeicherte Funk (aeltere Mission, oder Reingest lief vor dem
        # Chat-Watcher), aus dem heute im Speicher gehaltenen NPC-Funk nachfuellen.
        if not dialog and char_id:
            dialog = " ".join(chatwatch.dialogue(str(char_id), st or 0, et or None))[:2000]
        # Der eingefuegte Frachtraum-Text dieser Mission ist die dritte Quelle.
        # Er ist an die einzelne Mission gebunden und damit sauberer als die
        # laufende Fracht, die bis zur Abgabe an Bord bleibt.
        # Selbst benannt schlaegt alles: das ist keine Erkennung mehr, das weisst
        # du. Sonst der Fingerabdruck als vierte Quelle, aber nur wenn keine
        # eindeutige Signatur greift, denn er misst nur Aehnlichkeit.
        mission = (({"name": label.strip(), "conf": 100, "selbst": True}
                    if (label or "").strip() else None)
                   or beste_mission(
                       detect_mission(enemies, dialog or "", loot_namen(loot_text)),
                       fingerprint_mission(enemies)))
        site = detect_site(enemies)
        # Belt-Ratten raus: eine echte Mission ist entweder erkannt, oder hat
        # spuerbaren eigenen Schaden (>5000), oder echte Bounty (>100k). Reine
        # Flotten-Bounty beim Mining (winziger/kein Schaden, Kleinst-Bounty von
        # Guertel-Ratten) faellt hier raus, das ist keine Mission.
        # Ein Logi-Einsatz hat naturgemaess weder Schaden noch Bounty. Ohne
        # diese Ausnahme faellt er hier raus und waere trotz Speicherung
        # unsichtbar.
        # Ein erkannter Ort (Abyss) zaehlt wie eine erkannte Mission: dort gibt
        # es gar keine Bounty, der Einsatz waere sonst nur ueber den Schaden
        # drin und bei einem kurzen Lauf auch der zu klein.
        if (not mission and not site and (do or 0) < 5000 and (bounty or 0) < 100000
                and not (lo or 0) and not (li or 0)):
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
            "mission": mission, "site": site, "npc": dlines,
            "faction": faction_info(enemies),
            "ewar": json.loads(ewj or "[]"),
            "logi_out": round(lo or 0), "logi_in": round(li or 0),
            "reward": vreward, "bonus": vbonus,
            "weapons": json.loads(wj or "[]"), "enemies": enemies,
            "loot_isk": round(loot) if loot else None, "loot_text": loot_text or "",
            "label": (label or "").strip(),
            # Fuer die beiden Auswahlfelder im Abyss: ist das ueberhaupt ein
            # Durchgang, und verraet ein Gegner die Stufe? Letzteres ist exakt,
            # aber selten: an 1.843 Logdateien gemessen fehlt das Signal in
            # mindestens vier von fuenf Durchgaengen.
            "abyss": ist_abyss(sysn, enemies),
            "tier_gegner": abyss_tier_aus_gegnern(enemies),
            # Was schon im selbst vergebenen Namen steht, damit die Auswahl-
            # felder vorbelegt sind. Ausgewertet wird derselbe Code wie im
            # Export, es kann also nicht auseinanderlaufen.
            "tier_name": abyss_tier_aus_name(label),
            "wetter": abyss_wetter_aus_name(label),
            "total": round((bounty or 0) + (loot or 0) + (vreward or 0) + (vbonus or 0))})
    return out, {"liste": ohne_mission, "summe": ohne_summe, "n": len(offen)}


def uhr_sichern():
    try:
        with DB_LOCK:
            DB.execute("INSERT OR REPLACE INTO meta VALUES('uhr',?)",
                       (json.dumps(UHR),))
            DB.commit()
    except Exception as e:
        log_error("CN-DB-01", "uhr_sichern", e)


def uhr_laden():
    try:
        with DB_LOCK:
            r = DB.execute("SELECT value FROM meta WHERE key='uhr'").fetchone()
        if r:
            UHR.update(json.loads(r[0]))
    except Exception as e:
        log_error("CN-DB-01", "uhr_laden", e)


# Die Momentaufnahme von m3 und ISK kommt aus der Oberflaeche mit. Beide werden
# in der Live-Ansicht gerechnet und liegen nicht auf der Sitzung; sie hier ein
# zweites Mal auszurechnen hiesse, zwei Rechenwege zu pflegen, die
# auseinanderlaufen koennen. Die Oberflaeche zeigt die Summen ohnehin an.


# ------------------------------------------------- EVE-Einstellungen (ALPHA)
# Fehlercodes siehe ERROR_HELP, Praefix CN-SET.
SET_BACKUP = "settings_backups"


def eve_settings_dirs():
    """Alle Einstellungsordner von EVE finden, neueste zuerst.

    Windows legt sie unter LOCALAPPDATA ab, macOS unter Application Support,
    Linux im Wine-Praefix neben den Logs. Es kann mehrere geben: pro Server
    (Tranquility, Singularity) und pro Profil (settings_Default und eigene).
    """
    kandidaten = []
    if os.name == "nt":
        basis = Path(os.environ.get("LOCALAPPDATA", "")) / "CCP" / "EVE"
        kandidaten.append(basis)
    elif sys.platform == "darwin":
        kandidaten.append(Path.home() / "Library" / "Application Support"
                          / "CCP" / "EVE")
    else:
        # Linux: EVE laeuft im Praefix, die Einstellungen liegen dort im
        # Benutzerprofil. Der Logordner ist bekannt, von dort aus hochlaufen.
        p = Path(CONFIG.get("log_dir") or "")
        for eltern in list(p.parents)[:6]:
            k = eltern / "AppData" / "Local" / "CCP" / "EVE"
            if k.is_dir():
                kandidaten.append(k)
    gefunden = []
    for basis in kandidaten:
        if not basis.is_dir():
            continue
        try:
            for ordner in basis.rglob("settings*"):
                if ordner.is_dir() and any(ordner.glob("core_*.dat")):
                    gefunden.append(ordner)
        except Exception as e:
            log_error("CN-SET-01", "eve_settings_dirs", e)
    gefunden.sort(key=lambda p: p.stat().st_mtime, reverse=True)
    return gefunden


def char_namen():
    """char_id -> Name, aus allem was Canary schon weiss."""
    namen = {}
    try:
        with DB_LOCK:
            for cid, name in DB.execute(
                    "SELECT DISTINCT char_id, char FROM missions "
                    "WHERE char_id IS NOT NULL AND char IS NOT NULL"):
                namen[str(cid)] = name
            for cid, name in DB.execute(
                    "SELECT DISTINCT char_id, char FROM events "
                    "WHERE char_id IS NOT NULL AND char IS NOT NULL"):
                namen.setdefault(str(cid), name)
    except Exception as e:
        log_error("CN-DB-01", "char_namen", e)
    for sess in list(ingest.sessions.values()):
        if getattr(sess, "char_id", None):
            namen[str(sess.char_id)] = sess.name
    return namen


def eve_laeuft():
    """Laeuft der EVE-Client gerade?

    Wichtig, denn der Client schreibt seine Einstellungen beim BEENDEN. Wer
    waehrend einer laufenden Sitzung zurueckspielt, dessen Arbeit ist beim
    naechsten Ausloggen wieder weg. Lieber verweigern als still verlieren.
    """
    import subprocess
    namen = ("exefile.exe",) if os.name == "nt" else ("exefile.exe", "eve")
    try:
        if os.name == "nt":
            r = subprocess.run(["tasklist", "/FO", "CSV", "/NH"],
                               capture_output=True, timeout=8)
            text = r.stdout.decode("utf-8", errors="replace").lower()
        else:
            r = subprocess.run(["ps", "-eo", "comm"], capture_output=True, timeout=8)
            text = r.stdout.decode("utf-8", errors="replace").lower()
    except Exception:
        return None                      # unbekannt, dann nicht behaupten
    return any(n.lower() in text for n in namen)


def set_dateien(ordner):
    """Die Einstellungsdateien eines Ordners, mit Namen wo bekannt."""
    namen = char_namen()
    raus = []
    for p in sorted(Path(ordner).glob("core_*.dat")):
        teile = p.stem.split("_")
        art = teile[1] if len(teile) > 1 else "?"
        kennung = teile[2] if len(teile) > 2 else ""
        # core_char__.dat und core_user__.dat sind leere Platzhalter von EVE
        if not kennung:
            continue
        raus.append({"datei": p.name, "art": art, "id": kennung,
                     "name": namen.get(kennung) or "",
                     "kb": round(p.stat().st_size / 1024, 1),
                     "stand": int(p.stat().st_mtime)})
    return raus


def set_sicherungen():
    """Sicherungen mit ihrem Inhalt, damit man einzelne Charaktere
    heraussuchen kann statt immer alles einspielen zu muessen."""
    import zipfile
    ziel = APP_DIR / SET_BACKUP
    if not ziel.is_dir():
        return []
    namen = char_namen()
    raus = []
    for p in sorted(ziel.glob("*.zip"), reverse=True):
        inhalt = []
        try:
            with zipfile.ZipFile(p) as z:
                for e in sorted(z.namelist()):
                    if e == "_herkunft.txt" or "/" in e or "\\" in e:
                        continue
                    teile = e.rsplit(".", 1)[0].split("_")
                    art = teile[1] if len(teile) > 1 and e.startswith("core_") else "sonst"
                    kennung = teile[2] if len(teile) > 2 else ""
                    if e.startswith("core_") and not kennung:
                        continue          # leere Platzhalter von EVE
                    inhalt.append({"datei": e, "art": art, "id": kennung,
                                   "name": namen.get(kennung) or ""})
        except Exception as e:
            log_error("CN-SET-01", "set_sicherungen", e)
        raus.append({"datei": p.name, "kb": round(p.stat().st_size / 1024, 1),
                     "stand": int(p.stat().st_mtime), "inhalt": inhalt})
    return raus


def set_sichern(ordner, grund=""):
    """Den ganzen Einstellungsordner als ZIP wegschreiben."""
    import zipfile
    q = Path(ordner)
    ziel = APP_DIR / SET_BACKUP
    ziel.mkdir(parents=True, exist_ok=True)
    stempel = time.strftime("%Y%m%d-%H%M%S")
    kurz = re.sub(r"[^\w.-]", "_", grund)[:24]
    name = "eve-settings-%s%s.zip" % (stempel, ("-" + kurz) if kurz else "")
    p = ziel / name
    with zipfile.ZipFile(p, "w", zipfile.ZIP_DEFLATED) as z:
        # ALLE Dateien, nicht nur die .dat: daneben liegen prefs.ini mit den
        # Grafikeinstellungen und core_public__.yaml. Wer nach einem Absturz
        # alles zurueckhaben will, meint auch die.
        for f in sorted(q.iterdir()):
            if f.is_file():
                z.write(f, f.name)
        # Woher es kam, mit hineinschreiben. Sonst weiss man beim
        # Zurueckspielen nicht mehr, zu welchem Profil es gehoert.
        z.writestr("_herkunft.txt", str(q) + "\n" + time.strftime("%Y-%m-%d %H:%M:%S"))
    return {"datei": name, "kb": round(p.stat().st_size / 1024, 1),
            "dateien": sum(1 for f in q.iterdir() if f.is_file())}


def query_uhr_liste(n=20):
    with DB_LOCK:
        rows = DB.execute(
            "SELECT id,label,start_ts,end_ts,sek,m3,isk,unsicher FROM uhr "
            "ORDER BY end_ts DESC LIMIT ?", (n,)).fetchall()
    return [{"id": r[0], "label": r[1] or "", "start": int(r[2] or 0),
             "end": int(r[3] or 0), "sek": int(r[4] or 0),
             "m3": round(r[5] or 0), "isk": round(r[6] or 0),
             "unsicher": bool(r[7])} for r in rows]


def uhr_json():
    return {"an": UHR["an"], "pause": UHR["pause"], "label": UHR["label"],
            "sek": round(uhr_laufzeit())}


def query_loot_tage(tage=30):
    """Tagessummen je Charakter: Runs, Bounty, Loot, Agenten-Belohnungen.

    Herkunft der drei Zahlen ist bewusst verschieden, und das steht auch so in
    der Oberflaeche: Bounty kommt aus dem Gamelog, die Belohnung aus dem
    Wallet-Journal, der Loot ist von Hand eingetragen. EVE schreibt beim
    Pluendern nichts mit, es gibt keine Datei, aus der sich das lesen liesse.

    Der Tag ist EVE-Zeit (UTC), wie ueberall sonst in Canary. Ein Run zaehlt zu
    dem Tag, an dem er begonnen hat, nicht an dem er endete: sonst rutschte ein
    Run ueber Mitternacht in den Folgetag, obwohl man ihn am Vorabend geflogen
    ist.

    Die Belohnungen kommen hier direkt aus dem Journal und NICHT ueber die
    Zuordnung aus query_mission_history. Fuer eine Tagessumme braucht es die
    gar nicht, und ohne sie zaehlen auch die Auftraege mit, zu denen es keinen
    Kampf gab (Kurier, Transport), die dort bewusst herausfallen."""
    cut = time.time() - tage * 86400
    with DB_LOCK:
        mrows = DB.execute(
            "SELECT char, start_ts, bounty, loot_isk FROM missions "
            "WHERE start_ts>=?", (cut,)).fetchall()
        jrows = DB.execute(
            "SELECT char, ts, ref_type, amount FROM journal "
            "WHERE ref_type LIKE 'agent_mission%' AND ts>=?", (cut,)).fetchall()

    def tag(ts):
        return time.strftime("%Y-%m-%d", time.gmtime(ts or 0))

    per = {}

    def eintrag(char, ts):
        k = (tag(ts), char or "?")
        return per.setdefault(k, {"tag": k[0], "char": k[1], "runs": 0,
                                  "bounty": 0.0, "loot": 0.0, "reward": 0.0,
                                  "bonus": 0.0, "mit_loot": 0})

    for char, st, bounty, loot in mrows:
        e = eintrag(char, st)
        e["runs"] += 1
        e["bounty"] += bounty or 0
        if loot:
            e["loot"] += loot
            e["mit_loot"] += 1
    for char, ts, ref, amt in jrows:
        # Belohnung und Zeitbonus getrennt, so wie es die alte Karte auch tat.
        e = eintrag(char, ts)
        e["reward" if ref == "agent_mission_reward" else "bonus"] += amt or 0

    out = []
    for e in per.values():
        e["total"] = round(e["bounty"] + e["loot"] + e["reward"] + e["bonus"])
        for k in ("bounty", "loot", "reward", "bonus"):
            e[k] = round(e[k])
        out.append(e)
    # Neueste zuerst, innerhalb eines Tages der ertragreichste Charakter oben.
    out.sort(key=lambda x: (x["tag"], x["total"]), reverse=True)
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
                      enemies, ewar, loot_text, label FROM missions
               WHERE start_ts>=?""", (cut,)).fetchall()
        erows = DB.execute(
            "SELECT char, ts, detail FROM events WHERE ts>=? AND kind='mine'", (cut,)).fetchall()
        jrows = DB.execute(
            "SELECT char, ts, ref_type, amount, party FROM journal WHERE ts>=? "
            "AND ref_type LIKE 'agent_mission%'", (cut,)).fetchall()

    for char, st, et, sysn, kills, bounty, do, di, ej, ewj, lt, lbl in mrows:
        enemies = json.loads(ej or "[]")
        # Loot-Text und Benennung mit auswerten, sonst zeigt der Verlauf "keine
        # Mission", waehrend die Missions-Historie dieselbe Mission erkennt.
        mission = (({"name": lbl.strip(), "conf": 100, "selbst": True}
                    if (lbl or "").strip() else None)
                   or beste_mission(detect_mission(enemies, "", loot_namen(lt)),
                                    fingerprint_mission(enemies)))
        site = detect_site(enemies)
        # Belt-Ratten raus, wie in der Missions-Historie
        if not mission and not site and (do or 0) < 5000 and (bounty or 0) < 100000:
            continue
        add(char, {"ts": int(st or 0), "kind": "combat",
                   "mission": mission, "site": site, "faction": faction_info(enemies),
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
                                 sorted(s.targets.items(), key=lambda x: -x[1]), ""),
                             "site": detect_site(
                                 sorted(s.targets.items(), key=lambda x: -x[1]))})
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
    aktiv = {c for c in raws if any(raws[c][k] for k in order)}
    # Auch per ESI verbundene Charaktere zeigen, die in 30 Tagen nichts
    # Messbares getan haben. Vorher fielen die kommentarlos raus: wer mit
    # sieben Chars unterwegs war und sechs sah, suchte den Fehler bei sich und
    # vermutete eine Obergrenze. Es gibt keine. Betrifft alle, die nicht
    # foerdern, schiessen oder komprimieren, also Transporter, Spaeher und
    # Booster ohne Kompression. Gemeldet von Vile Gangster.
    zeigen = sorted(aktiv | set(echars))
    threat.request(zeigen)     # loest Corp/Allianz/Sec fuer die eigenen Chars auf (gecacht)
    out = []
    for c in zeigen:
        raw = raws.get(c) or {k: 0 for k in order}
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
                    "leer": c not in aktiv,
                    "poll_ts": ec.get("poll_ts")})
    out.sort(key=lambda x: x["char"])
    return out


# Journal-Posten, die im Wallet Buddy als Einnahme-/Ausgabe-Kategorie
# zusammengefasst werden. Alles nicht Genannte landet unter "sonstiges".
WB_GROUPS = {
    "handel": ("market_transaction",),
    "gebuehren": ("brokers_fee", "transaction_tax", "market_provider_tax",
                  "market_fine_paid", "cspa"),
    "bounty": ("bounty_prizes", "bounty_prize", "agent_mission_reward",
               "agent_mission_time_bonus_reward"),
    "industrie": ("industry_job_tax", "reprocessing_tax", "manufacturing", "copying"),
    "planeten": ("planetary_import_tax", "planetary_export_tax",
                 "planetary_construction"),
    "vertraege": ("contract_price", "contract_reward", "contract_brokers_fee",
                  "contract_sales_tax", "contract_deposit",
                  "contract_price_payment_corp", "contract_reward_deposited"),
    "geschenke": ("player_donation", "corporation_account_withdrawal"),
    "skills": ("skill_purchase",),
    "versicherung": ("insurance",),
    # Nachgetragen, weil diese Arten in einem echten Wallet zusammen 450 Mio ISK
    # ausmachten und unbenannt unter "sonstiges" verschwanden. Aufgenommen ist
    # nur, was belegt ist: flux_ticket_sale gehoert laut CCPs eigener
    # ref_type-Liste zur Hypernet-Gruppe, der Rest ist aus dem Namen eindeutig.
    # Was nicht belegt ist, bleibt bewusst bei "sonstiges" stehen.
    "hypernet": ("flux_ticket_sale",),
    "reparatur": ("repair_bill",),
    "klone": ("jump_clone_activation_fee", "jump_clone_installation_fee"),
    "belohnungen": ("project_payouts", "daily_goal_payouts",
                    "campaign_objective_isk_reward", "air_career_program_reward"),
    "direkthandel": ("player_trading",),
}
# NICHT in die Einnahmen-/Ausgaben-Rechnung: market_escrow ist kein Verlust,
# sondern nur Geld, das fuer offene Kauforders geparkt wird und zurueckkommt,
# sobald die Order zieht oder storniert wird. Ohne diese Ausnahme sieht jedes
# Wallet eines Traders nach einer Katastrophe aus (hier: -2,0 Mrd).
WB_IGNORE = ("market_escrow", "contract_deposit_refund", "market_escrow_refund")


def query_wallet(days=30):
    """Wallet Buddy: vollstaendige Wallet-Analyse mit Schwerpunkt Handel.

    Handelsgewinn wird per FIFO gerechnet: jeder Verkauf wird gegen die
    aeltesten noch offenen Kaeufe desselben Typs verrechnet. Das ist die
    uebliche Methode und die einzige, die ohne Zusatzangaben auskommt.

    WICHTIG und bewusst getrennt: Typen, die nur GEKAUFT und nie verkauft
    wurden, sind meist Eigenbedarf (das eigene Schiff, Module, Munition) und
    keine Handelsware. Sie wuerden die Bilanz sonst voellig verzerren, ein
    gekaufter Hulk sieht sonst aus wie ein Verlust von 200 Mio. Deshalb weist
    Canary den Handelsgewinn NUR ueber echte Rundlaeufe aus und listet den
    Rest getrennt als Bestand.

    days=0 heisst "alles, was in der Datenbank steht"."""
    seit = (time.time() - days * 86400) if days else 0
    with DB_LOCK:
        tx = DB.execute("SELECT char, ts, type_id, qty, price, is_buy, loc_id "
                        "FROM trades WHERE ts>=? ORDER BY ts", (seit,)).fetchall()
        jr = DB.execute("SELECT ref_type, SUM(amount), COUNT(*) FROM wbook "
                        "WHERE ts>=? GROUP BY ref_type", (seit,)).fetchall()
        # Fuer die Bilanz: Ein- und Ausgaben je Art getrennt. Eine Art kann
        # beides haben (Spenden gehen hin UND her), eine Summe allein wuerde
        # das verschlucken.
        jr_vz = DB.execute(
            "SELECT ref_type, SUM(CASE WHEN amount>0 THEN amount ELSE 0 END), "
            "SUM(CASE WHEN amount<0 THEN amount ELSE 0 END), COUNT(*) "
            "FROM wbook WHERE ts>=? GROUP BY ref_type", (seit,)).fetchall()
        zeitraum = DB.execute("SELECT MIN(ts), MAX(ts) FROM wbook WHERE ts>=?",
                              (seit,)).fetchone()
    gekauft = {t[2] for t in tx if t[5]}
    verkauft = {t[2] for t in tx if not t[5]}
    rund = gekauft & verkauft            # nur diese gelten als Handel

    lager = {}                            # type_id -> [[menge, preis], ...]
    stat = {}                             # type_id -> Kennzahlen
    for _, ts, tid, qty, price, is_buy, _loc in tx:
        s = stat.setdefault(tid, {"kauf_st": 0, "kauf_isk": 0.0, "verk_st": 0,
                                  "verk_isk": 0.0, "gewinn": 0.0, "matched": 0,
                                  "letzte": 0.0})
        s["letzte"] = max(s["letzte"], ts)
        if is_buy:
            lager.setdefault(tid, []).append([qty, price])
            s["kauf_st"] += qty
            s["kauf_isk"] += qty * price
        else:
            s["verk_st"] += qty
            s["verk_isk"] += qty * price
            rest = qty
            while rest > 0 and lager.get(tid):
                los = lager[tid][0]
                n = min(rest, los[0])
                s["gewinn"] += n * (price - los[1])
                s["matched"] += n
                los[0] -= n
                rest -= n
                if los[0] == 0:
                    lager[tid].pop(0)

    # Alle benoetigten Typnamen in EINEM Abruf holen. Einzeln aufgeloest kostete
    # das nach jedem Neustart gemessene 15,4 Sekunden, in denen die Ansicht stand.
    esi.type_names_bulk([t for t in stat if t in rund]
                        + [o["type_id"] for n, c in
                           ((CONFIG.get("esi") or {}).get("chars") or {}).items()
                           for o in (c.get("orders") or [])])

    posten = []
    for tid, s in stat.items():
        if tid not in rund or not s["matched"]:
            continue
        ek = s["kauf_isk"] / s["kauf_st"] if s["kauf_st"] else 0.0
        vk = s["verk_isk"] / s["verk_st"] if s["verk_st"] else 0.0
        posten.append({"type_id": tid, "name": esi.type_name(tid) or str(tid),
                       "stk": s["matched"], "ek": round(ek, 2), "vk": round(vk, 2),
                       "gewinn": round(s["gewinn"]),
                       "marge": round(100 * s["gewinn"] / (ek * s["matched"]), 1)
                       if ek and s["matched"] else 0.0,
                       "letzte": int(s["letzte"])})
    posten.sort(key=lambda p: -p["gewinn"])

    grupp, sonst = {}, 0.0
    steuer = broker = 0.0
    for ref, summe, n in jr:
        if ref in WB_IGNORE:
            continue
        if ref == "transaction_tax":
            steuer += -(summe or 0.0)
        elif ref == "brokers_fee":
            broker += -(summe or 0.0)
        ziel = next((g for g, refs in WB_GROUPS.items() if ref in refs), None)
        if ziel:
            grupp[ziel] = round(grupp.get(ziel, 0.0) + (summe or 0.0))
        else:
            sonst += summe or 0.0
    grupp["sonstiges"] = round(sonst)

    brutto = sum(p["gewinn"] for p in posten)
    # Gebuehren ANTEILIG auf die Rundlauf-Ware umlegen. Die Brutto-Marge stammt
    # nur aus Rundlaeufen, die gebuchten Gebuehren dagegen aus dem GESAMTEN
    # Marktgeschaeft (auch Eigenbedarf und noch nicht verkaufter Bestand).
    # Beides direkt zu verrechnen waere Aepfel gegen Birnen. Der effektive Satz
    # kommt aus dem eigenen Wallet, ist also keine geratene Pauschale.
    m_kauf = sum(s["kauf_isk"] for s in stat.values())
    m_verk = sum(s["verk_isk"] for s in stat.values())
    r_kauf = sum(s["kauf_isk"] for t, s in stat.items() if t in rund)
    r_verk = sum(s["verk_isk"] for t, s in stat.items() if t in rund)
    s_satz = steuer / m_verk if m_verk else 0.0            # Steuer faellt beim Verkauf an
    b_satz = broker / (m_kauf + m_verk) if (m_kauf + m_verk) else 0.0
    geb = s_satz * r_verk + b_satz * (r_kauf + r_verk)
    # Die Gruppe "handel" kam bisher allein aus market_transaction und zeigte
    # damit NUR die Verkaeufe, im Testwallet +3,97 Mrd, waehrend 5,90 Mrd
    # Einkauf gar nicht auftauchten (Begruendung siehe Bilanz weiter unten).
    # Jetzt steht dort der Saldo, wie bei jeder anderen Gruppe auch.
    grupp["handel"] = round(m_verk - m_kauf)
    wallets = {n: c.get("wallet") for n, c in
               ((CONFIG.get("esi") or {}).get("chars") or {}).items()
               if c.get("wallet") is not None}
    orders = []
    for n, c in ((CONFIG.get("esi") or {}).get("chars") or {}).items():
        for o in (c.get("orders") or []):
            orders.append({**o, "char": n,
                           "name": esi.type_name(o["type_id"]) or str(o["type_id"])})
    orders.sort(key=lambda o: -(o["price"] * o["rest"]))
    scope = any(c.get("orders_scope") for c in
                ((CONFIG.get("esi") or {}).get("chars") or {}).values())

    # ---------------------------------------------------------------- Bilanz
    # WARUM die Kaeufe NICHT aus dem Journal kommen: EVE bucht einen Kauf ueber
    # eine Buy-Order nicht als negative market_transaction, sondern schon beim
    # EINSTELLEN der Order als market_escrow. Wer nur ueber Orders kauft, hat
    # deshalb null negative Markt-Zeilen im Journal (an einem echten Wallet
    # gemessen: 0 von 695). market_escrow selbst taugt aber nicht als Ausgabe,
    # weil es bei Storno zurueckkommt. Die Tabelle trades kennt dagegen beide
    # Richtungen sauber, ihre Verkaufssumme stimmt auf die ISK genau mit dem
    # Journal ueberein. Also: alles aus dem Journal AUSSER dem Markt, und die
    # Marktseite komplett aus trades.
    ein_kat, aus_kat = {}, {}
    for ref, pos, neg, n in jr_vz:
        if ref in WB_IGNORE or ref in WB_GROUPS["handel"]:
            continue        # Markt kommt unten aus trades, escrow gar nicht
        ziel = next((g for g, refs in WB_GROUPS.items() if ref in refs), "sonstiges")
        if pos:
            ein_kat[ziel] = round(ein_kat.get(ziel, 0.0) + pos)
        if neg:
            aus_kat[ziel] = round(aus_kat.get(ziel, 0.0) + abs(neg))
    if m_verk:
        ein_kat["handel"] = round(ein_kat.get("handel", 0.0) + m_verk)
    if m_kauf:
        aus_kat["handel"] = round(aus_kat.get("handel", 0.0) + m_kauf)
    ein_ges = sum(ein_kat.values())
    aus_ges = sum(aus_kat.values())
    # Was noch in offenen Kauforders geparkt ist. Weder ausgegeben noch
    # verfuegbar, gehoert deshalb weder in Einnahmen noch in Ausgaben.
    geparkt = round(sum((o.get("price") or 0) * (o.get("rest") or 0)
                        for n, c in ((CONFIG.get("esi") or {}).get("chars") or {}).items()
                        for o in (c.get("orders") or []) if o.get("is_buy")))
    bilanz = {
        "ein": ein_ges, "aus": aus_ges, "saldo": ein_ges - aus_ges,
        "ein_kat": sorted(({"k": k, "isk": v} for k, v in ein_kat.items()),
                          key=lambda x: -x["isk"]),
        "aus_kat": sorted(({"k": k, "isk": v} for k, v in aus_kat.items()),
                          key=lambda x: -x["isk"]),
        "geparkt": geparkt,
        "von": int(zeitraum[0]) if zeitraum and zeitraum[0] else None,
        "bis": int(zeitraum[1]) if zeitraum and zeitraum[1] else None,
    }

    # ------------------------------------------------------------- Top-Listen
    # Namen fuer ALLE gehandelten Typen holen, nicht nur fuer die Rundlaeufe:
    # sonst steht in der Umsatzliste die nackte Typnummer.
    esi.type_names_bulk(list(stat))

    def nm(tid):
        return esi.type_name(tid) or str(tid)

    top_umsatz = sorted(
        ({"type_id": t, "name": nm(t), "isk": round(s["kauf_isk"] + s["verk_isk"]),
          "kauf": round(s["kauf_isk"]), "verkauf": round(s["verk_isk"]),
          "stk": s["kauf_st"] + s["verk_st"]}
         for t, s in stat.items()), key=lambda x: -x["isk"])[:10]
    top_menge = sorted(
        ({"type_id": t, "name": nm(t), "stk": s["verk_st"],
          "isk": round(s["verk_isk"])}
         for t, s in stat.items() if s["verk_st"]), key=lambda x: -x["stk"])[:10]
    # Nur verkauft, nie gekauft: selbst gefoerdert, gebaut oder erbeutet. Fuer
    # einen Miner ist genau das die Haupteinnahme, und im Handelsgewinn taucht
    # es nicht auf, weil es keinen Einkaufspreis gibt.
    eigen = sorted(
        ({"type_id": t, "name": nm(t), "stk": s["verk_st"], "isk": round(s["verk_isk"])}
         for t, s in stat.items() if t in (verkauft - gekauft) and s["verk_isk"]),
        key=lambda x: -x["isk"])[:10]
    eigen_ges = round(sum(s["verk_isk"] for t, s in stat.items()
                          if t in (verkauft - gekauft)))
    # Eigenbedarf: gekauft und nie verkauft.
    bedarf = sorted(
        ({"type_id": t, "name": nm(t), "stk": s["kauf_st"], "isk": round(s["kauf_isk"])}
         for t, s in stat.items() if t in (gekauft - verkauft) and s["kauf_isk"]),
        key=lambda x: -x["isk"])[:10]
    bedarf_ges = round(sum(s["kauf_isk"] for t, s in stat.items()
                           if t in (gekauft - verkauft)))
    tops = {"umsatz": top_umsatz, "menge": top_menge,
            "eigen": eigen, "eigen_ges": eigen_ges, "eigen_n": len(verkauft - gekauft),
            "bedarf": bedarf, "bedarf_ges": bedarf_ges, "bedarf_n": len(gekauft - verkauft),
            "rund_n": len(rund), "typen": len(stat)}

    return {"tage": days, "bilanz": bilanz, "tops": tops, "posten": posten[:40],
            "gruppen": grupp, "brutto": round(brutto), "gebuehren": round(geb),
            "netto": round(brutto - geb),
            "geb_gesamt": round(steuer + broker),
            "satz_steuer": round(100 * s_satz, 2), "satz_broker": round(100 * b_satz, 2),
            "kauf": round(r_kauf), "verkauf": round(r_verk),
            "wallets": wallets, "orders": orders[:30], "orders_scope": scope,
            "trades": len(tx)}


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
    total_isk = total_ext_isk = total_rest_isk = 0
    prodagg = {}
    oldest = soonest = None
    # Aeltester echter Kolonie-Stand ueber alle Chars. Das ist die ehrliche
    # Altersangabe fuer Lagerwerte, nicht der Cache-Zeitstempel der Antwort.
    stale = None
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
            if col.get("updated"):
                stale = col["updated"] if stale is None else min(stale, col["updated"])
            col_rest = col_rest_isk = 0
            for e in (col.get("extractors") or []):
                n_ex += 1
                exp = e.get("expiry")
                # RESTertrag jetzt rechnen, nicht beim Abruf: er faellt mit
                # jeder Minute. Die gespeicherte Gesamtmenge bleibt daneben
                # stehen, aber sie ist NICHT das, was noch kommt.
                rest = extractor_total(e.get("install"), exp, e.get("cycle"),
                                       e.get("qty"), ab=now)
                rest_isk = round(rest * (e.get("px") or 0))
                col_rest += rest
                col_rest_isk += rest_isk
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
                                   "rest": rest, "cycle": e.get("cycle"),
                                   "expiry": exp})
            col["rest_units"], col["rest_isk"] = col_rest, col_rest_isk
            # Fabrik-Produkte flottenweit aufsummieren (fuer den Gesamtausstoss)
            for pr in (col.get("products") or []):
                a = prodagg.setdefault(pr["name"], {"name": pr["name"], "tier": pr.get("tier"),
                                                    "type_id": pr.get("type_id"), "count": 0})
                a["count"] += pr.get("count", 1)
        cisk = sum(col.get("isk", 0) for col in cols)
        cext = sum(col.get("ext_isk", 0) for col in cols)
        crest = sum(col.get("rest_isk", 0) for col in cols)
        total_isk += cisk
        total_ext_isk += cext
        total_rest_isk += crest
        chars.append({"name": nm, "cols": cols, "isk": cisk, "ext_isk": cext,
                      "rest_isk": crest,
                      "as_of": p.get("as_of"), "next": p.get("next")})
    extractors.sort(key=lambda x: x.get("expiry") or 9e18)
    chars.sort(key=lambda x: x["name"])
    order = {"P0": 0, "P1": 1, "P2": 2, "P3": 3, "P4": 4}
    products = sorted(prodagg.values(), key=lambda p: (order.get(p.get("tier"), 9), p["name"]))
    # Was PI wirklich gekostet hat. Steht laengst im Wallet-Journal, das Canary
    # ohnehin vollstaendig mitschreibt: kein neuer Scope, kein neuer Abruf.
    # ESI gibt nur 30 Tage zurueck, die lokale Tabelle sammelt darueber hinaus,
    # deshalb wird das Fenster hier offen ausgewiesen.
    kosten = {"export": 0, "import": 0, "bau": 0, "tage": 30, "seit": None}
    cut = now - 30 * 86400
    try:
        with DB_LOCK:
            rows = DB.execute(
                "SELECT ref_type, sum(amount), min(ts) FROM wbook "
                "WHERE ts>=? AND ref_type LIKE 'planetary%' GROUP BY ref_type",
                (cut,)).fetchall()
            frueh = DB.execute("SELECT min(ts) FROM wbook").fetchone()
        for rt, summe, _mn in rows:
            k = ("export" if "export" in rt else
                 "import" if "import" in rt else "bau")
            kosten[k] += abs(summe or 0)
        # Wie weit reicht die eigene Aufzeichnung ueberhaupt zurueck? Wer Canary
        # erst seit einer Woche laufen laesst, sieht keine 30 Tage.
        if frueh and frueh[0]:
            kosten["seit"] = int(max(frueh[0], cut))
    except Exception as e:
        log_error("CN-SRV-01", "query_planeten/kosten", e)
    kosten["summe"] = round(kosten["export"] + kosten["import"] + kosten["bau"])
    return {"chars": chars, "extractors": extractors, "reconnect": reconnect,
            "as_of": oldest, "next": soonest, "stale": stale, "n_char": len(chars),
            "n_col": n_col, "n_ex": n_ex, "n_soon": n_soon, "n_exp": n_exp,
            "total_isk": total_isk, "total_ext_isk": total_ext_isk,
            "total_rest_isk": total_rest_isk, "kosten": kosten, "products": products}


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


# Die Rogue-Drone-Schlachtschiffe des Abyss heissen je Filament-Stufe anders.
# Am EVE-University-Wiki verifiziert (13.08.2026, Seite "Abyssal Deadspace"),
# nicht aus dem Gedaechtnis. Alle sechs Namen stehen ohnehin schon in
# site_sigs.json, bisher nur als Ortsmarke. WICHTIG: nicht jeder Durchgang hat
# Rogue Drones, das Signal ist also exakt, aber nicht immer da. Von Nirahse
# selbst bestaetigt: "wenn sie da sind, hat man eine sichere Info".
ABYSS_TIER_GEGNER = {"photic abyssal overmind": 1, "twilit abyssal overmind": 2,
                     "bathyic abyssal overmind": 3, "hadal abyssal overmind": 4,
                     "benthic abyssal overmind": 5, "endobenthic abyssal overmind": 6}
# Dasselbe aus dem SELBST VERGEBENEN Namen: wer seinen Lauf "Chaotic Firestorm"
# nennt, hat die Stufe schon hingeschrieben. Nur die englischen Filamentnamen,
# denn nur die sind belegt. Steht dort etwas anderes, bleibt die Stufe leer,
# statt geraten zu werden.
ABYSS_TIER_NAME = {"calm": 1, "agitated": 2, "fierce": 3,
                   "raging": 4, "chaotic": 5, "cataclysmic": 6}
ABYSS_WETTER = ["dark", "electrical", "exotic", "firestorm", "gamma"]


def abyss_tier_aus_gegnern(enemies):
    """Filament-Stufe aus den Gegnernamen, oder None. Exakter Namensvergleich,
    kein Teilwort: 'benthic' steckt in 'endobenthic'."""
    for name, _cnt in (enemies or []):
        t = ABYSS_TIER_GEGNER.get((name or "").strip().lower())
        if t:
            return t
    return None


def _wort_drin(wort, text):
    return re.search(r"(?<![a-z])" + wort + r"(?![a-z])", text) is not None


def abyss_tier_aus_name(label):
    """Filament-Stufe aus dem selbst vergebenen Namen, oder None."""
    low = (label or "").lower()
    for wort, t in ABYSS_TIER_NAME.items():
        if _wort_drin(wort, low):
            return t
    return None


def abyss_wetter_aus_name(label):
    low = (label or "").lower()
    for w in ABYSS_WETTER:
        if _wort_drin(w, low):
            return w
    return None


def ist_abyss(system, enemies):
    """Zwei Wege, damit auch Laeufe mitkommen, bei denen der Chatlog den Ort
    nicht liefern konnte: der Ort selbst, sonst ein site-eindeutiger Gegner."""
    if (system or "") == ABYSS_ORT:
        return True
    return bool(detect_site(enemies))


_ABYSS_N = {"ts": 0.0, "n": 0}


def abyss_anzahl():
    """Wie viele Abyss-Durchgaenge stehen in der Datenbank? Nur fuer den
    Export-Knopf, der sonst auch bei null Laeufen herumstuende. Gecacht, weil
    der Missionen-Tab im 2-Sekunden-Takt fragt und die Pruefung jede Zeile
    einzeln ansieht."""
    if time.time() - _ABYSS_N["ts"] < 30:
        return _ABYSS_N["n"]
    with DB_LOCK:
        rows = DB.execute("SELECT system, enemies FROM missions").fetchall()
    n = 0
    for system, enemies_j in rows:
        try:
            enemies = json.loads(enemies_j or "[]")
        except Exception:
            enemies = []
        if ist_abyss(system, enemies):
            n += 1
    _ABYSS_N.update({"ts": time.time(), "n": n})
    return n


def abyss_export_tsv():
    """Alle erkannten Abyss-Durchgaenge als Tabelle zum Weitergeben.

    Bewusst OHNE Charakternamen (nur 'Char 1', 'Char 2' in der Reihenfolge des
    ersten Auftretens), ohne Tokens und ohne Pfade, genau wie die Diagnose.
    Tabulatorgetrennt, damit es sich in jede Tabellenkalkulation einfuegen
    laesst und trotzdem im Textfeld lesbar bleibt."""
    spalten = ["start_utc", "dauer_s", "char", "system", "name", "stufe_name",
               "stufe_gegner", "wetter", "dmg_out", "dmg_in", "treffer",
               "fehl_out", "fehl_in", "kills", "bounty", "loot_isk",
               "ewar", "gegner_top"]
    zeilen = ["\t".join(spalten)]
    nummern, n = {}, 0
    with DB_LOCK:
        rows = DB.execute(
            "SELECT start_ts,end_ts,char_id,system,label,dmg_out,dmg_in,hits,"
            "miss_out,miss_in,kills,bounty,loot_isk,ewar,enemies "
            "FROM missions ORDER BY start_ts").fetchall()
    for (start, ende, cid, system, label, dout, din, hits, mout, min_, kills,
         bounty, loot, ewar_j, enemies_j) in rows:
        try:
            enemies = json.loads(enemies_j or "[]")
        except Exception:
            enemies = []
        if not ist_abyss(system, enemies):
            continue
        if cid not in nummern:
            n += 1
            nummern[cid] = n
        try:
            ewar = json.loads(ewar_j or "[]")
        except Exception:
            ewar = []
        zeilen.append("\t".join(str(x) for x in [
            datetime.fromtimestamp(start or 0, timezone.utc).strftime("%Y-%m-%d %H:%M:%S"),
            int((ende or 0) - (start or 0)),
            "Char " + str(nummern[cid]),
            (system or "?"),
            (label or "").replace("\t", " "),
            abyss_tier_aus_name(label) or "",
            abyss_tier_aus_gegnern(enemies) or "",
            abyss_wetter_aus_name(label) or "",
            int(dout or 0), int(din or 0), int(hits or 0),
            int(mout or 0), int(min_ or 0), int(kills or 0),
            int(bounty or 0), int(loot or 0),
            " ".join(f"{k}x{v}" for k, v in ewar) if ewar else "",
            " ".join(f"{k}x{v}" for k, v in enemies[:8]).replace("\t", " "),
        ]))
    if len(zeilen) == 1:
        zeilen.append("# keine Abyss-Durchgaenge gefunden")
    return "\n".join(zeilen)


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
    # HTTP/1.1 statt der Vorgabe 1.0. Mit 1.0 schliesst der Server nach JEDER
    # Antwort die Verbindung, der Browser baut also fuer jeden 2s-Tick eine neue
    # auf. Zusammen mit dem localhost/IPv6-Umweg (siehe Serverstart unten) waren
    # das gemessene 171 ms je Abruf, obwohl der Server die Antwort in 1 bis 2 ms
    # fertig hat. Erlaubt ist HTTP/1.1 nur, weil _send und _deny IMMER ein
    # Content-Length mitschicken — sonst wuerde der Browser ewig weiterlesen.
    protocol_version = "HTTP/1.1"
    # Offene Keep-Alive-Verbindungen sollen keinen Thread dauerhaft binden.
    timeout = 30

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
        if p == "/obs":
            # Schlanke Seite fuer OBS als Browser-Quelle. Alles Weitere steht
            # in der Adresse, siehe OBS_PAGE.
            body = OBS_PAGE.encode("utf-8")
            self.send_response(200)
            self.send_header("Content-Type", "text/html; charset=utf-8")
            self.send_header("Content-Length", str(len(body)))
            self.send_header("Cache-Control", "no-store")
            self.end_headers()
            self.wfile.write(body)
            return
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
            elif view == "uhr":
                data["uhr_liste"] = query_uhr_liste()
            elif view == "missionen":
                data["missions"] = query_missions()
                data["mission_log"], data["mission_offen"] = query_mission_history()
                data["abyss_n"] = abyss_anzahl()
                data["loot_tage"] = query_loot_tage()
                data["chars"] = snapshot_live()
            elif view == "vault":
                data["vault"] = query_vault()
                data["vault"]["advisor"] = query_ore_advisor(CONFIG["region"])
            elif view == "planeten":
                data["planeten"] = query_planeten()
            elif view == "wallet":
                # Zeitraum aus der URL: 7, 30 oder 0 fuer "alles". Alles andere
                # faellt auf 30 zurueck, damit ein Tippfehler nichts sprengt.
                try:
                    tage = int(self.path.split("days=")[1].split("&")[0]) \
                        if "days=" in self.path else 30
                except ValueError:
                    tage = 30
                data["wallet"] = query_wallet(tage if tage in (0, 7, 30, 90) else 30)
            elif view == "timeline":
                data["timeline"] = query_timelines()
            elif view == "profil":
                data["profiles"] = query_profiles()
            elif view in ("rechner", "beute"):
                pass  # beide holen ihre Daten per POST, sonst liefe hier
                      # unnoetig die grosse Gesamt-Abfrage mit
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
        elif p == "/abyss.tsv":
            self._send(abyss_export_tsv(), "text/tab-separated-values; charset=utf-8",
                       "abyss_runs.tsv")
        elif p == "/export.csv":
            self._send(export_csv(), "text/csv; charset=utf-8", "eve_dashboard_export.csv")
        elif p == "/export.json":
            self._send(json.dumps({"month": query_month(), "total": query_total(),
                                   "analyse": query_analyse()}, indent=1),
                       "application/json", "eve_dashboard_export.json")
        elif p == "/reparieren":
            # Rettungsanker ohne jedes JavaScript. Erreichbar auch dann, wenn
            # die Oberflaeche gar nicht mehr laeuft. Siehe notfall_banner().
            refresh_update_info()
            chk = check_update()
            if chk.get("ok") and chk.get("available"):
                txt = ("<h2>Neue Version " + html_escape(str(chk.get("latest")))
                       + " verfuegbar</h2><p>Installiert ist "
                       + html_escape(VERSION) + ".</p>")
                knopf = ('<form method="post" action="/reparieren">'
                         '<button type="submit" style="' + NOTFALL_KNOPF + '">'
                         'Jetzt aktualisieren</button></form>')
            elif chk.get("ok"):
                txt = ("<h2>Alles aktuell</h2><p>Du hast bereits Version "
                       + html_escape(VERSION) + ".</p>")
                knopf = ('<form method="post" action="/reparieren">'
                         '<button type="submit" style="' + NOTFALL_KNOPF + '">'
                         'Trotzdem neu laden</button></form>')
            else:
                txt = ("<h2>Update-Server nicht erreichbar</h2><p>"
                       + html_escape(str(chk.get("error") or "")) + "</p>")
                knopf = ('<form method="post" action="/reparieren">'
                         '<button type="submit" style="' + NOTFALL_KNOPF + '">'
                         'Nochmal versuchen</button></form>')
            self._send(notfall_seite(
                txt + knopf + '<p style="opacity:.6;margin-top:26px;font-size:12px">'
                'Diese Seite kommt ohne JavaScript aus und funktioniert auch, '
                'wenn das Dashboard leer bleibt.</p>'),
                "text/html; charset=utf-8")
        else:
            # Der Update-Hinweis wird hier eingesetzt, nicht vom Skript gebaut.
            self._send(PAGE.replace("<!--NOTFALL-->", notfall_banner()),
                       "text/html; charset=utf-8")

    def _do_POST(self):
        if not _host_ok(self.headers) or not _origin_ok(self.headers):
            return self._deny()
        if self.path.split("?")[0] == "/reparieren":
            # Formular statt JSON: der Rettungsweg darf kein Skript brauchen.
            try:
                self.rfile.read(int(self.headers.get("Content-Length", 0) or 0))
            except Exception:
                pass
            r = do_update()
            if r.get("ok") and r.get("updated"):
                txt = ("<h2>Aktualisiert</h2><p>" + html_escape(str(r.get("message") or ""))
                       + "</p><p>Canary startet sich neu. Warte ein paar Sekunden "
                       "und rufe dann <b>localhost:8765</b> auf.</p>")
            elif r.get("ok"):
                txt = ("<h2>Nichts zu tun</h2><p>"
                       + html_escape(str(r.get("message") or "Bereits aktuell.")) + "</p>")
            else:
                txt = ("<h2>Hat nicht geklappt</h2><p>"
                       + html_escape(str(r.get("error") or "")) + "</p>"
                       "<p>Dann hilft der Installer von der Canary-Seite. "
                       "Einstellungen und Daten bleiben dabei erhalten.</p>")
            return self._send(notfall_seite(txt), "text/html; charset=utf-8")
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
            # Zahl absichern: ein unerwarteter Wert wuerde die ganze Anfrage mit
            # HTTP 500 beenden statt die Einstellung einfach zu ignorieren.
            try:
                CONFIG["idle_warn"] = max(0, int(body.get("seconds") or 0))
            except (TypeError, ValueError):
                pass
        elif action == "laser_off_mode":
            if body.get("modus") in ("immer", "rate", "leer", "aus"):
                CONFIG["laser_off_mode"] = body["modus"]
        elif action == "tool_warn_delay":
            # Nach oben begrenzt: die Warnung steht ohnehin nur 60 Sekunden,
            # ein groesserer Wert wuerde sie schlicht nie erscheinen lassen.
            try:
                CONFIG["tool_warn_delay"] = min(60, max(0, int(body.get("seconds") or 0)))
            except (TypeError, ValueError):
                pass
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
        elif action == "mission_reopen":
            # Notausgang fuer alles, was die Automatik nicht erwischt: der
            # Nutzer sagt selbst, dass die Mission noch laeuft. Die Werte
            # wandern zurueck in die laufende Sitzung, der Eintrag verschwindet
            # und entsteht beim naechsten Abschluss neu, dann vollstaendig.
            mid = str(body.get("mid") or "")
            with DB_LOCK:
                row = DB.execute(
                    "SELECT char_id,char,start_ts,system,dmg_out,dmg_in,kills,bounty,"
                    "hits,miss_out,miss_in,weapons,enemies,loot_isk,loot_text "
                    "FROM missions WHERE mid=?", (mid,)).fetchone()
            if not row:
                self._send(json.dumps({"ok": False, "error": "Eintrag nicht gefunden"}))
                return
            m = {"char_id": row[0], "char": row[1], "start_ts": row[2], "system": row[3],
                 "dmg_out": row[4], "dmg_in": row[5], "kills": row[6], "bounty": row[7],
                 "hits": row[8], "miss_out": row[9], "miss_in": row[10],
                 "weapons": json.loads(row[11] or "[]"), "enemies": json.loads(row[12] or "[]")}
            with ingest.lock:
                s = ingest.sessions.get(str(row[0]))
                if s:
                    s.wieder_aufnehmen(m)
                    s.zuletzt_zu = None
            with DB_LOCK:
                DB.execute("DELETE FROM missions WHERE mid=?", (mid,))
                DB.commit()
            # Ob die Sitzung noch laeuft, entscheidet ob die Werte wirklich
            # weitergezaehlt werden. Eingetragener Loot geht verloren, denn der
            # Eintrag entsteht spaeter neu: beides gehoert in die Rueckmeldung.
            self._send(json.dumps({"ok": True, "sitzung_aktiv": bool(s),
                                   "loot_war_da": bool(row[13] or row[14])}))
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
        elif action == "share_ore":
            CONFIG["share_ore"] = bool(body.get("on"))
        elif action == "clip_watch":
            CONFIG["clip_watch"] = bool(body.get("on"))
        elif action == "calc":
            self._send(json.dumps(calc_hubs(body.get("text") or "")))
            return
        elif action == "loot":
            self._send(json.dumps(calc_loot(body.get("text") or "")))
            return
        elif action == "settings":
            # Alles rund um die EVE-Einstellungen unter einer Aktion. ALPHA.
            was = str(body.get("was") or "")
            ordner = str(body.get("ordner") or "")
            # Sicherheitsgurt: nur Ordner, die eve_settings_dirs selbst
            # gefunden hat. Sonst koennte ein Aufruf beliebige Pfade
            # ueberschreiben, und das hier schreibt echte Dateien.
            erlaubt = {str(p): p for p in eve_settings_dirs()}
            if was == "liste":
                self._send(json.dumps({
                    "ok": True,
                    "ordner": [{"pfad": str(p), "name": p.name,
                                "eltern": p.parent.name,
                                "dateien": set_dateien(p)} for p in erlaubt.values()],
                    "sicherungen": set_sicherungen(),
                    "eve_laeuft": eve_laeuft()}))
                return
            if ordner not in erlaubt:
                self._send(json.dumps({"ok": False,
                                       "msg": "Unbekannter Einstellungsordner."}))
                return
            q = erlaubt[ordner]
            if was == "sichern":
                try:
                    self._send(json.dumps({"ok": True, "gesichert": set_sichern(q)}))
                except Exception as e:
                    log_error("CN-SET-01", "settings/sichern", e)
                    self._send(json.dumps({"ok": False, "msg": str(e)}))
                return
            # Ab hier wird geschrieben. Laeuft EVE, wuerde der Client beim
            # Beenden alles ueberschreiben: dann lieber gar nicht erst.
            if eve_laeuft():
                self._send(json.dumps({"ok": False, "msg":
                    "EVE laeuft gerade. Der Client schreibt seine Einstellungen "
                    "beim Beenden und wuerde alles ueberschreiben. Bitte erst "
                    "EVE schliessen."}))
                return
            if was == "kopieren":
                quelle = str(body.get("quelle") or "")
                ziele = [str(z) for z in (body.get("ziele") or [])]
                if not quelle or not ziele:
                    self._send(json.dumps({"ok": False, "msg": "Quelle oder Ziel fehlt."}))
                    return
                da = {d["datei"] for d in set_dateien(q)}
                if quelle not in da or any(z not in da for z in ziele):
                    self._send(json.dumps({"ok": False, "msg": "Datei nicht in diesem Ordner."}))
                    return
                if quelle in ziele:
                    self._send(json.dumps({"ok": False, "msg": "Quelle ist auch Ziel."}))
                    return
                try:
                    vorher = set_sichern(q, "vor-kopieren")
                    roh = (q / quelle).read_bytes()
                    for z in ziele:
                        (q / (z + ".neu")).write_bytes(roh)
                        os.replace(q / (z + ".neu"), q / z)
                    self._send(json.dumps({"ok": True, "kopiert": len(ziele),
                                           "gesichert": vorher}))
                except Exception as e:
                    log_error("CN-SET-02", "settings/kopieren", e)
                    self._send(json.dumps({"ok": False, "msg": str(e)}))
                return
            if was == "zurueck":
                import zipfile
                name = os.path.basename(str(body.get("sicherung") or ""))
                p = APP_DIR / SET_BACKUP / name
                if not name.endswith(".zip") or not p.is_file():
                    self._send(json.dumps({"ok": False, "msg": "Sicherung nicht gefunden."}))
                    return
                # Leere Auswahl heisst: alles. Sonst nur die genannten
                # Dateien, damit man einen einzelnen Charakter zurueckholen
                # kann, ohne die anderen mit zurueckzuwerfen.
                nur = {str(x) for x in (body.get("dateien") or [])}
                try:
                    vorher = set_sichern(q, "vor-zurueck")
                    getan = []
                    with zipfile.ZipFile(p) as z:
                        for eintrag in z.namelist():
                            # Ohne Pfadanteil, und die eigene Herkunftsnotiz
                            # gehoert nicht in den Einstellungsordner.
                            if "/" in eintrag or "\\" in eintrag \
                                    or eintrag == "_herkunft.txt":
                                continue
                            if nur and eintrag not in nur:
                                continue
                            (q / (eintrag + ".neu")).write_bytes(z.read(eintrag))
                            os.replace(q / (eintrag + ".neu"), q / eintrag)
                            getan.append(eintrag)
                    self._send(json.dumps({"ok": True, "gesichert": vorher,
                                           "dateien": getan}))
                except Exception as e:
                    log_error("CN-SET-02", "settings/zurueck", e)
                    self._send(json.dumps({"ok": False, "msg": str(e)}))
                return
            self._send(json.dumps({"ok": False, "msg": "Unbekannter Befehl."}))
            return
        elif action == "uhr":
            # Eine Aktion mit Unterbefehl statt vier Endpunkten: die Stoppuhr
            # hat genau einen Zustand, den soll auch nur eine Stelle aendern.
            was = str(body.get("was") or "")
            # m3 und ISK kommen aus der Oberflaeche mit, siehe Kommentar bei
            # uhr_laden: sie werden in der Live-Ansicht gerechnet.
            m3 = float(body.get("m3") or 0)
            isk = float(body.get("isk") or 0)
            if was == "start":
                UHR.update({"an": True, "pause": False,
                            "label": (body.get("label") or "").strip()[:60],
                            "start": time.time(), "sek": 0.0,
                            "snap_m3": m3, "snap_isk": isk})
            elif was == "pause" and UHR["an"] and not UHR["pause"]:
                UHR["sek"] = uhr_laufzeit()
                UHR["pause"] = True
            elif was == "weiter" and UHR["an"] and UHR["pause"]:
                UHR["start"] = time.time()
                UHR["pause"] = False
            elif was == "verwerfen":
                UHR.update({"an": False, "pause": False, "label": "",
                            "start": 0.0, "sek": 0.0})
            elif was == "speichern" and UHR["an"]:
                sek = uhr_laufzeit()
                d_m3 = m3 - UHR["snap_m3"]
                d_isk = isk - UHR["snap_isk"]
                # Faellt die Summe unter die Momentaufnahme, wurde eine Sitzung
                # mittendrin zurueckgesetzt (Andocken). Dann ist die Differenz
                # nicht mehr das, was in diesem Zeitraum passiert ist. Statt
                # eine falsche Zahl zu speichern, wird der Eintrag markiert.
                unsicher = d_m3 < 0 or d_isk < 0
                if unsicher:
                    d_m3 = max(0.0, m3)
                    d_isk = max(0.0, isk)
                with DB_LOCK:
                    DB.execute(
                        "INSERT INTO uhr(label,start_ts,end_ts,sek,m3,isk,unsicher) "
                        "VALUES(?,?,?,?,?,?,?)",
                        (UHR["label"] or "Trip", time.time() - sek, time.time(),
                         sek, d_m3, d_isk, 1 if unsicher else 0))
                    DB.commit()
                UHR.update({"an": False, "pause": False, "label": "",
                            "start": 0.0, "sek": 0.0})
            uhr_sichern()
            self._send(json.dumps({"ok": True, "uhr": uhr_json()}))
            return
        elif action == "uhr_weg":
            with DB_LOCK:
                DB.execute("DELETE FROM uhr WHERE id=?", (int(body.get("id") or 0),))
                DB.commit()
            self._send(json.dumps({"ok": True}))
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
        elif action == "cargo_diff":
            # Zwei Frachtraum-Kopien vergleichen. Kein Netz, kein Speichern:
            # der eingefuegte Text bleibt in dieser einen Antwort.
            self._send(json.dumps(cargo_diff(body.get("vorher") or "",
                                             body.get("nachher") or "")))
            return
        elif action == "loot_calc":
            # Beliebige Frachtraum-Kopie bewerten, ohne sie an eine Mission zu
            # haengen. Gleiche Rechnung wie beim Loot-Feld der Missionen.
            self._send(json.dumps(calc_loot(body.get("text") or "")))
            return
        elif action == "mission_label":
            # Einen Lauf selbst benennen. Das ist gleichzeitig die Vorlage, an
            # der kuenftige Laeufe derselben Mission wiedererkannt werden.
            # Leerer Name loescht die Benennung wieder.
            mid = str(body.get("mid") or "")
            name = str(body.get("name") or "").strip()[:80]
            with DB_LOCK:
                DB.execute("UPDATE missions SET label=? WHERE mid=?",
                           (name or None, mid))
                DB.commit()
            marken_laden()
            self._send(json.dumps({"ok": True, "name": name,
                                   "vorlagen": len(MARKEN)}))
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
            # Wie oben: eine unbrauchbare Zahl darf die Anfrage nicht sprengen.
            try:
                menge = max(0.0, float(units)) if units is not None else None
            except (TypeError, ValueError):
                menge = None
            with CONFIG_LOCK:
                hw = CONFIG.setdefault("heavy_water", {})
                if char and menge is None:
                    hw.pop(char, None)
                elif char:
                    hw[char] = {"units": menge, "fill": menge,
                                "core": "t2" if body.get("core") == "t2" else "t1",
                                "ts": time.time(), "warned": False, "ck": 0}
        elif action == "mission_close":
            # Mission von Hand abschliessen, bevor abgedockt wird. Wunsch aus der
            # Praxis: erst Loot eintragen und den Laderaum leeren, dann weiter.
            # Es wird GENAU derselbe Weg gegangen wie beim Abdocken, damit es
            # keine zweite Wahrheit gibt: Mission sichern, dann die Session ueber
            # ein Abdock-Ereignis frisch machen. Dockt der Spieler danach wirklich
            # ab, entsteht keine zweite Mission, weil dann keine Kampfdaten mehr
            # da sind.
            char = str(body.get("char") or "")
            jetzt = time.time()
            gespeichert = None
            an_station = False
            with ingest.lock:
                s = next((x for x in ingest.sessions.values() if x.name == char), None)
                if s:
                    # Anflug zur Station gesehen und seither weder Erz noch
                    # Schaden? Dann steht der Pilot dort, die Mission wird also
                    # nicht aus der Ferne abgegeben.
                    an_station = s.dock_ts is not None
                    md = s.mission_dict(jetzt)
                    if md:
                        md["dialog"] = " ".join(chatwatch.dialogue(
                            s.char_id, md["start_ts"], jetzt))[:2000] or None
                        gespeichert = md
                    # live=False: das ist kein frisch gelesenes Log-Ereignis,
                    # es soll also keine Alarme und keine Toene ausloesen.
                    s.feed({"kind": "hold_reset", "key": "dock", "ts": jetzt,
                            "char_id": s.char_id, "day": time.strftime("%Y-%m-%d"),
                            "value": 1}, live=False)
                    # Dauerhaft merken, sonst ist der Abschluss nach dem
                    # naechsten Neustart wieder weg. Siehe zu_laden().
                    zu_merken(s.char_id, jetzt)
            if gespeichert:
                save_mission(gespeichert)
                mins = max(1, round((gespeichert["end_ts"] - gespeichert["start_ts"]) / 60))
                self._send(json.dumps({
                    "ok": True, "saved": True, "mid": f"{gespeichert['char_id']}:{int(gespeichert['start_ts'])}",
                    "min": mins, "bounty": gespeichert["bounty"], "kills": gespeichert["kills"],
                    "docked": an_station}))
            else:
                self._send(json.dumps({"ok": True, "saved": False,
                                       "msg": "Kein Kampf seit dem letzten Abdocken."
                                              if s else "Charakter gerade nicht aktiv."}))
            return
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
<link rel="icon" href="data:image/png;base64,iVBORw0KGgoAAAANSUhEUgAAACAAAAAgCAYAAABzenr0AAAFJklEQVR42u1We0xTZxSvwfmcm24uJoKD8bpFxa5Mngpth21vmdlA3RJdtiy6uMzFseHcPz5QE4dm6BS0IM/qQB5qgWKhKmLpXCh94CQBy6MI9HVvyxtB58bOvnsRRFnCY+hfnOSX795z7/1+v3POd24OgzFjMzYJE6kal+E64ltcTxaItLZrCAqRDgFd49XIpyei+cqGZdNPXNG0VKQnkxBxkUhr3cyX6xc9/w7lw7XWTaJqskioI5Ijbje/NS3kuMYSjlfblUK1af1Ev4moMoegjChxrYX//8h1tk+EevKyUFm/8Nkncxim/JDPuku4Z7tKuAc65LydjmLeR7ZCbmB9bvg8+tvyuoX4H456kcbiPSVyocYSKkR15eWqZo/2381Yt9B2Ofh8e0Ew9MjXw8AN3hCuD629Cm4tIQtn4VXmKCR+79Qiv2VYJNCTKqGq6fXRfuPFYF9SGlznkAYAkcuGWjEGdxIxaMxkge1SAPSWhEFfSSh0SP0fGjPWCKaceoGOPIIy8OFoX3Om73Zr1poBs4QJpjQvqI53hbJYZxp5P7j+Jt2HyW/GLv+nSexBP7cnRajtcdFukybnybTzhXqiHNv+NHu6UyuXtqZ6PzKleUMb2tycxYL7v7LBKGFBbYI77NnK3r1REBZ1I3YFefuoCxAJLBiM/hT+PrLr4cP4mLiWuJgFk6i9NUqgJaJH+5qSsRhTOiJP9wJDEgb91zgj6CoMgIZkrLUmkakzZ3hB2xkm9O7+AHq+iIQ/v9wCg7u3waP9X0nL9+ycNbH068nTfJXRZ/j+u0hPRksqdo+KXHP8begsCqGJB4ZFXOeguq+HbiSEzFoN5DehYI7kgC2SCxa0mqJ4fc1bNsTf3bF56cQyoCPkAUdTnIbv68Q+oXT0SEBThi9NTEPBGbnuLw0FRy4LzJneYEpggm1HEHRt43R2fbzhUEPk+29Orv20ttJnDt857AIlwIxgEHtBZ2HwEDmNMOiS+oNVgoElE50NVILKn1bAzYPLQbHPeduYvStNOZMSoDm5anFbGjZgfiKg+ZwHKI+4gCnbD/quhgCZvYqOeghecOeEK5RTnXHQ2Sj+2t1pTHk1VsUEBBDFXIli7iynuQxHQcjp9jw2ipBJR2fO8IbKuBU0iR61Id0RyEfBcMad9lNQ7HfZ9fy+78Ycm4WCG18AX236Xlhev7hdxtnb/6TW/SjV3YWBYM/xBcNZDyg/5EyjAmXjHiJuTvEE5WEX2lcW60Jkx7wzf8y+ykZMoCfEEzoHjiLO54h8kCYvDYOewiDolQ3V/gH609mvIDGXA0fWNslKqEt0h5pf3EB93O3YfwamtUbzq8ybxiUnC0Lx3uKQxx2X3gMCtZU5HYP2fDadhZH+Vzxd++Tr0Fnwpd+l/oDo0CY+v6f/4SQkwHaLW6iZN66Ahgw/L0OSD8uQtJJFrY2pq1l2GZdlL3qKzuIw6bCIjnw/dAYwWogl0wfup2Bj6ixQmzYjAQembUApO7XulW455xKVFavEh85ST1EQ9MiCoCUFMz5Drmx4Q6CzKcMVNQsY02l3JNzZ7VcC8yhyukx5bLokjny/v7J+9J1DvbNR1TgH1xPFAnXb2hcyI/5+gjW7NZVJi7CdX0ULeFDKeVwlDn4toqJxiUhHFONVlogXOqhWnmQ5tab65FIiqFmgp4R7Fb9tdBXpbSpRlSnwpUzLlafYlIicLjSoOGS8rfxb9Z78stpXX+rIXvEz28lycW1azYXwBYwZm7FJ2L/GN0lccEwtAwAAAABJRU5ErkJggg==">
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
/* KEINE transition auf der Flaeche. Wenn der Hintergrund aus einer Variablen
   kommt und die Variable sich aendert (Themen- oder Skin-Wechsel), friert der
   Browser den alten Wert ein, statt auf den neuen zu blenden. Gemessen: nach
   dem Umschalten auf Hell stand --bg auf #f2f4f8, der Body blieb aber auf
   rgb(11,14,20), also wurden die Karten hell und der Grund dahinter blieb
   dunkel. Mit transition:none folgt der Wert sofort korrekt, mit
   background-color statt background aendert sich nichts. Ein harter Wechsel
   ist der Preis, ein halb umgeschaltetes Fenster war der Fehler. */
body{background:var(--bg);color:var(--txt);padding:18px}
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
/* Elf Tabs passen in schmalen Fenstern nicht nebeneinander. Vorher wurde die
   Leiste rechts einfach abgeschnitten ("PLA…" statt Planeten), jetzt laesst
   sie sich seitlich schieben. */
#loadbar{height:2px;background:var(--inset);overflow:hidden;margin-bottom:-2px;position:relative;z-index:2}
#loadtxt{font-size:12.5px;color:var(--cyan);padding:6px 2px 0;display:flex;gap:7px;align-items:center}
#loadtxt:before{content:'';width:9px;height:9px;border-radius:50%;background:var(--cyan);
 animation:lbp 900ms ease-in-out infinite}
#loadtxt.lang{color:var(--gold)}
#loadtxt.lang:before{background:var(--gold)}
@keyframes lbp{0%,100%{opacity:.25}50%{opacity:1}}
#loadbar>div{height:100%;width:35%;background:var(--cyan);border-radius:2px;
 animation:lb 900ms ease-in-out infinite}
@keyframes lb{0%{margin-left:-35%}100%{margin-left:100%}}
nav{display:flex;gap:2px;border-bottom:1px solid var(--line);margin-bottom:14px;
 overflow-x:auto;scrollbar-width:thin}
nav::-webkit-scrollbar{height:4px}
nav::-webkit-scrollbar-thumb{background:var(--line);border-radius:2px}
nav span{white-space:nowrap;flex:none}
/* Kopfleiste: je enger das Fenster, desto kompakter die Schalter. Sonst geht
   sie auf vier Zeilen auf und frisst den halben Bildschirm, besonders wenn
   jemand das Dashboard im Stream oder neben dem Spiel zeigt. */
@media (max-width:1600px){
 header .pill{font-size:10px;padding:4px 8px}
 header h1{font-size:13px;letter-spacing:1px}
 header .byline{display:none}
}
@media (max-width:1200px){
 header{gap:6px}
 header .pill{padding:3px 7px}
 header h1{font-size:12px;letter-spacing:0}
 nav span{padding:7px 11px}
}
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
.alert.mission{border-color:var(--green);color:var(--green)}
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
/* Item-Namen kopieren (Wallet Buddy): direkt in die EVE-Suche einfuegbar.
   Erscheint dezent und wird beim Ueberfahren der Zeile deutlich. */
.cpy{cursor:pointer;opacity:.35;margin-left:7px;user-select:none;font-size:11px}
tr:hover .cpy{opacity:.8}
.cpy:hover{opacity:1}
.cpy.ok{opacity:1;color:var(--grn,#4fd47f)}
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
/* Auswahlfeld in den Optionen. BEWUSST ohne appearance:none, damit der Browser
   seinen Aufklapp-Pfeil zeichnet. Die Pillen-Form daneben sah aus wie eine
   Beschriftung: ein Nutzer hat die Auswahl schlicht nicht als Bedienelement
   erkannt und links davon gesucht, weil dort in allen anderen Zeilen das
   Eingabefeld steht. Deshalb steht dieses hier ebenfalls links. */
select.feld{background:var(--inset);border:1px solid var(--line);color:var(--txt);
font:inherit;font-size:12px;padding:4px 8px;border-radius:8px;cursor:pointer;min-width:210px}
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
/* Spaltenkoepfe: leise, aber da. Ohne sie muss man aus den Zahlen raten,
   welche Spalte Menge, welche Volumen und welche Wert ist. */
thead th{font-size:10px;text-transform:uppercase;letter-spacing:.8px;
 color:var(--dim);font-weight:600;text-align:left;border-top:none;
 padding-top:0;padding-bottom:5px}
thead th.r{text-align:right}
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
.pistale{display:inline-block;margin-top:3px;color:var(--gold);opacity:.85}
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
.pclogo{width:20px;height:20px;vertical-align:-5px;margin-right:5px;border-radius:3px}
.alogo{width:22px;height:22px;vertical-align:-6px;margin-right:7px;border-radius:3px}
.pwatch{background:var(--red);color:#fff;border-radius:4px;padding:1px 6px;
 font-size:11px;font-weight:700;letter-spacing:.4px;white-space:nowrap}
html[data-skin=photon] .pwatch{border-radius:1px}

/* ===================================================== Cockpit-Skin (Auswahl)
   Der dritte Skin, bewusst NICHT der Standard. Jede Regel haengt an
   html[data-skin=cockpit], damit "Klassisch" Zeichen fuer Zeichen bleibt wie
   es ist und ein Umschalten nichts kaputtmachen kann.

   Am HTML wird NICHTS geaendert. Die Seitenleiste entsteht allein daraus, dass
   das vorhandene <nav> fest an den linken Rand gestellt wird und der Body
   entsprechend einrueckt. Das ist robuster als ein Raster-Umbau, weil laufend
   Elemente per JS in den Body nachwachsen und ein Raster die dann in die
   falsche Spalte setzen wuerde.

   Drei Messungen aus der laufenden Oberflaeche haben den Ausschlag gegeben:
   1. --dim kam auf 3,31:1 Kontrast, verlangt sind 4,5:1. Betroffen war
      ausgerechnet der Kleintext und die Zahlenspalten.
   2. Zellpolster 3px und Zeilenhoehe "normal" ergaben die Tabellenwand.
   3. Segoe UI Variable liegt auf Windows 11 bereit, hat aber UNGLEICH breite
      Ziffern ("111111" 31,8px gegen "888888" 45,3px). Ohne tabular-nums
      wuerde jede Zahlenspalte zappeln, deshalb steht es hier verbindlich. */
html[data-skin=cockpit]{
 --bg:#0a0f17;--card:#121a26;--inset:#0f1826;--line:#22304a;
 --txt:#e6edf7;--dim:#93a3bd;--cyan:#4cd9f5;--red:#ff8b80;--green:#5fe08f;
 --gold:#f5c451;--violet:#b39bff;--blue:#7cb2ff;--white:#fff;
 /* Kachelflaechen je Bedeutung. Der erste Anlauf tuepfelte alles mit 6 Prozent
    Tuerkis ein, das ergab auf Weiss #F2FAFD und war schlicht unsichtbar. Hier
    stehen deshalb ausgerechnete Flaechen statt Beimischungen. */
 --t-cyan:#0e2430;--t-gold:#241e0f;--t-red:#2a1615;
 --t-green:#0e2419;--t-violet:#1c1733;
 /* Eigene Groessen des Skins, damit die Klassik-Werte unberuehrt bleiben */
 --seite:236px;      /* Breite der Seitenleiste */
 --rund:12px;
 /* Abstands-Skala. Vorher standen dort gemessene 4, 10, 10, 12, 14, 16 und
    18 Pixel ohne erkennbare Ordnung, jeder Wert einzeln gewachsen. Ab hier
    ist jeder Abstand ein Vielfaches von 8, und es gibt nur drei Stufen:
    8 innerhalb einer Gruppe, 16 zwischen Gruppen, 24 zwischen Bloecken. */
 --s1:8px;
 --s2:16px;
 --s3:24px;
 --luft:var(--s3);
}
/* Im hellen Thema muss der Grund deutlich grauer sein als die Karte, sonst
   verschwimmt alles zu einer weissen Flaeche. Gemessen lagen #eef1f6 und #fff
   so dicht beieinander, dass keine Karte mehr als Karte zu erkennen war. */
/* Getoente Neutrale statt reinem Grau: eine Karte in #FFF liest sich als
   Blatt Papier, nicht als Oberflaeche. Die Farbwerte sind gegen ihre eigene
   Flaeche durchgerechnet, der schlechteste Fall liegt bei 4,9:1. */
html[data-skin=cockpit][data-theme=light]{
 --bg:#e8ecf3;--card:#fbfcfe;--inset:#edf1f7;--line:#cfd8e6;
 /* #4e5d75 kam auf der Kartenflaeche auf 4,47:1, knapp unter der Norm.
    Zwei Stufen dunkler reichen fuer 4,7:1, ohne dass der Ton grau wirkt. */
 --txt:#0f1723;--dim:#485670;--cyan:#0a6280;--red:#b32318;--green:#0f6b3f;
 --gold:#8a5a00;--violet:#5b31b0;--blue:#1d4ed8;--white:#0c1119;
 --t-cyan:#e3f1f7;--t-gold:#fbf1d9;--t-red:#fcebe8;
 --t-green:#e4f2ea;--t-violet:#eee9fb;
}
html[data-skin=cockpit] body,
html[data-skin=cockpit] dialog,
html[data-skin=cockpit] .btn,
html[data-skin=cockpit] input,
html[data-skin=cockpit] select,
html[data-skin=cockpit] textarea{
 /* Segoe UI Variable ist die moderne Variante und liegt auf Windows 11
    bereit. Faellt sie aus (Linux, aeltere Systeme), greift die Kette
    lueckenlos weiter, geladen wird nichts. */
 font-family:"Segoe UI Variable Text","Segoe UI Variable","Segoe UI",
   system-ui,-apple-system,"Noto Sans","Liberation Sans",sans-serif;
 font-variant-numeric:tabular-nums;
 -webkit-font-feature-settings:"tnum" 1;font-feature-settings:"tnum" 1;
}
/* Jeder Hauptblock haelt denselben Abstand zum naechsten. Vorher hatte jeder
   Block seinen eigenen gewachsenen Wert, deshalb gab es keinen Rhythmus. */
html[data-skin=cockpit] body>header,
html[data-skin=cockpit] body>#loadtxt,
html[data-skin=cockpit] body>#viewinfo,
html[data-skin=cockpit] body>#alerts,
html[data-skin=cockpit] body>#hero,
html[data-skin=cockpit] body>#setup,
html[data-skin=cockpit] body>#updBanner,
html[data-skin=cockpit] body>#grid{margin:0 0 var(--s3)}
html[data-skin=cockpit] body>#loadtxt{margin-bottom:var(--s1)}
/* margin-top ausdruecklich auf null: sonst addiert sich der eigene obere
   Abstand des naechsten Blocks dazu und aus 8 werden 10. */
html[data-skin=cockpit] body>*{margin-top:0}
html[data-skin=cockpit] body{
 padding:0 var(--s3) 40px calc(var(--seite) + var(--s3));
 line-height:1.5;
 /* Kein flacher Grundton. Ein weiter radialer Verlauf von oben gibt der Seite
    eine Lichtrichtung, und erst dadurch koennen Karten darauf als Ebene
    liegen statt als Umriss auf Papier. */
 background:radial-gradient(120% 78% at 50% -8%,
   color-mix(in srgb,var(--card) 78%,var(--bg)), var(--bg) 62%) fixed;
 min-height:100vh;
}
/* --------------------------------------------------- Seitenleiste aus <nav> */
html[data-skin=cockpit] nav{
 position:fixed;left:0;top:0;bottom:0;width:var(--seite);z-index:40;
 display:flex;flex-direction:column;gap:2px;align-items:stretch;
 padding:64px 10px 14px;margin:0;overflow-y:auto;overflow-x:hidden;
 background:var(--card);border:none;border-right:1px solid var(--line);
}
html[data-skin=cockpit] nav span{
 flex:none;font-size:13px;padding:9px 12px;border-radius:8px;
 border-bottom:none;white-space:nowrap;overflow:hidden;text-overflow:ellipsis;
 /* Nur der Hintergrund wird weich, NICHT die Schriftfarbe. Beim Umschalten
    des Skins aendert sich --dim, und eine laufende Farb-Transition haelt dann
    den alten Wert fest: gemessen blieb der Reiter auf dem alten #5d6b80 mit
    3,36:1 stehen, bis die Seite neu geladen wurde. */
 transition:background .12s;
}
html[data-skin=cockpit] nav span:hover{background:var(--inset);color:var(--txt)}
html[data-skin=cockpit] nav span.on{
 background:color-mix(in srgb,var(--cyan) 16%,transparent);
 color:var(--cyan);border-bottom:none;font-weight:600;
 /* Der Balken sitzt links statt unten: in einer Spalte liest sich die
    Markierung dort als "hier stehst du", unten wuerde sie wie ein Trenner
    zwischen zwei Eintraegen wirken. */
 box-shadow:inset 3px 0 0 var(--cyan);
}
/* Der Name oben in der Leiste, damit die Kopfzeile ihn nicht doppelt traegt */
html[data-skin=cockpit] nav::before{
 content:"EVE CANARY";position:absolute;top:0;left:0;right:0;
 padding:20px 14px 12px;font-size:12px;font-weight:700;letter-spacing:2.4px;
 color:var(--cyan);background:var(--card);
}
/* ------------------------------------------------------------- Kopfleiste */
html[data-skin=cockpit] header{
 position:sticky;top:0;z-index:30;gap:8px;
 padding:12px 0 10px;margin-bottom:4px;
 background:linear-gradient(var(--bg) 78%,transparent);
 border-bottom:1px solid var(--line);
}
html[data-skin=cockpit] header h1{font-size:0;margin:0;padding:0}
/* Form fuer alle Pillen, Farbe aber NUR fuer die inaktiven. Die aktive
   bekommt von der Grundregel cyan als Flaeche mit dunklem Text darauf, und das
   ist gut lesbar. Ohne das :not(.on) gewinnt diese Regel nach Spezifitaet
   gegen .pill.on und faerbt den Text hell auf hell: gemessen 1,42:1. */
html[data-skin=cockpit] .pill{border-radius:8px;font-size:12px;padding:5px 11px}
html[data-skin=cockpit] .pill:not(.on){color:var(--dim)}
/* --------------------------------------------------------------- Flaechen */
/* Zwoelf Spalten statt auto-fit. Vorher bekam jede Karte dieselbe Breite, egal
   ob sie vierzig Tabellenzeilen oder drei Zahlen enthaelt. Die Breite sagt
   jetzt etwas aus, und dense fuellt die Loecher, die unterschiedlich hohe
   Karten sonst unten stehen lassen. Die Hoechstbreite verhindert, dass auf
   einem breiten Schirm alles in die Laenge gezogen wird statt Spalten zu
   bilden. */
html[data-skin=cockpit] #grid{
 grid-template-columns:repeat(12,minmax(0,1fr));
 grid-auto-flow:row dense;
 gap:var(--s2);max-width:1780px;
}
html[data-skin=cockpit] #grid>.card{grid-column:span 4;min-width:0}
html[data-skin=cockpit] #grid>.card:has(table){grid-column:span 8}
/* Reine Kennzahlenkarten bleiben schmal, damit ihre Kacheln nicht aufblasen.
   Vier statt drei Spalten: mit span 3 neben einer span 8 blieben 137 Pixel
   uebrig, also eine leere Spalte am rechten Rand. 4 und 8 ergeben genau 12. */
html[data-skin=cockpit] #grid>.card:has(.stats):not(:has(table)):not(:has(.spark)):not(:has(.chead img)){
 grid-column:span 4;
}
/* Charakterkarten tragen Portrait, viele Kacheln und Abschnitte. Bei span 3
   wurden daraus gemessene 235 Pixel Breite auf 970 Pixel Hoehe, also eine
   Saeule. Sie brauchen die halbe Reihe. */
html[data-skin=cockpit] #grid>.card:has(.chead img){grid-column:span 6}
html[data-skin=cockpit] #grid>.card:has(svg),
html[data-skin=cockpit] #grid>.card:has(.spark),
html[data-skin=cockpit] #grid>.card.mlive{grid-column:1/-1}
/* Wenige Karten fuellen die Reihe. Mit nur einem aktiven Charakter stand die
   einzige Karte mit 814 Pixeln in einem 1644 Pixel breiten Raster, die rechte
   Haelfte blieb leer. Ein Raster, das nichts zu verteilen hat, darf nicht so
   tun als ob. */
html[data-skin=cockpit] #grid:has(>.card:only-child)>.card{grid-column:1/-1}
html[data-skin=cockpit] #grid:has(>.card:nth-child(2):last-child)>.card{grid-column:span 6}
html[data-skin=cockpit] #grid:has(>.card:nth-child(3):last-child)>.card{grid-column:span 4}
/* Die Ausnahmen brauchen dieselbe Zahl an Pseudoklassen wie die Grundregeln,
   sonst gewinnt trotz spaeterer Position die spezifischere Regel von oben:
   genau daran hing die 235-Pixel-Saeule bei 1280px Fensterbreite. */
@media(max-width:1480px){
 html[data-skin=cockpit] #grid>.card{grid-column:span 6}
 html[data-skin=cockpit] #grid>.card:has(table){grid-column:1/-1}
 html[data-skin=cockpit] #grid>.card:has(.stats):not(:has(table)):not(:has(.spark)):not(:has(.chead img)){
  grid-column:span 4;
 }
 html[data-skin=cockpit] #grid>.card:has(.chead img){grid-column:1/-1}
}
@media(max-width:1000px){
 html[data-skin=cockpit] #grid>.card,
 html[data-skin=cockpit] #grid>.card:has(.stats):not(:has(table)):not(:has(.spark)):not(:has(.chead img)){
  grid-column:1/-1;
 }
}
/* Drei Ebenen statt einer: Grund, Karte, Innenflaeche. Der erste Anlauf legte
   alles auf dieselbe Hoehe mit derselben Kantenstaerke, deshalb fand das Auge
   keinen Einstieg und die Seite wirkte gleich laut ueberall. Die Karte traegt
   jetzt einen eigenen Verlauf, eine Lichtkante oben und einen gestaffelten
   Schatten. Das ist der Unterschied zwischen Umriss und Material. */
html[data-skin=cockpit] .card{
 position:relative;isolation:isolate;
 border-radius:var(--rund);padding:var(--s2);
 border:1px solid color-mix(in srgb,var(--txt) 9%,transparent);
 background:
   linear-gradient(168deg,color-mix(in srgb,var(--txt) 4%,transparent),transparent 44%),
   var(--card);
 box-shadow:
   inset 0 1px 0 color-mix(in srgb,var(--white) 12%,transparent),
   0 1px 2px rgba(0,0,0,.22),
   0 6px 16px -8px rgba(0,0,0,.28),
   0 22px 48px -30px rgba(0,0,0,.55);
}
/* Jede Karte bekommt eine echte Kopfzeile: der bisherige fette Titel wird zur
   gesperrten Versalzeile mit Akzentkante darunter. Das ist der eine Griff, der
   aus einer Liste von Kaesten eine gegliederte Ansicht macht. */
/* Die Titel heissen je nach Ansicht <b>, div.char oder div.chead. Alle drei
   nur als erstes Element der Karte. Das :not(:has(img)) haelt die
   Charakterzeile der Live-Seite heraus: die ist ebenfalls .chead, traegt aber
   ein Portrait und soll ein Name in Lesegroesse bleiben, keine Versalzeile. */
/* Nur Karten MIT Kopfzeile verzichten oben auf den Innenabstand, weil die
   Kopfzeile selbst bis an den Rand laeuft und ihren Abstand mitbringt. Vorher
   galt padding-top:0 pauschal, dadurch klebten die Kacheln einer Karte ohne
   Kopfzeile direkt an der Oberkante. */
/* ACHTUNG: :has() darf kein weiteres :has() enthalten. Ein ungueltiger
   Selektor macht die GANZE Gruppe unwirksam, auch die gueltigen Zeilen
   daneben. Genau daran ist der erste Versuch gescheitert, ohne Fehlermeldung.
   Die Charakterkarte wird deshalb ueber :not(:has(...)) an der Karte selbst
   ausgeschlossen, das ist erlaubt. */
html[data-skin=cockpit] .card:has(>.char:first-child),
html[data-skin=cockpit] .card:has(>b:first-child){padding-top:0}
html[data-skin=cockpit] .card:has(>.chead:first-child):not(:has(.chead img)){padding-top:0}
html[data-skin=cockpit] .card>.char:first-child,
html[data-skin=cockpit] .card>.chead:first-child:not(:has(img)),
html[data-skin=cockpit] .card>b:first-child{
 display:block;margin:0 calc(var(--s2) * -1) var(--s2);padding:var(--s2) var(--s2) var(--s1);
 font-size:11px;font-weight:700;letter-spacing:1.5px;text-transform:uppercase;
 color:var(--txt);
 border-bottom:1px solid var(--line);
 border-radius:var(--rund) var(--rund) 0 0;
}
/* Der Akzentstrich NUR auf den breiten Karten. Zwanzig gleiche tuerkise
   Striche sind kein Akzent mehr, sondern Tapete. Und die 6-Prozent-Toenung
   war auf Weiss ohnehin unsichtbar (#F2FAFD), also lieber ganz weg. */
html[data-skin=cockpit] #grid>.card:has(table)>b:first-child,
html[data-skin=cockpit] #grid>.card:has(table)>.char:first-child,
html[data-skin=cockpit] #grid>.card:has(table)>.chead:first-child:not(:has(img)){
 box-shadow:inset 0 2px 0 var(--cyan);
 background:color-mix(in srgb,var(--cyan) 14%,transparent);
}
html[data-skin=cockpit] .sub{font-size:12.5px;line-height:1.6;margin-bottom:var(--s2)}
/* -------------------------------------------------- Kennzahlen als Kacheln */
/* auto-fill mit Obergrenze statt auto-fit mit 1fr. Das war die eine Zeile, die
   die leeren Rechtecke erzeugt hat: 1fr verteilt die gesamte Restbreite auf
   die verbliebenen Kacheln, in einer breiten Karte wurden aus 158px Mindest-
   breite ueber 600px, und darin stand dann eine einzelne Null. */
html[data-skin=cockpit] .stats{
 grid-template-columns:repeat(auto-fill,minmax(148px,206px));
 justify-content:start;gap:var(--s1);margin-bottom:var(--s2);
}
/* Kein Rahmen mehr, nur Flaeche mit Akzentkante links. Die Zahl ist der Held
   der Kachel: vorher stand eine 24px-Zahl in einer 89px hohen Box, das war
   viel Rand um wenig Aussage. */
/* Flacher und dichter: 95px Hoehe fuer eine einzelne Null war ein leeres
   Rechteck. Die Innenflaeche liegt als dritte Ebene ueber der Karte, mit
   eigener Lichtkante. */
html[data-skin=cockpit] .stat{
 border-radius:8px;padding:var(--s1) 12px;border:none;
 background:var(--inset);
 border-left:3px solid color-mix(in srgb,var(--dim) 34%,transparent);
 box-shadow:inset 0 1px 0 color-mix(in srgb,var(--white) 7%,transparent);
}
/* Farbe wird Information statt Schmuck: die Kante nimmt die Bedeutung der
   Zahl an, die in der Kachel steht. Vorher trug jede Kachel dieselbe
   tuerkise Kante, damit markierte sie nichts. */
html[data-skin=cockpit] .stat:has(.v.isk){
 border-left-color:var(--gold);background:var(--t-gold);
}
html[data-skin=cockpit] .stat:has(.v.grn){
 border-left-color:var(--green);background:var(--t-green);
}
html[data-skin=cockpit] .stat:has(.v.out){
 border-left-color:var(--cyan);background:var(--t-cyan);
}
html[data-skin=cockpit] .stat:has(.v.red),
html[data-skin=cockpit] .stat:has(.v.inn){
 border-left-color:var(--red);background:var(--t-red);
}
html[data-skin=cockpit] .stat .l{
 font-size:9.5px;letter-spacing:1.1px;color:var(--dim);line-height:1.3;
 text-transform:uppercase;
}
html[data-skin=cockpit] .stat .v{
 font-size:clamp(19px,1.35vw,24px);font-weight:700;margin-top:1px;line-height:1.2;
 letter-spacing:-.3px;
 /* NICHT break-word: das zerlegte "12.062.213 m³" mitten in der Zahl zu
    "12.062.2" und "13 m³", was sich wie zwei Zahlen liest. Ohne die Regel
    bricht es nur am Leerzeichen, die Zahl bleibt also am Stueck und nur die
    Einheit rutscht notfalls in die zweite Zeile. */
 overflow-wrap:normal;word-break:keep-all;
}
/* Die wichtigsten Kacheln (Bounty, Loot, Session, Tagesertrag) tragen im
   Markup ein festes style="font-size:24px". Inline schlaegt jede Regel, ohne
   !important bliebe genau der Blickfang der kleinste Wert der Seite. Statt
   ihn nur einzufangen bekommt er hier den ersten Rang: groesser als die
   uebrigen Kacheln, damit eine Rangfolge entsteht statt einer Reihe gleich
   lauter Zahlen. */
html[data-skin=cockpit] .stat .v[style]{
 font-size:clamp(26px,2.1vw,36px) !important;letter-spacing:-.5px;
 overflow-wrap:normal;word-break:keep-all;
}
/* Die Leitzahl nimmt zwei Spalten. Rangfolge muss in der FLAECHE sichtbar
   sein, nicht nur im Schriftgrad: gemessen waren vorher alle Kacheln exakt
   310x91 Pixel gross, deshalb las sich alles als gleichfoermiges Raster. */
html[data-skin=cockpit] .stats>.stat:has(.v[style]){grid-column:span 2}
/* Die oberste Kennzahlenreihe traegt repeat(3,1fr) INLINE im Markup. Inline
   schlaegt jede Regel, deshalb wurden ihre Kacheln bei 1920px Fensterbreite
   525 Pixel breit fuer eine einzelne Null. Sie darf drei Spalten behalten,
   aber nicht beliebig weit. */
/* Eine Zeile, so viele Spalten wie Kacheln, jede gedeckelt. Mit auto-fill
   legte der Browser Spuren fuer die ganze Breite an und liess die
   ueberzaehligen leer stehen, gemessen 683 Pixel weisse Flaeche neben drei
   Kacheln. Mit fest gezaehlten Spalten stimmt auch die Breite der Karte
   darum, die sonst auf eine einzige Spalte zusammenfiel. */
html[data-skin=cockpit] .stats[style]{
 grid-template-columns:none !important;
 grid-auto-flow:column;
 grid-auto-columns:minmax(190px,296px);
 justify-content:start;
}
html[data-skin=cockpit] .stats[style]>.stat:has(.v[style]){grid-column:auto}
/* Und die Karte darum schrumpft auf ihren Inhalt. Sie traegt im Markup
   grid-column:1/-1, also die volle Reihe. Bei drei Kacheln zu je 296 Pixeln
   blieben davon 683 Pixel leere weisse Flaeche rechts stehen: gemessen fuenf
   angelegte Spuren, drei davon gefuellt. Eine Flaeche, die nichts traegt,
   darf nicht so aussehen als gehoerte sie dazu. */
html[data-skin=cockpit] #hero>.card:has(>.stats[style]){
 width:fit-content;max-width:100%;
}
/* Das zweite Label unter dem Wert ist eine Fussnote, keine Ueberschrift */
html[data-skin=cockpit] .stat .v+.l{font-size:9.5px;letter-spacing:.9px;margin-top:3px}
html[data-skin=cockpit] .stat .v.isk,
html[data-skin=cockpit] .stat .v.out{color:var(--cyan)}
/* --------------------------------------------------------------- Tabellen */
html[data-skin=cockpit] table{font-size:13px}
html[data-skin=cockpit] td,
html[data-skin=cockpit] th{padding:var(--s1) 12px;vertical-align:baseline}
html[data-skin=cockpit] td:first-child,
html[data-skin=cockpit] th:first-child{padding-left:0}
html[data-skin=cockpit] td:last-child,
html[data-skin=cockpit] th:last-child{padding-right:0}
html[data-skin=cockpit] th{
 font-size:10.5px;text-transform:uppercase;letter-spacing:1px;color:var(--dim);
 font-weight:600;padding-bottom:6px;
}
/* Zebra statt Linie in jeder Zeile: das Auge folgt der Flaeche leichter als
   einem Gitter, und es nimmt der Tabelle genau das Tabellenkalkulations-
   Aussehen. Die Trennlinien bleiben trotzdem fuer den Fall, dass jemand
   Transparenz abgeschaltet hat. */
html[data-skin=cockpit] tbody tr:nth-child(odd) td,
html[data-skin=cockpit] table tr:nth-child(even) td{
 background:color-mix(in srgb,var(--txt) 3.5%,transparent);
}
html[data-skin=cockpit] td{border-top-color:color-mix(in srgb,var(--line) 55%,transparent)}
html[data-skin=cockpit] td.r{color:var(--txt);font-weight:500}
/* Abschnittsmarken bekommen eine Linie, die bis zum Rand laeuft. Sie sind die
   einzige Gliederung innerhalb einer Karte und waren vorher nur grauer Text. */
html[data-skin=cockpit] .sect{
 font-size:10px;letter-spacing:1.4px;color:var(--dim);
 margin:var(--s3) 0 var(--s1);padding-bottom:var(--s1);font-weight:600;
}
/* Steht ein Abschnitt ganz oben in einer Karte, addiert sich sein Abstand auf
   den Innenrand der Karte: gemessen 41 statt 17 Pixel. Der erste braucht ihn
   nicht, die Karte polstert bereits. */
html[data-skin=cockpit] .card>.sect:first-child{margin-top:0}
html[data-skin=cockpit] .sect+.sect{margin-top:var(--s2)
 border-bottom:1px solid color-mix(in srgb,var(--line) 70%,transparent);
}
/* Der Charaktername ist die Ueberschrift seiner Karte und muss als solche
   lesbar sein, nicht als eine Zeile unter vielen. */
html[data-skin=cockpit] .chead b,
html[data-skin=cockpit] .cname,
html[data-skin=cockpit] .chead>span:first-of-type{
 font-size:16px;font-weight:700;letter-spacing:-.2px;
}
html[data-skin=cockpit] .chead{
 padding:var(--s2) 0 var(--s1);gap:var(--s1);
 border-bottom:1px solid var(--line);margin-bottom:var(--s2);
}
/* Zahlenspalten in Tabellen sind der Grund, warum jemand herschaut. Etwas
   mehr Gewicht, damit sie sich vom Beschriftungstext daneben abheben. */
html[data-skin=cockpit] td.r{font-weight:550;letter-spacing:-.2px}
/* Hier stand .isk{color:var(--cyan)}. Das hat die Grundregel ueberschrieben,
   in der ISK-Betraege Gold tragen, und damit die zweite Farbe der Oberflaeche
   geloescht: ISK und Volumen sahen danach gleich aus, obwohl das die beiden
   wichtigsten Groessen sind. Gold bleibt Gold. */
/* ------------------------------------------------------- Barrierefreiheit */
/* Ohne sichtbaren Fokus weiss niemand, der mit der Tastatur bedient, wo er
   steht. Im Klassik-Skin steht dort outline:none, das ist ein echter Mangel
   und keine Geschmacksfrage. */
html[data-skin=cockpit] :focus-visible{
 outline:2px solid var(--cyan);outline-offset:2px;border-radius:6px;
}
html[data-skin=cockpit] .btn{border-radius:8px;font-size:12.5px;padding:6px 13px}
/* Modale Fenster mittig. Der globale Reset *{margin:0} nimmt dem Browser das
   margin:auto, mit dem er sie sonst zentriert, deshalb kleben sie oben links.
   Gemessen bei 1280px Fensterbreite: Dialog 620px breit, linker Rand 0 statt
   330. Im Cockpit stuende er damit auch noch auf der Seitenleiste. */
html[data-skin=cockpit] dialog{margin:auto}
/* ------------------------------------------------------------ Sternenkarte */
/* Die Karte der Blutspur traegt inline width:100%;height:auto und ein
   viewBox von 1000x700. Auf einem breiten Monitor waechst sie damit
   ungebremst mit: bei 2000px Fensterbreite waeren das rund 1400px Hoehe, also
   zwei Bildschirmhoehen fuer eine Uebersicht. Sie wird deshalb nach der HOEHE
   begrenzt und mittig gestellt, das Seitenverhaeltnis behaelt das SVG selbst.
   Das !important ist noetig, weil die Breite inline im Markup steht. */
html[data-skin=cockpit] #packBox svg{
 width:auto !important;max-width:100%;
 /* 520px waren zu knapp, die Systemnamen ruecken dann ineinander. 78vh laesst
    die Karte gross wirken und passt trotzdem mit Kopfzeile auf einen Schirm. */
 max-height:min(78vh,760px);
 display:block;margin:0 auto;
 border-radius:10px;
}
@media (prefers-reduced-motion:reduce){
 html[data-skin=cockpit] *{
  animation-duration:.001ms !important;animation-iteration-count:1 !important;
  transition-duration:.001ms !important;
 }
}
/* Schmales Fenster: die Leiste kostet dort mehr als sie bringt, also zurueck
   in die Zeile. Genau die Breite, ab der zwei Karten nicht mehr nebeneinander
   passen, sonst bliebe fuer den Inhalt kaum Platz. */
@media (max-width:1000px){
 html[data-skin=cockpit] body{padding:0 12px 30px}
 html[data-skin=cockpit] nav{
  position:sticky;top:0;left:auto;bottom:auto;width:auto;height:auto;
  flex-direction:row;padding:6px 0;border-right:none;
  border-bottom:1px solid var(--line);overflow-x:auto;
 }
 html[data-skin=cockpit] nav::before{display:none}
 html[data-skin=cockpit] nav span.on{box-shadow:inset 0 -3px 0 var(--cyan)}
}

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
/* margin:auto gehoert HIERHIN und nicht an einzelne Dialoge. Der globale
   Reset *{margin:0} kippt die Zentrierung, mit der der Browser modale Dialoge
   mittig setzt, und dann klebt das Popup oben links. Vorher stand das nur bei
   zwei Dialogen, jeder neue klebte wieder. So gilt es fuer alle, auch fuer
   die, die es noch nicht gibt.
   max-height plus overflow: ein langer Dialog soll in sich scrollen statt aus
   dem Bild zu laufen. */
dialog{background:var(--card);color:var(--txt);border:1px solid var(--line);border-radius:12px;
padding:20px 22px;max-width:620px;width:94%;margin:auto;
max-height:88vh;overflow-y:auto}
dialog::backdrop{background:rgba(0,0,0,.55)}
#newsGas{max-width:560px}
#obsDlg{max-width:660px}
#setDlg{max-width:720px}
/* Die Einrichtungsseite bringt ihre eigenen Farben mit und ist durchsichtig,
   damit sie in OBS ueber dem Spiel liegt. Im hellen Thema waere weisse Schrift
   auf weissem Grund unlesbar, also bekommt der Rahmen einen dunklen Boden. */
#obsFrame{display:block;width:100%;height:min(70vh,660px);border-radius:10px;
 border:1px solid var(--line);background:#0b0e14}
#newsGas p{margin:0 0 10px}
/* Danksagung an den Melder: bewusst groesser und mit Gold-Akzent, das ist
   die Botschaft, die haengen bleiben soll. */
#newsGas .thanks{font-size:14px;line-height:1.55;color:var(--txt);margin:16px 0 0;
 padding:11px 13px;border-left:3px solid var(--gold);background:var(--inset);border-radius:6px}
#newsGas .thanks b{color:var(--gold);font-size:15px}
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
<!--NOTFALL-->
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
 <h1><img src="data:image/png;base64,iVBORw0KGgoAAAANSUhEUgAAACAAAAAgCAYAAABzenr0AAAFJklEQVR42u1We0xTZxSvwfmcm24uJoKD8bpFxa5Mngpth21vmdlA3RJdtiy6uMzFseHcPz5QE4dm6BS0IM/qQB5qgWKhKmLpXCh94CQBy6MI9HVvyxtB58bOvnsRRFnCY+hfnOSX795z7/1+v3POd24OgzFjMzYJE6kal+E64ltcTxaItLZrCAqRDgFd49XIpyei+cqGZdNPXNG0VKQnkxBxkUhr3cyX6xc9/w7lw7XWTaJqskioI5Ijbje/NS3kuMYSjlfblUK1af1Ev4moMoegjChxrYX//8h1tk+EevKyUFm/8Nkncxim/JDPuku4Z7tKuAc65LydjmLeR7ZCbmB9bvg8+tvyuoX4H456kcbiPSVyocYSKkR15eWqZo/2381Yt9B2Ofh8e0Ew9MjXw8AN3hCuD629Cm4tIQtn4VXmKCR+79Qiv2VYJNCTKqGq6fXRfuPFYF9SGlznkAYAkcuGWjEGdxIxaMxkge1SAPSWhEFfSSh0SP0fGjPWCKaceoGOPIIy8OFoX3Om73Zr1poBs4QJpjQvqI53hbJYZxp5P7j+Jt2HyW/GLv+nSexBP7cnRajtcdFukybnybTzhXqiHNv+NHu6UyuXtqZ6PzKleUMb2tycxYL7v7LBKGFBbYI77NnK3r1REBZ1I3YFefuoCxAJLBiM/hT+PrLr4cP4mLiWuJgFk6i9NUqgJaJH+5qSsRhTOiJP9wJDEgb91zgj6CoMgIZkrLUmkakzZ3hB2xkm9O7+AHq+iIQ/v9wCg7u3waP9X0nL9+ycNbH068nTfJXRZ/j+u0hPRksqdo+KXHP8begsCqGJB4ZFXOeguq+HbiSEzFoN5DehYI7kgC2SCxa0mqJ4fc1bNsTf3bF56cQyoCPkAUdTnIbv68Q+oXT0SEBThi9NTEPBGbnuLw0FRy4LzJneYEpggm1HEHRt43R2fbzhUEPk+29Orv20ttJnDt857AIlwIxgEHtBZ2HwEDmNMOiS+oNVgoElE50NVILKn1bAzYPLQbHPeduYvStNOZMSoDm5anFbGjZgfiKg+ZwHKI+4gCnbD/quhgCZvYqOeghecOeEK5RTnXHQ2Sj+2t1pTHk1VsUEBBDFXIli7iynuQxHQcjp9jw2ipBJR2fO8IbKuBU0iR61Id0RyEfBcMad9lNQ7HfZ9fy+78Ycm4WCG18AX236Xlhev7hdxtnb/6TW/SjV3YWBYM/xBcNZDyg/5EyjAmXjHiJuTvEE5WEX2lcW60Jkx7wzf8y+ykZMoCfEEzoHjiLO54h8kCYvDYOewiDolQ3V/gH609mvIDGXA0fWNslKqEt0h5pf3EB93O3YfwamtUbzq8ybxiUnC0Lx3uKQxx2X3gMCtZU5HYP2fDadhZH+Vzxd++Tr0Fnwpd+l/oDo0CY+v6f/4SQkwHaLW6iZN66Ahgw/L0OSD8uQtJJFrY2pq1l2GZdlL3qKzuIw6bCIjnw/dAYwWogl0wfup2Bj6ixQmzYjAQembUApO7XulW455xKVFavEh85ST1EQ9MiCoCUFMz5Drmx4Q6CzKcMVNQsY02l3JNzZ7VcC8yhyukx5bLokjny/v7J+9J1DvbNR1TgH1xPFAnXb2hcyI/5+gjW7NZVJi7CdX0ULeFDKeVwlDn4toqJxiUhHFONVlogXOqhWnmQ5tab65FIiqFmgp4R7Fb9tdBXpbSpRlSnwpUzLlafYlIicLjSoOGS8rfxb9Z78stpXX+rIXvEz28lycW1azYXwBYwZm7FJ2L/GN0lccEwtAwAAAABJRU5ErkJggg==" alt="" width="22" height="22" style="vertical-align:-4px;margin-right:3px"> EVE <b>CANARY</b> <span class="byline">by Askend</span></h1>
 <span class="pill modesel" data-mode="mining" title="Mining-Ansicht">⛏ Mining</span><span class="pill modesel" data-mode="combat" title="PvP- und Missions-Ansicht">⚔ PvP &amp; Missionen</span>
 <span class="pill rolef on" data-role="" title="Alle Charaktere">Alle</span>
 <span class="pill rolef" data-role="mining" title="Nur Mining-Charaktere">⛏</span>
 <span class="pill rolef" data-role="mission" title="Nur Mission-Runner">🎯</span>
 <span class="pill rolef" data-role="pvp" title="Nur PvP-Charaktere">⚔</span>
 <span class="pill" id="showOffline" title="Standardmäßig zeigt Live nur eingeloggte Charaktere. Hier einschalten, um auch Offline-Charaktere zu sehen.">💤 Offline zeigen</span>
 <select class="pill" id="charFilter" title="Charakter-Filter"><option value="">Alle Charaktere</option></select>
 <span class="pill" id="collapseAll">Alle einklappen</span>
 <span class="pill" id="beltBtn" title="Ergebnisse der Bergbauvermessung einfügen und sehen, wie viel Volumen und ISK im Belt liegen">🪨 Belt auswerten</span>
 <span class="pill langsel" data-l="de" title="Deutsch">DE</span><span class="pill langsel" data-l="en" title="English">EN</span>
 <div class="pills" id="regions"></div>
 <span class="pill srv" id="srvStatus" hidden title="EVE-Server (Tranquility)"></span>
 <span class="pill upd" id="updBadge" hidden title="Neue Version verfügbar, Klick installiert sie"></span>
 <span class="pill" id="ovToggle" title="Always-on-top Mini-Overlay (Chrome, Edge, Firefox)">◱ Overlay</span>
 <span class="pill" id="obsBtn" title="Overlay fuer OBS einrichten: Aussehen waehlen, Adresse kopieren, in OBS als Browser-Quelle einfuegen. Mit Anleitung.">🎥 OBS Overlay</span>
 <span class="pill" id="uhrBtn" title="Stoppuhr fuer eine Aktivitaet: starten, pausieren, am Ende als Trip speichern. Zaehlt mit, wieviel in der Zeit gefoerdert wurde.">⏱ Stoppuhr</span>
 <span class="pill" id="setBtn" title="EVE-Einstellungen sichern, wiederherstellen und das UI eines Charakters auf andere uebertragen. Alpha.">💾 EVE-Einstellungen</span>
 <span class="pill" id="fontsize" title="Schriftgröße (3 Stufen)">A</span>
 <span class="pill" id="theme" title="Dark/Light">◐</span>
 <span class="pill" id="gear">⚙ Optionen</span>
</header>
<div id="loadbar" hidden><div></div></div>
<div id="loadtxt" hidden></div>
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
 <span data-v="wallet">🧾 Wallet Buddy</span>
 <span data-v="beute">📦 Beute</span>
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
  <label><input type="radio" name="skin" value="cockpit"> Cockpit (neu, in Erprobung: Seitenleiste statt Reiterzeile, größere Schrift, mehr Luft, höhere Kontraste)</label>
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
  <div style="display:flex;gap:6px;align-items:center;margin-top:8px">
   <input type="number" id="toolDelay" min="0" max="60" step="5" style="width:110px">
   <span class="hint" style="margin:0">Sekunden Karenz, bevor eine Modul-Warnung erscheint (0 = sofort)</span>
   <button class="btn" id="saveToolDelay">Speichern</button>
  </div>
  <div style="display:flex;gap:6px;align-items:center;margin-top:8px;flex-wrap:wrap">
   <select id="laserOffMode" class="feld">
    <option value="immer">immer, bei jeder Abschaltung</option>
    <option value="rate">nur wenn die Ausbeute einbricht</option>
    <option value="leer">nur wenn gar kein Erz mehr kommt</option>
    <option value="aus">gar nicht</option>
   </select>
   <span class="hint" style="margin:0">⛔ wann die Meldung „Laser aus, neues Ziel erfassen" kommt</span>
  </div>
  <div class="hint" style="margin:4px 0 0 2px"><b>immer</b> meldet jede Abschaltung, auch wenn du sofort nachzielst. <b>Bei Einbruch</b> meldet nur, wenn deine Ausbeute wirklich fällt, das ist der sinnvolle Standard. <b>Nur bei leer</b> ist am stillsten, verschweigt aber den Ausfall eines einzelnen von mehreren Lasern, weil die übrigen weiter liefern. Wie oft du am Ende etwas siehst, hängt stark von Flottengröße, Erz und Brockengröße ab.</div>
  <div class="hint" style="margin:4px 0 0 2px">Für Flotten-Miner: an kleinen Brocken schalten die Laser ständig ab, das ist normal und keine Störung. Canary meldet ohnehin nichts mehr, solange danach wieder Erz fließt. Wem es trotzdem zu oft blinkt, stellt hier zusätzlich eine Karenzzeit ein. Die Warnung bei einem echten Ratenverlust bleibt davon unberührt.</div>
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
  <label><input type="checkbox" id="shareOre"> Erz-Erträge für die Homepage-Statistik freigeben</label>
  <div class="hint">Standardmäßig aus. Ist es an, holt Canary einmal im Monat eine weitere leere Datei, deren Name die Größenklasse deiner Fördermenge des Vormonats trägt (zum Beispiel „ab 3 Mio m³"). Auch hier wird nichts gesendet: keine genaue Zahl, keine Kennung, keine Namen, keine Charaktere, keine Orte. Aus der Summe aller Klassen entsteht auf der Homepage eine Gesamtmenge, die bewusst als Untergrenze ausgewiesen wird. Deine eigenen Zahlen bleiben auf deinem Rechner, verraten wird allein die Größenordnung.</div>
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

<!-- Einmaliger Hinweis nach dem Update auf Gas-Mining. Wird ueber einen eigenen
     localStorage-Schluessel gemerkt und danach nie wieder gezeigt. -->
<dialog id="newsGas">
 <h2>🫧 Neu: Gas-Mining wird jetzt erkannt</h2>
 <p>Canary erfasst ab sofort auch Gas: Mykoserocin, Cytoserocin und Fullerite, roh und komprimiert.
 Menge, m³ und ISK-Wert stehen damit genauso in deiner Statistik wie beim Erz.</p>
 <p>Deine bisherigen Logs werden dafür einmalig neu eingelesen, die Gas-Ausbeute der letzten Tage
 taucht also rückwirkend auf. Nebenbei behoben: Rückstände wurden beim Gas fälschlich als Ertrag
 mitgezählt, das ist jetzt sauber getrennt.</p>
 <p class="thanks">Danke an <b>And-I</b> für die Meldung, dass Gas-Mining nicht erkannt wurde. Wenn dir
 etwas auffällt, sag Bescheid, genau so entstehen diese Verbesserungen.</p>
 <div style="text-align:right"><button class="btn" id="newsGasOk">Alles klar</button></div>
</dialog>

<!-- Belt-Auswertung. Bewusst ein eigener Dialog im festen HTML und NICHT im
     Grid: die Live-Ansicht baut sich alle zwei Sekunden neu auf und wuerde ein
     Eingabefeld darin samt Inhalt wegwerfen. -->
<dialog id="setDlg">
 <h2>💾 EVE-Einstellungen <span class="alphabanner" style="font-size:11px">ALPHA</span></h2>
 <p class="sub">EVE legt sein Fensterlayout je Charakter in einer Datei ab, dazu
 die Konto- und Grafikeinstellungen. Canary kann den ganzen Ordner sichern,
 zurueckspielen und das Layout eines Charakters auf andere uebertragen.
 <b>EVE muss dabei geschlossen sein</b>, der Client schreibt seine Einstellungen
 erst beim Beenden und wuerde sonst alles ueberschreiben.</p>
 <div id="setInhalt"></div>
 <div style="text-align:right;margin-top:10px"><button class="btn" id="setZu">Schließen</button></div>
</dialog>

<dialog id="uhrDlg">
 <h2>⏱ Stoppuhr</h2>
 <p class="sub">Fuer eine einzelne Aktivitaet: einen Belt, eine Runde Abyss, ein
 Event. Beim Speichern haelt Canary fest, wie lange es lief und wieviel in der
 Zeit gefoerdert wurde. Das ist etwas anderes als die Trips, die Canary selbst
 am Abdocken zaehlt.</p>
 <div id="uhrAn"></div>
 <div id="uhrListe" style="margin-top:12px"></div>
 <div style="text-align:right;margin-top:10px"><button class="btn" id="uhrZu">Schließen</button></div>
</dialog>

<dialog id="obsDlg">
 <h2>🎥 Overlay für OBS einrichten</h2>
 <iframe id="obsFrame" src="about:blank" title="OBS-Einrichtung"></iframe>
 <div class="btnrow" style="margin-top:10px">
  <button class="btn" id="obsTab">In eigenem Tab öffnen</button>
  <button class="btn" id="obsZu">Schließen</button>
 </div>
</dialog>

<dialog id="beltDlg">
 <h2>🪨 Was steckt in diesem Belt?</h2>
 <p class="sub">Im Spiel das Fenster „Ergebnisse der Bergbauvermessung“ öffnen, hineinklicken,
 alles markieren (Strg+A), kopieren (Strg+C) und hier einfügen. Die Spalten für Volumen,
 Wert und Entfernung darfst du mitkopieren, Canary nimmt sich nur die Mengen.</p>
 <textarea id="beltIn" rows="8" style="width:100%" placeholder="Pyroxeres II-Grade*	2.870	861 m3	69.800,00 ISK	2.352 m"></textarea>
 <div class="btnrow" style="margin-top:6px">
  <button class="btn" id="beltGo">Berechnen</button>
  <span class="sub" id="beltStat"></span>
 </div>
 <div id="beltOut" style="margin-top:10px"></div>
 <div style="text-align:right;margin-top:10px"><button class="btn" id="beltClose">Schließen</button></div>
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
// Muss ALLE Bereiche aus dem nav enthalten, sonst landet ein direkt
// aufgerufener Pfad oder die Zurueck-Taste stumm auf "live". Genau das ist
// dem Wallet-Tab passiert, er fehlte hier seit seiner Einfuehrung.
const VIEWS=['live','month','total','analyse','intel','missionen','timeline','profil','planeten','vault','wallet','beute','rechner'];
// Filament-Stufen in der Reihenfolge T1 bis T6 und die fuenf Wetterlagen. Die
// Namen sind die englischen aus dem Spiel, denn genau die schreibt Canary in
// den Namen des Laufs und liest sie dort auch wieder heraus.
const ABYSS_STUFEN=['Calm','Agitated','Fierce','Raging','Chaotic','Cataclysmic'];
const ABYSS_WETTER=['Dark','Electrical','Exotic','Firestorm','Gamma'];
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
$('#shareOre').onchange=()=>post({action:'share_ore',on:$('#shareOre').checked});
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
// Zeitraum der Wallet-Bilanz: 7, 30 oder 0 fuer "alles". Bleibt gemerkt, damit
// nicht bei jedem Start wieder umgestellt werden muss.
let walletTage=Number(localStorage.getItem('walletTage')??30);
if(![0,7,30].includes(walletTage))walletTage=30;
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
 total:{d:'Alles zusammengezählt, seit Canary mitschreibt. ISK gesamt ist Erz-Wert plus Bounties. Der Erz-Wert ist das, was dein Erz heute am Markt bringen würde, nicht das, was du damals dafür bekommen hast. Bounties sind Kopfgelder für abgeschossene NPCs. Bester Tag meint den Tag mit dem höchsten ISK-Ertrag. In den Tabellen sagen die Spaltenköpfe, welche Zahl Menge, Volumen und Wert ist.',
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
 wallet:{d:'Dein Wallet unter der Lupe. Oben die Bilanz: Einnahmen, Ausgaben und was unterm Strich bleibt, je Kategorie und umschaltbar für 7 Tage, 30 Tage oder alles. Darunter der Handel im Detail, welches Item wirklich Gewinn bringt und was Gebühren und Steuer fressen, dazu Ranglisten nach Umsatz und verkaufter Menge.',
  q:'Daten: nur über den EVE-Login, aus deinem Wallet-Journal und deinen Markt-Transaktionen. Beides ist bis zu eine Stunde alt. Die Käufe kommen aus den Transaktionen und nicht aus dem Journal, denn EVE bucht eine Kauforder schon beim Einstellen als hinterlegte Sicherheit, und die käme bei Storno zurück. Gewinn wird per FIFO gerechnet, also jeder Verkauf gegen deine ältesten Einkäufe desselben Typs. Als Handel zählen nur Sachen, die du gekauft UND verkauft hast, sonst würde dein eigenes Schiff als Riesenverlust dastehen. Was du nur verkauft hast, etwa selbst gefördertes Erz, steht deshalb in einer eigenen Liste.'},
 vault:{d:'Dein Erz in den Stationen, und der Rat, was sich mehr lohnt: roh verkaufen, komprimiert verkaufen oder einschmelzen.',
  q:'Daten: EVE-Login für den Bestand, Marktpreise von Fuzzwork. Der Einschmelz-Wert ist vorsichtig gerechnet, dein echter Erlös liegt eher darüber.'},
 rechner:{d:'Ein Preisrechner. Frachtraum im Spiel markieren, kopieren, hier einfügen, und du siehst sofort, was es an welchem Handelsplatz wert ist.',
  q:'Daten: Marktpreise von Fuzzwork für die großen Handelsplätze. Der Text, den du einfügst, bleibt auf deinem Rechner.'},
 beute:{d:'Zeigt dir, was ein Lauf eingebracht hat. Du fügst deinen Frachtraum zweimal ein, einmal vor und einmal nach der Mission oder dem Abyss, und Canary rechnet aus, was dazugekommen und was verbraucht worden ist. Das Ergebnis lässt sich mit einem Klick kopieren und passt in das Loot-Feld einer Mission.',
  q:'Daten: nur der Text, den du selbst einfügst, verglichen auf diesem Rechner. Erst wenn du auf Wert berechnen klickst, werden Marktpreise geholt, dabei gehen nur die Item-Namen raus.'}};
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
let ladeTimer=null,ladeTimer2=null;
// Sichtbares Zeichen, dass der Klick angekommen ist. Erst nach 150 ms, weil ein
// Wechsel oft in 15 ms durch ist und Balken samt Text dann nur flackern wuerden.
// Der Name kommt aus der Beschriftung des angeklickten Tabs, damit er ohne
// eigene Uebersetzungstabelle in jeder Sprache stimmt.
function ladeAn(was){
 clearTimeout(ladeTimer);clearTimeout(ladeTimer2);
 const t=$('#loadtxt');
 ladeTimer=setTimeout(()=>{
  const b=$('#loadbar');if(b)b.hidden=false;
  if(t){
   t.className='';
   t.textContent=(lang==='en'?'Loading ':'Lade ')+(was||'')+' …';
   t.hidden=false;
  }
  // Zweite Stufe: dauert es ungewoehnlich lange, sagen wir das auch. Sonst
  // sieht ein haengender Abruf genauso aus wie ein normaler.
  ladeTimer2=setTimeout(()=>{
   if(t&&!t.hidden){
    t.className='lang';
    t.textContent=(lang==='en'
      ?'Still loading '+(was||'')+' … the data fetch is taking longer than usual'
      :'Lade '+(was||'')+' … der Abruf dauert länger als sonst');
   }},1500);
 },150);
}
function ladeAus(){
 clearTimeout(ladeTimer);clearTimeout(ladeTimer2);
 const b=$('#loadbar');if(b)b.hidden=true;
 const t=$('#loadtxt');if(t){t.hidden=true;t.className='';}
}
document.querySelectorAll('nav span').forEach(el=>el.onclick=()=>{
 if(view===el.dataset.v)return;            // derselbe Tab, nichts zu tun
 document.querySelectorAll('nav span').forEach(x=>x.classList.remove('on'));
 el.classList.add('on');view=el.dataset.v;
 ladeAn(el.textContent.trim());
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
$('#saveToolDelay').onclick=async()=>{await post({action:'tool_warn_delay',seconds:Number($('#toolDelay').value)||0});syncOpts();};
$('#laserOffMode').onchange=async()=>{await post({action:'laser_off_mode',modus:$('#laserOffMode').value});syncOpts();};
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
 $('#shareOre').checked=state.share_ore===true;
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
 $('#toolDelay').value=state.tool_warn_delay??0;
 $('#laserOffMode').value=state.laser_off_mode||'rate';
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
  // Wappen nur bauen, wenn der Pfad exakt passt. So kann ueber dieses Feld
  // keine fremde Adresse ins Bild kommen, auch nicht ueber Umwege.
  const lg=(a.logo&&/^(corporations|alliances)\\/[0-9]+$/.test(a.logo))
   ? `<img class="alogo" src="https://images.evetech.net/${a.logo}/logo?size=32" alt="">` : '';
  return `<div class="alert ${a.kind}">${lg}[${t}] ${esc(a.text)}</div>`}).join('');
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
// ---- Belt auswerten (Bergbauvermessung einfuegen) ------------------------
$('#beltBtn').onclick=()=>{
 $('#beltStat').textContent='';
 $('#beltDlg').showModal();
 const t=$('#beltIn'); if(t){t.focus(); t.select();}
};
$('#beltClose').onclick=()=>$('#beltDlg').close();
$('#beltGo').onclick=async()=>{
 const en=lang==='en';
 const txt=($('#beltIn')||{}).value||'';
 // Statusfeld JEDES MAL frisch holen: der Dialog liegt zwar ausserhalb des
 // Grids, aber die Regel hat uns beim Loot schon einmal Zeit gekostet.
 const setz=s=>{const el=$('#beltStat'); if(el)el.textContent=s;};
 if(!txt.trim()){setz(en?'Nothing pasted yet.':'Noch nichts eingefügt.');return;}
 setz(en?'Calculating …':'Rechne …');
 let r;try{r=await post({action:'calc',text:txt});}catch(e){r=null;}
 if(!r||!r.ok){setz(en?'Server not reachable':'Server nicht erreichbar');return;}
 const rows=r.items||[];
 if(!rows.length){
  setz(en?'No ore recognised. Did you copy the survey window?'
        :'Kein Erz erkannt. Hast du das Vermesser-Fenster kopiert?');
  $('#beltOut').innerHTML='';
  return;
 }
 setz('');
 const gesISK=rows.reduce((s,x)=>s+x.isk,0);
 const gesCISK=rows.reduce((s,x)=>s+(x.cisk||0),0);
 // Wieviel kleiner wird die Fuhre? Nur zeigen, wenn es ueberhaupt etwas zu
 // komprimieren gibt, sonst stuende da ein sinnloses "1x".
 const schrumpf=(r.cm3>0)?(r.m3/r.cm3):0;
 // Wie lange braeuchte die Flotte dafuer? Nur zeigen, wenn gerade wirklich
 // gemint wird, sonst waere es eine erfundene Zahl.
 // Woher die Rate kommt, gehoert in die Anzeige selbst. Genau danach wurde
 // gefragt: es sind die AKTIVEN Mining-Chars, und gerechnet wird mit ihren
 // fuenf besten Minuten der letzten Stunde, nicht mit dem Schnitt. Sonst
 // zoege jedes Andocken und jeder Anflug die Rate nach unten und der Belt
 // saehe kuenstlich langwierig aus.
 const miner=(lastChars||[]).filter(c=>c.active&&autoRole(c)==='mining');
 const rate=miner.reduce((s,c)=>s+sustainedRate(c),0);
 const dauer=rate>0?(r.m3/rate):0;
 const h=Math.floor(dauer/60), m=Math.round(dauer%60);
 $('#beltOut').innerHTML=`
  <div class="stats" style="grid-template-columns:repeat(4,1fr)">
   <div class="stat"><div class="l">${en?'Volume, raw':'Volumen roh'}</div><div class="v">${fmtC(r.m3)} m³</div></div>
   <div class="stat"><div class="l">${en?'Volume, compressed':'Volumen komprimiert'}</div><div class="v">${fmtC(r.cm3)} m³</div>
    ${schrumpf>1.5?`<div class="sub">${en?'fits in':'passt in'} 1/${Math.round(schrumpf)}</div>`:''}</div>
   <div class="stat"><div class="l">${en?'Worth (Jita, instant sell)':'Wert (Jita, Sofortverkauf)'}</div><div class="v isk">${fmtM(gesCISK)}</div>
    ${Math.abs(gesCISK-gesISK)>gesISK*0.005?`<div class="sub">${en?'raw':'roh'}: ${fmtM(gesISK)}</div>`:''}</div>
   <div class="stat"><div class="l">${en?'Ore types':'Erzsorten'}</div><div class="v">${rows.length}</div></div>
  </div>
  ${rate>0?`<div class="sub" style="margin-top:6px">${en
    ? `At ${fmt(Math.round(rate))} m³/min from ${miner.length} active mining ${miner.length===1?'character':'characters'}
       (${miner.map(c=>esc(c.name)).join(', ')}) that is about <b>${h?h+' h ':''}${m} min</b> of actual lasering.
       Based on your five best minutes of the last hour, so approach and docking come on top.`
    : `Bei ${fmt(Math.round(rate))} m³/min aus ${miner.length} aktiven Mining-${miner.length===1?'Char':'Chars'}
       (${miner.map(c=>esc(c.name)).join(', ')}) sind das etwa <b>${h?h+' Std ':''}${m} min</b> reines Lasern.
       Gerechnet mit euren fünf besten Minuten der letzten Stunde, Anflug und Andocken kommen also noch dazu.`}</div>`
   :`<div class="sub" style="margin-top:6px">${en
    ? 'No mining character active right now, so there is no rate to estimate the time from.'
    : 'Gerade ist kein Mining-Char aktiv, deshalb steht hier keine Zeitschätzung.'}</div>`}
  <table style="margin-top:8px"><tr><th>${en?'Ore':'Erz'}</th><th class="r">${en?'Units':'Einheiten'}</th>
   <th class="r">${en?'m³ raw':'m³ roh'}</th><th class="r">${en?'m³ compr.':'m³ kompr.'}</th><th class="r">ISK</th></tr>`
  +rows.map(x=>`<tr><td>${esc(x.name)}${x.comp?'':` <span class="sub">${en?'(not compressible)':'(nicht komprimierbar)'}</span>`}</td>
    <td class="r">${fmt(x.qty)}</td>
    <td class="r">${fmt(x.m3)}</td><td class="r">${fmt(Math.round(x.cm3))}</td>
    <td class="r isk">${fmtM(x.cisk)}</td></tr>`).join('')
  +`</table>
  <div class="sub" style="margin-top:8px">${en
    ? 'Valued at the current Jita buy offer for the COMPRESSED ore, because that is how anyone actually hauls it. Compression is one to one in units, the whole gain sits in the volume per unit, and that factor is not the same for every ore. EVE shows its own estimated price in the survey window, which is why the totals differ a little. And of course: the ore is still in the rocks.'
    : 'Bewertet zum aktuellen Jita-Ankaufsgebot der KOMPRIMIERTEN Variante, weil so auch wirklich transportiert wird. Komprimieren ist in Stück eins zu eins, der ganze Gewinn steckt im Volumen je Stück, und der Faktor ist nicht bei jedem Erz gleich. EVE rechnet im Vermesser-Fenster mit seinem eigenen Schätzpreis, deshalb weichen die Summen etwas ab. Und natürlich: das Erz steckt noch im Fels.'}</div>
  ${(r.ohne_comp&&r.ohne_comp.length)?`<div class="sub" style="margin-top:6px">${en
    ? 'No compressed form exists for: ':'Keine komprimierte Form gibt es für: '}${r.ohne_comp.map(esc).join(', ')}. ${en
    ? 'Those keep their raw values.':'Für die stehen oben die Rohwerte.'}</div>`:''}
  ${(r.unknown&&r.unknown.length)?`<div class="sub" style="margin-top:6px">${en?'Not recognised':'Nicht erkannt'}: ${r.unknown.map(esc).join(', ')}</div>`:''}`;
 if(en)tr($('#beltOut'));
};
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
 const gd=` <a href="https://duckduckgo.com/?q=${encodeURIComponent('EVE Online '+m.name+' mission guide')}" target="_blank" rel="noopener">Guide</a>`;
 // Selbst benannt ist keine Erkennung, sondern Wissen. Deshalb kein Prozentwert,
 // sonst sieht die eigene Angabe aus wie eine Schaetzung.
 if(m.selbst)return `🔖 ${esc(m.name)} <span class="mconf">${lang==='en'?'named by you':'von dir benannt'}</span>${gd}`;
 // Fingerabdruck: ehrlich als Aehnlichkeit ausweisen, nicht als Treffer. Wer
 // "gleicht deinem Lauf vom 07.08." liest, weiss sofort, worauf das beruht.
 if(m.quelle){
  const dt=m.wie?new Date(m.wie*1000).toLocaleDateString():'';
  const wo=m.quelle==='eigen'
    ? (lang==='en'?'% like your run of '+dt:'% wie dein Lauf vom '+dt)
    : (lang==='en'?'% like a shared template':'% wie eine geteilte Vorlage');
  return `🔗 ${esc(m.name)} <span class="mconf">${lang==='en'?m.conf+wo:'zu '+m.conf+wo}</span>${gd}`;
 }
 const c=m.conf!=null?` <span class="mconf">~${m.conf}% sicher</span>`:'';
 return `🎯 ${esc(m.name)}${c}${gd}`;
}
// Ort statt Mission. Ein Abyss-Lauf ist keine Mission, deshalb eigenes Zeichen
// und kein Prozentwert: die Gegnernamen dort gibt es nirgendwo sonst, das ist
// keine Schaetzung. Ohne Prozent sieht man auch sofort den Unterschied zur
// Missionserkennung, die immer eine Genauigkeit mitfuehrt.
// Verstrichene Zeit im Abyss. Dort laeuft eine harte Grenze von 20 Minuten,
// danach ist das Schiff verloren. Ab 15 Minuten wird die Zahl rot.
function abyssUhr(c){
 if(c.abyss_min==null)return '';
 const m=Math.floor(c.abyss_min), sek=Math.floor((c.abyss_min-m)*60);
 const rot=c.abyss_min>=15?' style="color:var(--red)"':'';
 return ` <b${rot}>${m}:${String(sek).padStart(2,'0')}</b>`;
}
function siteHtml(s){
 if(!s||!s.name)return '';
 return `🌀 ${esc(s.name)}`;
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
// Heavy-Water-Status, wenn gerade nicht komprimiert wird. EVE loggt NIRGENDS,
// ob der Industriekern an ist; der einzige harte Beleg ist eine Kompression,
// die ohne aktiven Kern gar nicht zustande kaeme. Bleibt es still, sagen wir
// genau das, statt "Kern inaktiv" zu behaupten: wer nur selten komprimiert,
// laesst den Kern trotzdem laufen.
function hwQuiet(hw){
 const m=hw&&hw.quiet!=null?Math.round(hw.quiet/60):null;
 if(m==null)return lang==='en'?'no compression yet, consumption paused'
                              :'noch keine Kompression, Verbrauch pausiert';
 return lang==='en'?`no compression for ${m} min, consumption paused`
                   :`seit ${m} min keine Kompression, Verbrauch pausiert`;
}
// Verbrauch seit dem letzten Nachfuellen. Mit EVE-Login ist das die Summe der
// per ESI GEMESSENEN Rueckgaenge, also kein Schaetzwert; ohne Login bleibt nur
// die Differenz zum selbst gesetzten Anfangsbestand.
function hwUsedTitle(hw){
 if(!hw||!hw.used)return '';
 const v=fmt(hw.used), src=hw.esi?(lang==='en'?'measured via ESI':'per ESI gemessen')
                               :(lang==='en'?'vs. the amount you entered':'gegenüber dem gesetzten Bestand');
 return (lang==='en'?`Used since last refill: ${v} (${src})`
                    :`Verbraucht seit dem letzten Nachfüllen: ${v} (${src})`);
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
    <span class="char">${esc(c.name)} <span class="sys">· ${esc(c.system)}${abyssUhr(c)}${c.ship?' · '+esc(c.ship):''}</span></span>
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
   <div class="sub">${c.trips>0?'Trip '+(c.trips+1)+' · seit Abdocken':'Session'} ${c.session_min} min · ${c.depleted} Asteroiden leergebaggert${c.boost?' · '+c.boost.n+' in der Flotte':''} · Preise: ${state.price_src==='esi'?'ESI · ':''}${state.regions[state.region]}</div>
   ${dangerLine(c)}
   <div class="stats">
    <div class="stat"><div class="l">${c.trips>0?'ISK Trip':'ISK Session'}</div><div class="v isk">${fmtM(c.total_isk)}</div></div>
    <div class="stat"><div class="l">Erz (${fmt(c.m3)} m³)</div><div class="v isk">${fmtM(c.ore_isk)}</div></div>
    <div class="stat"><div class="l">m³/h</div><div class="v out">${fmt(c.m3h)}</div></div>
    ${(c.bonus&&c.bonus.n>0)?`<div class="stat" title="Lieferungen mit vervielfachtem Ertrag. Canary erkennt sie daran, dass die Menge ein exaktes Vielfaches deiner Normallieferung ist. Gezeigt wird nur der Teil, der über die Normalmenge hinausging.">
     <div class="l">Bonus-Erträge (${c.bonus.n} von ${c.bonus.von} · ${c.bonus.quote}%)</div>
     <div class="v isk">${fmtM(c.bonus.isk)}<span class="sub" style="display:block;font-weight:400">${fmt(c.bonus.m3)} m³ extra</span></div></div>`:''}
    <div class="stat"><div class="l">Laderaum ≈ ${fmt(c.hold_m3)} m³ · ${state.regions[state.region]}</div><div class="v isk">${
      c.hold_prices==='none'
       ?'<span style="color:var(--dim);font-size:12px;font-weight:400">keine Preisdaten</span>'
       :'~'+fmtM(c.hold_isk)+(c.hold_prices==='partial'?' <span style="color:var(--dim)" title="Für einzelne Erztypen fehlen Preisdaten">±</span>':'')
    }</div></div>
    ${c.heavy_water||!c.esi_linked?`<div class="stat"><div class="l">Heavy Water${c.heavy_water?' · '+c.heavy_water.core.toUpperCase():''}${c.heavy_water&&c.heavy_water.esi?' · ESI':''} ${c.heavy_water&&c.heavy_water.esi?'':`<span class="hwset" data-char="${esc(c.name)}" data-core="${c.heavy_water?c.heavy_water.core:''}" data-fill="${c.heavy_water&&c.heavy_water.fill?c.heavy_water.fill:''}" title="Bestand im Laderaum setzen">⛽</span>`}</div><div class="v ${c.heavy_water&&c.heavy_water.on&&c.heavy_water.min_left<30?'in':''}" title="${esc(hwUsedTitle(c.heavy_water))}">${c.heavy_water?fmt(c.heavy_water.units):'—'}</div><div class="l">${c.heavy_water?(c.heavy_water.on&&c.heavy_water.eta?'reicht bis ~'+new Date(c.heavy_water.eta*1000).toLocaleTimeString().slice(0,5)+' Uhr'+(c.heavy_water.src==='esi'?(lang==='en'?' (ESI usage)':' (ESI-Verbrauch)'):''):hwQuiet(c.heavy_water)):'per ⛽ setzen'}</div></div>`:''}
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
const DMG_LABEL={de:{em:'EM',therm:'Thermal',kin:'Kinetik',exp:'Explosiv',
  omni:'alle gleich'},
                 en:{em:'EM',therm:'Thermal',kin:'Kinetic',exp:'Explosive',
                     omni:'all alike'}};
function dmgList(codes){const M=DMG_LABEL[lang==='en'?'en':'de'];return (codes||[]).map(c=>M[c]||c).join('/');}
function factionHtml(f){
 if(!f||!f.fac)return '';
 const mixed=f.share!=null&&f.share<85?` <span class="fdim">~${f.share}%</span>`:'';
 const ew=f.ewar?(EWAR_LABEL[f.ewar]||f.ewar):'';
 return `<div class="ftag">
   <span class="fbadge">🛡️ ${esc(f.fac)}${mixed}</span>
   ${(f.shoot&&f.shoot.length)?`<span class="fshoot">${lang==='en'?'shoot':'schieße'} <b>${dmgList(f.shoot)}</b></span>`:''}
   ${(f.deal&&f.deal.length)?`<span class="ftank">${lang==='en'?'tank':'tanke'} <b>${dmgList(f.deal)}</b></span>`:''}
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
    <span class="char">${esc(c.name)} <span class="sys">· ${esc(c.system)}${abyssUhr(c)}${c.ship?' · '+esc(c.ship):''}</span></span>
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
      ?`<div class="mtag" style="margin-top:8px">${missionHtml(c.mission)}${c.site?' '+siteHtml(c.site):''}</div>`
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
    ${logiBlock(c)}
   </div>
  </div>`;
}

// Fernunterstuetzung. Wer Logi fliegt, teilt keinen Schaden aus und bekommt
// keine Bounty: ohne diesen Block sieht seine Karte aus, als haette er nichts
// getan. cap in GJ, die Reparaturen in Hitpoints, deshalb getrennte Zeilen.
const LOGI_LABEL={cap:'Cap',armor:'Panzerung',shield:'Schild',hull:'Struktur'};
const LOGI_EINH={cap:'GJ',armor:'HP',shield:'HP',hull:'HP'};
function logiZeile(d){
 const k=Object.keys(d||{}).filter(a=>d[a]>0);
 if(!k.length)return '';
 return k.sort((a,b)=>d[b]-d[a]).map(a=>
   (LOGI_LABEL[a]||a)+' '+fmt(d[a])+' '+(LOGI_EINH[a]||'')).join(' · ');
}
function logiBlock(c){
 const L=c.logi;
 if(!L)return '';
 const raus=logiZeile(L.out), rein=logiZeile(L.in);
 if(!raus&&!rein&&!L.unklar)return '';
 let h='<div class="sect">🔗 Fernunterstützung</div>';
 if(raus)h+='<div class="l">gegeben: '+raus+'</div>';
 if(rein)h+='<div class="l">bekommen: '+rein+'</div>';
 if(L.unklar)h+='<div class="l">ohne erkennbare Richtung: '+fmt(L.unklar)+'</div>';
 if(L.partner&&L.partner.length){
  h+='<table><tr><th>Pilot</th><th>Schiff</th><th class="r">gegeben</th><th class="r">bekommen</th></tr>'
   +L.partner.map(p=>`<tr><td>${esc(p.name)}</td><td>${esc(p.ship||'')}</td>`
   +`<td class="r">${p.out?fmt(p.out):''}</td>`
   +`<td class="r">${p.in?fmt(p.in):''}</td></tr>`).join('')+'</table>';
 }
 return h;
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
    <div class="stat" title="Erz-Wert plus Bounties. Das ist die Summe, die unten in der Spalte ISK gesamt je Charakter noch einmal aufgeteilt steht."><div class="l">ISK gesamt</div><div class="v isk">${fmtM(t.total_isk)}</div></div>
    <div class="stat" title="Was dein gefoerdertes Erz zu den heutigen Marktpreisen der gewaehlten Region bringen wuerde. Nicht das, was du damals dafuer bekommen hast."><div class="l">Erz-Wert</div><div class="v isk">${fmtM(t.ore_isk)}</div></div>
    <div class="stat" title="Kopfgeld fuer abgeschossene NPCs, so wie es im Log steht. Loot und Missionsbelohnungen sind nicht enthalten."><div class="l">Bounties</div><div class="v grn">${fmtM(t.bounty)}</div></div>
    <div class="stat" title="Gesamtvolumen des gefoerderten Erzes in Kubikmetern, unkomprimiert gerechnet."><div class="l">Erz gesamt</div><div class="v">${fmt(t.m3)} m³</div></div>
    <div class="stat" title="Der Tag mit dem hoechsten ISK-Ertrag. Das Datum steht unter den Kacheln."><div class="l">Bester Tag</div><div class="v isk">${fmtM(t.best_day.isk)}</div></div>
    <div class="stat" title="Schaden, den du ausgeteilt hast, und Schaden, den du eingesteckt hast. Beides aus dem Kampflog, ueber den gesamten Zeitraum."><div class="l">Schaden raus/rein</div><div class="v"><span class="out">${fmtM(t.dmg_out)}</span> / <span class="in">${fmtM(t.dmg_in)}</span></div></div>
   </div>
   <div class="sub">Bester Tag: ${t.best_day.day}</div>
   <div class="sub" style="margin-top:6px">ISK gesamt = Erz-Wert + Bounties. Der Erz-Wert rechnet mit den heutigen Marktpreisen, nicht mit denen von damals. Beim Zeigen auf eine Kachel steht, was genau dahintersteckt.</div>
  </div>
  <div class="card"><div class="char">Erz-Bilanz (nach Wert)</div><table>
   <thead><tr><th>Erz</th><th class="r">Menge</th><th class="r">Volumen</th><th class="r">Wert</th></tr></thead>${t.ores.map(o=>
   `<tr><td>${o.ore}<div class="bar" style="width:${100*o.isk/maxOre}%"></div></td>
    <td class="r">${fmt(o.units)}</td><td class="r">${fmt(o.m3)} m³</td><td class="r isk">${fmtM(o.isk)}</td></tr>`).join('')}</table></div>
  <div class="card"><div class="char">Pro Charakter</div><table>
   <thead><tr><th>Charakter</th><th class="r">Erz</th><th class="r">Bounties</th><th class="r">ISK gesamt</th></tr></thead>${Object.entries(t.chars).map(([n,c])=>
   `<tr><td>${esc(n)}</td><td class="r">${fmt(c.m3)} m³</td><td class="r grn">${fmtM(c.bounty)}</td><td class="r isk">${fmtM(c.ore_isk+c.bounty)}</td></tr>`).join('')}</table></div>
  <div class="card"><div class="char">Komprimiert pro Charakter</div>
   <div class="sub">Alles, was über die Schiffs-Kompression gelaufen ist</div>
   <div style="overflow-x:auto"><table>
   <thead><tr><th>Charakter</th><th>Typ</th><th class="r">Menge</th><th class="r">Volumen</th><th class="r">Wert</th></tr></thead>${t.compressed.length?t.compressed.map(k=>
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
 const tbl=rows=>'<thead><tr><th>Typ</th><th class="r">Menge</th>'
  +'<th class="r">Volumen</th><th class="r">Wert</th></tr></thead>'+rows.map(k=>
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
  <div class="sub">Alles, was ueber die Schiffs-Kompression gelaufen ist. Das Volumen ist das der komprimierten Bloecke, nicht das des Roherzes.</div>
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
   <div class="sub">Was lohnt sich am meisten pro Laderaum? Die erste Spalte entscheidet, die beiden anderen zeigen, wie viel du davon bisher gefoerdert hast.</div>
   <table><thead><tr><th>Erz</th><th class="r">ISK je m³</th>
    <th class="r">bisher gefoerdert</th><th class="r">Wert davon</th></tr></thead>${a.efficiency.map(e=>
   `<tr><td>${e.ore}</td><td class="r">${e.isk_per_m3} ISK/m³</td><td class="r">${fmt(e.m3)} m³</td><td class="r isk">${fmtM(e.isk)}</td></tr>`).join('')}</table></div>
  <div class="card"><div class="char">Stillstand-Verlust</div>
   <div class="sub">Geschätzt entgangenes ISK, weil Laser oder Drohnen standen oder die Rate einbrach (je Trip beim Docken erfasst).</div>
   <div class="v isk" style="font-size:22px">${fmtM(a.lost_isk||0)}</div></div>
  <div class="card"><div class="char">Waffen-Bilanz</div>
   <div class="sub">Womit du deinen Schaden gemacht hast, aus dem Kampflog.</div>
   <table>${a.weapons.length?'<thead><tr><th>Waffe</th><th class="r">Schaden</th></tr></thead>'+a.weapons.map(w=>
   `<tr><td>${esc(w[0])}</td><td class="r out">${fmt(w[1])} dmg</td></tr>`).join(''):'<tr><td class="r">Noch keine Kampfdaten</td></tr>'}</table></div>
  <div class="card"><div class="char">Spielzeit</div>
   <div class="sub">Die letzten 14 Tage, gerechnet aus den Zeiten in deinen Logdateien.</div>
   <table><thead><tr><th>Tag</th><th class="r">Zeit</th></tr></thead>${a.playtime.slice(-14).reverse().map(p=>
   `<tr><td>${p.day}<div class="bar" style="width:${100*p.minutes/maxP}%"></div></td>
    <td class="r">${Math.floor(p.minutes/60)}h ${p.minutes%60}m</td></tr>`).join('')}</table></div>
  <div class="card"><div class="char">Sicherheit</div>
   <div class="sub">Wer dich als Spieler angegriffen hat, ueber den gesamten Zeitraum. NPCs stehen hier nicht.</div>
   <table>${a.pvp.length?'<thead><tr><th>Angreifer</th><th class="r">Dein Charakter</th>'
    +'<th class="r">Schaden</th><th class="r">Zuletzt</th></tr></thead>'+a.pvp.map(p=>
   `<tr><td class="in">${p.attacker}</td><td class="r">${p.char}</td><td class="r">${fmt(p.dmg)} dmg</td><td class="r">${p.days[p.days.length-1]}</td></tr>`).join(''):'<tr><td>Keine Spieler-Angriffe erkannt ✓</td></tr>'}</table></div>`;
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
/* Schiffsname im Overlay. Eigene Zeile statt hinter dem System, weil im
   Stream jede Zeile schmal ist und ein Hulk sonst umbricht. Gedaempft, damit
   Name und ISK die Blicke behalten. */
.shp{font-size:9px;color:#8a97a8;line-height:1.3;margin-top:1px}
/* Flottensumme, abgesetzt durch eine Linie statt durch einen weiteren Kasten:
   im Overlay ist jeder Rahmen ein Stueck Hoehe, das im Stream fehlt. */
.sum{display:flex;align-items:center;justify-content:space-between;
 margin-top:6px;padding-top:6px;border-top:1px solid #1e2636;
 font-size:9px;letter-spacing:1.2px;color:#5d6b80;text-transform:uppercase}
.sv{text-align:right;font-size:12px;color:#35c8e8;font-weight:700;
 letter-spacing:0;text-transform:none;line-height:1.2}
.sv small{display:block;font-size:9px;color:#e8c645;font-weight:600}
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
     ${c.ship?`<div class="shp">${esc(c.ship)}</div>`:''}
     ${txt?`<div class="st ${cls==='bad'?'bad':''}">${txt}</div>`:''}</span>
     <span class="val">${fmtM(c.total_isk)}<small>${fmt(c.m3h)} m³/h</small></span></div>`;}).join('')+
   // Flottensumme. Im Stream ist das die Zahl, nach der im Chat gefragt wird:
   // was hat die Truppe zusammen geholt. Einzelwerte stehen darueber, hier
   // zaehlt nur das Ergebnis. Nur zeigen, wenn wirklich gefoerdert wurde,
   // sonst steht dort eine leere Null herum.
   (()=>{const m3=d.chars.reduce((s,c)=>s+(c.m3||0),0);
     const isk=d.chars.reduce((s,c)=>s+(c.ore_isk||0),0);
     if(!m3)return '';
     return `<div class="sum"><span>${d.chars.length} ${d.chars.length===1?'Char':'Chars'}</span>
      <span class="sv">${fmtC(m3)} m³<small>${fmtM(isk)} ISK</small></span></div>`;})()+
   alerts.map(a=>`<div class="al ${a.kind}">[${new Date(a.ts*1000).toLocaleTimeString()}] ${esc(a.text)}</div>`).join('');
  // Das Overlay ist ein EIGENES Dokument, tr(document.body) erreicht es nicht.
  if(lang!=='de')tr(doc.body);
 }catch(e){}
}
setInterval(overlayTick,2000);
// Nur wenn der Dialog offen ist: sonst baut der Takt staendig HTML, das
// niemand sieht.
setInterval(()=>{const d=$('#uhrDlg'); if(d&&d.open)uhrMalen();},1000);
$('#ovToggle').onclick=toggleOverlay;
$('#obsBtn').onclick=()=>{
 const f=$('#obsFrame');
 if(f.getAttribute('src')!=='/obs') f.setAttribute('src','/obs');
 $('#obsDlg').showModal();
};
$('#obsZu').onclick=()=>$('#obsDlg').close();

/* Stoppuhr. Die Summen fuer m3 und ISK kommen von hier mit: sie werden in der
   Live-Ansicht gerechnet, nicht auf der Sitzung gehalten. Beide Seiten aus
   derselben Quelle zu speisen ist sicherer, als sie im Server ein zweites Mal
   auszurechnen. */
function uhrSummen(){
 const cs=(state && state.chars || []).filter(c=>c.active);
 return {m3:cs.reduce((a,c)=>a+(c.m3||0),0),
         isk:cs.reduce((a,c)=>a+(c.ore_isk||0),0)};
}
function uhrZeit(sek){
 const h=Math.floor(sek/3600), m=Math.floor(sek%3600/60), s2=Math.floor(sek%60);
 return (h?h+':':'')+String(m).padStart(h?2:1,'0')+':'+String(s2).padStart(2,'0');
}
async function uhrTun(was,extra){
 const r=await post({action:'uhr',was,...uhrSummen(),...(extra||{})});
 if(r&&r.uhr&&state)state.uhr=r.uhr;
 uhrMalen(); uhrListeMalen();
}
function uhrMalen(){
 const box=$('#uhrAn'); if(!box)return;
 const u=(state&&state.uhr)||{an:false,sek:0,label:'',pause:false};
 if(!u.an){
  box.innerHTML=`<div class="btnrow" style="align-items:center;gap:8px">
    <input id="uhrLabel" type="text" placeholder="Wofür? z.B. Belt Gisleres, Abyss T4"
     style="flex:1;min-width:220px">
    <button class="btn" id="uhrStart">▶ Starten</button></div>`;
  $('#uhrStart').onclick=()=>uhrTun('start',{label:$('#uhrLabel').value});
  $('#uhrLabel').onkeydown=(e)=>{if(e.key==='Enter')$('#uhrStart').click();};
  return;
 }
 box.innerHTML=`<div class="btnrow" style="align-items:center;gap:10px">
   <span style="font-size:26px;font-weight:700;color:var(--cyan);font-variant-numeric:tabular-nums">${uhrZeit(u.sek)}</span>
   <span class="sub">${esc(u.label||'Trip')}${u.pause?' · pausiert':''}</span>
   <span style="margin-left:auto"></span>
   <button class="btn" id="uhrPause">${u.pause?'▶ Weiter':'⏸ Pause'}</button>
   <button class="btn" id="uhrSpeichern">✔ Trip speichern</button>
   <button class="btn warn" id="uhrWeg">Verwerfen</button></div>`;
 $('#uhrPause').onclick=()=>uhrTun(u.pause?'weiter':'pause');
 $('#uhrSpeichern').onclick=()=>uhrTun('speichern');
 $('#uhrWeg').onclick=()=>{if(confirm('Stoppuhr verwerfen? Der Trip wird nicht gespeichert.'))uhrTun('verwerfen');};
}
async function uhrListeMalen(){
 const box=$('#uhrListe'); if(!box)return;
 let d; try{ d=await (await fetch('/data?view=uhr',{cache:'no-store'})).json(); }catch(e){ return; }
 const l=d.uhr_liste||[];
 box.innerHTML=l.length?`<div class="sect">Gespeicherte Trips</div><table>
  <thead><tr><th>Wann</th><th>Wofür</th><th class="r">Dauer</th><th class="r">Erz</th><th class="r">Wert</th><th></th></tr></thead>`
  +l.map(x=>`<tr><td>${new Date(x.end*1000).toLocaleString().slice(0,16)}</td>
   <td>${esc(x.label)}${x.unsicher?'<span title="Während des Trips wurde eine Sitzung zurückgesetzt (Andocken). Erz und Wert sind deshalb der Stand am Ende, nicht die Differenz." style="color:var(--gold)"> *</span>':''}</td>
   <td class="r">${uhrZeit(x.sek)}</td><td class="r">${fmt(x.m3)} m³</td>
   <td class="r isk">${fmtM(x.isk)}</td>
   <td class="r"><span class="uhrweg" data-id="${x.id}" style="cursor:pointer;color:var(--dim)">✕</span></td></tr>`).join('')
  +'</table>'
  +(l.some(x=>x.unsicher)?'<div class="sub" style="margin-top:6px">* Während dieser Trips wurde eine Sitzung zurückgesetzt. Erz und Wert sind dann der Stand am Ende statt der Differenz.</div>':'')
  :'<div class="sub">Noch keine Trips gespeichert.</div>';
 box.querySelectorAll('.uhrweg').forEach(e=>e.onclick=async()=>{
  await post({action:'uhr_weg',id:parseInt(e.dataset.id,10)}); uhrListeMalen();});
}
$('#uhrBtn').onclick=()=>{uhrMalen();uhrListeMalen();$('#uhrDlg').showModal();};

/* EVE-Einstellungen. Jede schreibende Aktion sichert vorher automatisch, das
   macht der Server. Hier wird nur gefragt und angezeigt. */
let setDaten=null, setOrdner=null;
function setZeit(t){return new Date(t*1000).toLocaleString().slice(0,16);}
async function setLaden(){
 const box=$('#setInhalt'); if(!box)return;
 box.innerHTML='<div class="sub">wird gelesen …</div>';
 let d; try{ d=await post({action:'settings',was:'liste'}); }catch(e){ d=null; }
 if(!d||!d.ok||!d.ordner||!d.ordner.length){
  box.innerHTML='<div class="sub">Kein EVE-Einstellungsordner gefunden. '
   +'Canary sucht ihn unter AppData (Windows), Application Support (Mac) und '
   +'im Wine-Präfix (Linux).</div>'; return;
 }
 setDaten=d;
 // Merken, welcher Ordner gewaehlt ist, sonst springt die Auswahl bei jedem
 // Neuaufbau zurueck.
 if(!setOrdner||!d.ordner.some(x=>x.pfad===setOrdner)) setOrdner=d.ordner[0].pfad;
 const o=d.ordner.find(x=>x.pfad===setOrdner);
 const chars=o.dateien.filter(f=>f.art==='char');
 const warn=d.eve_laeuft===true
  ? '<div class="cardwarn" style="margin-bottom:10px">⚠ EVE läuft gerade. '
    +'Sichern geht, Zurückspielen und Übertragen sind gesperrt: der Client '
    +'würde beim Beenden alles überschreiben.</div>' : '';
 box.innerHTML=warn
  +`<div class="sect">Ordner</div>`
  +(d.ordner.length>1
    ? `<div class="btnrow" style="align-items:center;gap:8px">
        <select id="setOrdnerWahl">${d.ordner.map(x=>
          `<option value="${esc(x.pfad)}"${x.pfad===o.pfad?' selected':''}>${esc(x.eltern)} / ${esc(x.name)}</option>`).join('')}</select>
        <span class="sub">${d.ordner.length} Profile gefunden</span></div>`
    : '')
  +`<div class="sub" style="word-break:break-all">${esc(o.pfad)}</div>
    <table><thead><tr><th>Datei</th><th>Charakter</th><th class="r">Größe</th><th class="r">Stand</th></tr></thead>`
  +o.dateien.map(f=>`<tr><td>${esc(f.datei)}</td>
     <td>${f.name?esc(f.name):'<span class="sub">'+(f.art==='user'?'Konto':'unbekannt')+'</span>'}</td>
     <td class="r">${f.kb} KB</td><td class="r">${setZeit(f.stand)}</td></tr>`).join('')
  +`</table>
    <div class="btnrow" style="margin-top:10px"><button class="btn" id="setSichern">💾 Jetzt sichern</button>
     <span class="sub" id="setStat"></span></div>

    <div class="sect" style="margin-top:16px">UI von einem Charakter übertragen</div>
    <div class="sub">Das Fensterlayout der Quelle wird auf die angekreuzten Charaktere kopiert. Vorher wird automatisch gesichert.</div>`
  +(chars.length<2
    ? '<div class="sub">Dafür braucht es mindestens zwei Charaktere im Ordner.</div>'
    : `<div class="btnrow" style="align-items:center;gap:8px;margin-top:6px">
        <span class="sub">von</span>
        <select id="setQuelle">${chars.map(f=>`<option value="${esc(f.datei)}">${esc(f.name||f.id)}</option>`).join('')}</select>
       </div>
       <div style="margin-top:6px">${chars.map(f=>`<label style="display:inline-flex;align-items:center;gap:6px;margin-right:14px">
         <input type="checkbox" class="setZiel" value="${esc(f.datei)}"> ${esc(f.name||f.id)}</label>`).join('')}</div>
       <div class="btnrow" style="margin-top:6px"><button class="btn" id="setKopieren">→ Übertragen</button></div>`)

    +`<div class="sect" style="margin-top:16px">Sicherungen</div>`
  +(d.sicherungen.length
    ? '<div class="sub">Ganz zurückspielen, oder aufklappen und einzelne Charaktere auswählen. Der aktuelle Stand wird vorher gesichert.</div>'
      +d.sicherungen.map((b,i)=>{
        const chars=(b.inhalt||[]).filter(x=>x.art==='char');
        return `<div style="border-top:1px solid var(--line);padding:8px 0">
         <div style="display:flex;align-items:center;gap:10px;flex-wrap:wrap">
          <b>${setZeit(b.stand)}</b>
          <span class="sub">${b.kb} KB · ${(b.inhalt||[]).length} Dateien</span>
          <span style="margin-left:auto"></span>
          ${chars.length?`<span class="setAuf" data-i="${i}" style="cursor:pointer;color:var(--cyan);font-size:12px">▸ einzeln</span>`:''}
          <button class="btn setZurueck" data-f="${esc(b.datei)}">alles zurückspielen</button>
         </div>
         <div class="setEinzeln" data-i="${i}" hidden style="margin-top:6px">
          ${chars.map(c=>`<label style="display:inline-flex;align-items:center;gap:6px;margin-right:14px">
            <input type="checkbox" class="setEinzelHaken" data-i="${i}" value="${esc(c.datei)}">
            ${esc(c.name||c.id)}</label>`).join('')}
          <div class="btnrow" style="margin-top:6px">
           <button class="btn setEinzelGo" data-i="${i}" data-f="${esc(b.datei)}">nur diese zurückspielen</button>
          </div>
         </div></div>`;}).join('')
    : '<div class="sub">Noch keine Sicherung vorhanden.</div>');

 const wahl=$('#setOrdnerWahl');
 if(wahl)wahl.onchange=()=>{setOrdner=wahl.value;setLaden();};
 const stat=(t)=>{const e=$('#setStat'); if(e)e.textContent=t;};
 $('#setSichern').onclick=async()=>{
  stat('sichert …');
  const r=await post({action:'settings',was:'sichern',ordner:o.pfad});
  stat(r.ok?('gesichert: '+r.gesichert.dateien+' Dateien'):('ging nicht: '+(r.msg||'')));
  if(r.ok)setLaden();
 };
 const kop=$('#setKopieren');
 if(kop)kop.onclick=async()=>{
  const quelle=$('#setQuelle').value;
  const ziele=[...document.querySelectorAll('.setZiel:checked')].map(e=>e.value)
    .filter(z=>z!==quelle);
  if(!ziele.length){stat('kein Ziel angekreuzt');return;}
  const namen=chars.filter(c=>ziele.includes(c.datei)).map(c=>c.name||c.id);
  if(!confirm('Das Layout wird auf '+namen.join(', ')+' übertragen. '
    +'Die bisherigen Einstellungen dieser Charaktere werden ersetzt. '
    +'Vorher wird automatisch gesichert. Fortfahren?'))return;
  stat('überträgt …');
  const r=await post({action:'settings',was:'kopieren',ordner:o.pfad,quelle,ziele});
  stat(r.ok?('übertragen auf '+r.kopiert+' Charakter(e)'):('ging nicht: '+(r.msg||'')));
  setLaden();
 };
 document.querySelectorAll('.setZurueck').forEach(b=>b.onclick=async()=>{
  if(!confirm('Die GANZE Sicherung zurückspielen? Damit werden auch die '
    +'anderen Charaktere auf diesen Stand gesetzt. Der aktuelle Stand wird '
    +'vorher gesichert, geht also nicht verloren.'))return;
  stat('spielt zurück …');
  const r=await post({action:'settings',was:'zurueck',ordner:o.pfad,
                      sicherung:b.dataset.f});
  stat(r.ok?('zurückgespielt: '+(r.dateien||[]).length+' Dateien'):('ging nicht: '+(r.msg||'')));
  setLaden();
 });
 document.querySelectorAll('.setAuf').forEach(a=>a.onclick=()=>{
  const k=document.querySelector('.setEinzeln[data-i="'+a.dataset.i+'"]');
  k.hidden=!k.hidden;
  a.textContent=(k.hidden?'▸':'▾')+' einzeln';
 });
 document.querySelectorAll('.setEinzelGo').forEach(b=>b.onclick=async()=>{
  const haken=[...document.querySelectorAll('.setEinzelHaken[data-i="'+b.dataset.i+'"]:checked')];
  if(!haken.length){stat('kein Charakter angekreuzt');return;}
  const namen=haken.map(h=>h.parentElement.textContent.trim());
  if(!confirm('Nur '+namen.join(', ')+' auf diesen Stand zurücksetzen? '
    +'Die anderen Charaktere bleiben, wie sie sind.'))return;
  stat('spielt zurück …');
  const r=await post({action:'settings',was:'zurueck',ordner:o.pfad,
    sicherung:b.dataset.f, dateien:haken.map(h=>h.value)});
  stat(r.ok?('zurückgespielt: '+(r.dateien||[]).join(', ')):('ging nicht: '+(r.msg||'')));
  setLaden();
 });
}
$('#setBtn').onclick=()=>{setLaden();$('#setDlg').showModal();};
$('#setZu').onclick=()=>$('#setDlg').close();
$('#uhrZu').onclick=()=>$('#uhrDlg').close();
$('#obsTab').onclick=()=>window.open('/obs','_blank','noopener');
// Beim Schliessen entladen, damit die Abfrage im Hintergrund wirklich aufhoert.
$('#obsDlg').addEventListener('close',()=>$('#obsFrame').setAttribute('src','about:blank'));
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
// Sicherheitsfarben wie im Spiel: EVE faerbt den Status in festen Stufen, und
// jeder Spieler liest sie im Schlaf. Eine eigene Skala waere hier nur
// Eigensinn, deshalb genau diese Werte.
function secFarbe(s){
 if(s==null)return '#8a99ab';
 if(s>=0.95)return '#2fefef';
 if(s>=0.85)return '#48f0c0';
 if(s>=0.75)return '#00ef47';
 if(s>=0.65)return '#00f000';
 if(s>=0.55)return '#8fef2f';
 if(s>=0.45)return '#efef00';
 if(s>=0.35)return '#d77700';
 if(s>=0.25)return '#f06000';
 if(s>=0.15)return '#f04800';
 if(s>0)     return '#d73000';
 return '#f00000';
}
function packMapSvg(mp,en){
 const S=mp.systems||[];
 // Die Karte bleibt schwarz, auch im hellen Thema. Eine Sternenkarte ist im
 // Spiel schwarz, und der Sicherheitsstatus ist nur auf dunklem Grund zu
 // lesen: 0.5-Gelb auf Weiss kaeme auf keinen brauchbaren Kontrast.
 const grund=`<rect x="0" y="0" width="1000" height="700" fill="#04070c"/>`;
 const edges=(mp.edges||[]).map(e=>{const a=S[e[0]],b=S[e[1]];
  return `<line x1="${a.x}" y1="${a.y}" x2="${b.x}" y2="${b.y}" stroke="#2b7f96" stroke-width="1" stroke-opacity=".85"/>`;}).join('');
 // Kill-Spur je Rudel: verbundene Segmente, aeltere Abschnitte blasser.
 const trails=(mp.trails||[]).map(t=>{
  let seg='';
  for(let i=1;i<t.pts.length;i++){const a=t.pts[i-1],b=t.pts[i];
   const op=Math.max(0.25,1-(a.age/7200));
   // Feste Rotwerte statt var(--red): auf dem schwarzen Kartengrund muss die
   // Spur in beiden Themen gleich kraeftig stehen.
   seg+=`<line x1="${a.x}" y1="${a.y}" x2="${b.x}" y2="${b.y}" stroke="#ff4136" stroke-width="2.2" stroke-opacity="${op.toFixed(2)}"/>`;}
  if(t.pts.length){const last=t.pts[t.pts.length-1];
   seg+=`<circle cx="${last.x}" cy="${last.y}" r="7" fill="none" stroke="#ff4136" stroke-width="2.2"><title>${esc(t.label)}</title></circle>`;}
  return seg;}).join('');
 const arrows=(mp.arrows||[]).map(a=>
  `<line x1="${a.x1}" y1="${a.y1}" x2="${a.x2}" y2="${a.y2}" stroke="#ff4136" stroke-width="1.8" stroke-dasharray="6 4"><title>${en?'estimated from kill order':'aus Kill-Reihenfolge geschätzt'}</title></line>`).join('');
 const dots=S.map(s=>{
  const sf=secFarbe(s.sec);
  const heat=s.heat?`<circle cx="${s.x}" cy="${s.y}" r="${Math.min(9+s.heat*2,20)}" fill="#ff3b30" fill-opacity="0.18"/>`:'';
  // Eigener Standort wie im Spiel: heller Punkt mit Hof, nicht nur ein Ring.
  const own=s.own?`<circle cx="${s.x}" cy="${s.y}" r="13" fill="#7fd8ff" fill-opacity=".14"/>`
    +`<circle cx="${s.x}" cy="${s.y}" r="8" fill="none" stroke="#cfefff" stroke-width="1.6"/>`:'';
  // fill ausdruecklich setzen: auf dem schwarzen Kartengrund erbte das Zeichen
  // sonst Schwarz und war unsichtbar, gemessen rgb(0,0,0).
  const pk=(s.packs&&s.packs.length)?`<text x="${s.x}" y="${s.y-11}" text-anchor="middle" fill="#ff4136" style="font-size:13px">🩸</text>`:'';
  const nm=esc(s.name||'');
  // Name und Sicherheitsstatus nebeneinander, der Status in seiner Farbe:
  // genau die Anordnung, die man aus der Sternenkarte kennt.
  const beschriftung=`<text x="${s.x+8}" y="${s.y+4}" style="font-size:11px;`
   +`font-family:Consolas,'Cascadia Mono',monospace;fill:${s.own?'#eaf6ff':'#b9c9d6'}">`
   +`${nm}${s.sec!=null?` <tspan fill="${sf}">${(+s.sec).toFixed(1)}</tspan>`:''}</text>`;
  return heat+own
   +`<circle cx="${s.x}" cy="${s.y}" r="3.2" fill="${sf}"><title>${nm} · Sec ${s.sec!=null?s.sec:'?'}`
   +`${s.jumps!=null?` · ${s.jumps} ${en?'jumps':'Sprünge'}`:''}${s.heat?` · ${s.heat} Kills/2h`:''}</title></circle>`
   +pk+beschriftung;}).join('');
 return `<div style="overflow-x:auto"><svg viewBox="0 0 1000 700" style="width:100%;height:auto">${grund}${edges}${trails}${arrows}${dots}</svg></div>`
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
   // Offizielles Corp-Logo (bei Allianz-Rudeln zusaetzlich das Allianz-Logo),
   // gleiche Bildquelle wie Portraits und Schiffsbilder.
   const logo=p.corp_id?`<img class="pclogo" src="https://images.evetech.net/corporations/${encodeURIComponent(p.corp_id)}/logo?size=32" alt="" loading="eager">`:'';
   // Bei einer gelisteten Gruppe deren Wappen zeigen, nicht die haeufigste
   // Allianz des Rudels: sonst passt das Bild nicht zum Namen daneben.
   const wid=p.achtung&&p.achtung.art==='alliance'?p.achtung.id:(p.achtung?null:p.alli_id);
   const alogo=wid?`<img class="pclogo" src="https://images.evetech.net/alliances/${encodeURIComponent(wid)}/logo?size=32" alt="" title="${en?'alliance':'Allianz'}">`:'';
   return `<div class="pinear"><span class="pidot ${cls}"></span>
     <b style="color:var(--${col});flex:none">${trend} ${en?'jumps':'Sprünge'}</b>
     <span class="pinearmid">${w}${logo}${alogo}[${esc(p.label)}] · ${p.members} ${en?'pilots':'Piloten'} · ${en?'last seen':'zuletzt'} ${packAge(now-p.last_seen,en)} in ${esc(p.last_system)}</span>
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
   const nm=it.mission?missionHtml(it.mission):(it.site?siteHtml(it.site):(lang==='en'?'<b>Combat</b>':'<b>Kampf</b>'));
   return `<div class="tlrow live"><span class="tlt">${now}</span><span><span class="tllive">●</span> ${lang==='en'?'live':'läuft'} ⚔ ${nm} · ${it.kills} Kills · <span class="isk">${fmtM(it.bounty)}</span> · ${it.min} min${it.sys&&it.sys!=='?'?' · '+esc(it.sys):''}</span></div>`;
  }
  return `<div class="tlrow live"><span class="tlt">${now}</span><span><span class="tllive">●</span> ${lang==='en'?'mining now':'am Minen'} ⛏ ${fmt(it.m3)} m³ · <span class="isk">${fmtM(it.isk)}</span> · ${it.min} min${it.ore?' · '+esc(it.ore):''}${it.sys&&it.sys!=='?'?' · '+esc(it.sys):''}</span></div>`;
 }
 if(it.kind==='mine')
  return `<div class="tlrow"><span class="tlt">${t}</span><span>⛏ <b>Mining-Trip</b> ${fmt(it.m3)} m³ · <span class="isk">${fmtM(it.isk)}</span> · ${it.min} min${it.ore?' · '+esc(it.ore):''}${it.sys&&it.sys!=='?'?' · '+esc(it.sys):''}</span></div>`;
 if(it.kind==='combat'){
  const nm=it.mission?missionHtml(it.mission):(it.site?siteHtml(it.site):(lang==='en'?'<b>Combat</b>':'<b>Kampf</b>'));
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
  // Ohne Aktivitaet ist jede Achse null und das Radar ein Punkt. Dann lieber
  // sagen warum, statt eine leere Form zu zeigen: der Charakter FEHLTE hier
  // frueher ganz, und das sah aus wie eine Obergrenze.
  const radar=p.leer
   ?`<div class="sbradar"><div class="sub" style="text-align:center;padding:22px 8px;line-height:1.5">${en
      ?'No measurable activity in the last 30 days.<br>Haulers, scouts and pure boosters end up here: Canary can only see mining, combat and compression.'
      :'Keine messbare Aktivität in den letzten 30 Tagen.<br>Transporter, Späher und reine Booster landen hier: Canary sieht nur Fördern, Kampf und Komprimieren.'}</div></div>`
   :`<div class="sbradar"><div class="sub" style="text-align:center;margin-bottom:2px">${en?'focus':'Schwerpunkt'}: ${esc(L[top.key]||top.key)}</div>${radarSvg(p.axes)}</div>`;
  html+=`<div class="card"><div class="steckbrief">${info}${radar}</div></div>`;
 }
 $('#grid').innerHTML=html;
}
// Wallet Buddy: Handels-Auswertung plus Herkunft der Einnahmen.
function renderWallet(w){
 w=w||{};
 const en=lang==='en';
 if(!w.trades){
  $('#grid').innerHTML='<div class="card" style="grid-column:1/-1"><div class="sub">'
   +(en?'No wallet data yet. Connect your characters via the EVE login (⚙ Options). After the first sync (up to 1 hour) your trades appear here.'
       :'Noch keine Wallet-Daten. Verbinde deine Chars per EVE-Login (⚙ Optionen). Nach dem ersten Abgleich (bis zu 1 Stunde) erscheinen hier deine Geschäfte.')+'</div></div>';
  return;
 }
 const g=w.gruppen||{};
 const kachel=(l,v,cls)=>`<div class="stat"><div class="l">${l}</div><div class="v ${cls||''}">${v}</div></div>`;
 const vz=n=>(n>=0?'grn':'in');
 // Namen der Buchungs-Kategorien an EINER Stelle, damit Bilanz und die alte
 // Herkunfts-Tabelle nie auseinanderlaufen.
 const KAT=en?{handel:'Market trades',gebuehren:'Fees & tax',bounty:'Bounty & missions',
               industrie:'Industry',planeten:'Planetary',vertraege:'Contracts',
               versicherung:'Insurance',geschenke:'Donations',skills:'Skills',
               hypernet:'Hypernet',reparatur:'Repairs',klone:'Clones',
               belohnungen:'Rewards',direkthandel:'Direct trades',sonstiges:'Other'}
            :{handel:'Markt-Geschäfte',gebuehren:'Gebühren & Steuer',bounty:'Bounty & Missionen',
              industrie:'Industrie',planeten:'Planeten',vertraege:'Verträge',
              versicherung:'Versicherung',geschenke:'Spenden',skills:'Skills',
              hypernet:'Hypernet',reparatur:'Reparaturen',klone:'Klone',
              belohnungen:'Belohnungen',direkthandel:'Direkthandel',sonstiges:'Sonstiges'};

 // ---- Zeitraum-Umschalter -------------------------------------------------
 const ZR=[[7,en?'7 days':'7 Tage'],[30,en?'30 days':'30 Tage'],[0,en?'all':'alles']];
 let h0=`<div class="card" style="grid-column:1/-1"><div class="mfphead">
   <span class="mfptitle">${en?'Period':'Zeitraum'}</span>
   <span>`+ZR.map(([t,l])=>`<span class="pill wtage${walletTage===t?' on':''}" data-wt="${t}">${l}</span>`).join(' ')
   +`</span></div></div>`;
 // ---- Bilanz: Einnahmen, Ausgaben, Saldo ---------------------------------
 const B=w.bilanz;
 if(B&&(B.ein||B.aus)){
  const zeile=(x,cls)=>`<tr><td>${KAT[x.k]||x.k}</td><td class="r ${cls}">${fmtM(x.isk)}</td></tr>`;
  h0+=`<div class="card" style="grid-column:1/-1"><div class="chead">
    <span class="char">⚖️ ${en?'Income and spending':'Einnahmen und Ausgaben'}</span>
    <span class="sub">· ${B.von?new Date(B.von*1000).toLocaleDateString():''} ${en?'to':'bis'} ${B.bis?new Date(B.bis*1000).toLocaleDateString():''}</span></div>
   <div class="stats" style="grid-template-columns:repeat(3,1fr)">
    ${kachel(en?'Income':'Einnahmen',fmtM(B.ein)+' ISK','grn')}
    ${kachel(en?'Spending':'Ausgaben','-'+fmtM(B.aus)+' ISK','in')}
    ${kachel(en?'Balance':'Saldo',fmtM(B.saldo)+' ISK',vz(B.saldo))}
   </div>
   <div class="advrow" style="margin-top:10px">
    <div style="flex:1"><div class="l" style="margin-bottom:4px">${en?'Income by category':'Einnahmen nach Kategorie'}</div>
     <table>${(B.ein_kat||[]).map(x=>zeile(x,'grn')).join('')}</table></div>
    <div style="flex:1"><div class="l" style="margin-bottom:4px">${en?'Spending by category':'Ausgaben nach Kategorie'}</div>
     <table>${(B.aus_kat||[]).map(x=>zeile(x,'in')).join('')}</table></div>
   </div>
   <div class="sub" style="margin-top:8px">${en
     ? `Purchases come from your transactions, not from the journal: EVE books a buy order the moment you place it, as escrow, and that money would come back on cancellation. ${B.geparkt?`Currently ${fmtM(B.geparkt)} ISK are parked in open buy orders and count as neither income nor spending.`:''}`
     : `Die Käufe stammen aus deinen Transaktionen und nicht aus dem Journal: EVE bucht eine Kauforder schon beim Einstellen als Sicherheit, und das Geld käme bei Storno zurück. ${B.geparkt?`Aktuell liegen ${fmtM(B.geparkt)} ISK in offenen Kauforders, die zählen weder als Einnahme noch als Ausgabe.`:''}`}</div>
  </div>`;
 }

 let h=`<div class="card" style="grid-column:1/-1"><div class="chead"><span class="char">🧾 ${en?'Trading result':'Handelsergebnis'}</span>
   <span class="sub">· ${w.tage?((en?'last ':'letzte ')+w.tage+(en?' days':' Tage')):(en?'all data':'alle Daten')} · ${w.trades} ${en?'executions':'Ausführungen'}</span></div>
  <div class="stats" style="grid-template-columns:repeat(4,1fr)">
   ${kachel(en?'Gross margin':'Brutto-Marge',fmtM(w.brutto)+' ISK',vz(w.brutto))}
   ${kachel(en?'Fees & tax':'Gebühren & Steuer','-'+fmtM(w.gebuehren)+' ISK','in')}
   ${kachel(en?'Net':'Netto',fmtM(w.netto)+' ISK',vz(w.netto))}
   ${kachel(en?'Turnover':'Umsatz',fmtM(w.verkauf)+' ISK')}
  </div>
  <div class="sub" style="margin-top:8px">${en
    ? `Counted as trading are only items you both bought and sold (FIFO). Items you only bought are listed separately as stock, otherwise your own ship would look like a huge loss. Fees are apportioned to that traded volume at your own effective rates (${w.satz_steuer}% tax on sales, ${w.satz_broker}% broker), because the ${fmtM(w.geb_gesamt)} ISK booked overall also covers stock you have not sold yet.`
    : `Als Handel zählen nur Sachen, die du gekauft UND verkauft hast (FIFO). Nur Gekauftes steht getrennt als Bestand, sonst sähe dein eigenes Schiff wie ein Riesenverlust aus. Die Gebühren sind anteilig auf diese Handelsmenge umgelegt, zu deinen echten Sätzen (${w.satz_steuer}% Steuer auf Verkäufe, ${w.satz_broker}% Broker), denn die insgesamt gebuchten ${fmtM(w.geb_gesamt)} ISK betreffen auch Bestand, den du noch nicht verkauft hast.`}</div>
 </div>`;
 const P=w.posten||[];
 if(P.length){
  h+=`<div class="card" style="grid-column:1/-1"><div class="chead"><span class="char">🏆 ${en?'What actually earns':'Was wirklich einbringt'}</span></div>
   <table><tr><th>${en?'Item':'Item'}</th><th class="r">${en?'Qty':'Stk'}</th>
   <th class="r">${en?'Bought Ø':'Einkauf Ø'}</th><th class="r">${en?'Sold Ø':'Verkauf Ø'}</th>
   <th class="r">${en?'Margin':'Marge'}</th><th class="r">${en?'Profit':'Gewinn'}</th></tr>`
   +P.map(p=>`<tr><td>${esc(p.name)}<span class="cpy" data-cpy="${esc(p.name)}" title="${en?'Copy name':'Namen kopieren'}">⧉</span></td><td class="r">${fmt(p.stk)}</td>
     <td class="r">${fmtP(p.ek)}</td><td class="r">${fmtP(p.vk)}</td>
     <td class="r ${p.marge>=0?'grn':'in'}">${p.marge.toFixed(1)}%</td>
     <td class="r ${p.gewinn>=0?'grn':'in'}"><b>${fmtM(p.gewinn)}</b></td></tr>`).join('')
   +`</table></div>`;
 }
 const O=w.orders||[];
 if(O.length){
  h+=`<div class="card" style="grid-column:1/-1"><div class="chead"><span class="char">📋 ${en?'Open orders':'Offene Orders'}</span>
    <span class="sub">· ${O.length}</span></div>
   <table><tr><th>${en?'Item':'Item'}</th><th>${en?'Side':'Seite'}</th><th class="r">${en?'Price':'Preis'}</th>
   <th class="r">${en?'Remaining':'Rest'}</th><th class="r">${en?'Value':'Wert'}</th></tr>`
   +O.map(o=>`<tr><td>${esc(o.name)}<span class="cpy" data-cpy="${esc(o.name)}" title="${en?'Copy name':'Namen kopieren'}">⧉</span></td>
     <td><span class="${o.buy?'grn':'out'}">${o.buy?(en?'Buy':'Kauf'):(en?'Sell':'Verkauf')}</span></td>
     <td class="r">${fmtP(o.price)}</td><td class="r">${fmt(o.rest)}/${fmt(o.total)}</td>
     <td class="r">${fmtM(o.price*o.rest)}</td></tr>`).join('')+`</table></div>`;
 }else if(!w.orders_scope){
  h+=`<div class="card" style="grid-column:1/-1"><div class="sub">${en
    ? '📋 Open orders need one extra permission. Reconnect your character in ⚙ Options to see them here.'
    : '📋 Für offene Orders fehlt eine Berechtigung. Verbinde deinen Charakter in ⚙ Optionen neu, dann stehen sie hier.'}</div></div>`;
 }
 // ---- Top-Listen ----------------------------------------------------------
 const T=w.tops||{};
 const liste=(titel,zusatz,spalten,daten,leer)=>{
  if(!daten||!daten.length)return leer||'';
  return `<div class="card"><div class="chead"><span class="char">${titel}</span>
    ${zusatz?`<span class="sub">· ${zusatz}</span>`:''}</div>
   <table><tr>${spalten.map(c=>`<th${c[2]?' class="r"':''}>${c[0]}</th>`).join('')}</tr>`
   +daten.map(d=>`<tr>${spalten.map(c=>`<td${c[2]?' class="r"':''}>${c[1](d)}</td>`).join('')}</tr>`).join('')
   +`</table></div>`;
 };
 const nameZelle=d=>`${esc(d.name)}<span class="cpy" data-cpy="${esc(d.name)}" title="${en?'Copy name':'Namen kopieren'}">⧉</span>`;
 h+=liste(`📊 ${en?'Top 10 by turnover':'Top 10 nach Umsatz'}`,
   en?'buy plus sell':'Kauf plus Verkauf',
   [[en?'Item':'Item',nameZelle,0],[en?'Bought':'Gekauft',d=>fmtM(d.kauf),1],
    [en?'Sold':'Verkauft',d=>fmtM(d.verkauf),1],[en?'Turnover':'Umsatz',d=>`<b>${fmtM(d.isk)}</b>`,1]],
   T.umsatz);
 h+=liste(`📦 ${en?'Top 10 by quantity sold':'Top 10 nach verkaufter Menge'}`,'',
   [[en?'Item':'Item',nameZelle,0],[en?'Qty':'Stk',d=>fmt(d.stk),1],[en?'Revenue':'Erlös',d=>fmtM(d.isk),1]],
   T.menge);
 h+=liste(`⛏ ${en?'Sold but never bought':'Verkauft, nie gekauft'}`,
   (T.eigen_n||0)+' '+(en?'types':'Sorten')+' · '+fmtM(T.eigen_ges||0)+' ISK',
   [[en?'Item':'Item',nameZelle,0],[en?'Qty':'Stk',d=>fmt(d.stk),1],[en?'Revenue':'Erlös',d=>`<b>${fmtM(d.isk)}</b>`,1]],
   T.eigen);
 h+=liste(`🛒 ${en?'Bought for your own use':'Für den Eigenbedarf gekauft'}`,
   (T.bedarf_n||0)+' '+(en?'types':'Sorten')+' · '+fmtM(T.bedarf_ges||0)+' ISK',
   [[en?'Item':'Item',nameZelle,0],[en?'Qty':'Stk',d=>fmt(d.stk),1],[en?'Cost':'Kosten',d=>fmtM(d.isk),1]],
   T.bedarf);
 if(T.eigen&&T.eigen.length){
  h+=`<div class="card" style="grid-column:1/-1"><div class="sub">${en
    ? `“Sold but never bought” is what you mined, built or looted yourself. It does not appear in the trading result above, because there is no purchase price to compare against. For a miner this is usually the main source of income.`
    : `„Verkauft, nie gekauft“ ist das, was du selbst gefördert, gebaut oder erbeutet hast. Im Handelsergebnis weiter oben taucht es nicht auf, weil es dafür keinen Einkaufspreis gibt. Bei einem Miner ist das meist die Haupteinnahme.`}</div></div>`;
 }

 const rows=Object.entries(g).filter(([k,v])=>v).sort((a,b)=>Math.abs(b[1])-Math.abs(a[1]));
 if(rows.length){
  h+=`<div class="card" style="grid-column:1/-1"><div class="chead"><span class="char">💼 ${en?'Where the ISK comes from':'Woher die ISK kommen'}</span>
    <span class="sub">· ${en?'net per category':'netto je Kategorie'}</span></div>
   <table><tr><th>${en?'Category':'Kategorie'}</th><th class="r">ISK</th></tr>`
   +rows.map(([k,v])=>`<tr><td>${KAT[k]||k}</td><td class="r ${v>=0?'grn':'in'}">${fmtM(v)}</td></tr>`).join('')
   +`</table></div>`;
 }
 $('#grid').innerHTML=h0+h;
 // Zeitraum umschalten: merken und sofort neu holen, nicht auf den Takt warten.
 $('#grid').querySelectorAll('.wtage').forEach(el=>{
  el.onclick=()=>{
   walletTage=Number(el.dataset.wt);
   localStorage.setItem('walletTage',walletTage);
   tick();
  };
 });
 // Kopier-Knoepfe: EIN Handler am Container statt einer je Zeile, sonst waeren
 // sie nach dem naechsten Neuzeichnen (2s-Takt) wieder weg.
 $('#grid').onclick=ev=>{
  const b=ev.target.closest('.cpy'); if(!b)return;
  const txt=b.dataset.cpy||'';
  navigator.clipboard.writeText(txt).then(()=>{
   const alt=b.textContent; b.textContent='✓'; b.classList.add('ok');
   setTimeout(()=>{b.textContent=alt;b.classList.remove('ok');},900);
  }).catch(()=>{});
 };
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
 const asof=pl.as_of?((en?'synced ':'Abgleich vor ')+Math.max(0,Math.round((now-pl.as_of)/60))+(en?' min ago':' min')):'';
 const nxt=pl.next?(()=>{const z=Math.round((pl.next-now)/60);return z>0?(en?'next sync in '+z+' min':'nächster Abgleich in '+z+' min'):(en?'syncing now':'Abgleich läuft gerade');})():'';
 // Zwei verschiedene Wahrheiten, deshalb zwei Zeilen. Ablaufzeiten und
 // Programme kommen vom Server und sind sofort richtig. Lagerstaende friert
 // EVE ein, bis die Kolonie im Client geoeffnet wird: an echten Daten
 // gemessen war der Cache 3 Minuten alt und der Lagerstand 4,5 Stunden.
 const staleTxt=pl.stale?(()=>{const h=(now-pl.stale)/3600;
   const t=h.toFixed(1);
   return h<1?Math.max(1,Math.round(h*60))+' min':(en?t:t.replace('.',','))+' h';})():'';
 const fresh=`🛰 ${[asof,nxt].filter(Boolean).join(' · ')}`
  +(staleTxt?`<br><span class="pistale">${en?'Stock levels are '+staleTxt+' old: EVE only recalculates a colony when you open it in the client. Expiry times and programs come from the server and are always current.':'Lagerstände sind '+staleTxt+' alt: EVE rechnet eine Kolonie erst, wenn du sie im Client öffnest. Ablaufzeiten und Programme kommen vom Server und stimmen immer.'}</span>`:'');
 const stored=(pl.total_isk?` · <span class="isk">≈ ${fmtM(pl.total_isk)} ISK ${en?'stored':'gelagert'}</span>`:'')
   +(pl.total_rest_isk?` · <span class="sub" title="${en?'Remaining yield of the running programs, valued at Jita buy. Not the same as the stored value on the left.':'Restertrag der laufenden Programme, bewertet zu Jita-Ankauf. Nicht mit dem gelagerten Wert links verrechnen.'}">~${fmtM(pl.total_rest_isk)} ISK ${en?'still to come':'kommt noch'}</span>`:'');
 const urg=(pl.n_exp||pl.n_soon)
  ?`<span style="color:var(--${pl.n_exp?'red':'gold'})">⚠ ${pl.n_exp?pl.n_exp+(en?' expired · ':' abgelaufen · '):''}${pl.n_soon}${en?' expiring < 6h':' laufen in < 6h ab'}</span>`
  :`<span style="color:var(--green)">${en?'all running':'alles läuft'}</span>`;
 // Was PI tatsaechlich gekostet hat. Steht im Wallet-Journal, das Canary
 // ohnehin vollstaendig mitschreibt: kein neuer Scope, kein neuer Abruf.
 const k=pl.kosten||{};
 const costline=k.summe?`<div class="piprodline">💸 <span class="sub">${en?'Costs, last 30 days':'Kosten, letzte 30 Tage'}:</span> `
   +[k.export?`${fmtM(k.export)} ${en?'export tax':'Exportsteuer'}`:'',
      k.import?`${fmtM(k.import)} ${en?'import tax':'Importsteuer'}`:'',
      k.bau?`${fmtM(k.bau)} ${en?'construction':'Bau'}`:''].filter(Boolean).join(' · ')
   +` <b>= ${fmtM(k.summe)} ISK</b></div>`:'';
 const prodline=pl.products&&pl.products.length?`<div class="piprodline">🏭 <span class="sub">${en?'Produces':'Produziert'}:</span> ${piProdList(pl.products)}</div>`:'';
 let html=`<div class="card mfp" style="grid-column:1/-1"><div class="mfphead"><span class="mfptitle">🪐 Planetary Industry</span></div>
   <div class="mfpmain"><span class="mfpval gold">${pl.n_col}</span><span class="mfpunit">${en?'colonies':'Kolonien'}</span>
    <span class="mfpsub">${pl.n_char} ${pl.n_char===1?'Char':'Chars'} · ${pl.n_ex}${en?' extractors':' Extraktoren'} · ${urg}${stored}</span></div>
   ${prodline}
   ${costline}
   <div class="sub" style="margin-top:8px">${fresh}</div></div>`;
 // Was zuerst nachfüllen (char-übergreifend, nach Ablauf sortiert)
 html+=`<div class="card" style="grid-column:1/-1"><div class="chead"><span class="char">${en?'What to reload first':'Was zuerst nachfüllen'}</span> <span class="sub">· ${en?'sorted by expiry':'nach Ablauf sortiert'}</span></div>`;
 const board=(pl.extractors||[]).slice(0,12);
 if(!board.length)html+=`<div class="sub">${en?'No extractors.':'Keine Extraktoren.'}</div>`;
 board.forEach(e=>{const L=piLeft(e.expiry,en);
  html+=`<div class="pirow"><span class="pidot ${L.cls}"></span>
    <span class="pichar">${esc(e.char)}</span>
    <span class="piplanet">${piGlobe(e.type_id,'piglobe')}<span class="pinm">${esc(e.planet)}</span> <span class="sub">${piTypeName(e.type,en)}</span></span>
    <span class="piprod">${esc(e.product||'?')}${piTierBadge(e.tier)}${e.rest?` <span class="sub">· ${en?'still':'noch'} ~${fmtC(e.rest)}</span>`:''}</span>
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
   let body=`<div class="picolhead"><b>${esc(col.planet)}</b> <span class="sub">${piTypeName(col.type,en)} · ${esc(col.system||'')} · ${en?'level':'Stufe'} ${col.upgrade||0} · ${col.pins||0} Pins${col.factories?' · '+col.factories+(en?' factories':' Fabriken'):''}</span>${col.isk?`<span class="isk" style="margin-left:auto">≈ ${fmtM(col.isk)} ISK ${en?'stored':'gelagert'}</span>`:''}</div>`;
   if((col.products||[]).length)body+=`<div class="piprodline">🏭 <span class="sub">${en?'Produces':'Produziert'}:</span> ${piProdList(col.products)}</div>`;
   (col.extractors||[]).forEach(e=>{const L=piLeft(e.expiry,en);
    body+=`<div class="piexrow"><span class="pidot ${L.cls}"></span>${e.product_id?`<img class="piicon" src="https://images.evetech.net/types/${e.product_id}/icon?size=32" onerror="this.style.visibility='hidden'">`:`<span class="piicon"></span>`}<span class="piname">${esc(e.product||'?')}${piTierBadge(e.tier)} <span class="sub" title="${en?'Remaining yield from now until expiry. The full program would be ':'Restertrag ab jetzt bis zum Ablauf. Das ganze Programm ergäbe '}${e.total?fmtC(e.total):'?'}${en?' units.':' Stück.'}">· ${e.heads} ${en?'heads':'Köpfe'}${e.rest?' · '+(en?'still ':'noch ')+'~'+fmtC(e.rest)+(en?' units':' Stk'):''}</span></span><span class="piexp ${L.cls}">${L.txt}</span></div>`;});
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
     ${c.mission?`<div class="mtag">${missionHtml(c.mission)}</div>`:c.site?`<div class="mtag">${siteHtml(c.site)}</div>`:`<div class="mtag mtired" title="Keine Mission erkannt. Entweder Ratting ohne feste Mission oder eine Signatur, die Canary noch nicht kennt.">🔍 Keine Erkennungsdaten gefunden</div>`}
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
// Blaetterung. Zwei Listen im Missionen-Tab, beide mit eigenem Zaehler.
const PRO_SEITE = 10;
let seiteRuns = 0, seiteTage = 0;
let letzteMissionen = null;

/* Blaetter-Leiste: nur zeigen, wenn es ueberhaupt mehr als eine Seite gibt.
   Eine Leiste "Seite 1/1" ist nur Rauschen. */
function blaettern(id, seite, gesamt){
 const n = Math.ceil(gesamt / PRO_SEITE);
 if (n <= 1) return '';
 return `<div class="sub" style="display:flex;align-items:center;gap:10px;
   margin-top:10px;padding-top:8px;border-top:1px solid var(--line)">
   <span class="pill" data-blatt="${id}" data-zu="${Math.max(0, seite - 1)}"
     style="${seite === 0 ? 'opacity:.35;pointer-events:none' : 'cursor:pointer'}">‹ Zurück</span>
   <span>Seite ${seite + 1} / ${n}</span>
   <span class="pill" data-blatt="${id}" data-zu="${Math.min(n - 1, seite + 1)}"
     style="${seite >= n - 1 ? 'opacity:.35;pointer-events:none' : 'cursor:pointer'}">Weiter ›</span>
  </div>`;
}

function renderMissions(d){
 letzteMissionen = d;
 lastMissionD=d;                         // fuer die lokale Simulation merken
 // Offene Loot-Eingaben ueber den Neubau retten. Diese Ansicht baut das Grid
 // im 2-Sekunden-Takt komplett neu, und dabei war das Eingabefeld wieder
 // zugeklappt: gemessen ging es nach 1.016 ms wieder zu, mitsamt allem, was
 // schon getippt war. Deshalb hier Zustand, Text und Cursor sichern und nach
 // dem Neubau zurueckschreiben. Das betraf jeden Browser, nicht nur Firefox.
 // Waehrend im Loot-Feld getippt wird, gar nicht erst neu bauen. Sonst
 // verliert die Eingabe bei jedem Takt kurz den Fokus, und genau das macht
 // das Einfuegen mit Strg+V unzuverlaessig.
 // Dasselbe gilt fuer das Feld zum Benennen einer Mission. Das war in 2.1.0
 // vergessen worden, und der Kasten klappte prompt nach einem Takt wieder zu,
 // mitsamt dem schon Getippten. Gemeldet von Nirahse, in Firefox wie in Chrome.
 const tippt=document.activeElement&&document.activeElement.classList;
 // Die Auswahlfelder gehoeren mit in den Schutz: ein aufgeklapptes select
 // schnappt beim Neubau zu, und dann waehlt man ins Leere.
 if(tippt&&(tippt.contains('mlootin')||tippt.contains('mnamein')
            ||tippt.contains('abysstier')||tippt.contains('abysswetter')))return;
 const lootOffen={};
 document.querySelectorAll('.mlootedit').forEach(b=>{
  if(b.hidden)return;
  const ta=b.querySelector('.mlootin');
  lootOffen[b.dataset.mid]={
   text:ta?ta.value:'',
   start:ta?ta.selectionStart:0, end:ta?ta.selectionEnd:0,
   fokus:document.activeElement===ta,
   status:(([...document.querySelectorAll('.mlootstat')].find(s=>s.dataset.mid===b.dataset.mid)||{}).textContent)||''};
 });
 const nameOffen={};
 document.querySelectorAll('.mnameedit').forEach(b=>{
  if(b.hidden)return;
  const inp=b.querySelector('.mnamein');
  nameOffen[b.dataset.mid]={
   text:inp?inp.value:'',
   start:inp?inp.selectionStart:0, end:inp?inp.selectionEnd:0,
   fokus:document.activeElement===inp,
   status:(([...document.querySelectorAll('.mnamestat')].find(s=>s.dataset.mid===b.dataset.mid)||{}).textContent)||''};
 });
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
   // Knopf nach RECHTS, Laufzeit links daneben: dort sucht man ihn.
   `<div class="sub" style="display:flex;flex-wrap:wrap;gap:10px;align-items:center;margin-bottom:6px">
     <span>⚔ <b>${esc(c.name)}</b>${c.ship?' · '+esc(c.ship):''} · ${c.kills} Kills · ${fmtM(c.bounty)} Bounties · DPS ${c.dps_out} raus / ${c.dps_in} rein</span>
     <span class="sub mclosestat" data-char="${esc(c.name)}" style="margin-left:auto"></span>
     <span class="sys">${lang==='en'?'running':'läuft seit'} ${c.session_min} min</span>
     <button class="btn mclose" data-char="${esc(c.name)}" title="${lang==='en'?'Close this mission now so you can enter the loot and empty your hold before undocking':'Mission jetzt abschließen, damit du den Loot eintragen und den Laderaum leeren kannst, bevor du abdockst'}">${lang==='en'?'Finish mission':'Mission abschließen'}</button>
    </div>`).join(''):''}
 </div>
 <div class="card" style="grid-column:1/-1">
  <div class="sect" style="display:flex;align-items:center;gap:10px;flex-wrap:wrap">
   <span>Missionen einzeln (aus den Gamelogs)</span>
   ${d.abyss_n?`<a class="btn" href="/abyss.tsv" download style="margin-left:auto;display:inline-block;font-size:12px"
     title="${lang==='en'?'Saves a table of all abyssal runs. Without character names, for sharing.':'Speichert eine Tabelle aller Abyss-Durchgänge. Ohne Charakternamen, zum Weitergeben.'}"
     >🌀 ${lang==='en'?'Export abyssal runs':'Abyss-Durchgänge exportieren'} (${d.abyss_n})</a>`:''}</div>
  ${(d.mission_log&&d.mission_log.length)?d.mission_log
     .slice(seiteRuns*PRO_SEITE,(seiteRuns+1)*PRO_SEITE).map(x=>`
   <div style="border-top:1px solid var(--line);padding:10px 0">
    <div style="display:flex;flex-wrap:wrap;gap:6px;align-items:baseline">
     <b>${new Date(x.start*1000).toLocaleString().slice(0,16)}</b>
     <span class="sys">${x.system&&x.system!=='?'?'· '+esc(x.system)+' ':''}· ${x.min} min</span>
     ${x.mission?`<span class="mtag">${missionHtml(x.mission)}</span>`:x.site?`<span class="mtag">${siteHtml(x.site)}</span>`:''}
     <span style="margin-left:auto" class="isk"><b>${fmtM(x.total)} ISK</b></span>
    </div>
    ${(!x.kills&&!x.bounty&&!x.dmg_out&&(x.logi_out||x.logi_in))
      ? `<div class="sub">${lang==='en'?'Support run, no damage of your own':'Unterstützungseinsatz, kein eigener Schaden'}${x.dmg_in?' · '+fmt(x.dmg_in)+' '+(lang==='en'?'damage taken':'Schaden rein'):''}</div>`
      : `<div class="sub">${x.kills} Kills · Bounty ${fmtM(x.bounty)} · Schaden ${fmt(x.dmg_out)} raus / ${fmt(x.dmg_in)} rein${x.hit!=null?' · Trefferquote '+x.hit+'%':''}${x.enemies.length?' · Top: '+esc(x.enemies[0][0]):''}</div>`}
    ${(x.reward!=null||x.bonus!=null)?`<div class="sub vreward">✅ ${lang==='en'?'ESI verified':'ESI-verifiziert'}: ${lang==='en'?'reward':'Belohnung'} <b class="isk">${fmtM(x.reward||0)}</b>${x.bonus?` + ${lang==='en'?'time bonus':'Zeitbonus'} <b class="isk">${fmtM(x.bonus)}</b>`:''}${x.min>0?` · ${fmtM(Math.round(((x.reward||0)+(x.bonus||0))/(x.min/60)))}/h`:''}</div>`:''}
    ${factionHtml(x.faction)}
    ${ewarHtml(x.ewar)}
    ${(x.logi_out||x.logi_in)?`<div class="sub">🔗 ${lang==='en'?'Remote assistance':'Fernunterstützung'}: ${fmt(x.logi_out||0)} ${lang==='en'?'given':'gegeben'} · ${fmt(x.logi_in||0)} ${lang==='en'?'received':'bekommen'}</div>`:''}
    ${(x.npc&&x.npc.length)?`<div class="npc">${x.npc.map(l=>`<div>💬 ${esc(l)}</div>`).join('')}</div>`:''}
    <div class="sub" style="margin-top:6px">${x.loot_isk!=null?'Loot: <b class="isk">'+fmtM(x.loot_isk)+'</b>':''}
     <span class="mloottoggle" data-mid="${esc(x.mid)}" style="cursor:pointer;color:var(--cyan);font-size:11px">${x.loot_isk!=null?'✎ Loot ändern':'＋ Loot eintragen'}</span>
     <span class="mreopen" data-mid="${esc(x.mid)}" style="cursor:pointer;color:var(--dim);font-size:11px;margin-left:10px" title="Andocken ist kein sicherer Abschluss. Wer nur kurz zum Reparieren reingeflogen ist, holt die Mission hiermit zurück und der weitere Kampf zählt dazu.">↩ Läuft doch noch</span>
     <span class="mnametoggle" data-mid="${esc(x.mid)}" style="cursor:pointer;color:var(--cyan);font-size:11px;margin-left:10px" title="Trag den Namen aus deinem Missionsjournal ein. Canary merkt sich dazu die Gegner und erkennt künftige Läufe derselben Mission von allein.">${x.label?'🔖 Name ändern':'🔖 Mission benennen'}</span></div>
    ${x.abyss?`<div class="sub" style="margin-top:6px;display:flex;gap:6px;align-items:center;flex-wrap:wrap">
     <span>🌀 Abyss:</span>
     <select class="abysstier" data-mid="${esc(x.mid)}">
      <option value="">Stufe wählen</option>
      ${ABYSS_STUFEN.map((n,i)=>`<option value="${n}"${x.tier_name===i+1?' selected':''}>T${i+1} ${n}</option>`).join('')}
     </select>
     <select class="abysswetter" data-mid="${esc(x.mid)}">
      <option value="">Wetter wählen</option>
      ${ABYSS_WETTER.map(n=>`<option value="${n}"${(x.wetter||'')===n.toLowerCase()?' selected':''}>${n}</option>`).join('')}
     </select>
     <span class="abystat sub" data-mid="${esc(x.mid)}"></span>
     ${(x.tier_gegner&&x.tier_name!==x.tier_gegner)?`<span class="sub">·
       ${lang==='en'?'the enemies say':'die Gegner sagen'} <b>T${x.tier_gegner}</b>
       <button class="btn geist abystake" data-mid="${esc(x.mid)}" data-tier="${x.tier_gegner}"
        title="${lang==='en'?'A rogue drone battleship is named per tier, so this one is certain. It is only there in about one run out of five.':'Ein Rogue-Drone-Schlachtschiff heißt je Stufe anders, das ist also sicher. Dabei ist es nur in etwa jedem fünften Durchgang.'}"
        >${lang==='en'?'apply':'übernehmen'}</button></span>`:''}
    </div>`:''}
    <div class="mnameedit" data-mid="${esc(x.mid)}" hidden>
     <input class="mnamein" data-mid="${esc(x.mid)}" style="width:100%;margin-top:4px" placeholder="Missionsname aus deinem Journal, z. B. Enemies Abound (1 of 5)" value="${esc(x.label||'')}">
     <div class="btnrow" style="margin-top:4px"><button class="btn mnamego" data-mid="${esc(x.mid)}">Merken</button>
      <button class="btn geist mnameteil" data-mid="${esc(x.mid)}" title="Legt Name und Gegnerliste als fertigen Text in die Zwischenablage. Canary lädt nichts von selbst hoch, du fügst den Block bewusst in eine Meldung ein.">Für alle beitragen</button>
      <span class="mnamestat sub" data-mid="${esc(x.mid)}"></span></div>
     <div class="sub" style="margin-top:4px">Wenn du fertig bist, drück <b>Merken</b>. Canary behält dann die ${x.enemies.length} Gegnertypen dieses Laufs und erkennt spätere Läufe mit ähnlicher Zusammenstellung von allein.</div>
    </div>
    <div class="mlootedit" data-mid="${esc(x.mid)}" hidden>
     <textarea class="mlootin" data-mid="${esc(x.mid)}" rows="2" style="width:100%;margin-top:4px" placeholder="Frachtraum-Loot dieser Mission hier einfügen (im Spiel Strg+A, Strg+C)">${esc(x.loot_text)}</textarea>
     <div class="btnrow" style="margin-top:4px"><button class="btn mlootgo" data-mid="${esc(x.mid)}">Loot bewerten</button> <span class="mlootstat sub" data-mid="${esc(x.mid)}"></span></div>
    </div>
   </div>`).join(''):'<div class="sub">Noch keine abgeschlossenen Missionen erfasst. Eine Mission gilt als abgeschlossen, sobald du fürs nächste Mal wieder abdockst.</div>'}
  ${blaettern('runs',seiteRuns,(d.mission_log||[]).length)}
  ${(()=>{const o=d.mission_offen; if(!o||!o.n)return '';
    const en3=lang==='en';
    return `<div class="sub" style="border-top:1px solid var(--line);margin-top:10px;padding-top:10px">
      ${en3
        ? `<b>${o.n} agent payouts could not be matched to a mission</b>, together ${fmtM(o.summe)} ISK.
           That happens with missions that involve no combat at all: courier runs, transports, pure dialogue steps,
           and many stages of the epic arcs. Nothing appears in the game log for those, so Canary never sees a mission.
           The ISK is counted in the daily totals above, it just has no combat data attached.`
        : `<b>${o.n} Agenten-Auszahlungen ließen sich keiner Mission zuordnen</b>, zusammen ${fmtM(o.summe)} ISK.
           Das passiert bei Aufträgen ganz ohne Kampf: Kurierflüge, Transporte, reine Dialog-Schritte und viele
           Stationen der Epic Arcs. Dazu steht nichts im Gamelog, Canary sieht also gar keine Mission.
           In den Tagessummen oben stecken die ISK trotzdem drin, sie haben nur keine Kampfdaten dabei.`}
      <div style="margin-top:6px">${(o.liste||[]).map(x=>
        `${new Date(x.ts*1000).toLocaleString().slice(0,16)} · ${esc(x.char)} · <span class="isk">${fmtM(x.isk)}</span>`
       ).join('<br>')}</div>
     </div>`;})()}
 </div>
 <div class="card" style="grid-column:1/-1">
  <div class="sect">Letzte 30 Tage</div>
  <div class="sub">Je Charakter und Tag. Bounty kommt aus den Gamelogs, Belohnung und Zeitbonus aus dem Wallet-Journal, der Loot ist von dir an den Runs eingetragen. EVE schreibt beim Plündern nichts mit, deshalb steht dort nur, was du selbst hinterlegt hast.</div>
  ${(d.loot_tage&&d.loot_tage.length)?(()=>{
    // Standardmaessig nur die letzten Tage: bei Vielfliegern werden das sonst
    // ueber dreissig Zeilen und die Seite wird endlos.
    const alle=d.loot_tage;
    const zeig=alle.slice(seiteTage*PRO_SEITE,(seiteTage+1)*PRO_SEITE);
    return `<div style="overflow-x:auto"><table>
   <thead><tr><th>Tag</th><th>Charakter</th><th class="r">Runs</th><th class="r">Bounty</th>
    <th class="r">Belohnung</th><th class="r">Zeitbonus</th><th class="r">Loot</th><th class="r">Gesamt</th></tr></thead>`+
   zeig.map(x=>`<tr><td>${esc(x.tag)}</td><td>${esc(x.char)}</td>
    <td class="r">${x.runs}${x.mit_loot<x.runs?`<span title="${x.runs-x.mit_loot} Run(s) ohne eingetragenen Loot" style="color:var(--gold)"> *</span>`:''}</td>
    <td class="r grn">${x.bounty?fmtM(x.bounty):'&middot;'}</td>
    <td class="r isk">${x.reward?fmtM(x.reward):'&middot;'}</td>
    <td class="r isk">${x.bonus?fmtM(x.bonus):'&middot;'}</td>
    <td class="r isk">${x.loot?fmtM(x.loot):'&middot;'}</td>
    <td class="r isk"><b>${fmtM(x.total)}</b></td></tr>`).join('')+
   '</table></div>'
   +blaettern('tage',seiteTage,alle.length)
   +(zeig.some(x=>x.mit_loot<x.runs)?'<div class="sub" style="margin-top:6px">* An diesen Tagen gibt es Runs ohne eingetragenen Loot. Die Summe ist dann niedriger als das, was wirklich rumkam.</div>':'');
   })():'<div class="sub">Noch nichts erfasst. Sobald ein Run abgeschlossen ist, steht er hier.</div>'}
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
 // Gesicherten Zustand zurueckschreiben, bevor irgendein Handler haengt.
 Object.entries(lootOffen).forEach(([mid,z])=>{
  const box=[...document.querySelectorAll('.mlootedit')].find(e=>e.dataset.mid===mid);
  if(!box)return;
  box.hidden=false;
  const ta=box.querySelector('.mlootin');
  if(ta){
   ta.value=z.text;
   if(z.fokus)ta.focus();
   // Cursor immer zuruecksetzen, sonst springt er beim naechsten Klick ans Ende.
   try{ta.setSelectionRange(z.start,z.end);}catch(e){}
  }
  const st=[...document.querySelectorAll('.mlootstat')].find(s=>s.dataset.mid===mid);
  if(st&&z.status)st.textContent=z.status;
 });
 Object.entries(nameOffen).forEach(([mid,z])=>{
  const box=[...document.querySelectorAll('.mnameedit')].find(e=>e.dataset.mid===mid);
  if(!box)return;
  box.hidden=false;
  const inp=box.querySelector('.mnamein');
  if(inp){
   inp.value=z.text;
   if(z.fokus)inp.focus();
   try{inp.setSelectionRange(z.start,z.end);}catch(e){}
  }
  const st=[...document.querySelectorAll('.mnamestat')].find(s=>s.dataset.mid===mid);
  if(st&&z.status)st.textContent=z.status;
 });
 // Mission von Hand abschliessen. Danach steht sie sofort unten in der Liste
 // und der Loot laesst sich eintragen, ohne dass man abdocken muss.
 document.querySelectorAll('.mclose').forEach(b=>b.onclick=async()=>{
  const char=b.dataset.char, en2=lang==='en';
  const finde=()=>[...document.querySelectorAll('.mclosestat')].find(s=>s.dataset.char===char);
  const setz=t=>{const el=finde(); if(el)el.textContent=t;};
  setz(en2?'Finishing …':'Schließe ab …');
  let r;try{r=await post({action:'mission_close',char});}catch(e){r=null;}
  if(!r||!r.ok){setz(en2?'Server not reachable':'Server nicht erreichbar');return;}
  if(r.saved){
   // Ob an der Station oder aus der Ferne, erkannt am Anflug zum Andock-
   // Perimeter. Das ist das einzige Andock-Signal, das in beiden Sprachen im
   // Log steht, die englische Bestaetigung gibt es auf Deutsch nicht.
   const wo=r.docked
     ? (en2?'Mission completed':'Mission abgeschlossen')
     : (en2?'Mission completed remotely':'Mission remote abgeschlossen');
   setz(`✅ ${wo} · ${r.min} min · ${fmtM(r.bounty)} ${en2?'bounty':'Bounty'} · `
        +(en2?'enter the loot below':'Loot unten eintragen'));
   setTimeout(tick,600);
  }else setz(r.msg||(en2?'Nothing to save':'Nichts zu speichern'));
 });
 document.querySelectorAll('.mreopen').forEach(t=>t.onclick=async()=>{
  const en3=lang==='en';
  // Vorher fragen: der Eintrag verschwindet aus der Liste, und ein bereits
  // eingetragener Loot geht mit. Das ist keine Kleinigkeit, die man
  // versehentlich anklickt.
  if(!confirm(en3
   ?'Take this run back into the current session? The entry disappears from the list and reappears when the run really ends. Loot you already entered is lost.'
   :'Diesen Einsatz zurück in die laufende Sitzung holen? Der Eintrag verschwindet aus der Liste und entsteht neu, wenn der Einsatz wirklich endet. Bereits eingetragener Loot geht dabei verloren.'))return;
  t.textContent=en3?'Taking back …':'Hole zurück …';
  let r;try{r=await post({action:'mission_reopen',mid:t.dataset.mid});}catch(e){r=null;}
  if(r&&r.ok){
   t.textContent=r.sitzung_aktiv
    ?(en3?'✓ back in the session':'✓ zurück in der Sitzung')
    :(en3?'✓ removed (character offline, no session to continue)'
         :'✓ entfernt (Char offline, es läuft keine Sitzung mehr)');
   setTimeout(()=>tick(),1200);
  }else t.textContent=en3?'failed':'hat nicht geklappt';
 });
 document.querySelectorAll('[data-blatt]').forEach(el=>el.onclick=()=>{
  const zu=parseInt(el.dataset.zu,10);
  if(el.dataset.blatt==='runs') seiteRuns=zu; else seiteTage=zu;
  if(letzteMissionen) renderMissions(letzteMissionen);
  if(lang!=='de') tr(document.body);
 });
 document.querySelectorAll('.mloottoggle').forEach(t=>t.onclick=()=>{
  const box=[...document.querySelectorAll('.mlootedit')].find(e=>e.dataset.mid===t.dataset.mid);
  if(box){box.hidden=!box.hidden; if(!box.hidden){const ta=box.querySelector('.mlootin'); if(ta)ta.focus();}}
 });
 document.querySelectorAll('.mlootgo').forEach(b=>b.onclick=async()=>{
  const mid=b.dataset.mid;
  // Das Statusfeld JEDES MAL frisch suchen statt es vor dem Abschicken zu
  // merken. Sobald der Knopf gedrueckt wird, verliert das Eingabefeld den
  // Fokus, damit greift der Tipp-Schutz nicht mehr und die Ansicht darf sich
  // neu aufbauen. Das gemerkte Element haengt dann nicht mehr im Dokument, und
  // "Prüfe …" blieb ewig stehen, obwohl der Server laengst geantwortet hatte
  // (gemessen: Antwort nach 1.029 ms).
  const finde=sel=>[...document.querySelectorAll(sel)].find(e=>e.dataset.mid===mid);
  const setzStatus=txt=>{const s=finde('.mlootstat'); if(s)s.textContent=txt;};
  const ta=finde('.mlootin');
  const text=ta?ta.value:'';
  setzStatus(lang==='en'?'Checking …':'Prüfe …');
  let r;try{r=await post({action:'mission_loot',mid,text});}catch(e){r=null;}
  const en2=lang==='en';
  if(r&&r.ok){
   setzStatus('Loot: '+fmtM(r.isk)
    +(r.unknown&&r.unknown.length?(en2?' · not recognised: ':' · nicht erkannt: ')+r.unknown.join(', '):''));
   // Nach dem Bewerten zuklappen. Seit das Feld den 2s-Takt uebersteht, blieb
   // es sonst offen stehen, und wer mehrere Missionen nacheinander eintraegt,
   // hatte am Ende einen Stapel offener Kaesten untereinander.
   const box=finde('.mlootedit'); if(box)box.hidden=true;
   setTimeout(tick,600);
  }else setzStatus(r?(en2?'Error':'Fehler')
                    :(en2?'Server not reachable':'Server nicht erreichbar'));
 });
 // Zwei Auswahlfelder statt Freitext, gewuenscht von Nirahse. Gespeichert wird
 // trotzdem der gewohnte Name ("Chaotic Firestorm"), damit Export, Anzeige und
 // Stufenerkennung unveraendert weiterarbeiten und nichts auseinanderlaeuft.
 const abyssSpeichern=async(mid,tier,wetter)=>{
  const finde=sel=>[...document.querySelectorAll(sel)].find(e=>e.dataset.mid===mid);
  const name=[tier,wetter].filter(Boolean).join(' ');
  const st=finde('.abystat'); if(st)st.textContent=lang==='en'?'Saving …':'Speichere …';
  let r;try{r=await post({action:'mission_label',mid,name});}catch(e){r=null;}
  const s2=finde('.abystat');
  if(s2)s2.textContent=(r&&r.ok)?'✓':(lang==='en'?'Error':'Fehler');
  setTimeout(tick,600);
 };
 document.querySelectorAll('.abysstier,.abysswetter').forEach(sel=>sel.onchange=()=>{
  const mid=sel.dataset.mid;
  const finde=k=>[...document.querySelectorAll(k)].find(e=>e.dataset.mid===mid);
  const t=finde('.abysstier'), w=finde('.abysswetter');
  abyssSpeichern(mid,t?t.value:'',w?w.value:'');
 });
 document.querySelectorAll('.abystake').forEach(b=>b.onclick=()=>{
  const mid=b.dataset.mid;
  const finde=k=>[...document.querySelectorAll(k)].find(e=>e.dataset.mid===mid);
  const w=finde('.abysswetter');
  abyssSpeichern(mid,ABYSS_STUFEN[Number(b.dataset.tier)-1],w?w.value:'');
 });
 document.querySelectorAll('.mnametoggle').forEach(t=>t.onclick=()=>{
  const box=[...document.querySelectorAll('.mnameedit')].find(e=>e.dataset.mid===t.dataset.mid);
  if(box){box.hidden=!box.hidden; if(!box.hidden){const i=box.querySelector('.mnamein'); if(i)i.focus();}}
 });
 document.querySelectorAll('.mnameteil').forEach(b=>b.onclick=async()=>{
  // Beitragen heisst hier: fertigen Text in die Zwischenablage, mehr nicht.
  // Canary schickt nichts von selbst irgendwohin, und das soll auch so bleiben.
  const mid=b.dataset.mid;
  const finde=sel=>[...document.querySelectorAll(sel)].find(e=>e.dataset.mid===mid);
  const setzStatus=t=>{const s=finde('.mnamestat'); if(s)s.textContent=t;};
  const run=(letzteMissionen&&letzteMissionen.mission_log||[]).find(m=>String(m.mid)===String(mid));
  const inp=finde('.mnamein');
  const name=(inp?inp.value:'').trim()||(run&&run.label)||'';
  const en2=lang==='en';
  if(!name){setzStatus(en2?'Enter the mission name first':'Erst den Missionsnamen eintragen');return;}
  const gegner=((run&&run.enemies)||[]).map(g=>g[0]);
  if(gegner.length<4){setzStatus(en2?'Too few enemies for a template':'Zu wenige Gegner für eine Vorlage');return;}
  const txt=['Mission: '+name,
             'System: '+((run&&run.system)||'?'),
             'Gegner ('+gegner.length+'):',
             ...gegner.map(g=>'  '+g),
             '',
             'Canary '+(state&&state.version||'')+', Gegner-Fingerabdruck'].join('\\n');
  // Nach dem Kopieren fehlte der naechste Schritt: es stand nur "kopiert",
  // aber nicht WOHIN damit. Gemeldet von Nirahse ("Es ist unklar wie man
  // danach weitermachen soll"). Deshalb hier gleich der Link zum Formular,
  // in einem neuen Tab, damit die Karte offen bleibt.
  const ziel='https://eve-online-askend.github.io/eve-canary/mission.html';
  try{await navigator.clipboard.writeText(txt);
      const s=finde('.mnamestat');
      if(s)s.innerHTML=(en2?'✓ copied. Now open the ':'✓ kopiert. Jetzt das ')
        +'<a href="'+ziel+'" target="_blank" rel="noopener">'
        +(en2?'report form':'Meldeformular')+'</a>'
        +(en2?' and paste it into the enemy list.'
             :' öffnen und in die Gegnerliste einfügen.');}
  catch(e){setzStatus(en2?'Clipboard blocked':'Zwischenablage blockiert');}
 });
 document.querySelectorAll('.mnamego').forEach(b=>b.onclick=async()=>{
  // Gleiches Vorgehen wie beim Loot: Statusfeld jedes Mal frisch suchen, weil
  // die Ansicht sich nach dem Fokusverlust neu aufbauen darf.
  const mid=b.dataset.mid;
  const finde=sel=>[...document.querySelectorAll(sel)].find(e=>e.dataset.mid===mid);
  const setzStatus=txt=>{const s=finde('.mnamestat'); if(s)s.textContent=txt;};
  const inp=finde('.mnamein');
  const name=inp?inp.value.trim():'';
  const en2=lang==='en';
  setzStatus(en2?'Saving …':'Speichere …');
  let r;try{r=await post({action:'mission_label',mid,name});}catch(e){r=null;}
  if(r&&r.ok){
   setzStatus(r.name
     ?(en2?`✓ saved, ${r.vorlagen} template(s)`:`✓ gemerkt, ${r.vorlagen} Vorlage(n)`)
     :(en2?'✓ name removed':'✓ Name entfernt'));
   const box=finde('.mnameedit'); if(box)box.hidden=true;
   setTimeout(tick,600);
  }else setzStatus(r?(en2?'Error':'Fehler')
                    :(en2?'Server not reachable':'Server nicht erreichbar'));
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
  Einzelne Zeilen wie "Compressed Veldspar 50000" funktionieren genauso. Auch die Ergebnisse der Bergbauvermessung lassen sich so einfügen, dann steht hier, wie viel Volumen und ISK im Belt liegen.</div>
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
// Eigener Bereich, weil zwischen "vorher" und "nachher" ein ganzer Lauf liegt:
// hier soll niemand erst an einem Preisrechner vorbeiscrollen muessen.
function renderBeute(){
 if(document.getElementById('diffBox'))return;   // schon gebaut, Eingaben stehen lassen
 $('#grid').innerHTML=`<div class="card" id="diffBox" style="grid-column:1/-1">
  <b>📦 Was hat der Lauf gebracht?</b>
  <div style="font-size:12px;color:var(--dim);margin:6px 0">EVE schreibt beim Plündern nichts mit, deshalb der Umweg über den Frachtraum. Vor dem Lauf im Spiel den Frachtraum öffnen, alles markieren (Strg+A), kopieren (Strg+C) und links einfügen. Nach der Mission oder dem Abyss dasselbe rechts. Canary zieht beides voneinander ab, und unten steht nur noch, was dazugekommen ist, fertig zum Kopieren für das Loot-Feld einer Mission.
  Beide Felder bleiben gespeichert, du kannst also in der Zwischenzeit den Bereich wechseln, die Seite neu laden oder Canary neu starten.</div>
  <div style="display:grid;grid-template-columns:repeat(auto-fit,minmax(260px,1fr));gap:10px">
   <div><div style="font-size:12px;margin-bottom:3px">Vorher</div>
    <textarea id="diffA" rows="10" style="width:100%" placeholder="Frachtraum vor der Aktion"></textarea></div>
   <div><div style="font-size:12px;margin-bottom:3px">Nachher</div>
    <textarea id="diffB" rows="10" style="width:100%" placeholder="Frachtraum nach der Aktion"></textarea></div></div>
  <div class="btnrow" style="margin:8px 0"><button class="btn" id="diffGo">Differenz bilden</button>
   <button class="btn" id="diffNext" title="Für den nächsten Durchgang: der Stand von rechts wandert nach links, rechts wird leer. Spart das doppelte Einfügen, wenn du mehrere Läufe hintereinander machst.">⬅ Nachher wird Vorher</button>
   <button class="btn" id="diffClr">Felder leeren</button>
   <span id="diffStat" style="font-size:12px;color:var(--dim)"></span></div>
  <div id="diffOut" style="overflow-x:auto"></div></div>`;
 $('#diffGo').onclick=doDiff;
 $('#diffClr').onclick=()=>{
  ['diffA','diffB'].forEach(id=>{$('#'+id).value='';localStorage.removeItem(id);});
  $('#diffOut').innerHTML='';$('#diffStat').textContent='';
 };
 // Mehrere Laeufe hintereinander: der Frachtraum von eben ist der Ausgangsstand
 // fuer den naechsten Durchgang. Ohne das muesste man dieselbe Kopie zweimal
 // einfuegen. Gewuenscht von Nirahse. Das Ergebnis bleibt absichtlich stehen,
 // sonst waere es weg, bevor man es kopiert hat.
 $('#diffNext').onclick=()=>{
  const a=$('#diffA'),b=$('#diffB');
  // tr() gleich selbst nachziehen: sonst steht die Meldung bis zu zwei Sekunden
  // auf Deutsch, bis der naechste Takt uebersetzt. Gemessen, nicht vermutet.
  const sagen=t=>{$('#diffStat').textContent=t; if(lang!=='de')tr(document.body);};
  if(!b.value.trim()){sagen('Im Feld Nachher steht noch nichts.');return;}
  a.value=b.value; b.value='';
  localStorage.setItem('diffA',a.value); localStorage.removeItem('diffB');
  sagen('Nachher ist jetzt Vorher. Das Ergebnis darunter bleibt stehen.');
  b.focus();
 };
 // Sofort mitschreiben: der Sinn des Werkzeugs ist, dass zwischen "vorher" und
 // "nachher" eine ganze Mission liegt. Ohne Speichern waere die erste Kopie
 // beim naechsten Bereichswechsel weg, denn #grid wird dabei neu gebaut.
 ['diffA','diffB'].forEach(id=>{
  const el=$('#'+id), alt=localStorage.getItem(id);
  if(alt)el.value=alt;
  el.oninput=()=>localStorage.setItem(id,el.value);
 });
}
// Frachtraum vorher gegen nachher. Der Vergleich laeuft im Server, damit
// derselbe Parser zaehlt, der spaeter auch das Loot-Feld liest.
async function doDiff(){
 const vorher=$('#diffA').value,nachher=$('#diffB').value;
 if(!vorher.trim()||!nachher.trim()){
  $('#diffStat').textContent='Bitte in beide Felder eine Frachtraum-Kopie einfügen.';return;}
 $('#diffStat').textContent='Vergleiche …';$('#diffOut').innerHTML='';
 let r;try{r=await post({action:'cargo_diff',vorher,nachher});}catch(e){r=null;}
 if(!$('#diffOut'))return;      // Bereich waehrend der Abfrage gewechselt
 if(!r||!r.ok){$('#diffStat').textContent='Vergleich fehlgeschlagen.';return;}
 $('#diffStat').textContent='';
 if(!r.plus.length&&!r.minus.length){
  $('#diffOut').innerHTML='<div class="sub">Kein Unterschied gefunden. Beide Kopien enthalten dasselbe.</div>';
  if(lang!=='de')tr(document.body);
  return;}
 const zeilen=(liste,farbe,zeichen)=>liste.map(i=>
  '<tr><td>'+esc(i.name)+'</td><td class="r">'+fmt(i.vor)+'</td><td class="r">'+fmt(i.nach)
  +'</td><td class="r" style="color:'+farbe+'">'+zeichen+fmt(i.qty)+'</td></tr>').join('');
 let h='';
 if(r.plus.length){
  h+='<div style="margin-top:4px"><b>Dazugekommen</b></div>'
   +'<textarea id="diffOutTxt" rows="'+Math.min(12,Math.max(3,r.plus.length))
   +'" style="width:100%;margin-top:4px"></textarea>'
   +'<div class="btnrow" style="margin:6px 0"><button class="btn" id="diffCopy">Kopieren</button>'
   +'<button class="btn" id="diffWert">Wert berechnen</button>'
   +'<span id="diffWertStat" style="font-size:12px;color:var(--dim)"></span></div>'
   +'<table><tr><th>Item</th><th class="r">Vorher</th><th class="r">Nachher</th><th class="r">Dazu</th></tr>'
   +zeilen(r.plus,'var(--gold)','+')+'</table>';
 }
 if(r.minus.length){
  h+='<div style="margin-top:12px"><b>Weniger geworden</b> <span class="sub">'
   +'verbraucht oder abgeladen, zum Beispiel Munition, Drohnen oder Filamente</span></div>'
   +'<table><tr><th>Item</th><th class="r">Vorher</th><th class="r">Nachher</th><th class="r">Weg</th></tr>'
   +zeilen(r.minus,'var(--red)','-')+'</table>';
 }
 if(r.gleich>0)h+='<div class="sub" style="margin-top:8px">'+r.gleich
  +(lang==='en'?(r.gleich===1?' kind stayed the same.':' kinds stayed the same.')
              :(r.gleich===1?' Sorte ist unverändert geblieben.':' Sorten sind unverändert geblieben.'))+'</div>';
 $('#diffOut').innerHTML=h;
 // Den Text ueber .value setzen und nicht in das HTML schreiben: sonst muesste
 // jeder Item-Name maskiert werden, und ein Tabulator im Markup ist heikel.
 const ta=$('#diffOutTxt');
 if(ta)ta.value=r.plus_text||'';
 const cp=$('#diffCopy');
 if(cp)cp.onclick=async()=>{
  try{await navigator.clipboard.writeText($('#diffOutTxt').value);
      $('#diffStat').textContent='✓ kopiert';}
  catch(e){$('#diffOutTxt').select();
           $('#diffStat').textContent='Kopieren ging nicht, Text ist markiert: Strg+C drücken.';}
 };
 const wb=$('#diffWert');
 if(wb)wb.onclick=async()=>{
  const st=$('#diffWertStat');
  st.textContent='Hole Preise von allen Handelsplätzen …';
  let x;try{x=await post({action:'loot_calc',text:$('#diffOutTxt').value});}catch(e){x=null;}
  if(!$('#diffWertStat'))return;
  if(!x||!x.ok){$('#diffWertStat').textContent='Preisabfrage fehlgeschlagen.';return;}
  const hubs=Object.values(x.hubs||{}).filter(h2=>!h2.error);
  if(!hubs.length){$('#diffWertStat').textContent='Keine Preisdaten erhalten.';return;}
  const best=Math.max(...hubs.map(h2=>h2.buy)),wo=hubs.find(h2=>h2.buy===best),en=lang==='en';
  // Hier steht ein Name mitten im Satz, deshalb beide Sprachen direkt im Code
  // und nicht ueber die Wortliste: ein Textknoten mit Variable passt auf keinen
  // festen Schluessel.
  $('#diffWertStat').innerHTML=(en?'Instant sale: ':'Sofortverkauf: ')
   +'<b class="isk">'+fmtM(best)+'</b> '
   +'<span class="sub">'+(en?'best hub: ':'bester Handelsplatz: ')+esc(wo?wo.name:'')+'</span>'
   +(x.unknown&&x.unknown.length
     ?'<span class="sub"> · '+(en?'not recognised: ':'nicht erkannt: ')
      +esc(x.unknown.slice(0,6).join(', '))+'</span>':'');
 };
 if(lang!=='de')tr(document.body);
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
'🚦 Intel':'🚦 Intel','🎯 Missionen':'🎯 Missions','💰 ISKray':'💰 ISKray','🕑 Verlauf':'🕑 Timeline','🪪 Steckbrief':'🪪 Character sheet','🪐 Planeten':'🪐 Planets','🧾 Wallet Buddy':'🧾 Wallet Buddy',
'Dein Wallet unter der Lupe. Oben die Bilanz: Einnahmen, Ausgaben und was unterm Strich bleibt, je Kategorie und umschaltbar für 7 Tage, 30 Tage oder alles. Darunter der Handel im Detail, welches Item wirklich Gewinn bringt und was Gebühren und Steuer fressen, dazu Ranglisten nach Umsatz und verkaufter Menge.':
 'Your wallet under the microscope. At the top the balance: income, spending and what is left, by category and switchable between 7 days, 30 days or everything. Below that trading in detail, which item actually turns a profit and how much fees and tax eat up, plus rankings by turnover and quantity sold.',
'Daten: nur über den EVE-Login, aus deinem Wallet-Journal und deinen Markt-Transaktionen. Beides ist bis zu eine Stunde alt. Die Käufe kommen aus den Transaktionen und nicht aus dem Journal, denn EVE bucht eine Kauforder schon beim Einstellen als hinterlegte Sicherheit, und die käme bei Storno zurück. Gewinn wird per FIFO gerechnet, also jeder Verkauf gegen deine ältesten Einkäufe desselben Typs. Als Handel zählen nur Sachen, die du gekauft UND verkauft hast, sonst würde dein eigenes Schiff als Riesenverlust dastehen. Was du nur verkauft hast, etwa selbst gefördertes Erz, steht deshalb in einer eigenen Liste.':
 'Data: through the EVE login only, from your wallet journal and your market transactions. Both are up to an hour old. Purchases come from the transactions rather than the journal, because EVE books a buy order as escrow the moment you place it, and that money would come back on cancellation. Profit is computed FIFO, every sale against your oldest buys of the same type. Only items you both bought AND sold count as trading, otherwise your own ship would show up as a huge loss. What you only sold, ore you mined yourself for instance, therefore has a list of its own.',
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
'Lieferungen mit vervielfachtem Ertrag. Canary erkennt sie daran, dass die Menge ein exaktes Vielfaches deiner Normallieferung ist. Gezeigt wird nur der Teil, der über die Normalmenge hinausging.':
 'Deliveries with multiplied yield. Canary spots them because the amount is an exact multiple of your normal delivery. Only the part beyond the normal amount is shown.',
'Asteroiden leergebaggert · Preise':'asteroids depleted · prices',
'per ⛽ setzen':'set via ⛽',
'noch keine Kompression, Verbrauch pausiert':'no compression yet, consumption paused',
'Keine Kompression im Zeitraum.':'No compression in this period.',
'Nach Charakter (gesamt)':'By character (total)',
'🪨 Belt auswerten':'🪨 Check this belt',
'🪨 Was steckt in diesem Belt?':'🪨 What is in this belt?',
'Ergebnisse der Bergbauvermessung einfügen und sehen, wie viel Volumen und ISK im Belt liegen':
 'Paste your survey scanner results and see how much volume and ISK the belt holds',
'Im Spiel das Fenster „Ergebnisse der Bergbauvermessung“ öffnen, hineinklicken, alles markieren (Strg+A), kopieren (Strg+C) und hier einfügen. Die Spalten für Volumen, Wert und Entfernung darfst du mitkopieren, Canary nimmt sich nur die Mengen.':
 'In game open the survey scanner results window, click into it, select everything (Ctrl+A), copy (Ctrl+C) and paste it here. Feel free to include the volume, value and distance columns, Canary only takes the quantities.',
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
'🫧 Neu: Gas-Mining wird jetzt erkannt':'🫧 New: gas mining is now recognised',
'Canary erfasst ab sofort auch Gas: Mykoserocin, Cytoserocin und Fullerite, roh und komprimiert. Menge, m³ und ISK-Wert stehen damit genauso in deiner Statistik wie beim Erz.':
 'Canary now tracks gas as well: Mykoserocin, Cytoserocin and Fullerite, raw and compressed. Amount, m³ and ISK value show up in your statistics just like ore.',
'Deine bisherigen Logs werden dafür einmalig neu eingelesen, die Gas-Ausbeute der letzten Tage taucht also rückwirkend auf. Nebenbei behoben: Rückstände wurden beim Gas fälschlich als Ertrag mitgezählt, das ist jetzt sauber getrennt.':
 'Your existing logs are read in once more for this, so the gas you mined over the last days shows up retroactively. Fixed along the way: residue was wrongly counted as yield for gas, that is cleanly separated now.',
'Alles klar':'Got it',
// Der <b>-Tag um den Spielernamen zerlegt den Satz in drei Textknoten, deshalb
// zwei Schluessel statt einem. xlate() trimmt und haengt den Leerraum wieder an.
'Danke an':'Thanks to',
'für die Meldung, dass Gas-Mining nicht erkannt wurde. Wenn dir etwas auffällt, sag Bescheid, genau so entstehen diese Verbesserungen.':
 'for reporting that gas mining was not being recognised. If you spot anything, let me know, that is exactly how these improvements come about.',
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
'Stufe wählen':'Pick tier','Wetter wählen':'Pick weather',
// Rechner
'Berechnen':'Calculate','Was lohnt sich am meisten pro Laderaum?':'What pays off most per cargo hold?',
'Sofortverkauf · mit Sell-Order':'Instant sale · with sell order',
'Hole Preise von allen Handelsplätzen …':'Fetching prices from all trade hubs …',
'Preisabfrage fehlgeschlagen.':'Price lookup failed.',
// Beute
'📦 Beute':'📦 Loot','📦 Was hat der Lauf gebracht?':'📦 What did the run bring in?',
'EVE schreibt beim Plündern nichts mit, deshalb der Umweg über den Frachtraum. Vor dem Lauf im Spiel den Frachtraum öffnen, alles markieren (Strg+A), kopieren (Strg+C) und links einfügen. Nach der Mission oder dem Abyss dasselbe rechts. Canary zieht beides voneinander ab, und unten steht nur noch, was dazugekommen ist, fertig zum Kopieren für das Loot-Feld einer Mission. Beide Felder bleiben gespeichert, du kannst also in der Zwischenzeit den Bereich wechseln, die Seite neu laden oder Canary neu starten.':
 'EVE records nothing when you loot, hence the detour through the cargo hold. Before the run, open your cargo hold in game, select everything (Ctrl+A), copy it (Ctrl+C) and paste it on the left. After the mission or the abyss do the same on the right. Canary subtracts one from the other, and below you get only what was added, ready to copy into the loot field of a mission. Both boxes are saved, so you can switch views, reload the page or restart Canary in between.',
'Vorher':'Before','Nachher':'After','Dazu':'Added','Weg':'Gone',
'Frachtraum vor der Aktion':'Cargo hold before','Frachtraum nach der Aktion':'Cargo hold after',
'Differenz bilden':'Compare','Felder leeren':'Clear the boxes','Kopieren':'Copy',
'⬅ Nachher wird Vorher':'⬅ After becomes before',
'Für den nächsten Durchgang: der Stand von rechts wandert nach links, rechts wird leer. Spart das doppelte Einfügen, wenn du mehrere Läufe hintereinander machst.':
 'For the next run: what is on the right moves to the left and the right box is emptied. Saves pasting the same copy twice when you do several runs in a row.',
'Im Feld Nachher steht noch nichts.':'The after box is still empty.',
'Nachher ist jetzt Vorher. Das Ergebnis darunter bleibt stehen.':
 'After is now before. The result below stays as it is.',
'Wert berechnen':'Get the value','Vergleiche …':'Comparing …',
'Bitte in beide Felder eine Frachtraum-Kopie einfügen.':'Please paste a cargo copy into both boxes.',
'Vergleich fehlgeschlagen.':'Comparison failed.',
'Kein Unterschied gefunden. Beide Kopien enthalten dasselbe.':
 'No difference found. Both copies hold the same things.',
'Dazugekommen':'Added','Weniger geworden':'Gone missing',
'verbraucht oder abgeladen, zum Beispiel Munition, Drohnen oder Filamente':
 'used up or dropped off, for example ammo, drones or filaments',
'✓ kopiert':'✓ copied','Keine Preisdaten erhalten.':'No price data received.',
// Desktop-Meldungen
'EVE: SPIELER-ANGRIFF!':'EVE: PLAYER ATTACK!','EVE: Frachtraum voll!':'EVE: Cargo hold full!',
'EVE: Mining steht!':'EVE: Mining stopped!','EVE: Drohnen prüfen!':'EVE: Check drones!',
'EVE: Abbaurate gefallen!':'EVE: Mining rate dropped!','EVE: Bedrohung erkannt!':'EVE: Threat detected!',
'EVE: Heavy Water fast leer!':'EVE: Heavy Water almost empty!','EVE: Watchlist':'EVE: Watchlist',
'Speichern':'Save','nicht gefunden!':'not found!',
'Erz-Bilanz (nach Wert)':'Ore balance (by value)','Gegner (letzte 30 Tage)':'Enemies (last 30 days)',
// Blaetterung\n'‹ Zurück':'‹ Back','Weiter ›':'Next ›',\n'Je Charakter und Tag. Bounty kommt aus den Gamelogs, Belohnung und Zeitbonus aus dem Wallet-Journal, der Loot ist von dir an den Runs eingetragen. EVE schreibt beim Plündern nichts mit, deshalb steht dort nur, was du selbst hinterlegt hast.':\n 'Per character and day. Bounties come from the game logs, rewards and time bonuses from the wallet journal, and the loot is what you entered on the runs. EVE records nothing when you loot, so that column only holds what you put there yourself.',\n// Loot pro Tag
'Pro Tag':'Per day','Runs':'Runs','Belohnung':'Reward','Loot':'Loot','Gesamt':'Total',
'Was an einem Tag zusammenkam, je Charakter. Bounty kommt aus den Gamelogs, die Belohnung aus dem Wallet-Journal, der Loot ist von dir eingetragen. EVE schreibt beim Plündern nichts mit, deshalb steht dort nur, was du selbst an den Runs hinterlegt hast.':
 'What a day brought in, per character. Bounties come from the game logs, rewards from the wallet journal, and the loot is what you entered yourself. EVE records nothing when you loot, so that column only holds what you put on the runs.',
'* An diesen Tagen gibt es Runs ohne eingetragenen Loot. Die Summe ist dann niedriger als das, was wirklich rumkam.':
 '* On those days there are runs with no loot entered. The total is then lower than what actually came in.',
'Noch nichts erfasst. Sobald ein Run abgeschlossen ist, steht er hier.':
 'Nothing recorded yet. As soon as a run is finished it shows up here.',
// Spaltenkoepfe und Erklaerungen der Analyse
'Waffe':'Weapon','Schaden':'Damage','Tag':'Day','Zeit':'Time',
'Angreifer':'Attacker','Zuletzt':'Last seen','Dein Charakter':'Your character',
'ISK je m³':'ISK per m³','bisher gefoerdert':'mined so far','Wert davon':'Value of that',
'Alles, was ueber die Schiffs-Kompression gelaufen ist. Das Volumen ist das der komprimierten Bloecke, nicht das des Roherzes.':
 'Everything run through ship compression. The volume is that of the compressed blocks, not of the raw ore.',
'Was lohnt sich am meisten pro Laderaum? Die erste Spalte entscheidet, die beiden anderen zeigen, wie viel du davon bisher gefoerdert hast.':
 'What pays best per unit of cargo space? The first column is the one that decides, the other two show how much of it you have mined so far.',
'Womit du deinen Schaden gemacht hast, aus dem Kampflog.':
 'What you dealt your damage with, taken from the combat log.',
'Die letzten 14 Tage, gerechnet aus den Zeiten in deinen Logdateien.':
 'The last 14 days, worked out from the timestamps in your log files.',
'Wer dich als Spieler angegriffen hat, ueber den gesamten Zeitraum. NPCs stehen hier nicht.':
 'Which players have attacked you, over the whole period. NPCs are not listed here.',
// Spaltenkoepfe und Erklaerungen der Gesamt-Ansicht
'Volumen':'Volume','Wert':'Value','Charakter':'Character','Bounties':'Bounties',
'ISK gesamt = Erz-Wert + Bounties. Der Erz-Wert rechnet mit den heutigen Marktpreisen, nicht mit denen von damals. Beim Zeigen auf eine Kachel steht, was genau dahintersteckt.':
 'Total ISK = ore value + bounties. The ore value uses today\\'s market prices, not the ones back then. Hover a tile to see exactly what is behind it.',
'Erz-Wert plus Bounties. Das ist die Summe, die unten in der Spalte ISK gesamt je Charakter noch einmal aufgeteilt steht.':
 'Ore value plus bounties. This is the sum broken down per character in the Total ISK column below.',
'Was dein gefoerdertes Erz zu den heutigen Marktpreisen der gewaehlten Region bringen wuerde. Nicht das, was du damals dafuer bekommen hast.':
 'What your mined ore would fetch at today\\'s market prices in the selected region. Not what you were paid for it at the time.',
'Kopfgeld fuer abgeschossene NPCs, so wie es im Log steht. Loot und Missionsbelohnungen sind nicht enthalten.':
 'Bounties for NPCs you destroyed, exactly as the log records them. Loot and mission rewards are not included.',
'Gesamtvolumen des gefoerderten Erzes in Kubikmetern, unkomprimiert gerechnet.':
 'Total volume of the ore you mined, in cubic metres, counted uncompressed.',
'Der Tag mit dem hoechsten ISK-Ertrag. Das Datum steht unter den Kacheln.':
 'The day with the highest ISK yield. The date is shown below the tiles.',
'Schaden, den du ausgeteilt hast, und Schaden, den du eingesteckt hast. Beides aus dem Kampflog, ueber den gesamten Zeitraum.':
 'Damage you dealt and damage you took. Both from the combat log, over the whole period.',
'Alles zusammengezählt, seit Canary mitschreibt. ISK gesamt ist Erz-Wert plus Bounties. Der Erz-Wert ist das, was dein Erz heute am Markt bringen würde, nicht das, was du damals dafür bekommen hast. Bounties sind Kopfgelder für abgeschossene NPCs. Bester Tag meint den Tag mit dem höchsten ISK-Ertrag. In den Tabellen sagen die Spaltenköpfe, welche Zahl Menge, Volumen und Wert ist.':
 'Everything added up since Canary started recording. Total ISK is ore value plus bounties. The ore value is what your ore would fetch on the market today, not what you were paid for it at the time. Bounties are the rewards for NPCs you destroyed. Best day means the day with the highest ISK yield. In the tables, the column headers tell you which number is quantity, volume and value.',
'Klassisch (das gewohnte Canary-Design)':'Classic (the familiar Canary look)',
'Sekunden ohne Erz bis zur Stillstand-Warnung (0 = aus)':'Seconds without ore before the idle warning (0 = off)',
'Sekunden Karenz, bevor eine Modul-Warnung erscheint (0 = sofort)':'Seconds of grace before a module warning appears (0 = at once)',
'⛔ wann die Meldung „Laser aus, neues Ziel erfassen" kommt':'⛔ when the message "laser off, acquire a new target" appears',
'immer, bei jeder Abschaltung':'always, on every cutout',
'nur wenn die Ausbeute einbricht':'only when the yield drops',
'nur wenn gar kein Erz mehr kommt':'only when no ore arrives at all',
'gar nicht':'never',
'<b>immer</b> meldet jede Abschaltung, auch wenn du sofort nachzielst. <b>Bei Einbruch</b> meldet nur, wenn deine Ausbeute wirklich fällt, das ist der sinnvolle Standard. <b>Nur bei leer</b> ist am stillsten, verschweigt aber den Ausfall eines einzelnen von mehreren Lasern, weil die übrigen weiter liefern. Wie oft du am Ende etwas siehst, hängt stark von Flottengröße, Erz und Brockengröße ab.':'<b>Always</b> reports every cutout, even when you retarget at once. <b>On a drop</b> reports only when your yield actually falls, which is the sensible default. <b>Only when empty</b> is the quietest, but it hides the failure of a single laser among several, because the others keep delivering. How often you end up seeing anything depends heavily on fleet size, ore and rock size.',
'Für Flotten-Miner: an kleinen Brocken schalten die Laser ständig ab, das ist normal und keine Störung. Canary meldet ohnehin nichts mehr, solange danach wieder Erz fließt. Wem es trotzdem zu oft blinkt, stellt hier zusätzlich eine Karenzzeit ein. Die Warnung bei einem echten Ratenverlust bleibt davon unberührt.':'For fleet miners: on small rocks the lasers cut out constantly, which is normal and not a fault. Canary already stays quiet as long as ore keeps flowing afterwards. If it still blinks too often for you, set an extra grace period here. The warning for a real drop in yield is not affected.',
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
'Im Spiel den Frachtraum oder Container öffnen, alles markieren (Strg+A) und kopieren (Strg+C), dann hier einfügen. Einzelne Zeilen wie "Compressed Veldspar 50000" funktionieren genauso. Auch die Ergebnisse der Bergbauvermessung lassen sich so einfügen, dann steht hier, wie viel Volumen und ISK im Belt liegen.':
 'Open your cargo hold or a container in game, select everything (Ctrl+A) and copy (Ctrl+C), then paste it here. Single lines like "Compressed Veldspar 50000" work just as well. Survey scanner results can be pasted the same way, then you see how much volume and ISK the belt holds.',
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
'Zeigt dir, was ein Lauf eingebracht hat. Du fügst deinen Frachtraum zweimal ein, einmal vor und einmal nach der Mission oder dem Abyss, und Canary rechnet aus, was dazugekommen und was verbraucht worden ist. Das Ergebnis lässt sich mit einem Klick kopieren und passt in das Loot-Feld einer Mission.':
 'Shows what a run brought in. You paste your cargo hold twice, once before and once after the mission or the abyss, and Canary works out what was added and what was used up. The result copies with one click and fits the loot field of a mission.',
'Daten: nur der Text, den du selbst einfügst, verglichen auf diesem Rechner. Erst wenn du auf Wert berechnen klickst, werden Marktpreise geholt, dabei gehen nur die Item-Namen raus.':
 'Data: only the text you paste yourself, compared on this machine. Market prices are fetched only when you click get the value, and only the item names leave your computer.',
'Daten: Marktpreise von Fuzzwork für die großen Handelsplätze. Der Text, den du einfügst, bleibt auf deinem Rechner.':
 'Data: market prices from Fuzzwork for the major trade hubs. The text you paste stays on your machine.',
'Anonym mitzählen lassen':'Let this install be counted anonymously',
'Erz-Erträge für die Homepage-Statistik freigeben':'Share ore yields for the homepage statistics',
'Standardmäßig aus. Ist es an, holt Canary einmal im Monat eine weitere leere Datei, deren Name die Größenklasse deiner Fördermenge des Vormonats trägt (zum Beispiel „ab 3 Mio m³"). Auch hier wird nichts gesendet: keine genaue Zahl, keine Kennung, keine Namen, keine Charaktere, keine Orte. Aus der Summe aller Klassen entsteht auf der Homepage eine Gesamtmenge, die bewusst als Untergrenze ausgewiesen wird. Deine eigenen Zahlen bleiben auf deinem Rechner, verraten wird allein die Größenordnung.':
 'Off by default. When on, Canary fetches one more empty file once a month whose name carries the size band of what you mined last month (for example "from 3M m³ up"). Nothing is sent here either: no exact figure, no identifier, no names, no characters, no locations. Adding up all the bands produces a total on the homepage that is deliberately published as a lower bound. Your own numbers stay on your machine, only the order of magnitude is revealed.',
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
 [/Bonus-Erträge \\(([0-9]+) von ([0-9]+)/, 'Bonus yields ($1 of $2'],
 [/abgeschaltet, Drohnen prüfen!/, 'switched off, check drones!'],
 [/abgeschaltet, Ziel prüfen/, 'switched off, check target'],
 [/Seit ([0-9]+) Minuten kein Erz/, 'No ore for $1 minutes'],
 [/Kein Erz seit/, 'No ore for'],
 [/^Ziel: /, 'Goal: '],
 // Einheiten mit g: sie stehen oft mehrfach in EINEM Textknoten, etwa
 // "1.59 Mrd / 2.50 Mrd (63.7%)" in der Ziel-Zeile. Ohne g wurde nur die
 // erste ersetzt und es stand "1.59 bn / 2.50 Mrd" da.
 [/ Mrd/g, ' bn'], [/ Stk/g, ' units'],
 [/seit Abdocken/, 'since undocking'], [/Preise:/, 'Prices:'],
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
 // Bekannte Gank-Gruppe naehert sich. MUSS vor dem allgemeinen
 // "([0-9.]+) Sprünge"-Muster weiter unten stehen: sonst ersetzt das zuerst
 // nur die Sprungzahl und der Rest der Zeile bleibt deutsch stehen.
 [/Achtung, (.+?): Rudel nähert sich, ([0-9]+) → ([0-9]+) Sprünge \\((.+?)\\)\\. ([0-9]+) Miner-Kills zuletzt\\./,
  'Caution, $1: pack closing in, $2 to $3 jumps ($4). $5 miner kills recently.'],
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
let tickBusy=false,tickErneut=false;
async function tick(){
 // Laeuft schon eine Abfrage, wird der Wunsch GEMERKT statt verworfen. Vorher
 // fiel ein Tab-Klick in diesem Fall ersatzlos aus und die Ansicht wechselte
 // erst beim naechsten Intervall: gemessen bis zu 1.755 ms, in denen der alte
 // Inhalt stehen blieb und nichts passierte.
 if(tickBusy){tickErneut=true;return;}
 tickBusy=true;
 const reqView=view;  // View einfrieren: nach dem await zählt der Stand von JETZT
 try{
  // Der Wallet-Bereich hat einen eigenen Zeitraum (7/30/alles), der Server
  // rechnet die Bilanz danach. Bei allen anderen Ansichten bleibt die URL wie sie war.
  const zusatz=(reqView==='wallet')?('&days='+walletTage):'';
  const d=await (await fetch('/data?view='+reqView+zusatz,{cache:'no-store'})).json();
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
   else if(view==='wallet')renderWallet(d.wallet);
   else if(view==='rechner')renderRechner();
   else if(view==='beute')renderBeute();
   else renderTotal(d.total);
  }
  if(lang!=='de')tr(document.body);   // frisch gerenderte Teile nachuebersetzen
 }catch(e){}
 finally{
  tickBusy=false;
  if(tickErneut){tickErneut=false;tick();}   // gemerkten Wunsch sofort nachholen
  else ladeAus();
 }
}
document.querySelectorAll('.langsel').forEach(b=>b.onclick=()=>{setLang(b.dataset.l);tick();});
setLang(lang);
tick();setInterval(tick,2000);

// Einmaliger Gas-Hinweis nach dem Update. Der Schluessel haengt am THEMA, nicht
// an der Version: einmal weggeklickt, kommt er nie wieder, auch nach spaeteren
// Updates nicht. Steht bewusst GANZ AM ENDE des Skripts, denn hier sind lang,
// tr() und setLang() fertig initialisiert — weiter oben wuerde der Zugriff auf
// das spaeter mit let deklarierte lang eine ReferenceError werfen und damit den
// ganzen Rest des Skripts (und das Dashboard) stilllegen.
(function(){
 const dlg=$('#newsGas'); if(!dlg||!dlg.showModal) return;
 try{ if(localStorage.getItem('news_gas')==='1') return; }catch(e){ return; }
 const zu=()=>{ try{localStorage.setItem('news_gas','1');}catch(e){} };
 $('#newsGasOk').onclick=()=>dlg.close();
 dlg.addEventListener('close',zu);
 if(lang!=='de')tr(dlg);
 dlg.showModal();
})();
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
    # Eine laufende Stoppuhr ueberlebt den Neustart: wer waehrend eines Trips
    # aktualisiert, soll nicht von vorn anfangen muessen.
    uhr_laden()
    # Die selbst benannten Missionen als Vorlagen einlesen. Muss vor der ersten
    # Abfrage stehen, sonst waere der Fingerabdruck bis zur ersten Benennung leer.
    marken_laden()
    # Einmal nachsehen, ob die Installation vollstaendig ist, und
    # nachholen was fehlt. Im Hintergrund, damit der Start nicht wartet.
    threading.Thread(target=pruefe_daten, daemon=True,
                     name="DatenPruefung").start()
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

    # Zweiter Lauscher auf dem IPv6-Loopback. Grund: "localhost" loest unter
    # Windows ZUERST auf ::1 auf. Lauscht dort niemand, wartet der Client auf
    # die Abweisung — gemessen 2.037 ms bei Python/curl, 192 ms in Chrome, und
    # das bei JEDER Verbindung. Mit diesem Lauscher ist localhost genauso schnell
    # wie 127.0.0.1 (gemessen 6 ms). ::1 ist Loopback wie 127.0.0.1, es wird also
    # nichts nach aussen geoeffnet, und _host_ok laesst ::1 ohnehin schon zu.
    # Scheitert der Bind (kein IPv6 im System), laeuft Canary einfach ohne ihn.
    srv6 = None
    try:
        class Server6(Server):
            address_family = socket.AF_INET6

        srv6 = Server6(("::1", port), Handler)
        threading.Thread(target=srv6.serve_forever, daemon=True).start()
    except OSError as e:
        log_error("CN-SRV-02", "IPv6-Lauscher", e)
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
