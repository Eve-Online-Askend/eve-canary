# EVE Canary 🐤

**Der Kanarienvogel im Bergwerk**: ein lokales Live-Dashboard für EVE Online.
Es liest die Spiel-Logs deines Clients, warnt bevor es teuer wird, und zeigt
live, was dein Abend wirklich bringt. Alles auf deinem eigenen Rechner, ohne
Konto, ohne Cloud.

*A local live dashboard for EVE Online, reading your game logs. Everything
stays on your machine. The dashboard speaks German and English, the homepage
also French and Russian.*

**Homepage & Details:** https://eve-online-askend.github.io/eve-canary/ ·
**Discord:** https://discord.gg/tKevTeqG

## Was es kann

- ⛏ **Mining live**: Erz, m³/h, ISK-Wert je Handelsplatz, Kompression,
  Laderaum-Schätzung, Bonus-Erkennung. Je Charakter, Multiboxing-tauglich,
  mit eigener Karten-Reihenfolge und einstellbarer Kartenbreite.
- 🚨 **Alarme mit Sprachausgabe**: Spieler-Angriff (Eigenbeschuss der eigenen
  Charaktere ausgenommen), Asteroid leer, Frachtraum voll, Drohnen inaktiv,
  Laser aus, Mining-Stillstand.
- 🩸 **Blutspur**: Gank-Rudel-Radar aus dem öffentlichen Killmail-Feed, mit
  Ego-Karte, bekannten Gank-Gruppen und Annäherungs-Warnung.
- 🎯 **Missionen**: Erkennung über Gegner, Funk, Fracht und Fingerabdruck,
  mit Genauigkeit in Prozent, Fraktions-Tipp (was schießen, was tanken),
  EWAR-Profil, verifizierten Belohnungen und Loot-Erfassung.
- 🌀 **Abyss**: Durchgänge mit Stufe und Wetter, Uhr gegen die 20-Minuten-Grenze,
  Export zum Teilen.
- 💼 **Job-Börse**: öffentliche Freelance-Aufträge mit Erz-Bezug, gruppiert je
  Sorte, umgerechnet auf die eigene Förderrate, mit Warnung vor Fallen-Sätzen.
- 💎 **Erz-Schatzkammer & Verwertungs-Berater**: Bestand in den Stationen und
  was sich mehr lohnt, roh verkaufen, komprimiert verkaufen oder raffinieren.
- 🧾 **Wallet Buddy**: Handelsbilanz mit FIFO-Gewinn, Gebühren und Steuern,
  Einnahmen und Ausgaben je Kategorie (mit EVE-Login).
- 🪐 **Planetary Industry**: Extraktor-Abläufe, Lagerwert, Produkte und
  Ertragsprognose (mit EVE-Login).
- 🕑 **Verlauf, Steckbrief, Statistik**: der Tag als Zeitstrahl, Spielstil-Radar
  je Charakter, 30 Tage und Gesamt, Spielzeit über alle Clients.
- 🎥 **OBS-Stream-Overlay**: Rollen je Charakter (Mining, Mission, PvP), Schaden
  raus und rein, Kill-Zähler mit zerstörten und verlorenen ISK, ESI-Haken,
  Downtime-Countdown, Flottensumme. Dazu ein Always-on-top-Mini-Overlay.
- 📦 **Beute-Rechner & ISKray**: Frachtraum vorher gegen nachher, und ein
  Preisrechner für alles, was sich kopieren lässt.
- 🔒 **Alles lokal und EULA-konform**: liest nur die Text-Logs des Clients,
  Client-Sprache egal, kein Konto nötig. Der EVE-Login ist optional und
  schaltet nur Zusatzdaten frei (Wallet, Bestände, Planeten).

## Installation

Ein Befehl, mehr nicht. Python wird bei Bedarf mitinstalliert.

**Windows** (PowerShell):

```
irm https://raw.githubusercontent.com/Eve-Online-Askend/eve-canary/main/install.ps1 | iex
```

**Linux** (EVE über Steam/Proton oder Wine) und **macOS** (experimentell):

```
curl -fsSL https://raw.githubusercontent.com/Eve-Online-Askend/eve-canary/main/install.sh | sh
```

Canary findet den Log-Ordner selbst, auch im Wine-Präfix. Details und
Handarbeit-Variante: [README_INSTALL.md](README_INSTALL.md).

## Updates

Der Versions-Chip im Kopf zeigt, ob du aktuell bist. Ein Klick installiert,
Canary startet sich selbst neu, auch das OBS-Overlay lädt sich danach von
allein. Wer mag, schaltet in den Optionen das Auto-Update ein, dann hält sich
Canary selbst aktuell. Geladen wird nur aus den Releases dieses Repositorys,
und der neue Code wird vor dem Einspielen geprüft.

## Mitmachen

Meldungen und Ideen kommen aus der Community und stehen oft noch am selben Tag
als Release im [Changelog](changelog.json), mit Namensnennung. Der kürzeste
Weg ist der Discord oben, für Missionsdaten gibt es ein
[eigenes Formular](https://eve-online-askend.github.io/eve-canary/mission.html).
