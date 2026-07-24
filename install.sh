#!/usr/bin/env sh
# EVE Canary Installer fuer Linux (Gegenstueck zu install.ps1).
# Aufruf:  curl -fsSL <repo>/install.sh | sh
set -eu

REPO="${CANARY_REPO:-https://raw.githubusercontent.com/Eve-Online-Askend/eve-canary/main}"
DIR="${CANARY_DIR:-${XDG_DATA_HOME:-$HOME/.local/share}/eve-canary}"

echo ""
echo "  EVE Canary wird installiert"
echo ""

PY=""
for c in python3 python; do
  if command -v "$c" >/dev/null 2>&1 && "$c" -c 'import sys; sys.exit(0 if sys.version_info[0]==3 else 1)' 2>/dev/null; then
    PY="$c"
    break
  fi
done
if [ -z "$PY" ]; then
  echo "  Python 3 wurde nicht gefunden."
  echo "  Bitte ueber die Paketverwaltung installieren, zum Beispiel:"
  echo "    Ubuntu/Debian:  sudo apt install python3"
  echo "    Fedora:         sudo dnf install python3"
  echo "    Arch:           sudo pacman -S python"
  echo "  Danach diesen Befehl noch einmal ausfuehren."
  exit 1
fi
echo "  Python gefunden ($PY)"

if command -v curl >/dev/null 2>&1; then
  DL='curl -fsSL -o'
elif command -v wget >/dev/null 2>&1; then
  DL='wget -q -O'
else
  echo "  Weder curl noch wget gefunden. Bitte eines davon installieren."
  exit 1
fi

FILES="eve_dashboard.py ore_types.json mining_tools.json mission_sigs.json market_types.json README_INSTALL.md start_dashboard.sh"

# Erst vollstaendig in einen Temp-Ordner laden, dann ans Ziel verschieben, damit
# ein abgebrochener Download keine halbe Installation hinterlaesst.
TMP="$(mktemp -d)"
trap 'rm -rf "$TMP"' EXIT INT TERM

# Bevorzugt vom GitHub-Release laden: nur dort zaehlt GitHub die Downloads.
# Klappt das nicht, geht es ueber raw weiter, die Installation haengt nicht daran.
RELBASE=""
if $DL "$TMP/version.json" "$REPO/version.json" 2>/dev/null; then
  SLUG=$(sed -n 's/.*"repo"[^"]*"\([^"]*\)".*/\1/p' "$TMP/version.json")
  TAG=$(sed -n 's/.*"tag"[^"]*"\([^"]*\)".*/\1/p' "$TMP/version.json")
  [ -n "$SLUG" ] && [ -n "$TAG" ] && RELBASE="https://github.com/$SLUG/releases/download/$TAG"
  rm -f "$TMP/version.json"
fi

for f in $FILES; do
  got=""
  if [ -n "$RELBASE" ] && $DL "$TMP/$f" "$RELBASE/$f" 2>/dev/null && [ -s "$TMP/$f" ]; then
    got=1
  elif $DL "$TMP/$f" "$REPO/$f" && [ -s "$TMP/$f" ]; then
    got=1
  fi
  if [ -z "$got" ]; then
    echo ""
    echo "  Download fehlgeschlagen bei: $f"
    echo "  Es wurde nichts installiert. Bitte Internetverbindung pruefen."
    exit 1
  fi
  echo "  geladen: $f"
done

mkdir -p "$DIR"
for f in $FILES; do
  mv -f "$TMP/$f" "$DIR/$f"
done
chmod +x "$DIR/start_dashboard.sh"

# Startmenue-Eintrag (XDG). Funktioniert in GNOME, KDE, XFCE gleichermassen.
APPS="${XDG_DATA_HOME:-$HOME/.local/share}/applications"
mkdir -p "$APPS"
cat > "$APPS/eve-canary.desktop" <<EOF
[Desktop Entry]
Type=Application
Name=EVE Canary
Comment=Mining- und Missions-Dashboard fuer EVE Online
Exec="$DIR/start_dashboard.sh"
Path=$DIR
Terminal=false
Categories=Game;Utility;
EOF
command -v update-desktop-database >/dev/null 2>&1 && update-desktop-database "$APPS" 2>/dev/null || true

echo ""
echo "  Fertig. Canary liegt in: $DIR"
echo "  Start ueber das Startmenue (EVE Canary) oder:"
echo "    $DIR/start_dashboard.sh"
echo ""
echo "  Hinweis: EVE laeuft unter Linux ueber Proton/Wine. Canary sucht die"
echo "  Logs in den Steam- und Wine-Praefixen selbst. Wird nichts gefunden,"
echo "  den Pfad in den Optionen eintragen (Ordner 'Gamelogs')."
echo ""

cd "$DIR"
exec ./start_dashboard.sh
