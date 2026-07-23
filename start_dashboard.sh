#!/usr/bin/env sh
# EVE Canary starten (Linux/macOS). Gegenstueck zu start_dashboard.bat.
cd "$(dirname "$0")" || exit 1

PY=""
for c in python3 python; do
  if command -v "$c" >/dev/null 2>&1 && "$c" -c 'import sys; sys.exit(0 if sys.version_info[0]==3 else 1)' 2>/dev/null; then
    PY="$c"
    break
  fi
done

if [ -z "$PY" ]; then
  echo
  echo " Python 3 wurde nicht gefunden!"
  echo " Bitte ueber die Paketverwaltung installieren, zum Beispiel:"
  echo "   Ubuntu/Debian:  sudo apt install python3"
  echo "   Fedora:         sudo dnf install python3"
  echo "   Arch:           sudo pacman -S python"
  echo
  exit 1
fi

# Der Browser wird aus dem Python-Code geoeffnet, sobald der Server laeuft.
exec "$PY" eve_dashboard.py "$@"
