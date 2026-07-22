@echo off
cd /d "%~dp0"
set PY=python
where python >nul 2>nul
if errorlevel 1 (
  where py >nul 2>nul
  if errorlevel 1 (
    echo.
    echo  Python wurde nicht gefunden!
    echo  Bitte von https://www.python.org/downloads/ installieren
    echo  und beim Setup "Add Python to PATH" anhaken.
    echo.
    pause
    exit /b 1
  )
  set PY=py -3
)
start "" http://localhost:8765
%PY% eve_dashboard.py
pause
