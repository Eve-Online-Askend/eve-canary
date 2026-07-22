@echo off
cd /d "%~dp0"
setlocal
set PY=

rem py-Launcher bevorzugen (umgeht den Windows-Store-Alias-Stub, der bei
rem "python" ohne echte Installation nur den Store oeffnet).
py -3 --version >nul 2>nul
if not errorlevel 1 (
  set PY=py -3
) else (
  rem Pruefen, ob "python" wirklich Python 3 ist (nicht der Store-Stub)
  for /f "tokens=1,2" %%a in ('python --version 2^>^&1') do (
    if /i "%%a"=="Python" set PY=python
  )
)

if "%PY%"=="" (
  echo.
  echo  Python 3 wurde nicht gefunden!
  echo  Bitte von https://www.python.org/downloads/ installieren
  echo  und beim Setup "Add Python to PATH" anhaken.
  echo.
  pause
  exit /b 1
)

rem Der Browser wird aus dem Python-Code geoeffnet, sobald der Server wirklich
rem laeuft (sonst zeigt der Tab beim Erststart "Verbindung abgelehnt").
%PY% eve_dashboard.py
pause
