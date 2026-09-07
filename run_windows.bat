@echo off
setlocal

rem  RosettaMath -- Windows launcher.  Double-click to start the explorer.
rem
rem  An equation can be supplied as an argument if you are running this from a
rem  prompt:
rem
rem      run_windows.bat "E = mc^2"
rem
rem  If the window flashes and nothing appears, open a Command Prompt in this
rem  folder and run `python rosettaui.py` -- that keeps the error on screen.

cd /d "%~dp0"

set PY=
set PYW=

py -3 --version >nul 2>&1
if errorlevel 1 goto :try_python
set PY=py -3
set PYW=pyw -3
goto :got_python

:try_python
python --version >nul 2>&1
if errorlevel 1 goto :no_python
set PY=python
set PYW=pythonw
goto :got_python

:no_python
echo.
echo  Python 3 was not found.  Double-click install_windows.bat first.
echo.
pause
exit /b 1

:got_python
rem  Check the interface is importable before launching.  The launch itself is
rem  windowless, so without this check a missing dependency would fail with no
rem  message anywhere -- the window would simply never appear.
%PY% -c "import PyQt5" >nul 2>&1
if errorlevel 1 goto :no_pyqt

rem  pyw.exe / pythonw.exe are the console-free builds: the GUI opens without a
rem  black terminal window sitting behind it for the whole session.
if "%~1"=="" goto :plain
start "" %PYW% rosettaui.py --tex "%~1"
goto :eof

:plain
start "" %PYW% rosettaui.py
goto :eof

:no_pyqt
echo.
echo  PyQt5 is not installed.  Double-click install_windows.bat first.
echo.
pause
exit /b 1
