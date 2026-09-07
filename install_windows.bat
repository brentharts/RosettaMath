@echo off
setlocal

rem  RosettaMath -- Windows installer.
rem
rem  Double-click this file.  It installs what rosettaui.py needs, then reports
rem  what it found.  Nothing here has to be typed at a prompt.
rem
rem  Everything installs for the current user only, so no administrator rights
rem  are needed and nothing outside your account is touched.
rem
rem  Note on style: this file checks results with `if errorlevel N` and jumps to
rem  labels rather than putting %errorlevel% inside ( ) blocks.  cmd.exe expands
rem  %errorlevel% when it *parses* a block, not when it runs it, so the tested
rem  value would be the one from before the command -- the single most common
rem  bug in batch files.

cd /d "%~dp0"

echo.
echo  ==============================================================
echo   RosettaMath -- installing dependencies for Windows
echo  ==============================================================
echo.

rem ---------------------------------------------------------------- Python
rem  The py.exe launcher ships with the python.org installer and is the
rem  dependable way to find Python.  Bare `python` is not: Windows provides a
rem  stub of that name which opens the Microsoft Store rather than running
rem  anything, and it reports success while doing it.

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
echo  [X] Python 3 was not found.
echo.
echo      Install it and run this file again.
echo.
echo      Option A ^(easiest^) -- press the Windows key, type "terminal",
echo      open it, and paste in this line:
echo.
echo          winget install Python.Python.3.12
echo.
echo      Option B -- download from https://www.python.org/downloads/
echo      IMPORTANT: on the first screen of that installer, tick the box
echo      "Add python.exe to PATH" before you click Install.
echo.
goto :done

:got_python
for /f "delims=" %%v in ('%PY% --version 2^>^&1') do set PYVER=%%v
echo  [ok] Found %PYVER%
echo.

rem ---------------------------------------------------------------- PyQt5
echo  Installing PyQt5 ^(the graphical interface^)...
%PY% -m pip install --user --upgrade pip >nul 2>&1
%PY% -m pip install --user PyQt5
if errorlevel 1 goto :pyqt_failed
echo  [ok] PyQt5 installed.
echo.
goto :scipy

:pyqt_failed
echo.
echo  [X] PyQt5 did not install.  The reason is in the output above;
echo      it is usually no internet connection, or a proxy.
goto :done

rem ---------------------------------------------------------------- scipy
rem  Optional.  Without it the generated Python still runs, but the physical
rem  constants it imports will not resolve.
:scipy
echo  Installing scipy ^(optional -- lets generated code resolve constants^)...
%PY% -m pip install --user scipy
if errorlevel 1 goto :scipy_skipped
echo  [ok] scipy installed.
echo.
goto :tex

:scipy_skipped
echo  [--] scipy did not install.  Not fatal; carrying on.
echo.

rem ---------------------------------------------------------------- MiKTeX
rem  Needed only for the "Typeset with pdflatex" button and for building the
rem  paper.  It is a large download, so ask rather than assume.  MiKTeX also
rem  bundles pdftoppm, which is what turns the typeset PDF into an image, so
rem  this one install covers both of the remaining requirements.
:tex
where pdflatex >nul 2>&1
if errorlevel 1 goto :offer_tex
echo  [ok] pdflatex is already installed.
goto :check

:offer_tex
echo  pdflatex was not found.  It is OPTIONAL: without it the explorer
echo  still runs and every symbol is still clickable, but the button
echo  marked "Typeset with pdflatex" will be greyed out.
echo.
echo  Installing it is roughly a 200 MB download.
echo.
set INSTALLTEX=N
set /p INSTALLTEX=  Install MiKTeX now? [y/N] 
if /i "%INSTALLTEX%"=="y" goto :want_tex
echo.
echo  Skipped.  To add it later, run:  winget install MiKTeX.MiKTeX
goto :check

:want_tex
where winget >nul 2>&1
if errorlevel 1 goto :no_winget
echo.
echo  Installing MiKTeX -- this takes a few minutes...
winget install --id MiKTeX.MiKTeX --accept-source-agreements --accept-package-agreements
echo.
echo  Note: MiKTeX fetches each LaTeX package the first time it is actually
echo  needed, so your first typeset may pause and show a progress box.
goto :check

:no_winget
echo.
echo  [X] winget is not available on this machine.
echo      Download MiKTeX by hand instead: https://miktex.org/download

:check
echo.
echo  ==============================================================
echo   Checking what is installed
echo  ==============================================================
echo.

rem  A fresh install edits PATH, but this window inherited the old copy, so
rem  `where pdflatex` can still say no immediately after installing.
rem  rosettaui.py also looks in the standard install directories, so let it
rem  give the authoritative answer.
%PY% rosettaui.py --check-deps

echo.
echo  ==============================================================
echo   Finished.  To start RosettaMath, double-click:  run_windows.bat
echo  ==============================================================

:done
echo.
pause
endlocal
