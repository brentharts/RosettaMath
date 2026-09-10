# macOS has no system package for PyQt5, and both Homebrew's Python and Apple's
# refuse `pip install` into themselves (PEP 668, "externally-managed
# environment").  install_apple therefore builds a virtualenv here, and every
# target below picks it up automatically once it exists.  Linux is unaffected:
# without a .venv this is plain python3, exactly as before.
ifeq ($(wildcard .venv/bin/python),)
PYTHON ?= python3
else
PYTHON ?= .venv/bin/python
endif

# What each package is actually needed for:
#   python3-pyqt5 ............ the rosettaui.py interface
#   texlive-latex-base ....... pdflatex, amsmath, amssymb, geometry
#   texlive-latex-recommended  listings (the source appendix)
#   texlive-latex-extra ...... orcidlink (the paper's title block)
#   texlive-science .......... algorithm, algpseudocode (the pseudocode blocks)
#   fonts-lmodern ............ Latin Modern Roman and Latin Modern Math, the
#                              fonts rosettaui.py renders equations with
#   poppler-utils ............ pdftoppm, used to rasterise typeset fragments
APT_PACKAGES = \
	python3 \
	python3-pyqt5 \
	texlive-latex-base \
	texlive-latex-recommended \
	texlive-latex-extra \
	texlive-science \
	fonts-lmodern \
	poppler-utils

# Not required, but nice to have:
#   python3-scipy ... so the constants in generated code resolve
#   imagemagick ..... trims whitespace from typeset previews
#   ghostscript ..... lets ImageMagick read PDFs, if poppler is absent
APT_OPTIONAL = \
	python3-scipy \
	imagemagick \
	ghostscript \
	python3-gi \
	gir1.2-evince-3.0

default:
	$(PYTHON) rosettaui.py

much:
	$(PYTHON) rosettaui.py --arxiv https://arxiv.org/abs/2510.24491

danny:
	$(PYTHON) rosettaui.py --arxiv https://arxiv.org/abs/1011.6654


help:
	@echo 'make install        install everything needed (Ubuntu/Debian)'
	@echo 'make install-all    the above, plus the optional extras'
	@echo 'make install_apple  install everything needed (macOS, via Homebrew)'
	@echo 'make check-deps     report what is present and what is missing'
	@echo 'make ui             launch the interactive explorer'
	@echo 'make test           run every self test'
	@echo 'make proofs         check the lean4 theorems'
	@echo 'make pdf            typeset the paper to /tmp/neomath.pdf'
	@echo 'make paper          the paper with the source appendix'
	@echo 'make crustos_eq     the supplement: Equation (1) checked by Lean 4'
	@echo 'make clean          remove caches and build products'
	@echo
	@echo 'Windows has no make: double-click install_windows.bat, then'
	@echo 'run_windows.bat.  See the Install section of README.md.'

install:
	sudo apt-get update
	sudo apt-get install -y --no-install-recommends $(APT_PACKAGES)
	@echo
	@echo 'Installed. Run "make check-deps" to verify, "make ui" to start.'

install-all: install
	sudo apt-get install -y --no-install-recommends $(APT_OPTIONAL)

# ------------------------------------------------------------------ macOS
#
# What the Homebrew names correspond to:
#   mactex-no-gui ... the full TeX Live, minus the GUI apps we never invoke.
#                     It is a large download (~5 GB) but it is the only cask
#                     that contains everything the paper needs -- orcidlink,
#                     algpseudocode and listings are not in BasicTeX.  It also
#                     ships pdftoppm and the Latin Modern OTFs, so it covers
#                     the rasteriser and the fonts at the same time.
#   poppler ......... pdftoppm on its own, as a fallback and for a lighter
#                     install; harmless alongside MacTeX.
#
# PyQt5 goes into a virtualenv rather than the system Python: see the note at
# the top of this file.  The cask install will ask for your password, since
# TeX Live installs outside your home directory.
#
# Lighter alternative, if 5 GB is too much:
#   brew install --cask basictex
#   sudo tlmgr update --self
#   sudo tlmgr install orcidlink algorithms algorithmicx listings lm lm-math
APPLE_BREW = poppler
APPLE_BREW_OPTIONAL = imagemagick ghostscript

install_apple:
	@command -v brew >/dev/null 2>&1 || { \
		echo 'Homebrew is required.  Install it with:'; \
		echo; \
		echo '  /bin/bash -c "$$(curl -fsSL https://raw.githubusercontent.com/Homebrew/install/HEAD/install.sh)"'; \
		echo; \
		echo 'then run "make install_apple" again.'; \
		exit 1; }
	brew install $(APPLE_BREW)
	brew install --cask mactex-no-gui
	python3 -m venv .venv
	.venv/bin/python -m pip install --upgrade pip
	.venv/bin/python -m pip install PyQt5 scipy
	@echo
	@echo 'Installed.  MacTeX puts its binaries in /Library/TeX/texbin, which'
	@echo 'this shell will not have on PATH until you open a new one --'
	@echo 'rosettaui.py looks there directly, so it works either way.'
	@echo
	@echo 'Run "make check-deps" to verify, "make ui" to start.'

# Same, plus the extras that only improve the typeset previews.
install_apple-all: install_apple
	brew install $(APPLE_BREW_OPTIONAL)

# Dash-spelled alias, to match install-all.
install-apple: install_apple

# ---------------------------------------------------------------- Windows
#
# make is not present on a stock Windows box, so this target exists only to
# answer someone who found the Makefile first and tried the obvious thing.
install_windows:
	@echo 'Windows does not use make.  In File Explorer, open this folder and'
	@echo 'double-click:'
	@echo
	@echo '    install_windows.bat     installs the dependencies'
	@echo '    run_windows.bat         starts the explorer'
	@echo
	@echo 'See the Install section of README.md for the details.'

install-windows: install_windows

# Reports rather than fails, so it stays useful on a partly configured machine.
#
# The extra PATH entry is where MacTeX symlinks its binaries.  It is added to
# the real PATH by /etc/paths.d, which only login shells read, so make cannot
# rely on having inherited it.  On Linux the directory does not exist and the
# entry is simply ignored.
check-deps: PATH := $(PATH):/Library/TeX/texbin
check-deps:
	@echo 'required:'
	@$(PYTHON) -c 'import PyQt5' 2>/dev/null \
		&& echo '  PyQt5           ok' || echo '  PyQt5           MISSING  (python3-pyqt5)'
	@command -v pdflatex >/dev/null \
		&& echo '  pdflatex        ok' || echo '  pdflatex        MISSING  (texlive-latex-base)'
	@kpsewhich algpseudocode.sty >/dev/null 2>&1 \
		&& echo '  algpseudocode   ok' || echo '  algpseudocode   MISSING  (texlive-science)'
	@kpsewhich orcidlink.sty >/dev/null 2>&1 \
		&& echo '  orcidlink       ok' || echo '  orcidlink       MISSING  (texlive-latex-extra)'
	@kpsewhich listings.sty >/dev/null 2>&1 \
		&& echo '  listings        ok' || echo '  listings        MISSING  (texlive-latex-recommended)'
	@# kpsewhich first: macOS has no fontconfig, and rosettaui.py loads these
	@# straight out of the texmf tree anyway, so presence there is what counts.
	@{ kpsewhich latinmodern-math.otf >/dev/null 2>&1 \
		|| fc-list 2>/dev/null | grep -qi 'latinmodern-math'; } \
		&& echo '  Latin Modern    ok' \
		|| echo '  Latin Modern    MISSING  (fonts-lmodern / MacTeX)'
	@command -v pdftoppm >/dev/null \
		&& echo '  pdftoppm        ok' || echo '  pdftoppm        MISSING  (poppler-utils)'
	@echo 'optional:'
	@$(PYTHON) -c 'import scipy' 2>/dev/null \
		&& echo '  scipy           ok' || echo '  scipy           missing  (python3-scipy)'
	@command -v convert >/dev/null \
		&& echo '  imagemagick     ok' || echo '  imagemagick     missing  (imagemagick)'
	@command -v gs >/dev/null \
		&& echo '  ghostscript     ok' || echo '  ghostscript     missing  (ghostscript)'
	@# Linux only, and optional: it drives the side-by-side PDF viewer.
	@$(PYTHON) -c "import gi; gi.require_version('EvinceDocument','3.0')" \
		>/dev/null 2>&1 \
		&& echo '  evince (pdf)    ok' \
		|| echo '  evince (pdf)    missing  (python3-gi gir1.2-evince-3.0)'

ui:
	$(PYTHON) rosettaui.py

# rosettamath.py self tests both bootstrap stages; rosettaui.py checks the
# parser, the classifier and the knowledge base.
test:
	$(PYTHON) rosettamath.py
	$(PYTHON) rosettaui.py --selftest
	$(PYTHON) lean4.py --selftest

# The micro-kernel on its own: proofs raise on failure, so this gates CI.
proofs:
	$(PYTHON) lean4.py

# Renders a sample equation offscreen, so it works without a display.
render-test:
	QT_QPA_PLATFORM=offscreen $(PYTHON) rosettaui.py --render-test

pdf:
	$(PYTHON) rosettamath.py --pdf

paper:
	$(PYTHON) rosettamath.py --pdf --appendix

# The third paper: the micro-kernel, the imperative fragment, and Crust.
leanproof:
	cd /tmp && pdflatex -interaction=nonstopmode -halt-on-error $(CURDIR)/leanproof.tex >/dev/null && pdflatex -interaction=nonstopmode $(CURDIR)/leanproof.tex >/dev/null && echo "/tmp/leanproof.pdf"

# The supplement: one equation, checked by lean4.py and by Lean 4, read four
# ways.  crustos_eq.py writes gen/ and CrustOS.lean (and runs lean if found).
crustos_eq:
	$(PYTHON) crustos_eq.py
	pdflatex -interaction=nonstopmode -halt-on-error -output-directory=/tmp crustos_eq.tex >/dev/null && pdflatex -interaction=nonstopmode -output-directory=/tmp crustos_eq.tex >/dev/null && echo "/tmp/crustos_eq.pdf"

clean:
	rm -rf __pycache__ /tmp/rosettaui-cache
	rm -f /tmp/neomath.aux /tmp/neomath.log /tmp/neomath.out /tmp/neomath.tex

.PHONY: default help install install-all check-deps ui test proofs \
	render-test pdf paper leanproof crustos_eq clean \
	install_apple install-apple install_apple-all \
	install_windows install-windows
