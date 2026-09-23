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

# ------------------------------------------------------------ Lean 4
#
# Optional.  Everything here runs without it -- crustos_eq.py falls back to
# lean4.py's micro-kernel alone -- but with `lean` present the generated
# CrustOS.lean is put to the real kernel as well, which is the whole point of
# the supplement.  `make install_lean` fetches one; two routes, in order.
#
#   elan     the upstream version manager.  Normal case.  It resolves
#            toolchains through release.lean-lang.org, so it needs that host
#            reachable as well as github.com.
#   tarball  the official binary release, unpacked into LEAN_PREFIX.  Used
#            when elan cannot reach its release index (locked-down networks,
#            proxies, CI images).  Only needs github.com.
#
# Neither needs root and neither touches the system prefix.  The generated
# Lean is Mathlib-free, so a bare toolchain is enough: no lake, no packages.
ELAN_HOME     ?= $(HOME)/.elan
LEAN_PREFIX   ?= $(HOME)/.local/lean
LEAN_VERSION  ?= 4.33.1
LEAN_URL_BASE ?= https://github.com/leanprover/lean4/releases/download
ELAN_INIT_URL ?= https://raw.githubusercontent.com/leanprover/elan/master/elan-init.sh

# Both routes in front of PATH for every recipe, so `make crustos_eq` finds
# lean in the same shell that ran `make install_lean`, with no sourcing of
# ~/.profile in between.  The tarball goes first: a half-installed elan
# leaves a `lean` shim that runs but has no toolchain behind it, and a real
# binary should win over that.  Neither directory existing is harmless.
export PATH := $(LEAN_PREFIX)/bin:$(ELAN_HOME)/bin:$(PATH)

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
	@echo 'make install_lean   install a Lean 4 toolchain (optional; Linux/macOS)'
	@echo 'make check-deps     report what is present and what is missing'
	@echo 'make ui             launch the interactive explorer'
	@echo 'make test           run every self test'
	@echo 'make proofs         check the lean4 theorems'
	@echo 'make pdf            typeset the paper to /tmp/neomath.pdf'
	@echo 'make paper          the paper with the source appendix'
	@echo 'make physpaper      the physics knowledge graph paper'
	@echo 'make rust_lean      Rust theorems from ../crust, checked by Lean 4'
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

# ------------------------------------------------------------------ Lean 4
#
# Unlike `install` and `install_apple` this one target covers both platforms:
# the only thing it needs from the package manager is curl and zstd, and the
# toolchain itself is the same kind of tarball on either.

install_lean: install_lean_deps
	@if command -v lean >/dev/null 2>&1 && lean --version >/dev/null 2>&1; then \
		echo "lean already present: $$(lean --version)"; \
		exit 0; \
	fi; \
	echo '==> installing elan into $(ELAN_HOME)'; \
	if curl -fsSL "$(ELAN_INIT_URL)" | sh -s -- -y --no-modify-path \
			--default-toolchain leanprover/lean4:v$(LEAN_VERSION) \
			>/dev/null 2>&1 \
		&& "$(ELAN_HOME)/bin/lean" --version >/dev/null 2>&1; then \
		echo '==> elan installed a toolchain'; \
	else \
		echo '==> elan could not fetch a toolchain; using the binary release'; \
		$(MAKE) --no-print-directory install_lean_tarball; \
	fi
	@echo
	@echo "lean: $$(lean --version)"
	@echo
	@echo '"make crustos_eq" will now put CrustOS.lean to the real kernel as'
	@echo 'well as the micro-kernel.  To get lean in your own shell:'
	@$(MAKE) --no-print-directory lean_env
	@echo

install-lean: install_lean

# LeanOS sketch: every number from the run, the PDF from pdflatex.  Lean is
# optional here as everywhere; without it the verdict macros are absent and
# the document says so by failing to build, which is the right failure.
leanos_paper:
	$(PYTHON) leanos_paper.py
	pdflatex -interaction=nonstopmode -halt-on-error leanos.tex >/dev/null
	pdflatex -interaction=nonstopmode leanos.tex >/dev/null
	@echo leanos.pdf

# Proof-Carrying Rust: every number produced by the run, Lean re-checking
# the Rust theorem when installed.  Needs a crust checkout beside this tree
# (or CRUST_DIR).
# Every Rust theorem lean4.py settles, each put to Lean 4 as its own file.
rust_lean:
	$(PYTHON) rustlean.py ../crust/leanos/regs.rs ../crust/leanos/alloc.rs

rustproof_paper:
	$(PYTHON) rustproof_paper.py
	pdflatex -interaction=nonstopmode -halt-on-error rustproof.tex >/dev/null
	pdflatex -interaction=nonstopmode rustproof.tex >/dev/null
	@echo rustproof.pdf

paperfast:
	pdflatex -interaction=nonstopmode -halt-on-error rustproof.tex >/dev/null
	pdflatex -interaction=nonstopmode rustproof.tex >/dev/null
	open rustproof.pdf

# The binary release, unpacked by hand.  No root, no package manager, no
# release index -- just github.com.
install_lean_tarball:
	@set -e; \
	os=$$(uname -s); arch=$$(uname -m); \
	case "$$os" in \
		Linux) case "$$arch" in \
			x86_64|amd64)  asset=linux ;; \
			aarch64|arm64) asset=linux_aarch64 ;; \
			*) echo "unsupported Linux arch: $$arch"; exit 1 ;; \
			esac ;; \
		Darwin) case "$$arch" in \
			x86_64) asset=darwin ;; \
			arm64)  asset=darwin_aarch64 ;; \
			*) echo "unsupported macOS arch: $$arch"; exit 1 ;; \
			esac ;; \
		*) echo "unsupported OS: $$os (Linux and Darwin only)"; exit 1 ;; \
	esac; \
	url="$(LEAN_URL_BASE)/v$(LEAN_VERSION)/lean-$(LEAN_VERSION)-$$asset.tar.zst"; \
	command -v curl >/dev/null 2>&1 || { echo 'need curl'; exit 1; }; \
	command -v unzstd >/dev/null 2>&1 || { echo 'need zstd (unzstd)'; exit 1; }; \
	tmp=$$(mktemp -d); trap 'rm -rf "'"$$tmp"'"' EXIT; \
	echo "==> fetching $$url"; \
	curl -fL --retry 3 -o "$$tmp/lean.tar.zst" "$$url"; \
	echo '==> unpacking into $(LEAN_PREFIX)'; \
	rm -rf "$(LEAN_PREFIX)"; mkdir -p "$(LEAN_PREFIX)"; \
	unzstd -c "$$tmp/lean.tar.zst" \
		| tar -x -C "$(LEAN_PREFIX)" --strip-components=1; \
	"$(LEAN_PREFIX)/bin/lean" --version >/dev/null

# curl and zstd, by whichever package manager is present.  Nothing else: the
# Lean side of this repo has no Python or TeX dependencies of its own.
install_lean_deps:
	@need=''; \
	for p in curl unzstd; do \
		command -v $$p >/dev/null 2>&1 || need="$$need $$p"; \
	done; \
	if [ -n "$$need" ]; then \
		if command -v apt-get >/dev/null 2>&1; then \
			echo '==> apt-get install curl zstd'; \
			sudo apt-get update -qq && \
			sudo apt-get install -y --no-install-recommends curl zstd; \
		elif command -v brew >/dev/null 2>&1; then \
			echo '==> brew install curl zstd'; \
			brew install curl zstd; \
		else \
			echo "missing:$$need -- install them and re-run"; exit 1; \
		fi; \
	fi

# The line to paste into ~/.bashrc or ~/.zshrc.
lean_env:
	@if [ -x "$(LEAN_PREFIX)/bin/lean" ]; then \
		echo '  export PATH="$(LEAN_PREFIX)/bin:$$PATH"'; \
	else \
		echo '  export PATH="$(ELAN_HOME)/bin:$$PATH"'; \
	fi

uninstall_lean:
	rm -rf "$(LEAN_PREFIX)"
	@echo 'removed $(LEAN_PREFIX).  elan, if it was used instead, lives in'
	@echo '$(ELAN_HOME) and is removed with: elan self uninstall'

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
	@# Optional: without it crustos_eq.py checks Equation (1) with lean4.py's
	@# micro-kernel alone, and skips the second opinion from Lean itself.
	@if command -v lean >/dev/null 2>&1 && lean --version >/dev/null 2>&1; then \
		echo "  lean 4          ok       ($$(lean --version | sed 's/Lean (version //;s/,.*//'))"; \
	else \
		echo '  lean 4          missing  (make install_lean)'; \
	fi
	@# Linux only, and optional: it drives the side-by-side PDF viewer.
	@$(PYTHON) -c "import gi; gi.require_version('EvinceDocument','3.0')" \
		>/dev/null 2>&1 \
		&& echo '  evince (pdf)    ok' \
		|| echo '  evince (pdf)    missing  (python3-gi gir1.2-evince-3.0)'

ui:
	$(PYTHON) rosettaui.py

# rosettamath.py self tests both bootstrap stages; rosettaphys.py validates
# every knowledge base entry; rosettaui.py checks the parser and the classifier.
test:
	$(PYTHON) rosettamath.py
	$(PYTHON) rosettaphys.py --selftest
	$(PYTHON) rosettalean.py --selftest
	$(PYTHON) rosettapaper.py --selftest
	$(PYTHON) rosettaui.py --selftest
	$(PYTHON) lean4.py --selftest

# What the knowledge base currently covers, graph and joins included.
census:
	$(PYTHON) rosettaphys.py

# Every join the graph offers, as a conjecture the micro-kernel has checked.
conjectures:
	$(PYTHON) rosettalean.py

# Letters the library uses for two different physical quantities, found by
# comparing what each equation declares its symbols denote.
collisions:
	@$(PYTHON) -c "import rosettaphys as P; \
	  [print('%-4s %-26s vs %-26s (%s / %s)' % (q, l, r, a.label, b.label)) \
	   for a, b, q, l, r in P.disagreements()]" 

# The same, written out as Lean 4 source for a second opinion.
RosettaPhys.lean:
	$(PYTHON) rosettalean.py --lean > $@
	@echo 'wrote $@ -- `lean $@` to have Lean check it.  The file is'
	@echo 'Mathlib-free, so a bare toolchain is enough: no lake, no packages.'
	@echo 'The `sorry` warnings are the point -- see the header.'

# The fourth paper.  Every number, table and equation in it is generated from
# rosettaphys.py at build time, so the paper cannot disagree with the code.
rosettaphys.tex: rosettaphys.py rosettalean.py rosettapaper.py
	$(PYTHON) rosettapaper.py

physpaper: rosettaphys.tex
	cd /tmp && pdflatex -interaction=nonstopmode -halt-on-error \
	  $(CURDIR)/rosettaphys.tex >/dev/null \
	  && pdflatex -interaction=nonstopmode $(CURDIR)/rosettaphys.tex >/dev/null \
	  && echo '/tmp/rosettaphys.pdf'

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

.PHONY: rust_lean default help install install-all check-deps ui test census \
	conjectures collisions physpaper proofs \
	render-test pdf paper leanproof crustos_eq rustproof_paper clean \
	install_apple install-apple install_apple-all \
	install_windows install-windows \
	install_lean install-lean install_lean_tarball install_lean_deps \
	lean_env uninstall_lean
