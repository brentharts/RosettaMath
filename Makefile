PYTHON ?= python3

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
	ghostscript

default: pdf

help:
	@echo 'make install        install everything needed (Ubuntu/Debian)'
	@echo 'make install-all    the above, plus the optional extras'
	@echo 'make check-deps     report what is present and what is missing'
	@echo 'make ui             launch the interactive explorer'
	@echo 'make test           run every self test'
	@echo 'make pdf            typeset the paper to /tmp/neomath.pdf'
	@echo 'make paper          the paper with the source appendix'
	@echo 'make clean          remove caches and build products'

install:
	sudo apt-get update
	sudo apt-get install -y --no-install-recommends $(APT_PACKAGES)
	@echo
	@echo 'Installed. Run "make check-deps" to verify, "make ui" to start.'

install-all: install
	sudo apt-get install -y --no-install-recommends $(APT_OPTIONAL)

# Reports rather than fails, so it stays useful on a partly configured machine.
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
	@fc-list 2>/dev/null | grep -qi 'latinmodern-math' \
		&& echo '  Latin Modern    ok' || echo '  Latin Modern    MISSING  (fonts-lmodern)'
	@command -v pdftoppm >/dev/null \
		&& echo '  pdftoppm        ok' || echo '  pdftoppm        MISSING  (poppler-utils)'
	@echo 'optional:'
	@$(PYTHON) -c 'import scipy' 2>/dev/null \
		&& echo '  scipy           ok' || echo '  scipy           missing  (python3-scipy)'
	@command -v convert >/dev/null \
		&& echo '  imagemagick     ok' || echo '  imagemagick     missing  (imagemagick)'
	@command -v gs >/dev/null \
		&& echo '  ghostscript     ok' || echo '  ghostscript     missing  (ghostscript)'

ui:
	$(PYTHON) rosettaui.py

# rosettamath.py self tests both bootstrap stages; rosettaui.py checks the
# parser, the classifier and the knowledge base.
test:
	$(PYTHON) rosettamath.py
	$(PYTHON) rosettaui.py --selftest

# Renders a sample equation offscreen, so it works without a display.
render-test:
	QT_QPA_PLATFORM=offscreen $(PYTHON) rosettaui.py --render-test

pdf:
	$(PYTHON) rosettamath.py --pdf

paper:
	$(PYTHON) rosettamath.py --pdf --appendix

clean:
	rm -rf __pycache__ /tmp/rosettaui-cache
	rm -f /tmp/neomath.aux /tmp/neomath.log /tmp/neomath.out /tmp/neomath.tex

.PHONY: default help install install-all check-deps ui test render-test \
	pdf paper clean
