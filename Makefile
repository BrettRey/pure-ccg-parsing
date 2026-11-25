MAIN := pure-ccg-parsing

.PHONY: all test
all: $(MAIN).pdf

$(MAIN).pdf: $(MAIN).tex .house-style/preamble.tex references-standalone.bib
	latexmk -xelatex -halt-on-error -interaction=nonstopmode -outdir=build $(MAIN).tex
	cp build/$(MAIN).pdf $@

references-standalone.bib: references-local.bib
	cp $< $@

test:
	lean +leanprover/lean4:v4.36.0 Shapes.lean
	python3 -B check_sat.py
	python3 -B check_clique.py
