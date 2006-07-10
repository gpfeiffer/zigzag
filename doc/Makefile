.SUFFIXES: .tex .pdf

LIB = ../lib
GAPFILES = $(LIB)/methods.g $(LIB)/iterator.g $(LIB)/walker.g\
	   $(LIB)/subsets.g $(LIB)/shapes.g $(LIB)/arrows.g $(LIB)/bundles.g

.tex.pdf:
	pdflatex $*
	bibtex $*
	pdflatex $*
	makeindex $*
	pdflatex $*

all: zigzag.pdf

zigzag.tex: zigzag.xml $(GAPFILES)
	gap4 -b -r < makedoc.g
