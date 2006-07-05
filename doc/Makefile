.SUFFIXES: .tex .pdf

LIB = ../lib
GAPFILES = $(LIB)/methods.g $(LIB)/walker.g $(LIB)/iterator.g $(LIB)/methods.g $(LIB)/shapes.g $(LIB)/arrows.g

.tex.pdf:
	pdflatex $*
	bibtex $*
	pdflatex $*
	makeindex $*
	pdflatex $*

all: zigzag.pdf

zigzag.tex: zigzag.xml $(GAPFILES)
	gap4 -b -r < makedoc.g
