.SUFFIXES: .tex .pdf .dvi

LIB = ../lib
DOC = .

GAPFILES = $(LIB)/methods.g $(LIB)/iterator.g $(LIB)/walker.g\
	   $(LIB)/subsets.g $(LIB)/shapes.g $(LIB)/arrows.g $(LIB)/bundles.g

XMLFILES = $(DOC)/zigzag.xml $(DOC)/introduc.xml

.tex.pdf:
	pdflatex $*
	bibtex $*
	pdflatex $*
	makeindex $*
	pdflatex $*

.tex.dvi:
	latex $*
	bibtex $*
	latex $*
	makeindex $*
	latex $*

all: zigzag.dvi zigzag.pdf

zigzag.tex: $(XMLFILES) $(GAPFILES) zigzag.bib
	gap4 -b -r < makedoc.g

clean:
	rm -fv *.{aux,log,blg,ilg}
	rm -fv *.{bbl,brf,ind,pnr,toc,out,idx}

install: zigzag.pdf
	scp $< schmidt:www/zigzag
