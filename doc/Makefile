.SUFFIXES: .tex .pdf .dvi

LIB = ../lib
DOC = .

GAPFILES = $(LIB)/zigzag.g $(LIB)/methods.g $(LIB)/iterator.g\
           $(LIB)/walker.g $(LIB)/subsets.g $(LIB)/shapes.g\
           $(LIB)/alleys.g $(LIB)/streets.g $(LIB)/category.g\
	   $(LIB)/groupoid.g

XMLFILES = $(DOC)/zigzag.xml $(DOC)/methods.xml $(DOC)/iterator.xml\
           $(DOC)/walker.xml $(DOC)/subsets.xml $(DOC)/shapes.xml\
           $(DOC)/alleys.xml $(DOC)/streets.xml $(DOC)/category.xml\
	   $(DOC)/groupoid.xml $(DOC)/introduc.xml

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

all: zigzag.pdf

zigzag.tex: $(XMLFILES) $(GAPFILES) descent.bib
	gap4 -b -r < makedoc.g

clean:
	rm -fv *.aux *.log *.blg *.ilg
	rm -fv *.bbl *.brf *.ind *.pnr *.toc *.out *.idx

install: zigzag.pdf
	scp $< schmidt:www/zigzag
