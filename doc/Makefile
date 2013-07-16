.SUFFIXES: .tex .pdf .dvi

LIB = ../lib
DOC = .

GAPFILES = $(LIB)/descent.g $(LIB)/methods.g $(LIB)/iterator.g\
           $(LIB)/walker.g $(LIB)/subsets.g $(LIB)/skyline.g\
           $(LIB)/shapes.g $(LIB)/classes.g $(LIB)/characte.g\
           $(LIB)/alleys.g $(LIB)/streets.g $(LIB)/category.g\
	   $(LIB)/groupoid.g

XMLFILES = $(DOC)/zigzag.xml  $(DOC)/introduc.xml\
	   $(DOC)/descent.xml $(DOC)/methods.xml $(DOC)/iterator.xml\
           $(DOC)/walker.xml $(DOC)/subsets.xml $(DOC)/skyline.xml\
           $(DOC)/shapes.xml $(DOC)/classes.xml $(DOC)/characte.xml\
           $(DOC)/alleys.xml $(DOC)/streets.xml $(DOC)/category.xml\
	   $(DOC)/groupoid.xml

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

zigzag.tex: $(XMLFILES) $(GAPFILES)
	gap4 -b -r < makedoc.g

zigzag.pdf: zigzag.tex zigzag.bib

clean:
	rm -fv *.aux *.log *.blg *.ilg
	rm -fv *.bbl *.brf *.ind *.pnr *.toc *.out *.idx
	rm -fv tempCONV.*

install: zigzag.pdf
	scp $< schmidt:www/zigzag
