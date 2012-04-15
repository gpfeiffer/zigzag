.SUFFIXES:	.ps .pdf .dia .mp


.dia.mp:
	dia -t mp $<
	sed -i 's/\\documentclass{minimal}/\\documentclass{minimal}\\usepackage[euler-digits]{eulervm}\\usepackage{amssymb}\\let\\emptyset\\varnothing/' $@

.mp.pdf:
	mptopdf $<
	mv $*-1.pdf $@

.ps.pdf:
	ps2pdf $< $@

.dvi.ps:
	dvips $< -o

.tex.dvi:
	latex $*
	bibtex $*
	latex $*
	latex $*

VERSION=0.79
DATE = $(shell date +%d-%m-%Y)


all: descent.ps

descent.dvi:	types.eps

descent.pdf:	types.pdf
	pdflatex descent

types.0: types.mp
	mpost $<

types.eps:
	cp types.0 types.eps

types.pdf: types.0
	mptopdf $<
	mv types-0.pdf types.pdf

zigzag: zigzag-${VERSION}.tgz

zigzag-${VERSION}.tgz:
	sed -i 's/^Version .*/Version ${VERSION}/' doc/zigzag.xml
	sed -i 's/^<Date>.*/<Date>${DATE}<\/Date>/' doc/zigzag.xml
	sed -i 's/^ZIGZAG.Version:= .*/ZIGZAG.Version:= "${VERSION}";/' init.g
	sed -i 's/^ZIGZAG.Date:= .*/ZIGZAG.Date:= "${DATE}";/' init.g
	cd doc; make
	cd doc; make clean
	tar zcvf $@ -C .. zigzag/dat zigzag/doc zigzag/lib zigzag/init.g zigzag/COPYING



clean:
	rm -fv *.blg *.out *.log *.aux *.mpx

distclean: clean
	rm -fv *.pdf *.dvi *.ps *.bbl *~
	rm -fv descent.0

