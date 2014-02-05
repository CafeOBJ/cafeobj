
SHELL=/bin/bash

ENGINE=xelatex

#	-V documentclass=book				\

PDOPTS=-f markdown -V biblio-files=manual.bib --biblatex	\
	--table-of-contents				\
	-V papersize=a4paper				\
	-V mainfont='Lucida Bright OT'			\
	-V sansfont='Lucida Sans OT'			\
	-V monofont='Lucida Sans Typewriter OT'		\
	-V documentclass=book				\
	--latex-engine=$(ENGINE)


MDFILES=reference-manual.md introduction.md overview.md \
	reference.md cloudsync.md

#
# we cannot use -T for gpp, as the @ would function as escape marker which
# destroys references in pandoc.
# For now we do *not* specify an escape marker, last argument to -U
GPPOPTS=-U "\\" "" "{" "}{" "}" "{" "}" "\#" ""

manuals: reference-manual.odt reference-manual.epub reference-manual.html reference-manual.pdf


reference-manual.odt: $(MDFILES) odt.gpp makefile
	gpp $(GPPOPTS) -DODT=1 reference-manual.md | pandoc ${PDOPTS} -t odt -s -o reference-manual.odt

reference-manual.epub: $(MDFILES) epub.gpp makefile
	gpp $(GPPOPTS) -DEPUB=1 reference-manual.md | pandoc ${PDOPTS} -t epub -s -o reference-manual.epub

reference-manual.tex: $(MDFILES) latex.gpp makefile manual.bib
	gpp $(GPPOPTS) -DLATEX=1 reference-manual.md | pandoc ${PDOPTS} -t latex -s -o reference-manual.tex

reference-manual.html: $(MDFILES) html.gpp makefile
	gpp $(GPPOPTS) -DHTML=1 reference-manual.md | pandoc ${PDOPTS} -t html -s -o reference-manual.html

reference-manual.bbl: reference-manual.tex manual.bib
	$(ENGINE) reference-manual.tex
	biber reference-manual

reference-manual.pdf: reference-manual.tex reference-manual.bbl
	$(ENGINE) reference-manual.tex
	$(ENGINE) reference-manual.tex

all: reference-manual.pdf reference-manual.html

clean:
	rm -f reference-manual.{aux,bbl,bcf,blg,log,out,run.xml,toc}
	rm -f reference-manual-blx.bib

realclean: clean
	rm -f reference-manual.pdf reference-manual.html
	rm -f reference-manual.tex

