
SHELL=/bin/bash

ENGINE=xelatex

#	-V documentclass=book				\

PDOPTS=-f markdown -V biblio-files=manual.bib --biblatex	\
	--template=template.tex				\
	--table-of-contents				\
	-V papersize=a4paper				\
	-V mainfont='Lucida Bright OT'			\
	-V sansfont='Lucida Sans OT'			\
	-V monofont='Lucida Sans Typewriter OT'		\
	-V documentclass=memoir				\
	--latex-engine=$(ENGINE)


#
# included md files, order is important!!!
MDFILES=reference-manual.md introduction.md overview.md cloudsync.md \
	reference-head.md reference.md

MDFILESORIG=reference-manual.md introduction.md overview.md cloudsync.md \
        reference-backup.md

manuals: reference-manual.odt reference-manual.epub reference-manual.html reference-manual.pdf

update-ref:
	cafeobj update-reference.cafe

reference-manual.odt: $(MDFILES) makefile
	pandoc ${PDOPTS} -t odt -s -o reference-manual.odt ${MDFILES}

reference-manual.epub: $(MDFILES) makefile
	pandoc ${PDOPTS} -t epub -s -o reference-manual.epub ${MDFILES}

reference-manual.tex: $(MDFILES) makefile manual.bib template.tex
	pandoc ${PDOPTS} -t latex -s -o reference-manual.tex ${MDFILES}

reference-manual-orig.tex: $(MDFILESORIG) makefile manual.bib template.tex
	pandoc ${PDOPTS} -t latex -s -o reference-manual-orig.tex ${MDFILESORIG}

reference-manual.html: $(MDFILES) makefile
	pandoc ${PDOPTS} -t html -s -o reference-manual.html ${MDFILES}

reference-manual.bbl: reference-manual.tex manual.bib
	$(ENGINE) reference-manual.tex
	biber reference-manual

reference-manual.pdf: reference-manual.tex reference-manual.bbl
	$(ENGINE) reference-manual.tex
	$(ENGINE) reference-manual.tex

all: reference-manual.pdf reference-manual.html

clean:
	rm -f reference-manual-orig.{aux,bbl,bcf,blg,log,out,run.xml,toc}
	rm -f reference-manual-orig-blx.bib
	rm -f reference-manual.{aux,bbl,bcf,blg,log,out,run.xml,toc}
	rm -f reference-manual-blx.bib

realclean: clean
	rm -f reference-manual.pdf reference-manual.html
	rm -f reference-manual.tex

