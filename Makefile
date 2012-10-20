# $Id: Makefile.in,v 1.3 2007-01-24 06:19:06 sawada Exp $
SHELL = /bin/sh

#### Start of system configuration section. ####
srcdir = .
top_srcdir = .

prefix = /usr/local
exec_prefix = ${prefix}
chaos_root = .
objdir = ./bin
mkinstalldirs = $(top_srcdir)/mkinstalldirs

PACKAGE = cafeobj
VERSION = 1.4
VMINOR = .9rc5
VMEMO = PigNose0.99
PATCHLEVEL = 

# Where to install the executables.
bindir = ${exec_prefix}/bin

# Where to install the libraries.
libdir = $(prefix)/$(PACKAGE)-$(VERSION)
cafeobjlibdir = $(libdir)
exsdir = $(cafeobjlibdir)/exs
xlibdir=$(cafeobjlibdir)/lib
preludedir = $(cafeobjlibdir)/prelude
cafeobjbindir = $(cafeobjlibdir)/bin

# Where to install the Info files.
infodir = ${prefix}/share/info

# Where to install the manuals.
mandir = ${prefix}/share/man

top_builddir = .

MAKEINFO = makeinfo
TEXI2DVI = texi2dvi
INSTALL = /usr/bin/install -c
INSTALL_DATA = ${INSTALL} -m 644
INSTALL_PROGRAM = ${INSTALL}
GCL = no
CMU = no
ACL = no
LISP = no
BIN = .fasl
EXEC_SRC = cafeobj.acl.in
EXEC = cafeobj.acl

#### End of system configuration section. ####

PROGS = cafeobj

DISTFILESTOP = \
	README README.First INSTALL configure configure.in Makefile.in \
	CHANGES TODO \
	mkinstalldirs install-sh make-cafeobj.lisp defsystem.lisp \
	version.in chaosx.system chaos-package.lisp \
	version.lisp

DISTDIRTOP = $(PACKAGE)-$(VERSION)$(VMINOR)

DISTSUBDIRS = cafeobj clII comlib thstuff chaos win mac \
	chaos/boot chaos/cafein chaos/construct chaos/decafe chaos/e-match \
	chaos/eval chaos/primitives chaos/term-parser chaos/tools \
	chaos/tram chaos/psup \
	elisp \
	dist \
	RefCard BigPink/codes BigPink/test

DISTBINSUBDIRS = bin/cafeobj bin/clII bin/comlib bin/obj3 bin/thstuff bin/chaos \
	bin/chaos/boot bin/chaos/cafein bin/chaos/construct bin/chaos/decafe bin/chaos/e-match \
	bin/chaos/eval bin/chaos/primitives bin/chaos/term-parser bin/chaos/tools \
	bin/chaos/tram bin/chaos/psup bin/BigPink/codes

DISTLIBDIRS = lib

DISTLIBSUBDIRS = lib/prelude lib/lib

DISTEXDIRS = exs

DISTXBINDIRS = xbin

OBJECTS = $(objdir)/*$(BIN) $(objdir)/*/*$(BIN) $(objdir)/*/*$(BIN) $(objdir)/*/*/*$(BIN)

CLEANFILES = $(OBJECTS) $(srcdir)/.\#* $(srcdir)/*/.\#* $(srcdir)/*/*/.\#* $(srcdir)/*$(BIN) $(srcdir)/xbin/$(EXEC) $(srcdir)/xbin/cafeobj foo *~ */*~ */*/*~ */*/*/*~

DISTCLEANFILES = $(srcdir)/.\#* $(srcdir)/*/.\#* $(srcdir)/*/*/.\#* $(srcdir)/*$(BIN) $(srcdir)/xbin/cafeobj $(srcdir)/xbin/$(EXEC) *~ */*~ */*/*~ */*/*/*~

# Set default target
all: Makefile defsystem$(BIN) version.lisp xcafeobj 

bigpink: Makefile defsystem$(BIN) version.lisp xbigpink

version.lisp: version.in
	cat $(top_srcdir)/version.in | \
	sed -e 's:VERSION:$(VERSION):g' \
	-e 's:VMINOR:$(VMINOR):g' \
	-e 's:VMEMO:$(VMEMO):g' \
	-e 's:PATCHLEVEL:$(PATCHLEVEL):g' \
	-e 's:BIGPINK:nil:g' > version.lisp

xcafeobj: ycafeobj
	cat $(top_srcdir)/make-cafeobj.lisp | \
	sed -e 's:XCHAOS_ROOT_DIR:\"$(chaos_root)\":g' \
	-e 's:XINSTALL_DIR:\"$(libdir)\":g' \
	-e 's:BIGPINK:nil:g' > foo
	$(LISP) < foo

ycafeobj:
	cat $(top_srcdir)/xbin/$(EXEC_SRC) | \
	sed -e 's:LISP:$(LISP):g' \
	-e 's:CAFEOBJPATH:$(cafeobjbindir)/$(EXEC):g' \
	-e 's:CAFEROOT:$(libdir):g' >$(top_srcdir)/xbin/cafeobj 
	chmod +x $(top_srcdir)/xbin/cafeobj

xbigpink: ycafeobj
	cat $(top_srcdir)/make-cafeobj.lisp | \
	sed -e 's:XCHAOS_ROOT_DIR:\"$(chaos_root)\":g' \
	-e 's:XINSTALL_DIR:\"$(libdir)\":g' \
	-e 's:BIGPINK:t:g' > foo
	$(LISP) < foo

defsystem$(BIN): defsystem.lisp
	echo '(compile-file "$(srcdir)/defsystem.lisp")' | $(LISP)

.PHONY:	dist
GZIP=gzip --best
GZIP_EXT=.gz
TAR_VERBOSE=

dist: dist-dir
	tar chf${TAR_VERBOSE} - $(DISTDIRTOP) | ${GZIP} > $(PACKAGE)-$(VERSION)$(VMINOR).tar${GZIP_EXT}

distclean:
	test -z "$(DISTCLEANFILES)" || rm -f $(DISTCLEANFILES)
	rm -fr $(DISTDIRTOP)
	rm -f Makefile
	rm -f config.cache config.log config.status

dist-dir:
	mkdir $(DISTDIRTOP)
	for f in $(DISTFILESTOP) ; do \
	  ln -s `pwd`/$$f $(DISTDIRTOP) ; \
	done
	for d in $(DISTSUBDIRS) ; do \
	  $(mkinstalldirs) $(DISTDIRTOP)/$$d ; \
	done
	for d in $(DISTSUBDIRS) ; do \
	  for f in $$d/*.{lisp,el,mod} ; do \
	    ln -s `pwd`/$$f $(DISTDIRTOP)/$$d ; \
	  done ; \
	done
	$(mkinstalldirs) $(DISTDIRTOP)/$(DISTEXDIRS)
	for f in $(DISTEXDIRS)/*.mod $(DISTEXDIRS)/*.lisp ; do \
	  ln -s `pwd`/$$f $(DISTDIRTOP)/$(DISTEXDIRS) ; \
	done
	$(mkinstalldirs) $(DISTDIRTOP)/$(DISTXBINDIRS)
	for f in $(DISTXBINDIRS)/*.in ; do \
	  ln -s `pwd`/$$f $(DISTDIRTOP)/$(DISTXBINDIRS) ; \
	done
	for d in $(DISTBINSUBDIRS) ; do \
	  $(mkinstalldirs) $(DISTDIRTOP)/$$d ; \
	done
	$(mkinstalldirs) $(DISTDIRTOP)/$(DISTLIBDIR)
	for d in $(DISTLIBSUBDIRS) ; do \
	  $(mkinstalldirs) $(DISTDIRTOP)/$$d ; \
	done
	for d in $(DISTLIBSUBDIRS) ; do \
	  ln -s `pwd`/$$d/*.mod $(DISTDIRTOP)/$$d; \
          ln -s `pwd`/$$d/*.bin $(DISTDIRTOP)/$$d; \
	done

# For an explanation of the following Makefile rules, see node
# `Automatic Remaking' in GNU Autoconf documentation.
Makefile: Makefile.in config.status
	CONFIG_FILES=$@ CONFIG_HEADERS= ./config.status
config.status: configure
	./config.status --recheck
$(srcdir)/configure: configure.in $(ACLOCAL) $(CONFIGURE_DEPENDENCIES)
	cd $(srcdir) && autoconf

tags: TAGS
TAGS:
	etags -l lisp *.lisp */*.lisp */*/*.lisp > TAGS

info:

dvi:

check: all

installcheck:

install-exec: 
	$(mkinstalldirs) $(cafeobjbindir)
	$(mkinstalldirs) $(bindir)
	@echo Installing cafeobj in $(cafeobjbindir)
	$(INSTALL_PROGRAM) $(top_srcdir)/xbin/$(EXEC) $(cafeobjbindir) 
	rm -f $(bindir)/cafeobj 
	$(INSTALL_PROGRAM) $(top_srcdir)/xbin/cafeobj $(bindir)/ ; \


# install-data: install-exs install-lib
install-data: install-exs install-lib
	@:
install-exs:
	$(mkinstalldirs) $(exsdir)
	@echo Installing example modules in $(exsdir)
	@for ex in $(top_srcdir)/exs/*.mod ; do \
	  $(INSTALL_DATA) $$ex $(exsdir) ; \
	done

install-lib:
	$(mkinstalldirs) $(cafeobjlibdir)
	$(mkinstalldirs) $(preludedir)
	$(mkinstalldirs) $(xlibdir)
	@echo Installing preludes and libraries in $(cafeobjlibdir)
	@for prelude in $(top_srcdir)/lib/prelude/*.mod $(top_srcdir)/lib/prelude/*.bin ; do \
	  $(INSTALL_DATA) $$prelude $(preludedir) ; \
	done
	@cd $(top_srcdir)/lib/lib ; \
	for f in *.mod *.bin ; do \
	  $(INSTALL_DATA) $$f $(xlibdir)/$$f ; \
	done
#	@cd $(top_srcdir)/lib/prelude ; \

install-bigpink: bigpink install-exec install-data
	@:

install: all install-exec install-data
	@:

clean-generic:
	test -z "$(CLEANFILES)" || rm -f $(CLEANFILES)

maintainer-clean-generic:
	test -z "$(MAINTAINERCLEANFILES)" || rm -f $(MAINTAINERCLEANFILES)
	test -z "$(BUILT_SOURCES)" || rm -f $(BUILT_SOURCES)

clean:  clean-generic

maintainer-clean:  maintainer-clean-generic distclean 
	@echo "This command is intended for maintainers to use;"
	@echo "it deletes files that may require special tools to rebuild."
	rm -f config.status

.PHONY: default distclean-generic clean-generic \
maintainer-clean-generic clean distclean maintainer-clean

cvs-dist: maintainer-check
	@if sed 1q $(srcdir)/NEWS | grep -e "$(VERSION)" > /dev/null; then :; else \
	  echo "NEWS not updated; not releasing" 1>&2; \
	  exit 1;				\
	fi
	cvs -q tag `echo "Release-$(VERSION)" | sed 's/\./-/g'`
	$(MAKE) dist

cvs-diff:
	thisver=`echo "Release-$(VERSION)" | sed 's/\./-/g'`; \
	prevno=`echo "$(VERSION)" - 0.01 | bc | sed 's/^\./0./'`; \
	prevver=Release-`echo $$prevno | sed 's/\./-/g'`; \
	cvs -f rdiff -c -r $$prevver -r $$thisver $(PACKAGE) \
	    > $(PACKAGE)-$$prevno-$(VERSION).diff
.SUFFIXES:

# Tell versions [3.59,3.63) of GNU make to not export all variables.
# Otherwise a system limit (for SysV at least) may be exceeded.
.NOEXPORT:
