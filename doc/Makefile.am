
# SUBDIRS = refman manual RefCard BigPink

if COND_TRADITIONAL
  cafeobjdir = $(prefix)/$(PACKAGE)-$(VERSION)
  examplesdir = $(cafeobjdir)/exs
  pdfdocdir = $(cafeobjdir)/doc
else
  examplesdir = $(docdir)/examples
  pdfdocdir = $(docdir)
endif

examples_DATA = examples/*.mod
pdfdoc_DATA = manual/manual.pdf PigNose/pnguide.pdf \
	refman/reference-manual.pdf RefCard/*.pdf



