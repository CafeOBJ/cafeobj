#
# Copyright (c) 2000-2014, Toshimi Sawada. All rights reserved.
# Copyright (c) 2014, Norbert Preining. All rights reserved.
#
# Redistribution and use in source and binary forms, with or without
# modification, are permitted provided that the following conditions
# are met:
#
#   * Redistributions of source code must retain the above copyright
#     notice, this list of conditions and the following disclaimer.
#
#   * Redistributions in binary form must reproduce the above
#     copyright notice, this list of conditions and the following
#     disclaimer in the documentation and/or other materials
#     provided with the distribution.
#
# THIS SOFTWARE IS PROVIDED BY THE AUTHOR 'AS IS' AND ANY EXPRESSED
# OR IMPLIED WARRANTIES, INCLUDING, BUT NOT LIMITED TO, THE IMPLIED
# WARRANTIES OF MERCHANTABILITY AND FITNESS FOR A PARTICULAR PURPOSE
# ARE DISCLAIMED.  IN NO EVENT SHALL THE AUTHOR BE LIABLE FOR ANY
# DIRECT, INDIRECT, INCIDENTAL, SPECIAL, EXEMPLARY, OR CONSEQUENTIAL
# DAMAGES (INCLUDING, BUT NOT LIMITED TO, PROCUREMENT OF SUBSTITUTE
# GOODS OR SERVICES; LOSS OF USE, DATA, OR PROFITS; OR BUSINESS
# INTERRUPTION) HOWEVER CAUSED AND ON ANY THEORY OF LIABILITY,
# WHETHER IN CONTRACT, STRICT LIABILITY, OR TORT (INCLUDING
# NEGLIGENCE OR OTHERWISE) ARISING IN ANY WAY OUT OF THE USE OF THIS
# SOFTWARE, EVEN IF ADVISED OF THE POSSIBILITY OF SUCH DAMAGE.
#

SUBDIRS = doc
DIST_SUBDIRS = doc

#
# specifying the files that go into the distribution is a pain,
# because we cannot simply include * as this would include the
# to be build dist dir, too.
# for now, let us simply not suport make dist ;-)
# EXTRA_DIST = *

CLEANFILES = 

dist_bin_SCRIPTS = xbin/cafeobj

#
# traditional layout means
# /usr/local/bin/cafeobj
# /usr/local/cafeobj-N.M/bin/DUMP
# /usr/local/cafeobj-N.M/{lib,prelude}
if COND_TRADITIONAL
  cafeobj_share = $(prefix)/$(PACKAGE)-$(VERSION)
  cafeobj_lib   = $(prefix)/$(PACKAGE)-$(VERSION)
  cafeobjdumpdir = $(cafeobj_lib)/bin
  cafeobjlibdir  = $(cafeobj_share)/lib
  cafeobjpreludedir = $(cafeobj_share)/prelude
else
  cafeobj_share = $(datadir)/$(PACKAGE)-$(VERSION)
  cafeobj_lib   = $(libdir)/$(PACKAGE)-$(VERSION)
  cafeobjdumpdir = $(cafeobj_lib)/$(lisp)
  cafeobjlibdir  = $(cafeobj_share)/lib
  cafeobjpreludedir = $(cafeobj_share)/prelude
endif
dist_cafeobjlib_DATA =  $(srcdir)/lib/lib/*.cafe	\
			$(srcdir)/lib/lib/*.bin		\
			$(srcdir)/lib/lib/*.desc
dist_cafeobjprelude_DATA = $(srcdir)/lib/prelude/*.bin
cafeobjdump_SCRIPTS = xbin/$(exec_bin)

#
# for dumping the image the lisp interpreter needs to know
# where the input files are during building
# used only in creating make-cafeobj.lisp script
chaos_root = @srcdir@

#
# TODO
# besides the trivial BIGPINK substitution, this could be
# generated from configure.ac by including version.lisp
# in the output files, and changing the strings to include @..@
version.lisp: $(srcdir)/version.lisp.in
	cat $(srcdir)/version.lisp.in | \
	sed -e 's:VERSION:$(VERSION):g' \
	-e 's:VMINOR:$(VMINOR):g' \
	-e 's:VMEMO:$(VMEMO):g' \
	-e 's:PATCHLEVEL:$(PATCHLEVEL):g' \
	-e 's:BIGPINK:nil:g' > version.lisp
CLEANFILES += version.lisp

make-cafeobj.lisp: $(srcdir)/make-cafeobj.lisp.in
	cat $(srcdir)/make-cafeobj.lisp.in | \
	sed -e 's:XCHAOS_ROOT_DIR:\"$(chaos_root)\":g' \
	-e 's:XINSTALL_DIR:\"$(cafeobj_share)\":g' \
	-e 's:BIGPINK:nil:g' > make-cafeobj.lisp
CLEANFILES += make-cafeobj.lisp

# this is the dump of the lisp process
xbin/$(exec_bin): make-cafeobj.lisp xbin/cafeobj version.lisp
	$(lisp_prog) $(build_option) < make-cafeobj.lisp
	chmod +x xbin/$(exec_bin)
CLEANFILES += xbin/$(exec_bin)

xbin/cafeobj:
	cat $(srcdir)/xbin/$(exec_command) | \
	sed -e 's:LISP:$(lisp_prog):g' \
	-e 's:CAFEOBJPATH:$(cafeobjdumpdir)/$(exec_bin):g' \
	-e 's:CAFEROOT:$(cafeobj_share):g' >$(srcdir)/xbin/cafeobj 
	chmod +x $(srcdir)/xbin/cafeobj
CLEANFILES += xbin/cafeobj



