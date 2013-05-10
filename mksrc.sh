#!/bin/sh
VERSION=1.4.9rc9
DISTDIR=dist/cafeobj-$VERSION
DISTFILE=cafeobj-$VERSION.tgz

if [[ ! -d $DISTDIR ]]; then
    mkdir -p $DISTDIR;
fi;

tar cf - mkinstalldirs exs install-sh sysdef.cl chaosx.system version.in configure.in configure Makefile.in Makefile lib xbin ./*.lisp */*.lisp */*/*.lisp RefCard manual BigPink/man INSTALL | tar xf - -C $DISTDIR;
cd dist; tar czvf $DISTFILE cafeobj-$VERSION;


