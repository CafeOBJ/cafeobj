dnl configure.ac for Chaos(CafeOBJ)
dnl apply autoconf to this file for producing a configure script.
dnl
dnl Copyright (c) 2000-2015, Toshimi Sawada. All rights reserved.
dnl Copyright (c) 2014-2015, Norbert Preining. All rights reserved.
dnl
dnl Redistribution and use in source and binary forms, with or without
dnl modification, are permitted provided that the following conditions
dnl are met:
dnl
dnl   * Redistributions of source code must retain the above copyright
dnl     notice, this list of conditions and the following disclaimer.
dnl
dnl   * Redistributions in binary form must reproduce the above
dnl     copyright notice, this list of conditions and the following
dnl     disclaimer in the documentation and/or other materials
dnl     provided with the distribution.
dnl
dnl THIS SOFTWARE IS PROVIDED BY THE AUTHOR 'AS IS' AND ANY EXPRESSED
dnl OR IMPLIED WARRANTIES, INCLUDING, BUT NOT LIMITED TO, THE IMPLIED
dnl WARRANTIES OF MERCHANTABILITY AND FITNESS FOR A PARTICULAR PURPOSE
dnl ARE DISCLAIMED.  IN NO EVENT SHALL THE AUTHOR BE LIABLE FOR ANY
dnl DIRECT, INDIRECT, INCIDENTAL, SPECIAL, EXEMPLARY, OR CONSEQUENTIAL
dnl DAMAGES (INCLUDING, BUT NOT LIMITED TO, PROCUREMENT OF SUBSTITUTE
dnl GOODS OR SERVICES; LOSS OF USE, DATA, OR PROFITS; OR BUSINESS
dnl INTERRUPTION) HOWEVER CAUSED AND ON ANY THEORY OF LIABILITY,
dnl WHETHER IN CONTRACT, STRICT LIABILITY, OR TORT (INCLUDING
dnl NEGLIGENCE OR OTHERWISE) ARISING IN ANY WAY OUT OF THE USE OF THIS
dnl SOFTWARE, EVEN IF ADVISED OF THE POSSIBILITY OF SUCH DAMAGE.
dnl

AC_INIT([CafeOBJ],[1.5], [], [cafeobj], [http://www.cafeobj.org/])
AC_CONFIG_SRCDIR([make-cafeobj.lisp.in])
AM_INIT_AUTOMAKE
AC_PREREQ(2.6)
VMINOR=.6
VMEMO=PigNose0.99
PATCHLEVEL=b1
AC_SUBST(VMINOR)
AC_SUBST(VMEMO)
AC_SUBST(PATCHLEVEL)
AC_ARG_PROGRAM
AC_PROG_INSTALL

dnl allow for specifying different names for cmd line interpreter
dnl
dnl disable currently not supported interpreter
dnl but make them available on request!


AC_ARG_WITH(sbcl,
   [AS_HELP_STRING([--with-sbcl=<cmd>],
      [specify the SBCL interpreter @<:@default: sbcl@:>@])],
   sbcl_interp=$withval,sbcl_interp=sbcl)
sbcl_dump=cafeobj.sbcl

AC_ARG_WITH(acl,
   [AS_HELP_STRING([--with-acl=<cmd>],
      [specify the ACL interpreter @<:@default: alisp@:>@])],
   acl_interp=$withval,acl_interp=alisp)
acl_dump=cafeobj.acl
dnl this is the dump file name generated for ACL standalone
acl_standalone_dump=CafeOBJ

AC_ARG_WITH(clisp,
   [AS_HELP_STRING([--with-clisp=<cmd>],
      [specify the CLISP interpreter @<:@default: clisp@:>@])],
   clisp_interp=$withval,clisp_interp=clisp)
clisp_dump=cafeobj.mem

dnl AC_ARG_WITH(ccl32,
dnl    [AS_HELP_STRING([--with-ccl32=<cmd>],
dnl      [specify the CCL(32) interpreter @<:@default: ccl@:>@])],
dnl    ccl32_interp=$withval,ccl32_interp=ccl)
ccl32_interp=ccl
ccl32_dump=cafeobj.img

dnl AC_ARG_WITH(ccl64,
dnl    [AS_HELP_STRING([--with-ccl64=<cmd>],
dnl       [specify the CCL64 interpreter @<:@default: ccl64@:>@])],
dnl    ccl64_interp=$withval,ccl64_interp=ccl64)
ccl64_interp=ccl64
ccl64_dump=cafeobj.img

dnl AC_ARG_WITH(gcl,
dnl    [AS_HELP_STRING([--with-gcl=<cmd>],
dnl       [specify the GCL interpreter @<:@default: gcl@:>@])],
dnl    gcl_interp=$withval,gcl_interp=gcl)
gcl_interp=gcl
gcl_dump=cafeobj.exe

dnl AC_ARG_WITH(cmu,
dnl   [AS_HELP_STRING([--with-cmu=<cmd>],
dnl      [specify the CMU interpreter @<:@default: lisp@:>@])],
dnl   cmu_interp=$withval,cmu_interp=lisp)
cmu_interp=lisp
cmu_dump=cafeobj.core


AC_PATH_PROG(gcl_path,gcl)
AC_PATH_PROG(cmu_path,$cmu_interp)
AC_PATH_PROG(sbcl_path,$sbcl_interp)
AC_PATH_PROG(acl_path,$acl_interp)
AC_PATH_PROG(clisp_path,$clisp_interp)
AC_PATH_PROG(ccl32_path,$ccl32_interp)
AC_PATH_PROG(ccl64_path,$ccl64_interp)

AC_PROG_MAKE_SET
AC_PROG_MKDIR_P
AC_ARG_WITH(lisp,
   [AS_HELP_STRING([--with-lisp=all|<interp>@<:@,<interp>@:>@],
      [specify a list of lisp interpreters from "acl", "sbcl", or "clisp". Alternatively "all" can be specified to select all available.])],
	lisp=$withval)


if test "x$lisp" = "x" 
then
	# no lisp specified, select one by default
	# we disable the currently not building ones!!!
	if   test -n "$acl_path" ; then lisp=acl ; 
	elif test -n "$sbcl_path" ; then lisp=sbcl ;
	elif test -n "$clisp_path" ; then lisp=clisp ;
	# elif test -n "$gcl_path" ; then lisp=gcl ;
	# elif test -n "$cmu_path" ; then lisp=cmu ;
	# elif test -n "$ccl32_path" ; then lisp=ccl ;
	# elif test -n "$ccl64_path" ; then lisp=ccl64 ;
	else
		AC_MSG_ERROR([no supported lisp interpreter found])
	fi
fi


dnl support building for all interpreters
do_all=0
if test "x$lisp" = "xall"
then
  do_all=1
  # this is the preferred order of interpreters!!
  # if nothing is specified, the first one found will be used!
  #lisp=acl,sbcl,clisp,gcl,cmu,ccl,ccl64
  # use only currently supported ones
  lisp=acl-standalone,acl,sbcl,clisp
fi

dnl convert comma serparated list to space separated list
lisp=$(echo $lisp | sed -e 's/,/ /g')

goodlisp=
firstchoice=
for i in $lisp
do
  case "x$i" in
    xcmu|xcmu-pc) 
          if test -z "$cmu_path"
          then
	     test $do_all = 1 || \
	     AC_MSG_ERROR([selected lisp interpreter $i is not available])
	  else
	     goodlisp="$goodlisp $i"
	     if test "x$firstchoice" = x
	     then
	       firstchoice=$i
	     fi
	  fi
	  ;;
    xsbcl)
          if test -z "$sbcl_path"
          then
	     test $do_all = 1 || \
	     AC_MSG_ERROR([selected lisp interpreter $i is not available])
	  else
	     goodlisp="$goodlisp $i"
	     if test "x$firstchoice" = x
	     then
	       firstchoice=$i
	     fi
	  fi
	  ;;
    xacl|xacl-standalone)
          if test -z "$acl_path"
          then
	     test $do_all = 1 || \
	     AC_MSG_ERROR([selected lisp interpreter $i is not available])
	  else
	     goodlisp="$goodlisp $i"
	     if test "x$firstchoice" = x
	     then
	       firstchoice=$i
	     fi
	  fi
	  ;;
    xclisp)
          if test -z "$clisp_path"
          then
	     test $do_all = 1 || \
	     AC_MSG_ERROR([selected lisp interpreter $i is not available])
	  else
	     goodlisp="$goodlisp $i"
	     if test "x$firstchoice" = x
	     then
	       firstchoice=$i
	     fi
	  fi
	  ;;
    xccl)
          if test -z "$ccl32_path"
          then
	     test $do_all = 1 || \
	     AC_MSG_ERROR([selected lisp interpreter $i is not available])
	  else
	     goodlisp="$goodlisp $i"
	     if test "x$firstchoice" = x
	     then
	       firstchoice=$i
	     fi
	  fi
	  ;;
    xccl64)
          if test -z "$ccl64_path"
          then
	     test $do_all = 1 || \
	     AC_MSG_ERROR([selected lisp interpreter $i is not available])
	  else
	     goodlisp="$goodlisp $i"
	     if test "x$firstchoice" = x
	     then
	       firstchoice=$i
	     fi
	  fi
	  ;;
    xgcl)
          if test -z "$gcl_path"
          then
	     test $do_all = 1 || \
	     AC_MSG_ERROR([selected lisp interpreter $i is not available])
	  else
	     goodlisp="$goodlisp $i"
	     if test "x$firstchoice" = x
	     then
	       firstchoice=$i
	     fi
	  fi
	  ;;
    *)
          AC_MSG_ERROR([unknown lisp interpreter $i])
	  ;;
  esac
done

lisp="$goodlisp"

if test -z "$lisp"
then
	AC_MSG_ERROR([no usable lisp interpreter])
fi

AC_MSG_NOTICE([Building for the following lisp interpreters: $lisp])

dnl check for emacs and lispdir
AM_PATH_LISPDIR


AC_SUBST(lisp)
AC_SUBST(firstchoice)
AC_SUBST(acl_interp)
AC_SUBST(sbcl_interp)
AC_SUBST(clisp_interp)
AC_SUBST(cmu_interp)
AC_SUBST(ccl32_interp)
AC_SUBST(ccl64_interp)
AC_SUBST(gcl_interp)
AC_SUBST(acl_dump)
AC_SUBST(acl_standalone_dump)
AC_SUBST(sbcl_dump)
AC_SUBST(clisp_dump)
AC_SUBST(cmu_dump)
AC_SUBST(ccl32_dump)
AC_SUBST(ccl64_dump)
AC_SUBST(gcl_dump)

AC_ARG_ENABLE([rebuild_doc],
       [AS_HELP_STRING([--enable-rebuild-doc],
               [Enable the rebuilding of documentation (not implemented) @<:@default=no@:>@])],
       [enable_rebuild_doc="${enableval}"],
       [enable_rebuild_doc=no])
if test x"$enable_rebuild_doc" = x"yes"
then
  dnl check for documentation building programs
  AC_CHECK_PROG(xelatex_avail, [xelatex], [yes], [no])
  AC_CHECK_PROG(bibtex_avail, [bibtex], [yes], [no])
  AC_CHECK_PROG(pandoc_avail, [pandoc], [yes], [no])
  AC_CHECK_PROG(pdflatex_avail, [pdflatex], [yes], [no])
  if test $xelatex_avail = no \
     -o $bibtex_avail = no   \
     -o $pandoc_avail = no  \
     -o $pdflatex_avail = no
  then
	AC_MSG_NOTICE([Not all TeX related programs are found, disabling rebuild of documentation.])
	enable_rebuild_doc=no
  fi
fi
AC_SUBST(enable_rebuild_doc)


AC_ARG_ENABLE(traditional_layout,
       [AS_HELP_STRING([--enable-traditional-layout],
               [Enable traditional layout @<:@default=no@:>@])],
       [enable_traditional_layout="${enableval}"],
       [enable_traditional_layout=no])
AC_SUBST(enable_traditional_layout)

AC_ARG_ENABLE(windows,
       [AS_HELP_STRING([--enable-windows],
          [Prepare for Windows building])],
       [enable_windows="${enableval}"],
       [enable_windows=no])
AC_SUBST(enable_windows)

AC_ARG_ENABLE(distribution,
       [AS_HELP_STRING([--enable-distribution],
          [Configure for binary distribution])],
       [enable_distribution="${enableval}"],
       [enable_distribution=no])
AC_SUBST(enable_distribution)

AC_CONFIG_FILES([
  Makefile 
  make-cafeobj.lisp
  version.lisp
  xbin/cafeobj.in
  doc/refman/Makefile
  doc/manual/Makefile
  doc/RefCard/Makefile
  doc/PigNose/Makefile
  doc/citp-manual/Makefile
])
AC_OUTPUT()
