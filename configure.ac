dnl configure.ac for Chaos(CafeOBJ)
dnl apply autoconf to this file for producing a configure script.
dnl
dnl Copyright (c) 2000-2014, Toshimi Sawada. All rights reserved.
dnl Copyright (c) 2014 Norbert Preining. All rights reserved.
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

AC_INIT([CafeOBJ],[1.4], [], [cafeobj], [http://www.cafeobj.org/])
AC_CONFIG_SRCDIR([make-cafeobj.lisp.in])
AM_INIT_AUTOMAKE
AC_PREREQ(2.6)
VMINOR=.15b3
VMEMO=PigNose0.99
PATCHLEVEL=
AC_SUBST(VMINOR)
AC_SUBST(VMEMO)
AC_SUBST(PATCHLEVEL)
AC_ARG_PROGRAM
AC_PROG_INSTALL
dnl AC_PATH_PROG(gcl_path,gcl)   ... no more gcl..
AC_PATH_PROG(cmu_path,lisp)
AC_PATH_PROG(sbcl_path,sbcl)
AC_PATH_PROG(acl_path,alisp)
AC_PATH_PROG(clisp_path,clisp)
dnl AC_PATH_PROG(acl8_path,alisp)
dnl AC_PATH_PROG(acl9_path,alisp)
dnl AC_PATH_PROG(openmcl_path,openmcl)
AC_PATH_PROG(clozurecl_32path,ccl)
AC_PATH_PROG(clozurecl_64path,ccl64)
AC_PROG_MAKE_SET
AC_PROG_MKDIR_P
AC_ARG_WITH(lisp,
   [AS_HELP_STRING([--with-lisp=all|<interp>@<:@,<interp>@:>@],
      [specify a list of lisp interpreters to build with, or all for all found])],

	lisp=$withval)


if test "x$lisp" = "x" 
then
	# no lisp specified, select one by default
	if   test -n "$acl_path" ; then lisp=acl ; 
	elif test -n "$sbcl_path" ; then lisp=sbcl ;
	elif test -n "$clisp_path" ; then lisp=clisp ;
	elif test -n "$gcl_path" ; then lisp=gcl ;
	elif test -n "$cmu_path" ; then lisp=cmu ;
	elif test -n "clozurecl_32path" ; then lisp=ccl ;
	elif test -n "clozurecl_64path" ; then lisp=ccl64 ;
	else
		AC_MSG_ERROR([no supported lisp interpreter found])
	fi
fi


dnl support building for all interpreters
do_all=0
if test "x$lisp" = "xall"
then
  do_all=1
  lisp=acl,sbcl,clisp,gcl,cmu,ccl,ccl64
fi

dnl convert comma serparated list to space separated list
lisp=$(echo $lisp | sed -e 's/,/ /g')

goodlisp=
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
	  fi
	  ;;
    xsbcl)
          if test -z "$sbcl_path"
          then
	     test $do_all = 1 || \
	     AC_MSG_ERROR([selected lisp interpreter $i is not available])
	  else
	     goodlisp="$goodlisp $i"
	  fi
	  ;;
    xacl)
          if test -z "$acl_path"
          then
	     test $do_all = 1 || \
	     AC_MSG_ERROR([selected lisp interpreter $i is not available])
	  else
	     goodlisp="$goodlisp $i"
	  fi
	  ;;
    xclisp)
          if test -z "$clisp_path"
          then
	     test $do_all = 1 || \
	     AC_MSG_ERROR([selected lisp interpreter $i is not available])
	  else
	     goodlisp="$goodlisp $i"
	  fi
	  ;;
    xccl)
          if test -z "$clozurecl_32path"
          then
	     test $do_all = 1 || \
	     AC_MSG_ERROR([selected lisp interpreter $i is not available])
	  else
	     goodlisp="$goodlisp $i"
	  fi
	  ;;
    xccl64)
          if test -z "$clozurecl_64path"
          then
	     test $do_all = 1 || \
	     AC_MSG_ERROR([selected lisp interpreter $i is not available])
	  else
	     goodlisp="$goodlisp $i"
	  fi
	  ;;
    xgcl)
          if test -z "$gcl_path"
          then
	     test $do_all = 1 || \
	     AC_MSG_ERROR([selected lisp interpreter $i is not available])
	  else
	     goodlisp="$goodlisp $i"
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
AC_SUBST(lisp)

AC_ARG_ENABLE([rebuild_doc],
       [AS_HELP_STRING([--enable-rebuild-doc],
               [Enable the rebuilding of documentation (not implemented) @<:@default=no@:>@])],
       [enable_rebuild_doc="${enableval}"],
       [enable_rebuild_doc=no])
if test x"$enable_rebuild_doc" = x"yes"
then
  dnl check for documentation building programs
  AC_CHECK_PROG(xelatex_avail, [xelatex], [yes], [no])
  AC_CHECK_PROG(biber_avail, [biber], [yes], [no])
  AC_CHECK_PROG(pandoc_avail, [pandoc], [yes], [no])
  AC_CHECK_PROG(pdflatex_avail, [pdflatex], [yes], [no])
  if test $xelatex_avail = no \
     -o $biber_avail = no   \
     -o $pandoc_avail = no  \
     -o $pdflatex_avail = no
  then
	AC_MSG_NOTICE([Not all TeX related programs are found, disabling rebuild of documentation.])
	enable_rebuild_doc=no
  fi
fi
AM_CONDITIONAL([COND_REBUILD_DOC], [test x"$enable_rebuild_doc" = x"yes"])


AC_ARG_ENABLE(traditional_layout,
       [AS_HELP_STRING([--enable-traditional-layout],
               [Enable traditional layout @<:@default=no@:>@])],
       [enable_traditional_layout="${enableval}"],
       [enable_traditional_layout=no])
AM_CONDITIONAL([COND_TRADITIONAL], [test x"$enable_traditional_layout" = x"yes"])


AC_CONFIG_FILES([
  Makefile 
  doc/Makefile
])
AC_OUTPUT()
