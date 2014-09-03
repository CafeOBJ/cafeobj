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
dnl AC_PATH_PROG(gcl_path,gcl, no)   ... no more gcl..
AC_PATH_PROG(cmu_path,lisp, no)
AC_PATH_PROG(sbcl_path,sbcl,no)
AC_PATH_PROG(acl_path,alisp, no)
AC_PATH_PROG(clisp_path,clisp, no)
dnl AC_PATH_PROG(acl8_path,alisp,no)
dnl AC_PATH_PROG(acl9_path,alisp,no)
dnl AC_PATH_PROG(openmcl_path,openmcl,no)
AC_PATH_PROG(clozurecl_32path,ccl,no)
AC_PATH_PROG(clozurecl_64path,ccl64,no)
AC_PROG_MAKE_SET
AC_PROG_MKDIR_P
AC_ARG_WITH(lisp,
[  --with-lisp[=lisp]	specify the path of Lisp interpter to be used 
			for building CafeOBJ (defaulted to gcl).],
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


saved_lisp=$lisp
case "x$lisp" in
xcmu)
	lisp=$cmu_path ;
	bin_suffix=".x86f" ;
	exec_command="cafeobj.cmu.in";
	exec_bin="cafeobj.core"
	;;
xcmu-pc)
	lisp=$cmu_path ;
	bin_suffix=".x86f" ;
	exec_command="cafeobj.cmu.in";
	exec_bin="cafeobj.core"
	;;
xsbcl)
	lisp=$sbcl_path ;
	bin_suffix=".fasl";
	exec_command="cafeobj.sbcl.in";
	exec_bin="cafeobj.sbcl";
	build_option="--dynamic-space-size 2048"
	;;
xacl)
	lisp=$acl_path ;
	bin_suffix=".fasl";
	exec_command="cafeobj.acl.in";
	exec_bin="cafeobj.acl"
	;;
xclisp)
	lisp=$clisp_path ;
	bin_suffix=".fas";
	exec_command="cafeobj.clisp.in";
	exec_bin="cafeobj.mem"
	;;
xccl)
	lisp=$clozurecl_32path ;
	bin_suffix=".dfsl";
	exec_command="cafeobj.openmcl.in";
	exec_bin="cafeobj.img"
	;;
xccl64)
	lisp=$clozurecl_64path ;
	bin_suffix=".dx64fsl";
	exec_command="cafeobj.openmcl.in";
	exec_bin="cafeobj.img"
	;;
xgcl|x)
	lisp=$gcl_path ;
	bin_suffix=".o";
	exec_command="cafeobj.gcl.in"
	exec_bin="cafeobj.exe"
	;;
*)
	echo "unknown lisp platform";
	exit 1
	;;
esac

if test -z "$lisp"
then
	AC_MSG_ERROR([selected lisp interpreter $saved_lisp is not available])
fi

AC_MSG_NOTICE([Lisp interpreter used: $saved_lisp])

AC_SUBST(lisp)
AC_SUBST(exec_command) 
AC_SUBST(exec_bin)
AC_SUBST(build_option)
AC_SUBST(bin_suffix)

enable_doc=yes
AC_ARG_ENABLE([doc],
  AS_HELP_STRING([--disable-doc],[Disable rebuilding the docs]))
AM_CONDITIONAL([COND_DOC], [test "x$enable_doc" = xyes])

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
