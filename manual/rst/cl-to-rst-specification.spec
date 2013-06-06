
Specification for a Lisp to RST conversion
==========================================

Every line starting with
	;d;
is consider "documentation input"

The documentation generation routine has the concept of
current output file. By default it is the name of the
input file currently read. I.e., if the file
	foo.cl
is converted the default output file is named
	foo.rst
The documentation conversion strips the last extension
(only 1) and adds rst. In case there is already a file
named like that, the translation process stops.

If the first character after the ";d;" of a documentation
line is a <SPACE>, i.e., the input line starts with
	;d;<SPACE>
where <SPACE> is a literal space, then everything
following the <SPACE> is written into the current 
output file.

If the first char after the ";d;" is an "=", then
some directives for the translation mechanism 
can follow. Current directives are:
	;d;=file=<outputfile>
	  changes the current output file
	;d;=priority=<NN>
	  gives the following block a priority of NN
	;d;=sortstring=<STRING>
	  gives a sort string within this priority

Output process:
- all file given on the command line are read
- blocks with the same output file but different
  priority are written in increasing priority
  sequence.
- blocks within the same priority are sorted 
  according to the sortstring directive
  all blocks without sortstring added at the end
- all block without specified priority get value 500

----------------------

This allows to combine function/syntax definitions
from various input files into one documentation file

Example:

head.lisp, defs-a.lisp, defs-b.lisp

;; head.lisp
;;

;d; Module head
;d; ===========
;d;
;d; The module defined in head and related files will be used
;d; to implement the documentation mechanism for foo bar baz
;d; 
;d; Toplevel functions
;d; ------------------
;d;
;d; repl-loop
;d;   the repl-loop implements the basic interaction with the
;d    user by providing a prompt and ...

(defun (repl-loop) ...)

;d;
;d; debug-handler
;d;   the debug-handler comes into action when a unparseable input
;d;   has been found

(defun (debug-handler ...) ...)

;d;
;d; Support functions
;d; -----------------
;d; .. include:: functions.rst
;d;

===================================

;; defs-a.lisp
;;

;d;=file=functions.rst
;d;

;d;=sortstring=print
;d;
;d; Print functions
;d; ---------------
;d;
;d; The following functions all print out their arguments in one
;d; or the other way. Arbitrary arguments can be passed in, and
;d; the printed representation is shipped out.
;d;
;d;=sortstring=print_a
;d;
;d; print_a
;d;   the function print_a does this and that
(defun ...)

;d;=sortstring=print_f
;d;
;d; print_f
;d;   the function print_f does this and that
;d;
(defun ...)

;d;=sortstring=print_b
;d;
;d; print_b
;d;  the function print_b does this and that
;d;

==============================

;; defs-b.lisp
;;
;d;=file=functions.rst
;d;=sortstring=debug
;d;=priority=400

;d; Debug functions
;d; ---------------
;d;
;d; The following functions are related to debugging
;d;
;d;=sortstring=debug_f
;d;
;d; debug_f
;d;   the function debug_f does this and that
(defun ...)

;d;=sortstring=debug_b
;d;
;d; debug_b
;d;   the function debug_b does this and that
;d;   
(defun ...)

;d;=sortstring=debug_d
;d;
;d; debug_d
;d;  the function debug_d does this and that
;d;
(defun ...)

======================================

Running these through the conversion would give


============== head.rst =================

Module head
===========

The module defined in head and related files will be used
to implement the documentation mechanism for foo bar baz

Toplevel functions
------------------

repl-loop
  the repl-loop implements the basic interaction with the
  user by providing a prompt and ...

debug-handler
  the debug-handler comes into action when a unparseable input
  has been found

Support functions
-----------------
.. include:: functions.rst


============ functions.rst ==================

Debug functions
---------------

The following functions are related to debugging

debug_b
  the function debug_b does this and that

debug_d
  the function debug_d does this and that

debug_f
  the function debug_f does this and that

Print functions
---------------

The following functions all print out their arguments in one
or the other way. Arbitrary arguments can be passed in, and
the printed representation is shipped out.

print_a
  the function print_a does this and that

print_b
 the function print_b does this and that

print_f
  the function print_f does this and that

================================================


Note that in the file functions.rst the debug and print functions
are ordered alphabetically, and the debug functions come
before the print (debug: priority=400, print: default priority=500)

This allows for proper ordering of practically all functions,
and at the same time allows for splitting the whole documentation
around in all source files.

