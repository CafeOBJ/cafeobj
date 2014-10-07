CafeOBJ Interpreter
===================
*Version 1.5.2*
2014-10-08

CafeOBJ is a new generation algebraic specification and programming language.
As a direct successor of OBJ, it inherits all its features (flexible mix-fix
syntax, powerful typing system with sub-types, and sophisticated module
composition system featuring various kinds of imports, parameterised
modules, views for instantiating the parameters, module expressions, etc.)
but it also implements new paradigms such as rewriting logic and hidden
algebra, as well as their combination.

----------------------------------------------------------------------

The files in this directory and its sub directories constitute the
complete source code for CafeOBJ interpreter. 

----------------------------------------------------------------------


CONTACT
-------
Please use `info AT cafeobj DOT org' to contact us for bug reports,
suggestions, requests, etc.


BINARY DISTRIBUTION
------------------
You can down load the binary executable of several platforms 
from [here](http://cafeobj.org/download).

----------------------------------------------------------------------

REQUIREMENT for compiling the system from source files
------------

CafeOBJ interpreter uses Common Lisp as a underlying implementation
language, and can be built on one of the following platforms:

1. Allegro CL version 8.0 or later
2. SBCL version 1.1.7 or later (<http://www.sbcl.org/platform-table.html>)
3. CLISP 2.4.9 or later (<http://www.clisp.org>)

All of these Lisp systems are freely available except Allegro CL.
Franz inc. provides free version, please refer to Franz's [download site](http://www.franz.com/downloads/clp/survey).

For more information on building see INSTALL

----------------------------------------------------------------------

OBTAINING THE SOURCES
---------------------

Source files are available from Bitbucket.
```bash
% git clone git://git.cafeobj.org/cafeobj.git
```

----------------------------------------------------------------------

INSTALLATION from sources
--------------------

Change to the directory in which the cafeobj resources are put.

Please read the INSTALL contained in the distribution for full installation
instructions. 
Here's a brief summary:

``````bash
	$ cd cafeobj
	$ ./configure --with-lisp={YOUR-LISP}
 	$ make
	$ sudo make install
``````
where, 
``````
YOUR-LISP ::= acl       ; Allegro CL
           |  sbcl      ; SBCL
           |  clisp     ; CLISP
``````

----------------------------------------------------------------------

NO WARRANTY
-------------

THIS SOFTWARE IS SUPPLIED COMPLETELY "AS IS". CafeOBJ is distributed 
in the hope that it will be useful, but WITHOUT ANY WARRANTY; without
even the implied warranty of MERCHANT-ABILITY of FITNESS FOR A PARTICULAR
PURPOSE.

-- EOF
