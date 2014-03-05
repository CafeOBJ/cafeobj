CafeOBJ Interpreter
===============
*Version 1.4.12*  
2014/3/5

CafeOBJ is a new generation algebraic specification and programming language. As a direct successor
of OBJ, it inherits all its features(flexible mix-fix syntax, powerful typing system with sub-types,
and sophisticated module composition system featuring various kinds of imports, parameterised
modules, views for instantiating the parameters, module expressions, etc.) but it also implements
new paradigms such as rewriting logic and hidden algebra, as well as their combination.

----------------------------------------------------------------------

The files in this directory and its sub directories constitute the
complete source code for CafeOBJ interpreter. 

----------------------------------------------------------------------

BINARY DISTRIBUTION
------------------
You can down load the binary executable of several platforms 
from [here](https://bitbucket.org/tswd/cafeobj/downloads).

----------------------------------------------------------------------

REQUIREMENT for compiling the system from source files
------------

CafeOBJ interpreter uses Common Lisp as a underlying implementation
language, and can be built on one of the following platforms:

1. Allegro CL version 8.0 or later
2. SBCL version 1.1.7 or later (<http://www.sbcl.org/platform-table.html>)
3. CMUCL version 20D or later (<http://www.cons.org/cmucl/download.html>)
4. CLISP 2.4.9 or later (<http://www.clisp.org>)

All of these Lisp systems are freely available except Allegro CL.
Franz inc. provides free version, please refer to Franz's [download site](http://www.franz.com/downloads/clp/survey).

----------------------------------------------------------------------

OBTAINING THE SOURCES
-----------------

Source files are available from Bitbucket.
```bash
% git clone https://tswd@bitbucket.org/tswd/cafeobj.git
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
           |  cmu-pc    ; CMUCL on X86, CMUCL on Sparcs are not supported.
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
