% CafeOBJ Reference Manual
% Ataru T. Nakagawa, Toshimi Sawada, Kokichi Futatsugi, Norbert Preining

\include{macros.gpp}

Introduction
============

(present a module (idea: stripped down version of the bank-account.mod)
which contains most important and often used constructs
describe the fundamental concepts of \_cafeobj 
(algebraic spec, order sort, model spec, ...)
also contains a quick intro to interaction [Ch 1] but much shorter)

\_cafeobj as TRS specification system, background, algebraic specification
based on equational theory. 

Overview of the system
======================

alternative title: Main concepts (?)

discuss the following topics in bit more details (parts of the
current manual, stripped down)

- sorts [Ch 3]
- operators [Ch 4, Ch 7]
- module [Ch 2, Ch 8]

do not contain the syntactic definition in all the details,
but explain these important items in more detail

Sorts
-----

use [Ch 3]

### Normal sorts ###

~~~
[ NzNat Zero < Nat ]
~~~

### Hidden sorts ###

Not to be included in the introduction

~~~
*[ Foo ]*
~~~

Term structure
--------------

use [Ch 4 and 7]

### Variable declarations ###

== vars M N : Nat ==

== N:Nat ==

### Records ###

~~~~
Record {
  ...
}
~~~~

### Operators ###

~~~
op 0 : -> Zero
op s_ : Nat -> NzNat
op _+_ : Nat Nat -> Nat
~~~

Rewriting - Equations
---------------------

### Equations ###

~~~
eq N:Nat + 0 = N .
eq N:Nat + s(M:Nat) = s(N + M) .
~~~

### Transitions ###

~~~
trans ...
~~~

Glueing it together - modules
-----------------------------

use [Ch 2 and 8]

~~~
module {
  ...sort definitions...
  ...operators...
  ...axioms and transitions...
}
~~~

### Views/Parametrization ###


The full module
---------------
~~~ {#mycode .cafeobj .numberLines startFrom="10"}
mod! SIMPLE-NAT {
  [ NzNat Zero < Nat ]
  op 0 : -> Zero
  op s_ : Nat -> NzNat
  op _+_ : Nat Nat -> Nat {comm}
  
  eq N:Nat + s(M:Nat) = s(N + M) .
  eq N:Nat + 0 = N . 
}
~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~

Gory Details
============

starting with the BNF definition of [Ch 12], go through
alphabetic list of syntax elements (care has to be taken for
infix ops etc) with explanations, taken from and adapted from
the current manual. Combining similar items. 
Full syntactic definition and semantics
(extraction/unification for the current manual):

list as in the attached pdf (extraction of current manual), but
merging following items (at least) (numbers also refer to the
Syntax elements in the current manual)

- 12,13
- 14,15
- 17,23,24,61,64-69
- 26-28
- 29-31
- 32,33
- 39,40
- 42,43
- 44,46,47
- 49,50

From the currently not treated chapters we would

- [Ch 5,6] -> part of the "part 3" (inspecting, evaluating, ...)
- [Ch 9,10]-> merged into either "part 2" or appendix on proving
- [Ch 11] -> part of the "part 3"






Testing
=======

Macros
------
Usage of macros in the code can be used like `\_cafeobj` and produces
\_cafeobj, depending on the definitions in `latex.gpp` and `html.gpp`.

References
----------
References are used like `@osa` this and produces this: @osa, so it
is better used in brackets [@osa-survey, p.23] or similar.

`biblatex` and `biber` is needed.

Definition lists
----------------

Order-sorted logic
  : [@osa]
    A sort may be a subset of another sort...

Rewriting logic
  : [@rew-logic]
	In addition to equality, which is subject to the law of symmetry, ...

and so on and so on

Literal blocks
--------------

A literal block, we could use it for syntax definitions or
so?

>  input command
>     input pathnam

Block quotes are quoted elements

>  Never give up, never surrender!
>
>  -- Someone in a funny movie

Here now comes a transition, something we normally don't use in
LaTeX as it is an evil thing:

-------

And here we continue after the transition

Option lists are very special, they are funny program like
stuff ahdnling a lot of cases:

~~~
  -a           a nice option
  -b arg       another option
  --long       long options supported
  --very-long-options-are-still-supported
               but how will it look?
               I don't know
~~~

Another funny thing are those quoted literal blocls

> hello world
> what is going on
> lets have a cup of thee

A completely different thing are those things called ``admonition``
which are really funny

.. note:: This is a note admonition
   It can continue for a long time

   - and even contain
   - bullet lists

Now we are back at writting normally


