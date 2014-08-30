Introduction
============

(present a module (idea: stripped down version of the bank-account.mod)
which contains most important and often used constructs
describe the fundamental concepts of CafeOBJ 
(algebraic spec, order sort, model spec, ...)
also contains a quick intro to interaction [Ch 1] but much shorter)

CafeOBJ as TRS specification system, background, algebraic specification
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

  - done 12,13
  - done 14,15
  - done 17,23,24,61,64-69 parts of module expressin todo
  - done 26-28
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
