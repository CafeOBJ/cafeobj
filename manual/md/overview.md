Overview of the system
======================

Let us start with a simple definition of a module, which are the basic
building blocks of any \_cafeobj program:
`````
mod NATPAIR {
  pr(NAT)
  [Pair]
  var P : Pair
  op <_,_> : Nat Nat -> Pair {constr}
  op fst : Pair -> Nat
  op snd : Pair -> Nat
  eq fst( < A:Nat , B:Nat > ) = A .
  eq snd( < A:Nat , B:Nat > ) = B .
}
`````
This example already presents most of the core concepts of \_cafeobj:

* modules as the basic building blocks
* import of other modules `pr(NAT)`
* sorts `[Pair]`
* operator signature and equations

Let us start with sorts, as they are the fundamental types.

Sorts
-----

Most programming languages allow for different sorts, or types of
objects. In this respect \_cafeobj is not different and allows to have
arbitrary sorts. In addition, these sorts can be ordered, more
specific one sort can be declared a sub-sort of another. In the above
example 

`````
[ Pair ]
`````

a new sort called `Pair` is introduced. This is a completely new sort
and is in no sub-sort relation to any other sort. This is a very
common case, and reflects the different types of objects in other
programming languages.

In case one wants to introduce ordering in the sorts, the order can be
expressed together with the definition of the sort, as in:
`````
[ Nat < Set ]
`````
which would introduce a new sort `Set` and declares it as supersort of
the (builtin) sort `Nat`.

For more details concerning sorts, see [`sort declaration`](#sort).

Imports
-------

\_cafeobj allows for importing and reusing of already defined
modules:
`````
pr(NAT)
`````
for example pulls in the natural numbers (in a very minimal
implementation). There are several modes of pulling in other modules,
differing in the way the (semantic) models of the included module are
treated.

After a statement of import, the sorts, variables, and operators of
the imported modules can be used.

For more details see [`protecting`](#protecting),
[`extending`](#extending), [`using`](#using), [`including`](#including)


Variables and Operators
-----------------------

While sorts define data types, variables hold objects of a specific
type, and operators define functionality. For each variable its sort
has to be declared, and for each operator the signature, i.e., the
sorts of the input data and the sort of the output, has to be given. 
`````
var P : Pair
op fst : Pair -> Nat
`````
This example declares a variable `P` of type pair, and an operator
`fst` which maps the sort `Pair` to the sort `Nat`, or in other words,
a function that maps pairs of natural numbers to natural numbers.

We have seen already a different way to specify operators, namely
`````
op <_,_> : Nat Nat -> Pair {constr}
`````
which introduces an infix operator. \_cafeobj is very flexible and
allows to freely specify the syntax. In an operator declaration as the
above, the underscores `_` represent arguments to the operator. That
also means that the number of underscores must match the number of
sorts given before the `->`. After the above declaration \_cafeobj
will be able to parse terms like `< 3 , 4 >` and correctly type them
as pair.

For further details, see [`var`](#var), [`op`](#op).


Equations (or Axioms)
---------------------
Using sorts, variables, and operators we have specified the terms that
we want to speak about. In the following equations, or sometimes
called axioms, will equate different terms.  Equating here is meant in
the algebraic sense, but also in the term-rewriting sense, as
equations form the basis of rewrite rules which provide \_cafeobj with
the executable semantics:
`````
eq fst( < A:Nat , B:Nat > ) = A .
eq snd( < A:Nat , B:Nat > ) = B .
`````
As soon as an operator like `fst` has been declared, we can give
equations. In this case we define `fst` of a pair to return the first
element. 

For further details see [`eq`](#eq).

*******************

In the following chapter we will include the specification of a
protocol with the full code, explaining some concepts on the way.



to be written

alternative title: Main concepts (?)

discuss the following topics in bit more details (parts of the
current manual, stripped down)

- sorts [Ch 3]
- operators [Ch 4, Ch 7]
- module [Ch 2, Ch 8]

do not contain the syntactic definition in all the details,
but explain these important items in more detail

