Introduction
============

This manual introduces the language \_cafeobj. Is is a reference manual
with the aim to document the current status of the language, and not
targeting at an exhaustive presentation of the mathematical and logical
background. Still, the next section will give a short summary of the
underlying formal approach and carry references for those in search
for details.

The manual is structured into three parts. The first one being this
introduction, the second one being the presentation of basic concepts
of \_cafeobj by providing a simple protocol which will get specified
and verified. Although the second part tries to give a view onto the
core features and their usage, it should not be considered a course in
\_cafeobj, and cannot replace a proper introduction to the language.
The \_cafeobj distribution also includes a _user manual_. This user
manual is slightly outdated with respect to the current status of the
language, but is targeting those without and prior knowledge of
\_cafeobj. 

Finally, the last part consists of explanations of all current
language elements in alphabetic order. This includes several higher
level concepts, as well as heavy cross-referencing.

While we hope that this manual and the introductory part helps
beginners to start programming in \_cafeobj, the main target are those
who already have acquired a certain level of fluency, but are in need
for a reference of the language.



Background of \_cafeobj
----------------------
\_cafeobj is an algebraic specification and verification
language. Although it can be employed for all kind of programming
(since it is Turing complete), the main target are algebraic
specification of software systems. This includes programs, protocols,
and all kind of interaction specifications. In addition to being a
specification language, it is also a _verification_ language, that is,
a specification given in \_cafeobj can be verified within the same
language environment.

_Specification_ here means that we are trying to describe the inner
workings of a software system in a mathematical way, while
_verification_ means that we give a mathematical proof of certain
properties.  A specification is a text, usually of
formal syntax. It denotes an algebraic system constructed out of
sorts (or data types) and sorted (or typed) operators. The system
is characterize by the axioms in the specification. An axiom was
traditionally a plain equation (``essentially algebraic''), but is now
construed much more broadly. For example, \_cafeobj accommodates
conditional equations, directed transitions, and (limited) use of
disequality.

\_cafeobj is based on three extensions to the basic many-sorted
equational logic:

Order-sorted logic
:    In addition to having different sorts (similar to types in other
     programming languages), these sorts can be ordered, or in other
     words, one sort can be a subset of another sort: Take for
     example the number stack: \_cafeobj allows for the provision of
     natural numbers, which are part of the rational numbers, which are
     part of the real numbers. This concept allows for operator
     inheritance and overloading.
Behavioral logic
:    Algebraic modeling is often based on constructors, i.e., all terms
     under discussion are built up from given operations, and equality
     can be decided via an equational theory. While being very
     successful, it is often necessary to model infinite objects (like
     data streams), which cannot be achieved in this way. \_cafeobj
     includes _behavioral logic_ and the respective _hidden sorts_ as
     methodology to model infinite objects which identity is defined via
     behavior instead of the equational theory.
Rewriting logic
:    Aim of a algebraic specification and verification is to give a
     formal proof of correctness. \_cafeobj contains order-sorted term
     rewriting as operational semantics, which allows for _execution of
     proof scores_, \_cafeobj code which forms a proof of the required
     properties. 

There is a wide range of literature on all of these subjects for the
interested reader in search for theoretical background. We refer the
reader to \cite{DBLP:conf/birthday/2014futatsugi} as a starting point.
