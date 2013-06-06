==========================
 CafeOBJ Reference Manual
==========================
:Authors: - Ataru T. Nakagawa
          - Toshimi Sawada
          - Kokichi Futatsugi
          - Norbert Preining
:Version: 0.1
:Copyright: 2013 the authors
:License: GFDL version 3 or higher

.. == various directives to get proper output
.. sectnum::
  :depth: 5

.. role:: raw-html(raw)
   :format: html

.. role:: raw-latex(raw)
   :format: latex

.. == various macros for short hands
.. == these macros support only output to latex and html at the moment
.. == don't expect that any other output works
.. |cafeobj| replace:: :raw-latex:`\texttt{CafeOBJ}`:raw-html:`<tt>CafeOBJ</tt>` 

.. == generate a table of contents
.. contents::
  :depth: 5


Introduction
============

(present a module (idea: stripped down version of the bank-account.mod)
which contains most important and often used constructs
describe the fundamental concepts of cafeobj 
(algebraic spec, order sort, model spec, ...)
also contains a quick intro to interaction [Ch 1] but much shorter)

|cafeobj| is a specification language based on three-way extensions to
many-sorted equational logic: the underlying logic is
order-sorted, not just many-sorted; it admits unidiretional transitions,
as well as equations; it also accommodates hidden sorts, on top of
ordinary, visible sorts. A subset of |cafeobj| is executable, where the
operational semantics is given by a conditional order-sorted term rewriting
system. These theoretical bases are indispensable to employ |cafeobj| properly.
Fortunately, there is an ample literature on these subjects, and we are able
to refer the reader to, e.g., [e-m85]_, [m-g82]_ (for basics of
algebraic specifications),  [osa]_, [osa-survey]_ (for order-sorted
logic), [hsa]_ (for hidden sorts), [eatcs-coalg]_ (for coinduction),
[rew-logic]_ (for rewriting
logic), [institution]_ (for institutions), and [trs-eatcs]_,
[trs-handbook]_ (for term rewriting systems), as primers.
The logical aspects of |cafeobj| are explained in detail in [razvan96-1]_
and [cafeobj-rep]_. This manual is for the initiated, and we sometimes
abandon the theoretical rigour for the sake of intuitiveness.

For a very brief introduction, we just highlight a couple of features
of |cafeobj|. |cafeobj| is an offspring of the family of algebraic
specification techniques. A specification is a text, usually of
formal syntax. It denotes an algebraic system constructed out of
sorts (or data types) and sorted (or typed) operators. The system
is characterised by the axioms in the specification. An axiom was
traditionally a plain equation (*essentially algebraic*), but is now
construed much more broadly. For example, |cafeobj| accommodates
conditional equations, directed transitions, and (limited) use of
disequality.

The underlying logic of |cafeobj| is as follows

**Order-sorted logic** [osa]_
  A sort may be a subset of
  another sort. For example, natural numbers may be embedded into rationals.
  This embedding makes valid the assertion that 3 equals 6/2. It also
  realises *operator inheritance*, in the sense that an operator
  declared on rationals are automatically declared on natural numbers.
  Moreover, the subsort relation offers you a simple way to define
  partial operations and exception handling.

**Rewriting logic** [rew-logic]_
  In addition to equality,
  which is subject to the law of symmetry, you may use transition relations,
  which are directed in one way only. State transitions are
  naturally formalised by those relations. In particular, transition
  relations are useful to represent concurrency and/or indeterminacy.

**Hidden sorts** [hsa]_
  You have two kinds of equivalence. One
  is a minimal equivalence, that identifies terms (elements) iff
  they are the same under the given equational theory. Another
  equivalence, employed for so-called hidden sorts, is behavioural:
  two terms are equivalent iff they behave identically under the
  given set of observations.


We would also like to emphasise a very useful feature of |cafeobj|.

**Parameters**
  There are many sorts that are inherently
  generic. Stacks, lists, sets and so on have operations that
  act independently of the properties of base (*data*) elements.
  A more tricky case is priority queues, which require base elements to
  have an order relation. You may define these sorts by
  parameterised modules, where base elements are parameterised out.
  A parameter may be subject to constraints. For example, the parameter
  of a priority queue module may be declared an ordered set, not
  an arbitrary set.


Main Concepts
=============

discuss the following topics in bit more details (parts of the
current manual, stripped down)

- sorts [Ch 3]
- operators [Ch 4, Ch 7]
- module [Ch 2, Ch 8]

do not contain the syntactic definition in all the details,
but explain these important items in more detail

Sorts
-----

Operators
---------

Modules
-------

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
12,13
14,15
17,23,24,61,64-69
26-28
29-31
32,33
39,40
42,43
44,46,47
49,50

From the currently not treated chapters we would
[Ch 5,6] -> part of the "part 3" (inspecting, evaluating, ...)
[Ch 9,10]-> merged into either "part 2" or appendix on proving
[Ch 11] -> part of the "part 3"



.. [e-m85] Ehrig, H. and Mahr, B.,
   *Fundamentals of Algebraic Specifications 1: Equations and Initial
   Semantics*, Springer-Verlag, 1985
.. [m-g82] Meseguer, J. and Goguen, J.A.,
   'Initiality, induction and computability',
   *Algebraic Methods in Semantics*,
   Cambridge University Press, 1984, pp.459--541
.. [osa] Goguen, J.A. and Meseguer, J.,
   *Order-Sorted Algebra 1:
   Equational Deduction for Multiple Inheritance, Polymorphism,
   Overloading and Partial Operations*,
   Technical Report SRI-CSL-89-10, SRI International, 1989
.. [osa-survey] Goguen, J. and Diaconescu, R.,
   'An Oxford Survey of Order Sorted Algebra',
   Mathematical Structures in Computer Science, Vol.4, 1994,
   pp.363--392
.. [hsa] Goguen, J. and Malcom, G.,
   *A Hidden Agenda*, technical report, UCSD, 1998
.. [eatcs-coalg] Jacobs, B. and Rutten, J.,
   'A Tutorial on (Co)Algebras and (Co)Induction',
   *EATCS Bulletin*, No.62, EATCS, 1997, pp.222--259
.. [rew-logic] Meseguer, J.,
   'Conditional Rewriting Logic: Deduction, Models and Concurrency',
   *Proc. 2nd International CTRS Workshop*, Lecture Notes in
   Computer Science 516, 1991, pp.64--91
.. [institution] Goguen, J. and Burstall, R.,
   'Institutions: Abstract Model Theory for Specification and Programming',
   *Journal of the Association for Computing Machinery*,
   Vol.39, 1992, pp.95--146
.. [trs-eatcs] Klop, J.W.,
   'Term Rewriting Systems: A Tutorial',
   *EATCS Bulletin*, No.32, EATCS, 1987, pp.143--182
.. [trs-handbook] Dershowitz, N. and Jouannaud, J.-P.,
   'Rewrite Systems', *Handbook of Theoretical Computer Science,
   Vol.B: Formal Models and Semantics*, The MIT Press/Elsevier Science
   Publishers, 1990, pp.245--320
.. [razvan96-1] Diaconescu, R. and Futatsugi, K.,
   *Logical Semantics of CafeOBJ*, Technical Report
   IS-RR-96-0024S, Japan Advanced Institute for Science and
   Teleology, 1996
.. [cafeobj-rep] Diaconescu, R. and Futatsugi, K.,
   *CafeOBJ Report*, World Scientific, 1998
