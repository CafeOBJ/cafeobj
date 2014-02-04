Introduction
============

This manual introduces the language \_cafeobj. Is is a reference manual
with the aim to document the current status of the language, and not
targetting at an exhaustive presentation of the mathematical and logical
background. Still, the next section will give a short summary of the
underlying formal approach and carry references for those in search
for details.

The manual is structured into three parts. The first one being this
introduction, the second one being the presenation of basic concepts
of \_cafeobj by providing a simple protocol which will get specified
and verified. Although the second part tries to give a view onto the
core features and their usage, it should not be considered a course in
\_cafeobj, and cannot replace a proper introduction to the language.

Finally, the last part consists of explanations of all current
language elements in alphabetic order. This includes several higher
level concepts, as well as heavy cross-referencing.

While we hope that this manual and the introductory part helps
beginners to start programming in \_cafeobj, the main target are those
who already have acquired a certain level of fluency, but are in need
for a reference of the language.


Background of \_cafeobj
----------------------
\_cafeobj is a specification language based on three-way extensions to
many-sorted equational logic: the underlying logic is
order-sorted, not just many-sorted; it admits unidiretional transitions,
as well as equations; it also accommodates hidden sorts, on top of
ordinary, visible sorts. A subset of \_cafeobj is executable, where the
operational semantics is given by a conditional order-sorted term rewriting
system. These theoretical bases are indispensable to employ \_cafeobj properly.
Fortunately, there is an ample literature on these subjects, and we are able
to refer the reader to, e.g., \cite{e-m85}, \cite{m-g82} (for basics of
algebraic specifications), \cite{osa}, \cite{osa-survey} (for order-sorted
logic), \cite{hsa} (for hidden sorts), \cite{eatcs-coalg} (for coinduction),
\cite{rew-logic} (for rewriting
logic), \cite{institution} (for institutions), and \cite{trs-eatcs},
\cite{trs-handbook} (for term rewriting systems), as primers.
The logical aspects of \_cafeobj are explained in detail in \cite{razvan96-1}
and \cite{cafeobj-rep}. This manual is for the initiated, and we sometimes
abandon the theoretical rigour for the sake of intuitiveness.

For a very brief introduction, we just highlight a couple of features
of \_cafeobj. \_cafeobj is an offspring of the family of algebraic
specification techniques. A specification is a text, usually of
formal syntax. It denotes an algebraic system constructed out of
sorts (or data types) and sorted (or typed) operators. The system
is characterised by the axioms in the specification. An axiom was
traditionally a plain equation (``essentially algebraic''), but is now
construed much more broadly. For example, \_cafeobj accommodates
conditional equations, directed transitions, and (limited) use of
disequality.

The underlying logic of \_cafeobj is as follows:

Order-sorted logic
  : [@osa] A sort may be a subset of
    another sort. For example, natural numbers may be embedded into rationals.
    This embedding makes valid the assertion that 3 equals 6/2. It also
    realises ``operator inheritance'', in the sense that an operator
    declared on rationals are automatically declared on natural numbers.
    Moreover, the subsort relation offers you a simple way to define
    partial operations and exception handling.

Rewriting logic
  : [@rew-logic] In addition to equality,
    which is subject to the law of symmetry, you may use transition relations,
    which are directed in one way only. State transitions are
    naturally formalised by those relations. In particular, transition
    relations are useful to represent concurrency and/or indeterminacy.

Hidden sorts
  : [@hsa] You have two kinds of equivalence. One
    is a minimal equivalence, that identifies terms (elements) iff
    they are the same under the given equational theory. Another
    equivalence, employed for so-called hidden sorts, is behavioural:
    two terms are equivalent iff they behave identically under the
    given set of observations.

We would also like to emphasise a very useful feature of \_cafeobj.

Parameters
  : There are many sorts that are inherently
    generic. Stacks, lists, sets and so on have operations that
    act independently of the properties of base (``data'') elements.
    A more tricky case is priority queues, which require base elements to
    have an order relation. You may define these sorts by
    parameterised modules, where base elements are parameterised out.
    A parameter may be subject to constraints. For example, the parameter
    of a priority queue module may be declared an ordered set, not
    an arbitrary set.


