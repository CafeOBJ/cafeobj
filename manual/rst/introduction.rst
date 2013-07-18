
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

