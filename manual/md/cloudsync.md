CloudSync
=========

In the following we will model a very simple protocol for cloud
syncronization of a set of PCs. The full code of the actual
specification, as well as parts of the verification proof score will
be included and discussed.

Besides giving an example of a specification and verification, we also
try to explain several of the most important concepts in \_cafeobj
using rather simple examples.

Protocoll
---------

One cloud computer and arbitrary many PCs have one value each that
they want to keep in sync. This value is a natural number, and higher
values mean more recent (like SVN revision numbers).

The Cloud can be in two states, *idle* and *busy*, while the PCs can
be on of the following three states: *idle*, *gotvalue*, *updated*.
The Cloud as well as all PCs are initially in the *idle* state. 
When a PC connects to the cloud, three things happen:

1. the cloud changes into *busy* state
2. the PC reads the value of the cloud and saves it in a temporary
   location
3. the PC changes into *gotvalue* state

In the *gotvalue* state the PC compares his own value against the
value it got from the cloud, and updates accordingly (changes either
the cloud or the own value to the larger one). After this the PC
changes into the *updated* state.

From the *update* state both the Cloud and the PC return into the
*idle* state.

TODO include a graphic that shows this TODO

Specification
-------------

We will now go through the full specification with explanations of
some of the points surfacing. We are starting with two modules that
specify the possible states the cloud and the PCs can be in:
`````
mod! CLLABEL {
  [ClLabelLt < ClLabel]
  ops idlecl busy : -> ClLabelLt {constr} .
  eq (L1:ClLabelLt = L2:ClLabelLt) = (L1 == L2) .
}
mod! PCLABEL {
  [PcLabelLt < PcLabel]
  ops idlepc gotvalue updated : -> PcLabelLt {constr} .
  eq (L1:PcLabelLt = L2:PcLabelLt) = (L1 == L2) .
}
`````
Both modules define two new sorts each, the actual label, and literals
for the labels. One can see that we declare the signatures of the
literal labels with the [`ops`](#op) keyword, which introduces several
operators of the same signature at the same time.

The last equation in each models provides a definition of equality by
using the _behavioral_ equality `==`. 
The predicate `==` is the equivalence predicate defined via
reduction. Thus, the two axioms given above state that two literals
for labels are the same if they are syntactically the same, since they
cannot be rewritten anymore.

Furthermore, note that we choose different names for the *idle* state
of the PCs and the cloud, to have easy separation.

The next module introduces a parametrized pair module. Parametrizing
modules is a very powerful construction, and common in object oriented
programming languages. In principle we leave open what are the actual
components of the pairs, and only specify the operational behaviour on
a single pair.

In this and the next example of the multi-set, there are no additional
requirements on the sorts that can be used to instantiate a pair (or
multi-set). In a more general setting the argument after the double
colon `::` refers to a sort, and an instantiation must be adequate for
this sort (details require deeper understanding of homomorphism).
`````
mod! PAIR(X :: TRIV,Y :: TRIV) {
  [Pair]
  op <_,_> : Elt.X Elt.Y -> Pair {constr}
  op fst : Pair -> Elt.X
  op snd : Pair -> Elt.Y
  eq fst(< A:Elt.X,B:Elt.Y >) = A .
  eq snd(< A:Elt.X,B:Elt.Y >) = B .
}
`````

The next module is also parametrized, axiomatizing the concept of
multi-set where a certain element can appear multiple times in the
multi-set. We want to use this module to present another feature,
namely the option to specify additional properties of some
operators. In this case we are specifying that the constructor for
sets is associative `assoc`, commutative `comm`, and has as identity
the `empty` set. 

While it is easily possible to add associativity and commutativity as
axioms directly, this is not advisable, especially for
commutativity. Assume adding the simple equation `eq A * B = B * A .`.
This defines a rewrite rule from left to right. But since `A` and `B`
are variables the can be instantiated with arbitrary subterms, and one
would end up with an infinite rewriting.
`````
mod MULTISET(X :: TRIV) {
  [ Elt.X < MultiSet ]
  op empty : -> MultiSet {constr} .
  -- associative and commutative set constructor with identity empty
  op (_ _) : MultiSet MultiSet -> MultiSet { constr assoc comm id: empty }
}
`````

With all this set up we can defined the cloud state as a pair of a
natural number, and a state. Here we see how a parametrized module is
instantiated. The details of the renaming for the second element are a
bit involved, but thinking about renaming of sorts and operators to
match the ones given is the best idea. 

Having this in mind we see that when we put the `CLLABEL` into the
second part of the pair, we tell the system that it should use the
`ClLabel` sort for the instantiation of the `Elt` sort, and not the
`ClLabelLt` sort. 

Furthermore, after the instantiation we rename the final outcome
again. In this case we rename the `Pair` to `ClState`, and the
operators to their cousins with extension in the name.
`````
mod! CLSTATE { 
  pr(PAIR(NAT, CLLABEL{sort Elt -> ClLabel})*
     {sort Pair -> ClState, op fst -> fst.clstate, op snd -> snd.clstate }) 
}
`````

The PC state is now very similar, only that we have to have a triple
(`3TUPLE` is a builtin predicate of \_cafeobj), since we need one
additional place for the temporary value. In the same way as above we
rename the `Elt` to `PcLabel` and the outcome back to `PcState`.
`````
mod! PCSTATE { 
  pr(3TUPLE(NAT, NAT, PCLABEL{sort Elt -> PcLabel})*{sort 3Tuple -> PcState})
}
`````

As we will have an arbitrary set of PCs, we define the multi-set of
all PC states, by instatiating the multi-set from above with the just
defined `PcState` sort, and rename the result to `PcStates`.
`````
mod! PCSTATES { 
  pr(MULTISET(PCSTATE{sort Elt -> PcState})*{sort MultiSet -> PcStates}) 
}
`````

Finally, the state of the whole system is declared as a pair of the
cloud state and the pc states.
`````
mod! STATE { 
  pr(PAIR(CLSTATE{sort Elt -> ClState},
          PCSTATES{sort Elt -> PcStates})*{sort Pair -> State}) 
}
`````

The final part is to specify transitions. We have described the
protocol by a state machine, and the following transitions will model
the transitions in this machine.

The first transition is the initialization of the syncronization by
reading the cloud value, saving it into the local register, and both
partners go into busy state. 

Note that, since we have declared multi-set as commutative and
associative, we can assume that the first element of the multi-set is
actually the one we are acting on.

Transitions are different from axioms in the sense that the do not
state that two terms are the same, but only that one terms can change
into another.
`````
mod! GETVALUE { pr(STATE)
  trans[getvalue]: 
    < < ClVal:Nat , idlecl > , 
      ( << PcVal:Nat ; OldClVal:Nat ; idlepc >> S:PcStates ) >
    =>
    < < ClVal , busy > , ( << PcVal ; ClVal ; gotvalue >> S ) > .
}
`````

The next transition is the critical part, the update of the side with
the lower value. Here we are using the built-in `if ... then ... else
... fi` operator.
`````
mod! UPDATE { pr(STATE)
  trans[update]:
    < < ClVal:Nat , busy > , 
      ( << PcVal:Nat ; GotClVal:Nat ; gotvalue >> S:PcStates ) >
    =>
      if PcVal <= GotClVal then
	< < ClVal , busy > , ( << GotClVal ; GotClVal ; updated >> S ) >
      else
	< < PcVal , busy > , ( << PcVal ; PcVal ; updated >> S ) >
      fi .
}
`````

The last transition is sending the both sides of the syncronization
into the idle states.
`````
mod! GOTOIDLE { pr(STATE)
  trans[gotoidle]: 
    < < ClVal:Nat , busy > , 
      ( << PcVal:Nat ; OldClVal:Nat ; updated >> S:PcStates ) >
    =>
    < < ClVal , idlecl > , ( << PcVal ; OldClVal ; idlepc >> S ) > .
}
`````

This completes the complete specification of the protocol, and we are
defining a module `CLOUD` that collects all that.
`````
mod! CLOUD { pr(GETVALUE + UPDATE + GOTOIDLE) }
`````



Verification
------------

Aim of the verification is to show *correctness* in the sense that no
two PCs are at the same time in the busy state. The idea of the proof
is to show using induction on the length of transition sequences from
initial states to reachable states, that for all reachable states this
property is fulfilled.

More specific, we give a characterization of initial states, and show
that for initial states the property holds (base case of the
induction). Then we show that for all possible transitions, if the
target property holds at the beginning of the transition, it also
holds at the end of the transition. 

Combining this with a (meta-level) induction proof on the length of
transition sequences, we show that the target property holds for all
reachable states. 

Like with loop invariants in other verification schemes, it turns out
that a single target property, the exclusion property mentioned above,
does not suffice to hold over transitions, i.e., act as transition
invariant. Thus, we have to extended it with additional properties.

The first part of this mini-tutorial on the specification of CloudSync
contained the full code, but in the following we will, due to space
reasons, only include partial code. The latest version of the
CloudSync code can be obtained from \cite{preining:cafeobj}.

But let us start with the definition of predicates for the initial
states. The first step is to define some elementary functions on
states, counting how many PCs are in a certain state:
`````
mod! STATEfuncs {
  pr(NAT + STATE) 
  -- no pc in gotvalue state
  pred zero-gotvalue : State .
  pred zero-updated : State .
  ...
}
`````

We are collecting a set of predicates, indicated by their predicate
name, and define `apply` as an operator that checks each single
predicate against a state, and forms the conjunct of the results.
`````
mod! APPLYPREDS {
  pr(STATE)
  [PredName < PredNameSeq]
  op (_ _) : PredNameSeq PredNameSeq -> PredNameSeq {assoc} .
  op apply : PredNameSeq State -> Bool .
  eq apply(P:PredName PS:PredNameSeq, S:State) = apply(P,S) and apply(PS,S) .
}
`````

Characterization of the initial state is easy, as it only requires
that all PCs as well as the cloud is in idle state.
`````
mod! INITPREDS {
  ...
  op cl-is-idle-name : -> PredName .
  op pcs-are-idle-name : -> PredName .
  ...
}
`````

In the following we define the predicate specifying initial states:
`````
mod! INITIALSTATE {
  pr(INITPREDS)
  op init-name : -> PredNameSeq .
  eq init-name = cl-is-idle-name pcs-are-idle-name .
  pred init : State .
  eq init(S:State) = apply(init-name, S) .
}
`````

Let us now turn to the most difficult part, that is finding an
invariant. This is not a one-shot technique, but mostly iterative. One
starts with a set of predicates, and realizes that the proofs don't
work out properly, due to some missing properties. Thus, we add new
predicates and iterate until the induction proof finally succeeds.

In the following case we ended up with five different predicates that
combined worked as invariant:

`cloud-idle-pcs-idle`
  : If the cloud is in the idle state, then all the pcs are also in
    the idle state.

`pc-clval`
  : If the cloud is in busy state, then the value of the cloud and
    the value in the temporary storage area of any PCs in the
    `gotvalue` or `updated` states agree. 

`one-active`
  : At most one PC is out of the idle state.

`gotvalue-cloud-value`
  : If a PC is in the `gotvalue` state, then the value saved in the
    temporary storage area and the one of the cloud agree.

`goal`
  : If a PC is in the `updated` state, then the value of the PC and
    the value of the cloud agree.

See the mentioned web-page for the full code of these modules.

In addition to the necessity to introduce additional predicates to
obtain an invariant, it also often turns out that some properties, or
lemmas, have to be stated or proven so that the verification can work
out. In our case some properties on `if_then_else_fi` constructs, as
well as consequences of rewriting are included in a module
`NECESSARYFACTS`. 

The final - and one of the most important parts - is the proof of the
two properties:

- base case: if a state satisfies the initial state predicate, it also
  satisfies the invariant:
     `````
     red init(S) implies invariant(S) . 
     `````
- induction step: if a state satisfies the invariant, and we apply a
  transition, then the next state also satisfies the invariant:
     `````
     red inv-condition(S, SS) .
     ````

In both cases we cannot work with a general variable `S`, as in this
case no rewriting can take place, and we will not obtain true. What
has to be done is to provide a covering set of state expressions,
i.e., a set of terms such that every possible instance of a state is
also an instance of one of these terms. In our case this is quite easy
to provide and consists of six different state terms, combining the
three possibilities for a PC with two options of states for the cloud:
`````
  ops s1 s2 s3 s4 t1 t2 t3 t4 : -> State .
  eq s1 =  < < N , idlecl > , ( << M ; K ; idlepc   >> PCS ) >  .
  eq s2 =  < < N , idlecl > , ( << M ; K ; gotvalue >> PCS ) >  .
  eq s3 =  < < N , idlecl > , ( << M ; K ; updated  >> PCS ) >  .
  eq t1 =  < < N , busy   > , ( << M ; K ; idlepc   >> PCS ) >  .
  eq t2 =  < < N , busy   > , ( << M ; K ; gotvalue >> PCS ) >  .
  eq t3 =  < < N , busy   > , ( << M ; K ; updated  >> PCS ) >  .
`````
It is easy to see that any arbitrary state term can be obtained as
instance of one of these six state terms.

What we then show is that the above properties do hold for each of
these terms, and thus for each of the reachable states. In details, we
show that:
`````
  red init(s1) implies invariant(s1) .
  red init(s2) implies invariant(s2) .
  red init(s3) implies invariant(s3) .
  red init(t1) implies invariant(t1) .
  red init(t2) implies invariant(t2) .
  red init(t3) implies invariant(t3) .
`````
all of these expressions reduce to `true`. And furthermore, all of the
following expressions, too:
`````
  red inv-condition(s1, SS) .
  red inv-condition(s2, SS) .
  red inv-condition(s3, SS) .
  red inv-condition(t1, SS) .
  red inv-condition(t2, SS) .
  red inv-condition(t3, SS) .
`````
Unfortunately, in the case of `t2` this didn't turn out to be directly
possible, and a further case distinction was necessary to complete the
proof. 

This concludes the presentation of the CloudSync protocol. We
described the cloud protocol using a _state system_ and
transitions. This is just one way of implementation. There are other
approaches to specification using purely term-based expressions that
do not use transitions, but equational theory only. 
One of the strength of \_cafeobj is that it does not require any
specific approach to modeling, but allows for freedom in choosing
methodology.


