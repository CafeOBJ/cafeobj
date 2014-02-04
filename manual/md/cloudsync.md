CloudSync
=========

In the following we will model a very simple protocol for cloud
syncronization of a set of PCs. The full code of the actual
specification, as well as parts of the verification proof score will
be included and discussed.

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

The reason why the equations given in the two modules are necessary
lie in the fact that the default equality `A = B` is defined via the
rewrite logic, and will not be decided for literals. In contrast to
this, the `A == B` equality TODO TODO TODO TODO that is not correct!!!

Furthermore, note that we choose different names for the *idle* state
of the PCs and the cloud, to have easy separation.

The next module introduces a parametrized pair module:
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

generic multi set 
`````
mod MULTISET(X :: TRIV) {
  [ Elt.X < MultiSet ]
  op empty : -> MultiSet {constr} .
  -- associative and commutative set constructor with identity empty
  op (_ _) : MultiSet MultiSet -> MultiSet { constr assoc comm id: empty }
}
`````

The cloud state
`````
mod! CLSTATE { 
  pr(PAIR(NAT, CLLABEL{sort Elt -> ClLabel})*{sort Pair -> ClState, op fst -> fst.clstate, op snd -> snd.clstate }) 
}
`````

once pc state and a set of pc states
`````
mod! PCSTATE { 
  pr(3TUPLE(NAT, NAT, PCLABEL{sort Elt -> PcLabel})*{sort 3Tuple -> PcState})
}
mod! PCSTATES { 
  pr(MULTISET(PCSTATE{sort Elt -> PcState})*{sort MultiSet -> PcStates}) 
}
`````

The state of the whole system is a pair of cloud state and set of pc
states 
`````
mod! STATE { 
  pr(PAIR(CLSTATE{sort Elt -> ClState},PCSTATES{sort Elt -> PcStates})*{sort Pair -> State}) 
}
`````

Transitions

`````
mod! GETVALUE { pr(STATE)
  -- since set is comm,assoc,dist we can assume that the first element
  -- of the multiset is th one that acts
  trans[getvalue]: 
    < < ClVal:Nat , idlecl > , ( << PcVal:Nat ; OldClVal:Nat ; idlepc >> S:PcStates ) >
    =>
    < < ClVal , busy > , ( << PcVal ; ClVal ; gotvalue >> S ) > .
}
`````

`````
mod! UPDATE {
  pr(STATE)
  trans[update]:
    < < ClVal:Nat , busy > , ( << PcVal:Nat ; GotClVal:Nat ; gotvalue >> S:PcStates ) >
    =>
      if PcVal <= GotClVal then
	< < ClVal , busy > , ( << GotClVal ; GotClVal ; updated >> S ) >
      else
	< < PcVal , busy > , ( << PcVal ; PcVal ; updated >> S ) >
      fi .
}
`````

`````
mod! GOTOIDLE {
  pr(STATE)
  trans[gotoidle]: 
    < < ClVal:Nat , busy > , ( << PcVal:Nat ; OldClVal:Nat ; updated >> S:PcStates ) >
    =>
    < < ClVal , idlecl > , ( << PcVal ; OldClVal ; idlepc >> S ) > .
}
`````

The full specification of the cloud

`````
mod! CLOUD { pr(GETVALUE + UPDATE + GOTOIDLE) }
`````


Verification
------------