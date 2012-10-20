** -*- Mode:CafeOBJ -*-

module! SET( X :: TRIV ) {
  [ Set, Elt < EltSeq ]
  signature {
    -- constructors ---------------------------------
    op {_} : EltSeq -> Set
    op nil : -> EltSeq 
    op _,_ : EltSeq EltSeq -> EltSeq { assoc comm idem id: nil }
    -- basic operations -----------------------------
    op _in_ : Elt Set -> Bool                             -- membership test
    op _U_  : Set Set -> Set { assoc comm id: ({ nil }) } -- Set union
    op _&_  : Set Set -> Set { assoc comm }               -- Set intersection
  }
  axioms {
    vars E E1 E2 : Elt    vars ES1 ES2 : EltSeq
    vars S1 S2   : Set
    -- ---------------------------------------------
    eq [member-test-1]: E in { nil } = false .
    eq [member-test-2]: E in { E1, ES1 } = if E == E1 then true 
                                             else E in { ES1 } fi .
    eq [Set-union]: { ES1 } U { ES2 } = { ES1, ES2 } .
    eq [Set-intersection-1]: { ES1 } & { nil }  = { nil } .
    eq [Set-intersection-2]: { E, ES1 } & { ES2 } 
                             = if E in { ES2 }
                               then { E } U ( { ES1 } & { ES2 } )
                               else { ES1 } & { ES2 } fi .
   }
}

module! STATE {
 protecting (CHAOS:IDENTIFIER)
 [ Identifier < State ]
}

make STATE-SET (SET[X <= view to STATE { sort Elt -> State }])

provide state
--
eof
--
$Id: state.mod,v 1.1.1.1 2003-06-19 08:30:17 sawada Exp $
