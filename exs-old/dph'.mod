** -*- Mode:CafeOBJ -*-
--
-- from Forsdonnet Sample
-- 


module EMPTY { [ Empty ] op * : -> Empty }

module MULTISET(X :: TRIV) {
  protecting (EMPTY)
  signature {
    [ Empty Elt < MultiSet ]
    op _,_ : MultiSet MultiSet -> MultiSet { assoc comm id: * }
  }
}


module NAME {
  signature {
    [ Variable < Primitive < Name ]
    op _[_] : Name Name -> Name
    op _[_:=_] : Name Variable Name -> Name
  }
  axioms {
    var X : Variable
    var P : Primitive
    vars L M N : Name
    cq P[X := N] = N if P == X .
    cq P[X := N] = P if not(P == X) .
    eq L[M][X := N] = L[X := N][M[X := N]] .
  }
}

module CHANNEL {
  protecting (NAME)
  signature {
    [ Channel ]
    ops ? ! : Name -> Channel
    op _[_:=_] : Channel Variable Name -> Channel
  }
  axioms {
    var X : Variable
    vars M N : Name
    eq ?(M)[X := N] = ?(M[X := N]) .
    eq !(M)[X := N] = !(M[X := N]) .
  }
}

view TRIV2CHANNEL from TRIV to CHANNEL
{
  sort Elt -> Channel
}

module CHANNELS {
  protecting ((MULTISET * { sort MultiSet -> Channels })[TRIV2CHANNEL])
  signature {
    op _[_:=_] : Channels Variable Name -> Channels
  }
  axioms {
    var N : Name
    var X : Variable
    var C : Channel
    var Cs : Channels
    eq *[X := N] = * .
    cq (C,Cs)[X := N] = (C[X := N]),(Cs[X := N]) if not(Cs == *) .
  }
}


module PROCESS {
  protecting (CHANNELS)
  signature {
    [ Unit < Process ]
    op @ : -> Unit
    op {_};_ : Channels Process -> Process
    op _[_:=_] : Process Variable Name -> Process
  }
  axioms {
    var N : Name
    var X : Variable
    var U : Unit
    var P : Process
    var Cs : Channels
    eq {*}; @ = @ .
    eq {*};({Cs}; P) = {Cs}; P .
    eq U[X := N] = U .
    eq ({Cs}; P)[X := N] = {Cs[X := N]};(P[X := N]) .
  }
}

module COMPOSITION {
  extending (PROCESS)
  signature {
    op _|_ : Process Process -> Process { assoc comm id: @ }
  }
  axioms {
    var X : Variable
    vars M N : Name
    vars Cs Ds : Channels
    vars P Q R : Process
    trans  ({!(N),Cs}; P)|({?(N),Ds}; Q) => ({Cs}; P)|({Ds}; Q) .
    trans ({!(M[N]),Cs}; P)|({?(M[X]),Ds}; Q) => ({Cs}; P)|({Ds};(Q[X := N])) .
    ctrans ({!(N),Cs}; P)|({?(N),Ds}; Q)| R =>
        ({Cs}; P)|({Ds}; Q)| R if not(R == @) .
    ctrans ({!(M[N]),Cs}; P)|({?(M[X]),Ds}; Q)| R =>
        ({Cs}; P)|({Ds};(Q[X := N]))| R if not(R == @) .
    cq  (P | Q)[X := N] = (P[X := N])|(Q[X := N]) if not(P == @ or Q == @).
  }
}

module NUMBER { [ Num ] ops 1 2 3 4 : -> Num }

module ACTION-on-FORK {
  extending (NAME)
  signature {
    ops pickup putdown : -> Primitive
  }
}

module FORK {
  extending (PROCESS)
  extending (ACTION-on-FORK)
  signature {
    op x : -> Variable
    op FK : -> Unit
    op fk : -> Process
  }
  axioms {
    eq fk = {?(pickup[x])};{?(putdown[x])}; FK .
    eq {*}; FK = fk .
  }
}

module ACTION-on-SEAT {
  extending (NAME)
  signature {
    ops sitdown getup : -> Primitive
  }
}


module SEAT {
  extending (PROCESS)
  extending (ACTION-on-SEAT)
  signature {
    op y : -> Variable
    op ST : -> Unit
    op st : -> Process
  }
  axioms {
    eq st = {?(sitdown[y])};{?(getup[y])}; ST .
    eq {*}; ST = st .
  }
}

module PHILOSOPHER {
  extending (PROCESS)
  extending (ACTION-on-FORK)
  extending (ACTION-on-SEAT)
  protecting (NUMBER)
  signature {
    [ Num < Primitive ]
    op PH : -> Unit
    op ph : Num -> Process
  }
  axioms {
    var i : Num
    eq ph(i) = {!(sitdown[i])};
               {!(pickup[i]),!(pickup[i])};
               {!(putdown[i]),!(putdown[i])};
               {!(getup[i])}; PH .
  }
}

module DININGROOM {
  extending (COMPOSITION)
  extending (FORK)
  extending (SEAT)
  extending (PHILOSOPHER)
}

open DININGROOM .
op sph : Num -> Process .
var j : Num .
eq sph(j) = ph(j) | st .
let droom = fk | fk | fk | sph(1) | sph(2) | sph(3) .

exec droom .
eof
close

--   {!(pickup[3])};{!(putdown[3]),!(putdown[3])};{!(getup[3])}; PH
-- | {?(putdown[3])}; FK
-- | {!(pickup[2])};{!(putdown[2]),!(putdown[2])};{!(getup[2])}; PH
-- | {?(putdown[2])}; FK
-- | {!(pickup[1])};{!(putdown[1]),!(putdown[1])};{!(getup[1])}; PH
-- | {?(putdown[1])}; FK
-- | {?(getup[1])}; ST
-- | {?(getup[2])}; ST
-- | {?(getup[3])}; ST
-- : Process
-- (0.000 sec for parse, 207 rewrites(37.150 sec), 632 match attempts)

open DININGROOM .
let droom = fk | fk | fk | ph(1) | ph(2) | ph(3) | st | st .
exec droom .
close


-- | {?(sitdown[y])};{?(getup[y])}; ST
-- | {?(sitdown[y])};{?(getup[y])}; ST
-- | {*}; PH
-- | {*}; PH
-- | {?(pickup[x])};{?(putdown[x])}; FK
-- | {?(pickup[x])};{?(putdown[x])}; FK
-- | {?(pickup[x])};{?(putdown[x])}; FK
-- : Process
-- (0.000 sec for parse, 332 rewrites(46.533 sec), 1175 match attempts)

eof

