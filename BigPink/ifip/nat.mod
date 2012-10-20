** --------------------------------------------------------------------
** nat.mod
** --------------------------------------------------------------------

mod* STREAM[X :: TRIV]
{
  signature {
    *[ Stream ]*
    bop head : Stream -> Elt
    bop tail : Stream -> Stream
    op _#_ : Elt Stream -> Stream { coherent }
  }
  axioms {
    var E : Elt   var S : Stream 
    eq head(E # S) = E .
    eq tail(E # S) = S .
  }
}

-- unprotect NAT .

mod! NAT*
{
  signature {
    [ Nat ]
    op 0 : -> Nat
    op s : Nat -> Nat
  }
}

mod* NAT-STREAM
{
  imports {
    protecting(STREAM(NAT*))
  }
  signature {
    ops nat nat' : Nat -> Stream
      op succ : Stream -> Stream
  }
  axioms {
    var N : Nat
    var S : Stream
    eq head(nat(N)) = N .
    beq tail(nat(N)) = nat(s(N)) .
    eq head(succ(S)) = s(head(S)) .
    beq tail(succ(S)) = succ(tail(S)) .
    eq head(nat'(N)) = N .
    beq tail(nat'(N)) = succ(nat'(N)) .
  }
}

mod PROOF
{
  imports {
    protecting(NAT-STREAM)
  }
  signature {
    pred R : Stream Stream 
  }
  axioms {
  -- reflexive, symmetric, transitive closure
    ax \A[S:Stream] R(S,S) .
    ax \A[S:Stream,T:Stream] R(S,T) -> R(T,S) .
    ax \A[S:Stream,T:Stream,U:Stream] R(S,T) & R(T,U) -> R(S,U) .

  -- closure by coherent operators
    ax \A[S:Stream,T:Stream] R(S,T) -> R(succ(S),succ(T)) .

    ax \A[N:Nat] R(nat(N),nat'(N)) .
    ax \A[N:Nat] R(tail(nat(N)),tail(nat'(N))) .
  -- goal [GOAL]: \A[N:Nat] R(tail(tail(nat(N))),tail(tail(nat'(N)))) . -- ok

  -- to check R is included in =*=
  -- goal [GOAL]: \A[S:Stream,T:Stream] R(S,T) -> head(S) = head(T) . -- ng 
  goal [GOAL]: R(S:Stream,T:Stream) -> head(S) = head(T) . -- ok!!???
  }
}

option reset
flag(process-input,on)
flag(print-kept,off)
flag(print-new-demod,off)
flag(print-back-demod,on)
flag(print-back-sub,off)
flag(control-memory,on)
param(max-sos,500)
param(pick-given-ratio,4)
param(stats-level,1)
param(max-seconds,86400)
flag(kb2,on)
flag(hyper-res,on)
flag(binary-res,on)
flag(unit-deletion,on)
flag(factor,on)
flag(universal-symmetry,on)
flag(input-sos-first,on)

flag(print-stats,on)
param(max-proofs,1)

open PROOF .

db reset

sos = { GOAL }

resolve .

close
**
eof
**
$Id: nat.mod,v 1.2 2003-11-04 03:11:26 sawada Exp $
