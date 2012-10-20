mod! NAT+ {
  [ Nat]
  op 0 : -> Nat
  op s_ : Nat -> Nat
  op _+_ : Nat Nat -> Nat

  eq 0 +  N:Nat = N .
  eq (s M:Nat) + N:Nat = s(M + N) .
}

open NAT+
[ NatHalt < Nat ]
op 0 : -> NatHalt .

parse 0 .       -- can be parsed as a term of the minimum sort 0:NatHalt
parse 0:Nat .   -- can be parsed
parse s 0 .     -- Ambiguous
parse s 0:NatHalt .  -- parsed
parse s 0:Nat .   -- parsed

parse 0:Nat + s 0:Nat . -- parsed
red 0:Nat + s 0:Nat .  -- no reduction; no matching

parse 0:NatHalt + s 0:NatHalt . -- parsed
red 0:NatHalt + s 0:NatHalt .  -- no reduction; no matching

close


mod NAT+test {
ex(NAT+)
[ NatHalt < Nat ]
op 0 : -> NatHalt }

select NAT+test

parse 0 .       -- can be parsed as a term of the minimum sort 0:NatHalt
parse 0:Nat .   -- can be parsed
parse s 0 .     -- ambiguous
parse s 0:NatHalt .  -- parsed
parse s 0:Nat .   -- parsed

parse 0:Nat + s 0:Nat . -- parsed
red 0:Nat + s 0:Nat .  -- no reduction; no matching

parse 0:NatHalt + s 0:NatHalt . -- parsed
red 0:NatHalt + s 0:NatHalt .  -- no reduction; no matching


eof
