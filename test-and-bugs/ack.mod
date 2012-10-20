--
-- Compute Ackermann's function
--
module! ACKERMANN
{
  [ N ]
  op 0 : -> N
  op s : N -> N 
  op ack : N N -> N { memo }
  -- op ack : N N -> N 
  eq ack(0, I:N) = s(I) .
  eq ack(s(I:N), 0) = ack(I, s(0)) .
  eq ack(s(I:N), s(J:N)) = ack(I, ack(s(I), J)) .
}

-- reduce ack(s(s(s(0))), s(0)) .
-- reduce ack(s(s(s(0))), s(s(0))) .
-- reduce ack(s(s(s(0))), s(s(s(0)))) .
-- reduce ack(s(s(s(0))), s(s(s(s(0))))) .
-- reduce ack(s(s(s(0))), s(s(s(s(s(0)))))) .
-- reduce ack(s(s(s(0))), s(s(s(s(s(s(0))))))) .
-- reduce ack(s(s(s(0))), s(s(s(s(s(s(s(0)))))))) .

module! ACKERMANN2
{
  protecting (NAT)
  op ack : Nat Nat -> Nat { memo }
  -- op ack : Nat Nat -> Nat
  vars I J : Nat
  vars M N : NzNat
  ceq ack(I, J) = J + 1 if I == 0 .
  eq ack(M, J) = if J == 0 then 
                    ack(p(M), 1)
                 else
                    ack(p(M), ack(M, p(J)))
                 fi .
}

