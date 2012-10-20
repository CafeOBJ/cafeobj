-- FILE: /home/diacon/LANG/Cafe/prog/integer.mod
-- CONTENTS: ADT specification of integers;
--           spec (almost) operationally complete
-- AUTHOR: Michihiro Matsumoto
-- DIFFICULTY: *

mod! DINT {
  [ DNat < DInt ]
  op 0 : -> DNat { constr }
  op s_ : DNat -> DNat { constr }
  op s_ : DInt -> DInt { constr }
  op p_ : DInt -> DInt { constr }

  op _+_ : DInt DInt -> DInt
  op _+_ : DNat DNat -> DNat
  op _-_ : DInt DInt -> DInt
  op -_ : DInt -> DInt

  op _<_ : DNat DNat -> Bool
  op _<=_ : DNat DNat -> Bool
  op _<_ : DInt DInt -> Bool
  op _<=_ : DInt DInt -> Bool 
        

  vars I J I' J' : DInt
  eq s p I = I .
  eq p s I = I .

  eq I + 0 = I .
  eq 0 + I = I .
  eq I + s J = s(I + J) .
  eq s I + J = s(I + J) .
  eq I + p J = p(I + J) .
  eq p I + J = p(I + J) .

  eq I - 0 = I .
  eq 0 - I = - I .
  eq I - s J = p(I - J) .
  eq s I - J = s(I - J) .
  eq I - p J = s(I - J) .
  eq p I - J = p(I - J) .

  eq - 0 = 0 .
  eq - (s I) = p (- I) .
  eq - (p I) = s (- I) .

  vars M N K L : DInt
  eq 0 < 0 = false .
  eq 0 < s N = true .
  eq s M < 0 = false .
  eq s M < s N = M < N .
  ceq M <= N = true if M < N .
  ceq M <= N = true if M == N .
  ceq M <= N = false if N < M .
  eq M <= (M + N) = true .
  eq N <= (M + N) = true .

  eq (- I) < (- J) = J < I .
  eq (- I) <= (- J) = J <= I .
  eq (- M) <= N = true .
  eq N <= (- M) = false .
  eq N < (- M) = false .
  ceq (- M) < N = true if (0 < M) or (0 < N) .
  
  ceq (I + J) <= (I' + J') = true if (I <= I') and (J <= J') .
}

--
eof
--
$Id: integer.mod,v 1.1.1.1 2003-06-19 08:30:10 sawada Exp $
