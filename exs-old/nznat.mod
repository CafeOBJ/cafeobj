** -*- Mode:CafeOBJ -*-
--  this file is originally /dir/goguen/obj/num/nznat.obj
-->  taken from ~diacon/OBJ/nznat.obj
--> nonzero natural numbers

module! NZNAT1 {
  protecting (BOOL)
  signature {
    [ NzNat ]
    op 1 : -> NzNat 
    op s_ : NzNat -> NzNat 
    ops (_+_)(_*_)(quot)(d) : NzNat NzNat -> NzNat 
    op _>_ : NzNat NzNat -> Bool 
    op gcd : NzNat NzNat -> NzNat {comm}
  }

  axioms {
    vars N' M' : NzNat 
    -- ---------------------
    eq 1 + N' = s N' .
    eq N' + 1 = s N' .
    eq (s N') + (s M') = s s (N' + M') .
    eq d(1,1) = 1 .
    eq d(s N',1) = N' .
    eq d(1,s N') = N' .
    eq d(s N', s M') = d(N',M') .
    eq quot(N',M') = if N' > M' then 1 + quot(d(N',M'),M') else 1 fi .
    eq N' * 1 = N' .
    eq 1 * N' = N' .
    eq (s N') * (s M') = s (N' + (M' + (N' * M'))) .
    eq 1 > M' = false .
    eq s N' > 1 = true . 
    eq s N' > s M' = N' > M' .
    eq gcd(N',M') = if N' == M' then N' else
                    (if N' > M' then gcd(d(N',M'),M') 
                     else gcd(N',d(N',M')) fi) fi .
   }
}

eof
**
$Id: nznat.mod,v 1.1.1.1 2003-06-19 08:30:16 sawada Exp $
--
