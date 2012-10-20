mod* STREAM (X :: TRIV) {
  *[ Stream ]*
  bop head : Stream -> Elt
  bop tail : Stream -> Stream
  ops odd even : Stream -> Stream
  op merge : Stream Stream -> Stream
  
  vars S S' : Stream
  eq [odd-head] : head(odd(S)) = head(S) .
  eq [odd-tail] : tail(odd(S)) = odd(tail(tail(S))) .
  eq [even] : even(S) = odd(tail(S)) .
  eq [merge-head] : head(merge(S,S')) = head(S) .
  eq [merge-tail] : tail(merge(S,S')) = merge(S',tail(S)) .
}

-- Theorem to prove: beq merge(odd(S),even(S)) = S .
-- 1. by context induction

open STREAM
reduce head(merge(odd(`s:Stream),even(`s))) == head(`s) .
op tail^n : Stream -> Stream .
eq [ind-hyp] : head(tail^n(merge(odd(S:Stream),even(S)))) = head(tail^n(S)) .
start head(tail^n(tail(merge(odd(`s:Stream),even(`s))))) ==
      head(tail^n(tail(`s))) .
apply .merge-tail within term .
apply .even within term .
apply .odd-tail within term .
apply -.even with S = (tail(`s:Stream)) within term .
apply .ind-hyp within term .
apply reduce at term .
close

-- eof

-- 2. by finality

open STREAM
reduce head(merge(odd(`s:Stream),even(`s))) == head(`s) .
reduce tail(merge(odd(`s:Stream),even(`s))) ==
       merge(odd(tail(`s)),even(tail(`s))) .
close
  
-- 3. by bisimulation

open STREAM
op _R_ : Stream Stream -> Bool .
eq merge(odd(S),even(S)) R S = true .
reduce head(merge(odd(`s:Stream),even(`s))) == head(`s) .
reduce tail(merge(odd(`s:Stream),even(`s))) R tail(`s) .
close

