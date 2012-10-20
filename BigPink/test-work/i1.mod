** translated from otter 3.0.5 examples/misc/i1.in
-- % From John Kalman:
-- % 
-- %      (1) The input file %i1 below. This is Example 4.27 on page 83
-- % of my latest notes. It illustrates that looping is possible when
-- % for_sub is clear, and would be possible if backward subsumption were done
-- % before forward subsumption.

-- set(hyper_res).
-- clear(for_sub).                 % switch off forward subsumption
-- set(print_lists_at_end).
-- assign(max_given,15).           % stop after 15 given clauses
-- assign(stats_level,1).  % changed from 0 to 1 by McCune

-- list(usable).
--   -P(x) | P(x).
-- end_of_list.

-- list(sos).
--   P(a).
-- end_of_list.

module I1
{ 
  protecting (FOPL-CLAUSE)
  [ E ]
  pred P : E
  ax ~ P(X:E) | P (X) .
}

option reset
flag(simplify-fol,off)
flag(hyper-res,on)
flag(for-sub,off)
param(max-given,15)

open I1 .
op a : -> E .
let ax1 = P(a) .
db reset
sos = { ax1 }
resolve .
close
** 
eof
**
$Id:
