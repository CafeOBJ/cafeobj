** translated from Otter 3.05 examples/misc/andrews.in
-- %  Challenge problem from Peter Andrews (1979)
-- %
-- %  Although this problem is more easily solved by direct simplification
-- %  of the quantified formula (Champeaux, J. ACM 1986 and SIGART Newsletter), 
-- %  it makes a good test problem for resolution theorem provers.  Otter
-- %  can do this problem, because it translates equivalences in two ways,
-- %  depending on the context, producing only 128 clauses.  (Also, FormEd
-- %  can prove it by direct simplification.)
-- %

module ANDREWS
{
  [ E ]
  pred p : E 
  pred q : E
}

open ANDREWS .
protecting (FOPL-CLAUSE)

let goal = ~( (( (\E[x:E] \A[y:E] (p (x) <-> p(y)))
		 <-> ( (\E[u:E] q(u)) <-> (\A[v:E] p(v)))))
	      <->
	      ((\E[w:E]\A[z:E] (q(z) <-> q(w)))
		<->
		  ((\E[x1:E] p(x1)) <-> (\A[x2:E] q(x2))))
	      ).
option reset
db reset
flag(binary-res,on)
flag(process-input,on)
flag(print-kept,off)
flag(print-back-sub,off)
param(stats-level,4)
sos = { goal }

resolve .
close
--
eof
--
$Id:
