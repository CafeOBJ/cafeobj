** translated from OTTER 3.0.5 examples/ringx2.in
-- %
-- %  Boolean (xx = x) rings are commutative.
-- %

-- set(auto).

-- list(usable).

-- x = x.

-- % Ring axioms

-- j(0,x) = x.
-- j(g(x),x) = 0.
-- j(j(x,y),z) = j(x,j(y,z)).
-- j(x,y) = j(y,x).
-- f(f(x,y),z) = f(x,f(y,z)).
-- f(x,j(y,z)) = j(f(x,y),f(x,z)).
-- f(j(y,z),x) = j(f(y,x),f(z,x)).

-- f(x,x) = x.        % Hypothesis

-- f(a,b) != f(b,a).  % Denial of conclusion

-- end_of_list.

module! RING
{ [E]
  op 0 : -> E
  op j : E E -> E
  op g : E -> E
  op f : E E -> E
  vars x y z : E
  -- % Ring axioms
  eq j(0,x) = x .
  eq j(g(x),x) = 0 .
  eq j(j(x,y),z) = j(x,j(y,z)) .
  eq j(x,y) = j(y,x) .
  eq f(f(x,y),z) = f(x,f(y,z)).
  eq f(x,j(y,z)) = j(f(x,y),f(x,z)).
  eq f(j(y,z),x) = j(f(y,x),f(z,x)).
  eq f(x,x) = x .        --  Hypothesis
}

open RING .
protecting (FOPL-CLAUSE)
ops a b : -> E .
option reset
flag(auto,on)
flag(universal-symmetry,on)
flag(back-sub,off)
-- flag(very-verbose,on)
goal f(a,b) = f(b,a). 
resolve .
close
--
eof
--
$Id:
