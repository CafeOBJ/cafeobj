** translated from otter3.0.5 examples/auto/z11.in
-- % If a group has relations ab=c, bc=d, cd=h, dh=a, ha=b, it is
-- % cyclic with order 11.  The following input will not cause a proof,
-- % but the result follows easily from examination of the lists near the
-- % end of the output.
--

module Z11 (E :: TRIV)
{
  op e : -> Elt
  ops a b c d : -> Elt
  op f : Elt Elt -> Elt
  op g : Elt -> Elt
  op h : -> Elt
  
  vars x y z : Elt

  eq f(e,x) = x .
  eq f(g(x),x) = e .
  eq f(f(x,y),z) = f(x,f(y,z)) .

  eq f(a,b) = c .
  eq f(b,c) = d .
  eq f(c,d) = h .
  eq f(d,h) = a .
  eq f(h,a) = b .
}

open Z11  .
protecting (FOPL-CLAUSE)
option reset
flag(auto,on)
flag(universal-symmetry,on)

resolve .
close
--
eof
--
$Id
