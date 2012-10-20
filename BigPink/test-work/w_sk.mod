** OK
" Combinatory Logic
  Construct W in terms of S and K, s.t.  Wxy = xyy.
"
**

module WSK
{
  [ E ]
  op __ : E E -> E { l-assoc }
  ops S K : -> E
  vars x y z : E
  eq S x y z = (x  z) (y z).
  eq K x y = x .
  goal \E[W:E]\A[x,y] W x y = x y y & ~($Ans(W)) .
}

select WSK
option reset
flag(auto,on)
flag(universal-symmetry,on)
resolve .
**
eof
**
$Id
