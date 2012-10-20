**>
**> Paramodulation の検査
**>
--  Robbins algebra
-- 
--  If a Robbins algebra has an element c such that x+c=c,
--  then it is Boolean.
-- 
--  Commutativity, associativity, and Huntington's axiom 
--  axiomatize Boolean algebra.

module! ROBBINS (E :: TRIV)
{
  op _+_ : Elt Elt -> Elt { r-assoc }
  op n : Elt -> Elt
  vars x y z : Elt
  eq x + y = y + x .
  eq (x + y) + z = x + (y + z) .
  eq  n(n(x + y) + n(x + n(y))) = x . -- Robbins axiom
}

**> オプションの初期化
option reset

**> auto モードで実行
flag(auto,on)
flag(universal-symmetry, on)

open ROBBINS
protecting (FOPL-CLAUSE)

ops A B C : -> Elt .

**> 仮定 --- exists a 1
--> eq x + C = C .
eq x + C = C .

**> 証明したい文
--> goal n(A + n(B)) + n(n(A) + n(B)) = B .
goal n(A + n(B)) + n(n(A) + n(B)) = B .

**> 反駁エンジンを起動
resolve .
close
** 
eof

