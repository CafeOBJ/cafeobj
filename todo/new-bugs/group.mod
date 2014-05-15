--
** very interesting examples using _:is_.
-- originally written by A.T.Nakagawa (nakagawa@sra.co.jp)
--
module* GROUP {
  [ G ]
  op 0 : -> G
  op _+_ : G G -> G { assoc }
  op -_ : G -> G
  var X : G
  eq [r-id]: X + 0 = X .
  eq [r-inv]: X + (- X) = 0 .
}

**> Theorem 1 (left inverse): (- g) + g = 0
open GROUP .
op g : -> G .
start - g + g == 0 .
apply -.r-id at (1 2) .
apply -.r-inv with X = - g at [3] of (1) .
apply reduce at term .
close
**

**> Theorem 2 (left identity) : 0 + g = g
open GROUP .
op g : -> G .
var U : G
eq [l-inv]: (- U) + U = 0 . ** by Theorem 1
start 0 + g == g .
apply -.r-inv with X = g at (1 1) .
apply +.l-inv within (1) .
apply reduce at term .
close

**> Theorem 3 (uniqueness): g' = - g if g' + g = 0
open GROUP .
op g : -> G .
op g' : -> G .
var U : G
eq [l-id]: 0 + U = U . ** by Theorem 2
eq [hypo]: g' + g = 0 . ** hypothesis
start g' == - g .
apply -.r-id at (1) .
apply -.r-inv with X = g at (1 2) .
apply reduce at term .
close
**

**> Theorem 4 (uniqueness): g = 0 if g + g' = g' (for all g')
open GROUP .
op g : -> G .
var U : G
eq [hypo] : g + U = U . ** hypothesis
eq [l-inv] : U + (- U) = 0 . ** by Theorem 1
start g == 0 .
apply -.r-id at (1) .
apply -.r-inv with X = g at (1 2) .
apply +.hypo at [1 .. 2] of (1) .
apply +.r-inv within term .
apply reduce at term .
close
**

**> Theorem 5: - (x + y) = - y + - x
open GROUP .
ops x y : -> G .
vars U V : G
eq - U == V = U + V == 0 . ** by Theorem 3
reduce - (x + y) == - y + - x .
close
**

module* A-GROUP {
  [ G ]
  op 0 : -> G
  op _+_ : G G -> G { assoc comm }
  op -_ : G -> G
  var X : G
  eq [r-id]: X + 0 = X .
  eq [r-inv]: X + (- X) = 0 .
}

module* G-HOM {
  protecting (GROUP * { sort G -> H })
  protecting (GROUP)
  op _h : H -> G
  vars U V : H
  eq [hom] : (U + V) h = (U h) + (V h) .
}

**> Theorem 6 (preserve neutral): 0 h = 0
open G-HOM .
start 0 h == 0 .
apply -GROUP.r-id at (1) .
apply -GROUP.r-inv with X = (0 h) at (1 2) .
apply -.hom at [1 .. 2] of (1) .
apply reduce at term .
close
**

**> Theorem 7 (preserve inverse): (- g) h = - (g h)
open G-HOM .
op g : -> H .
vars U V : H
eq [l-inv-H] : (- U) + U = 0 . ** by Theorem 1
vars P Q : G
eq [hom-0]: 0 h = 0 . ** by Theorem 6
eq [l-inv-G]: (- P) + P = 0 . ** by Theorem 1
eq [l-id-G]: 0 + P = 0 . ** by Theorem 2
ceq [!inv]: P == - Q = true if P + Q == 0 . ** by Theorem 2
start (- g) h == - (g h) .
apply +.!inv at term .
apply -GROUP.r-id at (1) of (1) .
apply -GROUP.r-inv with X = (g h) within (1) .
apply -.hom at [1 .. 2] of (1) .
apply reduce at term .
close
**

module* SUBGROUP {
  protecting (GROUP)
  [ H < G ]
  vars U V : G
  eq [sub-0]: 0 :is H = true .
  ceq [sub-+]: U + V :is H = true if (U :is H) and (V :is H) .
  ceq [sub--]: - U :is H = true if U :is H .
}

module* NORMAL {
  using (SUBGROUP * { sort H -> N })
  var U : N
  var V : G
  eq [normal]: (- V) + U + V :is N = true .
}

module* KERNEL {
  protecting (G-HOM)
  [ K < H ]
  var U : H
  eq [kernel]: U :is K = U h == 0 .
}

module* IMAGE {
  protecting (G-HOM)
  [ I < G ]
  var U : G
  var V : H
  eq [image]: U :is I = V h == U .
}

**> Theorem 8: the kernel is a normal subgroup
** view K-is-N from KERNEL to NORMAL {
**   sort K -> H,
**   sort H -> G,
**   op _+_ -> _+_
** }

**> 8.1: the kernel is a subgroup
**> 8.1.1: the kernel contains zero
open KERNEL .
eq [hom-0]: 0 h = 0 . ** by Theorem 6
reduce 0 :is K .
close
**

**> 8.1.2: the kernel is closed under application
open KERNEL .
ops k k' : -> H .
eq [hom-0]: 0 h = 0 . ** by Theorem 6
eq [hypo-1]: k h = 0 . ** hypothesis
eq [hypo-2]: k' h = 0 . ** ditto
reduce k + k' :is K .
close
**

**> 8.1.3: the kernel is closed under inverse
open KERNEL .
op k : -> H .
var U : H
eq [hom-inv]: (- U) h = - (U h) . ** by Theorem 7
eq - (0):G = (0):G . ** from 0 + 0 = 0 and Theorem 3
eq [hypo]: k h = 0 . ** hypothesis
reduce - k :is K .
close
**

**> 8.2: the kernel is normal
open KERNEL .
op u : -> H .
op k : -> H .
var V : H
eq [l-inv]: - V + V = 0 . ** by Theorem 1
eq [hom-0]: 0 h = 0 . ** by Theorem 6
eq [hypo]: k h = 0 . ** hypothesis
start (- u) + k + u :is K .
apply +.kernel at term .
apply +G-HOM.hom within term .
apply +G-HOM.hom within term .
apply +.hypo within term .
apply +GROUP.r-id at [1 .. 2] of (1) .
apply -G-HOM.hom within term .
apply +.l-inv within term .
apply reduce at term .
close

**> Theorem 9: the image is a subgroup
** view I-is-S from IMAGE to SUBGROUP {
**   sort I -> H,
**   sort G -> G
** }

**> 9.1: the image contains zero
open IMAGE .
eq [hom-0]: 0 h = 0 . ** by Theorem 6
-- start dirty work
-- op x : -> H .
-- eq x = 0 .
-- end dirty work
start 0 :is I .
apply +.image with V = (0):H at term .
-- currently (0):H does not work, hence the dirty work
apply reduce at term .
close
**

**> 9.2: the image is closed under _+_
open IMAGE .
ops i i' : -> G .
ops v v' : -> H .
eq [hypo-1]: v h = i . ** hypothesis
eq [hypo-2]: v' h = i' . ** hypothesis
start i + i' :is I .
apply +.image with V = v + v' at term .
apply reduce at term .
close
**

**> 9.3: the image is closed under inverse
open IMAGE .
op i : -> G .
op v : -> H .
eq [hom-inv]: (- V) h = - (V h) . ** by Theorem 7
eq [hypo]: v h = i . ** hypothesis
start - i :is I .
apply +.image with V = - v at term .
apply reduce at term .
close
**

module* QUOTIENT {
  protecting (NORMAL)
  *[ Q ]*
  op n : -> Q
  bop _+_ : G Q -> Q
  bop _in_ : G Q -> Bool
  op _+_ : Q Q -> Q { coherent }
  op -_ : Q -> Q { coherent }
  vars X Y : G
  vars U V : Q
  eq [cos-1]: X in n = X :is N .
  eq [cos-2]: X in (Y + U) = (X + - Y) in U .
  beq [cos-3]: X + (Y + n) = (X + Y) + n .
  beq [quo-+]: (X + n) + (Y + n) = (X + Y) + n .
  beq [quo--]: - (X + n) = (- X) + n .
  --
  op _=#=_ : Q Q -> Bool { coherent }
  eq [cos-=] : U =#= V = (X in U) == (X in V) .
}

**> Theorem 10: x + n =#= n if x :is N
open QUOTIENT .
op x : -> G .
ops a b : -> G .
eq - 0 = 0 . ** from 0 + 0 = 0 and Theorem 3
eq a :is N = false . ** spliting
eq b :is N = true .  ** cases
eq x :is N = true .
start x + n =#= n .
apply +.cos-= with X = a at term .
apply +.cos-2 within term .
apply reduce at term .

**> Theorem 10: the quotient is a group

**> 10.0: _+_ is well-defined: (x + n) + (y + n) =#= (x + n) + (y' + n)
**>    if y + n =#= y' + n, similarly for the 1st argument
open QUOTIENT .
ops x y y' : -> G .
op a : -> G .
eq [hypo] : y + n =#= y' + n = true .
start (x + n) + (y + n) =#= (x + n) + (y' + n) .
apply +.quo-+ within term .
apply -.cos-3 within term .
apply +.cos-= with X = a at term .
apply +.cos-2 within term .
apply -.cos-= within term .
apply +.hypo at term .
close
open QUOTIENT .
ops x x' y : -> G .
op a : -> G .
vars X Y : G
eq [2inv] : - (X + Y) = - Y + - X . ** by Theorem 5
eq [hypo] : x + n =#= x' + n = true .
start (x + n) + (y + n) =#= (x' + n) + (y + n) .
apply +.quo-+ within term .
apply +.cos-= with X = a at term .
apply +.cos-2 within term .
apply +.2inv within term .
apply -.cos-2 within term .
apply -.cos-= within term .
apply +.hypo at term .
close

**> 10.1: _+_ is associative
open QUOTIENT .
ops x y z : -> G .
ops a b : -> G .
eq a + - (x + y + z) :is N = true .  ** splitting
eq b + - (x + y + z) :is N = false . ** cases
start (x + n) + ((y + n) + (z + n)) =#= ((x + n) + (y + n)) + (z + n) .
apply +.cos-= with X = a at term .
apply reduce at term .
start (x + n) + ((y + n) + (z + n)) =#= ((x + n) + (y + n)) + (z + n) .
apply +.cos-= with X = b at term .
apply reduce at term .
close
**

**> 10.2.0 lemma: 0 + n =#= n
open QUOTIENT .
op x : -> G .
ops a b : -> G .
eq - 0 = 0 . ** from 0 + 0 = 0 and Theorem 3
eq a :is N = false . ** spliting
eq b :is N = true .  ** cases
start 0 + n =#= n .
apply +.cos-= with X = a at term .
apply +.cos-2 within term .
apply reduce at (1 1) .
apply reduce at term .
start 0 + n =#= n .
apply +.cos-= with X = b at term .
apply +.cos-2 within term .
apply reduce at (1 1) .
apply reduce at term .
close
**


**> 10.2: n is neutral
open QUOTIENT .
op x : -> G .
ops a b : -> G .
eq a + - x :is N = true .  ** splitting
eq b + - x :is N = false . ** cases
beq [lema]: 0 + n = n . ** by the lemma
start (x + n) + n =#= (x + n) .
apply -.lema at (1 2) .
apply +.quo-+ at (1) .
apply +.cos-= with X = a at term .
apply reduce at term .
start (x + n) + n =#= (x + n) .
apply -.lema at (1 2) .
apply +.quo-+ at (1) .
apply +.cos-= with X = b at term .
apply reduce at term .
close
**

**> 10.3: -_ is the inverse
open QUOTIENT .
op x : -> G .
ops a b : -> G .
beq [lema]: 0 + n = n . ** by 10.2.0
eq a :is N = true .
eq b :is N = false .
start (x + n) + - (x + n) =#= n .
apply +.quo-- within term .
apply +.quo-+ within term .
apply reduce at (1 1) .
apply +.cos-= with X = a at term .
apply reduce at term .
start (x + n) + - (x + n) =#= n .
apply +.quo-- within term .
apply +.quo-+ within term .
apply reduce at (1 1) .
apply +.cos-= with X = b at term .
apply reduce at term .
close
**

module* Q-MAP {
  protecting (QUOTIENT)
  op _q : G -> Q
  var X : G
  eq X q = X + n .
}

**> Theorem 10: G -> G/N is a homomorphism
open Q-MAP .
ops x y : -> G .
ops a b : -> G .
eq a + - (x + y) :is N = true .
eq b + - (x + y) :is N = false .
start (x + y) q =#= x q + y q .
apply +QUOTIENT.cos-= with X = a at term .
apply reduce at term .
start (x + y) q =#= x q + y q .
apply +QUOTIENT.cos-= with X = b at term .
apply reduce at term .
close
**

module* ISO-1 {
  protecting (KERNEL)
  protecting (IMAGE)
  *[ Q ]*
  op n : -> Q
  bop _+_ : H Q -> Q
  bop _in_ : H Q -> Bool
  op _+_ : Q Q -> Q { coherent }
  op -_ : Q -> Q { coherent }
  vars X Y : H
  vars U V : Q
  eq [cos-1]: X in n = X :is K .
  eq [cos-2]: X in (Y + U) = (X + - Y) in U .
  beq [cos-3]: X + (Y + n) = (X + Y) + n .
  beq [quo-+]: (X + n) + (Y + n) = (X + Y) + n .
  beq [quo--]: - (X + n) = (- X) + n .
  --
  op _=#=_ : Q Q -> Bool { comm coherent }
  eq [cos-=]: U =#= V = (X in U) == (X in V) .
  --
  op iso : Q -> G -- should be I but syntactically has to be G
  eq [iso-1]: iso(n) = 0 .
  eq [iso-2]: iso(X + n) = X h .
}

** !!!!!

**> Theorem 11: iso is indeed iso
**> 11.1: iso is well-defined: iso(x + n) = iso(x' + n) if x + n =#= x' + n
open ISO-1 .
ops x x' : -> H .
vars P Q : G
ceq [!inv]: P == Q = true if P + - Q == 0 . ** by Theorem 2 and x = - - x
eq [hypo]: x + n =#= x' + n = true .
ceq [coll]: X in U = X in V if U =#= V . ** from cos-=
eq [hom-0]: 0 h == 0 = true . ** by Theorem 6
eq [hom-inv]: - (X h) = (- X) h . ** by Theorem 7
start iso(x + n) == iso(x' + n) .
apply +.iso-2 within term .
apply +.!inv at term .
apply +.hom-inv within term .
apply -G-HOM.hom within term .
apply -KERNEL.kernel at term .
apply -.cos-1 at term .
apply -.cos-2 at term .
apply +.coll with V = x + n at term .
apply +.hypo at term .
apply +.cos-2 at term .
apply reduce at (1) .
apply +.cos-1 at term .
apply +KERNEL.kernel at term .
apply +.hom-0 at term .
close
**

**> 11.2: iso is a homomorphism
open ISO-1 .
ops x x' : -> H .
reduce iso(x + n) + iso(x' + n) == iso((x + n) + (x' + n)) .
close
**

**> 11.3: iso is surjective
open ISO-1 .
op g : -> G .
op x : -> H .
eq g :is I = true .
start iso(x + n) == g  .
apply +.iso-2 within term .
apply -IMAGE.image at term .
apply reduce at term .
close
**

**> 11.4: iso is injective: x + n =#= x' + n if iso(x + n) = iso(x' + n)
open ISO-1 .
ops x x' : -> H .
eq [hypo]: iso(x + n) = iso(x' + n) .
start x + n =#= x' + n .
apply +.cos-= with X = x at term .
apply +.cos-2 within term .
apply reduce at (1 1) .

close
**
eof
