** -*- Mode:CafeOBJ -*-
**> various examples of order-sortedness.
**> orignal file: ~diacon/OBJ/prog/osa.obj
--> adapted to CafeOBJ syntax and semantics.
--> 

module! STACK {
  protecting (NAT)
  signature {
    [ NeStack < Stack ]
    op empty : -> Stack 
    op push : Nat Stack -> NeStack 
    op top_ : NeStack -> Nat 
    op pop_ : NeStack -> Stack 
  }
  axioms {
    var N : Nat  var S : Stack 
    -- ----------------
    eq top push(N,S) = N .
    eq pop push(N,S) = S .
  }
}

select STACK
red top push(2,push(1,push(0,empty))) .
red top pop push(2,push(1,push(0,empty))) .
red top pop pop push(2,push(1,push(0,empty))) .
red top pop pop pop push(2,push(1,push(0,empty))) .

module! PNAT {
  signature {
    [ Pos < Nat ]
    op 0 : -> Nat 
    op s_ : Nat -> Pos 
    op _-_ : Nat Nat -> Nat 
  }
  axioms {
    vars N M : Nat 
    eq [e1]: N - 0 = N .
    eq [e2]: 0 - N = 0 .
    eq [e3]: N - N = 0 .
    eq [e4]: (s N) - N = s 0 .
    eq [e5]: (s N) - (s M) = N - M .
  }
}

module! ANTIMI {
 extending (PNAT)
 signature {
  op f_ : Nat -> Nat
  op f_ : Pos -> Nat 
 }
 axioms {
  var P : Pos 
  eq [e6]: f P = P .
  eq [e7]: f 0 = s f 0 .
 }
}

select ANTIMI
start s f 0 - f 0 .
show term 
apply -.e7 within term 
apply .e3 at term 
**> should be: 0

start s f 0 - f 0 .
apply .e4 at term 
**> should be: s 0
**> therefore 0 = 1 .

module! BSTACK {
  protecting (NAT)
  [ NeStack < Stack ]
  op empty : -> Stack 
  op bound : -> Nat 
  eq bound = 3 .

  op push : Nat Stack -> Stack
  op length_ : Stack -> Nat 

  var N : Nat   var S : Stack
  eq length empty = 0 .
  eq length push(N,S) = 1 + length S . 

  -- op-as push : Nat Stack -> NeStack for push(N,S) if length(S) < bound .
  op push : Nat Stack -> NeStack
  op top_ : NeStack -> Nat 
  op pop_ : NeStack -> Stack 
  eq top push(N,S) = N .
  eq pop push(N,S) = S .
}

open BSTACK
eq length push(N,S) = 1 + length S .

red length(empty) .
red length(push(0,empty)) < bound .
red length(push(1,push(0,empty))) < bound .
red top(push(1,push(0,empty))) .
red top(push(2,push(1,push(0,empty)))) .
red length(push(2,push(1,push(0,empty)))) < bound .
**> the sort constraint is NOT satisfied in the following:
red top(push(3,push(2,push(1,push(0,empty))))) .
close 

** should try it with these:
** op overflow : -> Stack
** cq push(N,S) = overflow if length(S) >= bound .

module! FACT {
  protecting (RAT)
  op _! : Nat -> Nat 
  eq 0 ! = 1 .
  var N : Nat 
  cq N ! = N *((N - 1)!) if N > 0 .
  var X : NzRat 
  ceq X ! = (X - X rem 1)! if X > 0 .
}

-- select FACT
-- red (22 / 7)! .
-- red (- 22 / 7)! .
-- red (- 22 / - 7)! .

**> points in Cartesian and Polar coordinates
**  this requires OBJ3 Version 2 and
**  PosFLOAT with builtin subsorts Angle < PosFloat < Float

-- in /users/diacon/OBJ/prog/PosFLOAT
require PosFLOAT

** notation for squaring
module! SQ {
 protecting (FLOAT2)
 var F : Float 
 op _**2 : Float -> Float {prec 2}
 eq F **2 = F * F .
}

** points and operations on points
module! POINT {
  protecting (SQ)
  [ Cart Polar < Point,
    NzPolar Origin < Polar ]

  op <_,_> : Float Float -> Cart {constr}

  op [_,_] : PosFloat Float -> Polar {strat:(1 2 0)}
  op [_,_] : PosFloat Angle -> NzPolar {constr}
  op origin : -> Origin {constr}
  var PF : PosFloat
  var F1 : Float
  cq [ PF, F1 ] = [ PF, angle(F1 + 2 * pi) ] if (F1 <= 0) or (F1 > 2 * pi) .

  op Cart_ : Polar -> Cart
  op Polar_ : Cart -> Polar

  vars X Y : Float
  var Rh : PosFloat
  var Th : Angle 

  cq Polar < X, Y > = [sqrt(X **2 + Y **2),atan(Y / X)] if X > 0 .
  cq Polar < X, Y > = [sqrt(X **2 + Y **2),pi + atan(Y / X)] if X < 0 .
  cq Polar < 0, Y > = [ Y, pi / 2 ] if Y > 0 .
  cq Polar < 0, Y > = [ - Y, (3 * pi) / 2 ] if Y < 0 .
  eq Polar < 0, 0 > = origin .
  eq Cart [ Rh, Th ] = < Rh * cos(Th), Rh * sin(Th) > .
  eq Cart origin = < 0, 0 > .

  op rho_ : Point -> Float
  op rho_ : Polar -> Float {strat:(1 0)}
  op theta_ : Point -> Angle
  op theta_ : NzPolar -> Angle {strat:(1 0)}

  eq rho [ Rh, Th ] = Rh .
  eq theta [ Rh, Th ] = Th .
  eq rho(origin) = 0 .
  vars Xc : Cart
  eq rho Xc = rho(Polar Xc) .
  eq theta Xc = theta(Polar Xc) .

  op x_ : Point -> Float
  op x_ : Cart -> Float 

  op y_ : Point -> Float
  op y_ : Cart -> Float

  vars Xp Yp : Polar
  eq x < X, Y > = X .
  eq y < X, Y > = Y .
  eq x Xp = x(Cart Xp) .
  eq y Yp = y(Cart Yp) .

  op d : Point Point -> Float
  op d : Cart Cart -> Float 

  op _+_ : Point Point -> Point 
  op _+_ : Cart Cart -> Cart 

  vars X1 Y1 X2 Y2 : Float 
  eq d(< X1, Y1 >, < X2, Y2 >) = sqrt((X2 - X1)**2 + (Y2 - Y1)**2).
  eq < X1, Y1 > + < X2, Y2 > = < X1 + X2, Y1 + Y2 > .
  eq Xp + Yp = (Cart Xp) + (Cart Yp) .
  eq d(Xp, Yp) = d(Cart Xp, Cart Yp) .
}

module! TEST {
  protecting (POINT)
  ops p1 p2 p3 : -> Polar 
  eq p1 = [ 1, pi ] .
  eq p2 = [ 2, - pi ] .
  eq p3 = [ 1, - pi ] .
}

select TEST
red x p1 .
red y p1 .
red d(p1, p2) .
red p1 + p2 .
red rho (p1 + p2) .
red theta(p1 + p2) .
red d(p1, p3) .
red p1 + p3 .
red rho (p1 + p3) .
red theta (p1 + p3) .

module! SCALARM {
  protecting (TEST)
  op _*_ : Float Polar -> Polar
  op _*_ : Float Cart -> Cart 

  vars F X Y : Float   var Rh : PosFloat   var Th : Angle 
  eq F * < X, Y > = < F * X, F * Y > .
  cq F * [ Rh, Th ] = [ F * Rh, Th ] if F > 0 .
  cq F * [ Rh, Th ] = [ - F * Rh, pi + Th ] if F < 0 .
  eq 0 * [ Rh, Th ] = origin .
  eq F * origin = origin .
}

select SCALARM
red 2 * origin .
red 2 * Cart origin .
red 2 * p1 .
red 2 * (p1 + p2) .

-- EOF
eof
**
$Id: osa.mod,v 1.1.1.1 2003-06-19 08:30:17 sawada Exp $
--
