** -*- Mode:CafeOBJ -*-
**> was: ~diacon/OBJ/prog/PosFLOAT.obj
**> was: ~goguen/osa/PosFLOAT.obj
**> was: ~hanyan/PosFLOAT.obj
**> and adopted to CafeOBJ

** evq (load "/home/sawada/prj/cafe/Chaos/exs-old/PosFLOAT.lisp")
evq (load "/Users/sawada/prj/cafe/Chaos/exs-old/PosFLOAT.lisp")

module! PosFLOAT {
  bsort PosFloat
    (obj_PosFLOAT$is_PosFloat_token obj_PosFLOAT$create_PosFloat
       obj_PosFLOAT$print_PosFloat obj_PosFLOAT$is_PosFloat) 
  protecting (BOOL)
}

module! ANGLE {
 bsort Angle
   (obj_ANGLE$is_Angle_token obj_ANGLE$create_Angle
      obj_ANGLE$print_Angle obj_ANGLE$is_ANGLE) 
 protecting (BOOL)
}

module! FLOAT2 {
  imports {
    protecting (FLOAT-VALUE)
    protecting (PosFLOAT)
    protecting (ANGLE)
  }

  signature {
    [ Angle < PosFloat < Float ]

    op -_ : Float -> Float {prec 15} 
    op _+_ : Float Float -> Float {assoc comm prec 33}
    op _-_ : Float Float -> Float {l-assoc prec 33}
    op _*_ : Float Float -> Float {assoc comm prec 31}
    op _/_ : Float Float -> Float {l-assoc prec 31}
    op _rem_ : Float Float -> Float {l-assoc prec 31}
    op exp : Float -> Float 
    op log : Float -> Float 
    op sqrt : Float -> Float
    op abs : Float -> Float 
    op sin : Float -> Float 
    op cos : Float -> Float 
    op atan : Float -> Float
    op pi : -> Float
    op _<_ : Float Float -> Bool {prec 51}
    op _<=_ : Float Float -> Bool {prec 51}
    op _>_ : Float Float -> Bool {prec 51}
    op _>=_ : Float Float -> Bool {prec 51}
    op _=[_]_ : Float Float Float -> Bool {prec 51}
  }
  axioms {
    vars X Y Z : Float 

    eq X + Y = #! (+ X Y) .
    eq - X = #! (- X) .
    eq X - Y = #! (- X Y) .
    eq X * Y = #! (* X Y) .
    eq X / Y = #! (/ X Y) .
    eq X rem Y = #! (rem X Y) .
    eq exp(X) = #! (exp X) .
    eq log(X) = #! (log X) .
    eq sqrt(X) = #! (sqrt X) . 
    eq abs(X) = #! (abs X) .
    eq sin(X) = #! (sin X) .
    eq cos(X) = #! (cos X) .
    eq atan(X) = #! (atan X) .
    eq pi = #! pi .
    eq X < Y = #! (< X Y) .
    eq X <= Y = #! (<= X Y) .
    eq X > Y = #! (> X Y) .
    eq X >= Y = #! (>= X Y) .
    eq (X =[ Z ] Y) = #! (< (abs (- X Y)) Z) .
  }
  op angle_ : Float -> Angle
  eq angle(X) = if X <= 0 then angle(X + 2 * pi)
     else if X > 2 * pi then angle(X - 2 * pi)
     else X
     fi
     fi .
}

provide PosFLOAT
--
eof
** 
$Id: PosFLOAT.mod,v 1.2 2010-07-29 07:45:27 sawada Exp $
