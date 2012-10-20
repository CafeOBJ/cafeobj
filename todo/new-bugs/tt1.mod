mod TEST {
  [ Test ]
  ops t1 t2 : -> Test
  trans [t1]: t1 => t2 .
}

open TEST
 red t1 =(2,1)=>* (T:Test) .
 op init : -> Test .
 eq init = t1 .
 red init =(2,1)=>* (T:Test) .
close
