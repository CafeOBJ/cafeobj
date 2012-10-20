mod SIMPLE-CLOCK {
  pr(INT)
  [ Clock ]
  op clock : Int -> Clock { constr }
  var T : Int 
  trans clock(T) => clock((T + 1) rem 24) .
}

** eof
**
red in SIMPLE-CLOCK : clock(0) ==>* clock(T) suchThat (T < 0 or T >= 24) .
