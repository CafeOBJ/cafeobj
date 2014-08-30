-- FILE: /home/diacon/LANG/Cafe/prog/tel.mod
-- CONTENTS: behavioural specification of a telephone system featuring
--           dynamic object composition (without synchronization)
-- AUTHOR: Razvan Diaconescu
-- DIFFICULTY: ***

-- we trust system's proof of congruency of =*=
set accept =*= proof on

-- --------------------------------------------------------------
-- telephone number
-- --------------------------------------------------------------
mod! NUMBER {
  protecting(NAT * { sort Nat -> Number })

  [ Number < Number* ]

  op no-tel : -> Number*   -- for errors
}

-- --------------------------------------------------------------
-- duration of calls (unit)
-- --------------------------------------------------------------
mod! UNIT {
  protecting(NAT * { sort Nat -> Unit })

  op no-tel : -> Unit   -- for errors
  eq no-tel = 0 .
}

-- --------------------------------------------------------------
-- telephone (client)
-- --------------------------------------------------------------
mod* TELEPHONE {
  protecting(NUMBER + UNIT)

  *[ Tel ]*

  op no-tel : -> Tel         -- for errors
  op init-tel : Number  -> Tel      -- initial state
  bop call : Unit Tel -> Tel        -- method
  bop clear : Tel -> Tel            -- method
  bop unit : Tel -> Unit            -- attribute
  bop number : Tel -> Number*        -- attribute

  var NUM : Number
  var U : Unit
  var T : Tel

  eq unit(init-tel(NUM)) = 0 .
  eq unit(call(U, T)) = U + unit(T) .
  eq unit(no-tel) = no-tel .
  eq unit(clear(T)) = 0 .

  eq number(init-tel(NUM)) = NUM .
  eq number(call(U, T)) = number(T) .
  eq number(no-tel) = no-tel .
  eq number(clear(T)) = number(T) . 
}

-- --------------------------------------------------------------
-- telephone system (server)
-- --------------------------------------------------------------
mod* TELEPHONE-SYSTEM {
  protecting(TELEPHONE)

  *[ TelSys ]*

  op init-sys : -> TelSys                  -- initial state
  bop tel : Number TelSys -> Tel           -- attribute
  bop add-tel : Number TelSys -> TelSys    -- method
  bop del-tel : Number TelSys -> TelSys    -- method
  bop call : Number Unit TelSys -> TelSys   -- method
  bop pay : Number TelSys -> TelSys        -- method

  vars NUM NUM' : Number
  var U : Unit
  var TS : TelSys

  eq tel(NUM, init-sys) = no-tel .
  ceq tel(NUM, add-tel(NUM', TS)) = init-tel(NUM) if NUM == NUM' . 
  ceq tel(NUM, add-tel(NUM', TS)) = tel(NUM, TS)  if NUM =/= NUM' .
  ceq tel(NUM, del-tel(NUM', TS)) = no-tel if NUM == NUM' .
  ceq tel(NUM, del-tel(NUM', TS)) = tel(NUM, TS)  if NUM =/= NUM' .
  ceq tel(NUM, call(NUM', U, TS)) = call(U, tel(NUM, TS)) if NUM == NUM' .
  ceq tel(NUM, call(NUM', U, TS)) = tel(NUM, TS)          if NUM =/= NUM' .
  ceq tel(NUM, pay(NUM', TS)) = tel(NUM, TS)        if NUM =/= NUM' .
  ceq tel(NUM, pay(NUM', TS)) = clear(tel(NUM, TS)) if NUM == NUM' .
}

--> define the  coinduction relation on TelSys by
mod COINDUCTION-REL {
  protecting(TELEPHONE-SYSTEM)

  op _R[_]_ : TelSys Number TelSys -> Bool {coherent}

  vars T1 T2 : TelSys 
  var N : Number 
    
  eq T1 R[N] T2 = tel(N, T1) =*= tel(N, T2) .
}

-- ---------------------------------------------------------------------
-- proof of true concurrency of phone calls
-- call(n1, u1, call(n2, u2, telsys)) R call(n2, u2, call(n1, u1, telsys))
-- ---------------------------------------------------------------------
open COINDUCTION-REL .
  op telsys :  -> TelSys .
  ops n n1 n2 :  -> Number .
  ops u1 u2  :  -> Unit .
-- n =/= n1, n =/= n2
red call(n1, u1, call(n2, u2, telsys)) R[n]
    call(n2, u2, call(n1, u1, telsys)) .
-- n = n1 or n = n2
red call(n1, u1, call(n2, u2, telsys)) R[n1]
    call(n2, u2, call(n1, u1, telsys)) .
close
--
eof
--
$Id: tel.mod,v 1.2 2010-07-30 04:20:09 sawada Exp $
