-- To: sawada@sra.co.jp, ishisone@sra.co.jp
-- cc: kokichi@jaist.ac.jp, diacon@jaist.ac.jp, s_iida@jaist.ac.jp
-- Subject: CafeOBJ BOOL
-- Date: Mon, 11 May 1998 02:21:35 JST
-- From: Shusaku Iida <s_iida@jaist.ac.jp>
-- Content-Type: text
-- Content-Length: 11008

-- Dear Sawada-san and Ishisone-san,

-- I found strange reduction related to BOOL module in
-- CafeOBJ ver.1.4.1(p5). I attached the spec I used at
-- the end of this email.

-- First problem is that the system outputs the following warning:

-- --------------------------------------------------------------------
-- [Warning]: Ambiguous term:
-- * Please select a term from the followings:
-- [1] _==_ : _ Cosmos _ _ Cosmos _ -> Bool ----------------------
--                _==_:Bool          
--          /                 \      
--     status_:Value      ready:Value
--          |                        
-- chopstick1:ChopStick1             
--           |                        
--        T:Table                    
--                                    
-- [2] _==_ : _ Cosmos _ _ Cosmos _ -> Bool ----------------------
--                _==_:Bool          
--          /                 \      
--     status_:Value      ready:Value
--          |                        
-- chopstick1:ChopStick1             
--           |                        
--       T:Table                    
                                   
-- [3] _==_ : _ Cosmos _ _ Cosmos _ -> Bool ----------------------
--                _==_:Bool          
--           /                 \      
--     status_:Value      ready:Value
--           |                        
-- chopstick1:ChopStick1             
--           |                        
--        T:Table                    
-- --------------------------------------------------------------------
-- I cannot find any differece among these three cases.

-- Second, I tried following reduction:
-- --------------------------------------------------------------------
-- TABLE> red status(right-hand(guest1(pick1r(pick1l(init-table))))) .
-- --------------------------------------------------------------------

-- And the trace of this reduction is:
-- --------------------------------------------------------------------
-- -- reduce in TABLE : status right-hand(guest1(pick1r(pick1l(init-table)
--     )))
-- 1>[1] apply trial #1
-- -- rule: ceq guest1(pick1r(T:Table)) = guest1(T:Table) if status 
--       chopstick1(T:Table) =/= ready
--     { T:Table |-> pick1l(init-table) }
-- 2>[1] rule: eq chopstick1(pick1l(T:Table)) = chopstick1(T:Table)
--     { T:Table |-> init-table }
-- 2<[1] chopstick1(pick1l(init-table)) --> chopstick1(init-table)
-- 2>[2] rule: eq chopstick1(init-table) = init-cs1
--     {}
-- 2<[2] chopstick1(init-table) --> init-cs1
-- 2>[3] rule: eq status init-cs1 = ready
--     {}
-- 2<[3] status init-cs1 --> ready
-- 2>[4] rule: eq CXU =/= CYU = #!! (coerce-to-bool
--                                      (not
--                                       (term-equational-equal cxu cyu)))
--     { CXU |-> ready, CYU |-> ready }
-- 2<[4] ready =/= ready --> true
-- ...
-- --------------------------------------------------------------------
-- It is really strage that the sytem said "ready =/= ready --> true".
-- I also tried brute but it claims me:

-- --------------------------------------------------------------------
-- [Error] error occured while reduction in comiled code...
-- error no valid parse for operator _==_.
-- error no valid parse for operator _=/=_.
-- error no valid parse for operator _==_.
-- error no valid parse for operator _=/=_.
-- error no valid parse for operator _==_.
-- error no valid parse for operator _=/=_.
-- error no valid parse for operator _==_.
-- error no valid parse for operator _=/=_.
-- ...
-- --------------------------------------------------------------------

-- In my spec I didn't modify the module BOOL, so it seems me the
-- problems is in the system.

-- Best regards,
-- ----
-- Shusaku Iida (s_iida@jaist.ac.jp)


set auto context on .

-- -------------------------------------------------------------
-- Values of SWITCH
-- -------------------------------------------------------------
mod! ON-OFF {
  [ Value ]
  ops on off : -> Value
}

-- -------------------------------------------------------------
-- SWITCH
-- -------------------------------------------------------------
mod* SWITCH {
  protecting(ON-OFF)

  *[ Switch ]*

  op init-sw : -> Switch         -- initial state
  bop on_ : Switch -> Switch     -- method
  bop off_ : Switch -> Switch    -- method
  bop status_ : Switch -> Value  -- attribute

  var S : Switch

  eq status(init-sw) = off .
  eq status(on(S)) = on .
  eq status(off(S)) = off .
}

mod* RIGHT-HAND {
  protecting(SWITCH *{ hsort Switch -> RightHand,
                       op init-sw -> init-rh,
                       bop on_ -> pick_,
                       bop off_ -> release_,
                       op on -> filled,
                       op off -> empty })
}

mod* LEFT-HAND {
  protecting(SWITCH *{ hsort Switch -> LeftHand,
                       op init-sw -> init-lh,
                       bop on_ -> pick_,
                       bop off_ -> release_,
                       op on -> filled,
                       op off -> empty })
}

mod* PHILOSOPHER {
  protecting(RIGHT-HAND + LEFT-HAND)

  *[ Phil ]*

  op init-phil : -> Phil
  bop pick-right : Phil -> Phil
  bop pick-left : Phil -> Phil
  bop rest : Phil -> Phil
  bop eating? : Phil -> Bool
  bop right-hand : Phil -> RightHand
  bop left-hand : Phil -> LeftHand

  var P : Phil

  eq eating?(P) = (status(right-hand(P)) == filled) and
                  (status(left-hand(P)) == filled) .

  eq right-hand(init-phil) = init-rh .
  eq right-hand(pick-right(P)) = pick(right-hand(P)) .
  eq right-hand(pick-left(P)) = right-hand(P) .
  eq right-hand(rest(P)) = release(right-hand(P)) .

  eq left-hand(init-phil) = init-lh .
  eq left-hand(pick-right(P)) = left-hand(P) .
  eq left-hand(pick-left(P)) = pick(left-hand(P)) .
  eq left-hand(rest(P)) = release(left-hand(P)) .
}

mod* GUEST1 {
  protecting(PHILOSOPHER *{ hsort Phil -> Guest1,
                            op init-phil -> init-guest1 })
}

mod* GUEST2 {
  protecting(PHILOSOPHER *{ hsort Phil -> Guest2,
                            op init-phil -> init-guest2 })
}

mod* GUEST3 {
  protecting(PHILOSOPHER *{ hsort Phil -> Guest3,
                            op init-phil -> init-guest3 })
}

mod* CHOP-STICK1 {
  protecting(SWITCH *{ hsort Switch -> ChopStick1,
                       op init-sw -> init-cs1,
                       bop on_ -> use_,
                       bop off_ -> release_,
                       op on -> in-use,
                       op off -> ready })
}

mod* CHOP-STICK2 {
  protecting(SWITCH *{ hsort Switch -> ChopStick2,
                       op init-sw -> init-cs2,
                       bop on_ -> use_,
                       bop off_ -> release_,
                       op on -> in-use,
                       op off -> ready })
}

mod* CHOP-STICK3 {
  protecting(SWITCH *{ hsort Switch -> ChopStick3,
                       op init-sw -> init-cs3,
                       bop on_ -> use_,
                       bop off_ -> release_,
                       op on -> in-use,
                       op off -> ready })

}

mod* TABLE {
  protecting(GUEST1 + GUEST2 + GUEST3 +
             CHOP-STICK1 + CHOP-STICK2 + CHOP-STICK3)

  *[ Table ]*

  op init-table : -> Table
  bop pick1r : Table -> Table
  bop pick1l : Table -> Table
  bop pick2r : Table -> Table
  bop pick2l : Table -> Table
  bop pick3r : Table -> Table
  bop pick3l : Table -> Table
  bop rest1 : Table -> Table
  bop rest2 : Table -> Table
  bop rest3 : Table -> Table

  bop eating1? : Table -> Bool
  bop eating2? : Table -> Bool
  bop eating3? : Table -> Bool

  bop guest1 : Table -> Guest1
  bop guest2 : Table -> Guest2
  bop guest3 : Table -> Guest3
  bop chopstick1 : Table -> ChopStick1
  bop chopstick2 : Table -> ChopStick2
  bop chopstick3 : Table -> ChopStick3

  var T : Table

  eq eating1?(T) = eating?(guest1(T)) .
  eq eating2?(T) = eating?(guest2(T)) .
  eq eating3?(T) = eating?(guest3(T)) .

  eq guest1(init-table) = init-guest1 .
  ceq guest1(pick1r(T)) = pick-right(guest1(T))
      if status(chopstick1(T)) == ready .
  ceq guest1(pick1r(T)) = guest1(T)
      if status(chopstick1(T)) =/= ready .
  ceq guest1(pick1l(T)) = pick-left(guest1(T))
      if status(chopstick3(T)) == ready .
  ceq guest1(pick1l(T)) = guest1(T)
      if status(chopstick3(T)) =/= ready .
  eq guest1(pick2r(T)) = guest1(T) .
  eq guest1(pick2l(T)) = guest1(T) .
  eq guest1(pick3r(T)) = guest1(T) .
  eq guest1(pick3l(T)) = guest1(T) .
  ceq guest1(rest1(T)) = rest(guest1(T))
      if eating1?(T) == true .
  ceq guest1(rest1(T)) = guest1(T)
      if eating1?(T) =/= true .
  eq guest1(rest2(T)) = guest1(T) .
  eq guest1(rest3(T)) = guest1(T) .

  eq guest2(init-table) = init-guest2 .
  eq guest2(pick1r(T)) = guest2(T) .
  eq guest2(pick1l(T)) = guest2(T) .
  ceq guest2(pick2r(T)) = pick-right(guest2(T))
      if status(chopstick2(T)) == ready .
  ceq guest2(pick2r(T)) = guest2(T)
      if status(chopstick2(T)) =/= ready .
  ceq guest2(pick2l(T)) = pick-left(guest2(T))
      if status(chopstick1(T)) == ready .
  ceq guest2(pick2l(T)) = guest2(T)
      if status(chopstick1(T)) =/= ready .
  eq guest1(pick3r(T)) = guest1(T) .
  eq guest1(pick3l(T)) = guest1(T) .
  eq guest2(rest1(T)) = guest2(T) .
  ceq guest2(rest2(T)) = rest(guest2(T))
      if eating2?(T) == true .
  ceq guest2(rest2(T)) = guest2(T)
      if eating2?(T) =/= true .
  eq guest2(rest3(T)) = guest2(T) .

  eq guest3(init-table) = init-guest3 .
  eq guest3(pick1r(T)) = guest3(T) .
  eq guest3(pick1l(T)) = guest3(T) .
  eq guest3(pick2r(T)) = guest3(T) .
  eq guest3(pick2l(T)) = guest3(T) .
  ceq guest3(pick3r(T)) = pick-right(guest3(T))
      if status(chopstick3(T)) == ready .
  ceq guest3(pick3r(T)) = guest3(T)
      if status(chopstick3(T)) =/= ready .
  ceq guest3(pick3l(T)) = pick-left(guest3(T))
      if status(chopstick2(T)) == ready .
  ceq guest3(pick3l(T)) = guest3(T)
      if status(chopstick2(T)) =/= ready .
  eq guest3(rest1(T)) = guest3(T) .
  eq guest3(rest2(T)) = guest3(T) .
  ceq guest3(rest3(T)) = rest(guest3(T))
      if eating3?(T) == true .
  ceq guest3(rest3(T)) = guest3(T)
      if eating3?(T) =/= true .

  eq chopstick1(init-table) = init-cs1 .
  eq chopstick1(pick1r(T)) = use(chopstick1(T)) .
  eq chopstick1(pick1l(T)) = chopstick1(T) .
  eq chopstick1(pick2r(T)) = chopstick1(T) .
  eq chopstick1(pick2l(T)) = use(chopstick1(T)) .
  eq chopstick1(pick3r(T)) = chopstick1(T) .
  eq chopstick1(pick3l(T)) = chopstick1(T) .

  eq chopstick2(init-table) = init-cs2 .
  eq chopstick2(pick1r(T)) = chopstick2(T) .
  eq chopstick2(pick1l(T)) = chopstick2(T) .
  eq chopstick2(pick2r(T)) = use(chopstick2(T)) .
  eq chopstick2(pick2l(T)) = chopstick2(T) .
  eq chopstick2(pick3r(T)) = chopstick2(T) .
  eq chopstick2(pick3l(T)) = use(chopstick2(T)) .

  eq chopstick3(init-table) = init-cs3 .
  eq chopstick3(pick1r(T)) = chopstick3(T) .
  eq chopstick3(pick1l(T)) = use(chopstick3(T)) .
  eq chopstick3(pick2r(T)) = chopstick3(T) .
  eq chopstick3(pick2l(T)) = chopstick3(T) .
  eq chopstick3(pick3r(T)) = use(chopstick3(T)) .
  eq chopstick3(pick3l(T)) = chopstick3(T) .
}

eof

red status(right-hand(guest1(pick1r(pick1l(init-table))))) .

-- set tram path brute .
-- tram red status(right-hand(guest1(pick1r(pick1l(init-table))))) .

