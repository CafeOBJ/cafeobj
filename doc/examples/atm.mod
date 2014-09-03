-- FILE: /home/diacon/LANG/Cafe/prog/atm.mod
-- CONTENTS: CASE study of an ATM (automated teller machine) system featuring
--           concurrent object composition
--           behavioural verification
--           automatic generation of case analysis by meta-level encoding
-- AUTHORS: Shuusaku Iida & Razvan Diaconescu
-- DIFFICULTY: ****

-- set tram path brute . <-- obsolete. now, we don't have tram.

-- we trust system's =*= proof
set accept =*= proof on

-- control-oriented definition of Boolean connectives
-- improves the efficiency of execution by 20%
-- (now this is already in built-in BOOL. --sawada@sra.co.jp)

"
module! BOOL+
{
  protecting(BOOL)
  op _and-also_ : Bool Bool -> Bool { r-assoc strategy: (1 0 2 0) prec: 55 }
  op _or-else_ : Bool Bool -> Bool { r-assoc  strategy: (1 0 2 0) prec: 59 }
  var X : Bool
  eq true and-also X = X .
  eq X and-also true = X .
  eq false and-also X = false .
  eq X and-also false = false .
  eq true or-else X = true .
  eq X or-else true = true .
  eq false or-else X = X .
  eq X or-else false = X .
}
"

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
  protecting (ON-OFF)

  *[ Switch ]*

  op init-sw : -> Switch         -- initial state
  -- switch on
  bop on_ : Switch -> Switch     -- method
  -- switch off
  bop off_ : Switch -> Switch    -- method
  -- observe the state of the switch
  bop status_ : Switch -> Value   -- attribute

  var S : Switch

  eq status(init-sw) = off .
  eq status(on(S)) = on .
  eq status(off(S)) = off .
}

-- -------------------------------------------------------------
-- User identification
-- -------------------------------------------------------------
mod! USER-ID {
  protecting (NAT)
  [ Nat < UId ]

  op unidentified-user : -> UId
}

-- -------------------------------------------------------------
-- Counter
-- -------------------------------------------------------------
mod* COUNTER {
  protecting(USER-ID + INT)

  *[ Counter ]*

  -- initialize counter with user ID
  op init-counter : UId -> Counter   -- initial state
  -- add a value to the counter
  bop add : Int Counter -> Counter   -- method
  -- read the value of the counter
  bop read_ : Counter -> Int         -- attribute

  var I : Int
  var C : Counter
  var U : UId

  eq read(init-counter(U)) = 0 .
  eq read(add(I, C)) = I + read(C) .
}

-- -------------------------------------------------------------
-- Counter with error
-- -------------------------------------------------------------
mod* COUNTER* {
  protecting (COUNTER)

  op counter-not-exist : -> Counter  -- error value
}

-- -------------------------------------------------------------
-- Account sytem
-- -------------------------------------------------------------
mod* ACCOUNT-SYSTEM {
  protecting (COUNTER* *{ hsort Counter -> Account,
			  op init-counter -> init-account,
			  op counter-not-exist -> no-account })

  *[ AccountSys ]*

  op init-account-sys : -> AccountSys             -- initial state
  -- add a user account with user ID
  bop add : UId Nat AccountSys -> AccountSys       -- method
  -- delete a user account
  bop del : UId AccountSys -> AccountSys           -- method
  -- deposit operation
  bop deposit : UId Nat AccountSys -> AccountSys   -- method
  -- withdraw operation
  bop withdraw : UId Nat AccountSys -> AccountSys  -- method
  -- calculate the balance of an user account
  bop balance : UId AccountSys -> Nat              -- attribute
  -- get the state of a counter from the state of an account
  bop account : UId AccountSys -> Account   {memo} -- projection

  vars U U' : UId
  var A : AccountSys
  var N : Nat

  eq account(U, init-account-sys) = no-account .
  ceq account(U, add(U', N, A)) = add(N, init-account(U))
       if U == U' .
  ceq account(U, add(U', N, A)) = account(U, A)
       if U =/= U' .
  ceq account(U, del(U', A)) = no-account
       if U == U' .
  ceq account(U, del(U', A)) = account(U, A)
       if U =/= U' .
  ceq account(U, deposit(U', N, A)) = add(N, account(U, A))
       if U == U' .
  ceq account(U, deposit(U', N, A)) = account(U, A)
       if U =/= U' .
  ceq account(U, withdraw(U', N, A)) = add(-(N), account(U, A))
       if U == U' .
  ceq account(U, withdraw(U', N, A)) = account(U, A)
       if U =/= U' .

  eq balance(U, A) = read(account(U, A)) .
}

-- -------------------------------------------------------------
-- Trivial module with an element (undefined)
-- -------------------------------------------------------------
mod* TRIV+ {
  [ Elt ]

  op undefined : -> Elt
}

-- -------------------------------------------------------------
-- Cell
-- -------------------------------------------------------------
mod* CELL(X :: TRIV+) {
  *[ Cell ]*

  op init-cell : -> Cell      -- initial state
  -- put the element to the cell
  bop put : Elt Cell -> Cell  -- method
  -- get the element from the cell
  bop get : Cell -> Elt       -- attribute

  var E : Elt
  var C : Cell

  eq get(init-cell) = undefined .
  eq get(put(E, C)) = E .
}

-- -------------------------------------------------------------
-- ATM identifier
-- -------------------------------------------------------------
mod! ATM-ID {
--  protecting(NAT *{ sort Nat -> AId })
  protecting(NAT)

  [ Nat < AId ]
}

-- -------------------------------------------------------------
--  Button
-- -------------------------------------------------------------
mod* BUTTON {
  protecting(SWITCH *{ hsort Switch -> Button,
                       sort Value -> Operation,
                       op init-sw -> init-button,
                       op on -> deposit,
                       op off -> withdraw })
}

-- -------------------------------------------------------------
--  Cell for card information
-- -------------------------------------------------------------
mod* CARD {
  protecting(CELL(X <= view to USER-ID
                  { sort Elt -> UId,
                    op undefined -> unidentified-user })
                  *{ hsort Cell -> Card,
                     op init-cell -> init-card })
}

-- -------------------------------------------------------------
--  Cell for input
-- -------------------------------------------------------------
mod* INPUT {
  protecting(CELL(X <= view to NAT
                  { sort Elt -> Nat,
                    op undefined -> 0 })
                  *{ hsort Cell -> Input,
                     op init-cell -> init-input })
}

-- -------------------------------------------------------------
--  Cell for ouput
-- -------------------------------------------------------------
mod* OUTPUT {
  protecting(CELL(X <= view to NAT
                  { sort Elt -> Nat,
                    op undefined -> 0 })
                  *{ hsort Cell -> Output,
                     op init-cell -> init-output })
}

-- -------------------------------------------------------------
--  Cell for request
-- -------------------------------------------------------------
mod* REQUEST {
  protecting(CELL(X <= view to NAT
                  { sort Elt -> Nat,
                    op undefined -> 0 })
                  *{ hsort Cell -> Request,
                     op init-cell -> init-request })
}

-- -------------------------------------------------------------
--  ATM client
-- -------------------------------------------------------------
mod* ATM-CLIENT {
-- importing data and the composing objects
  protecting(ATM-ID + BUTTON + CARD + INPUT + OUTPUT + REQUEST)

  *[ Atm ]*

  op init-atm : AId -> Atm              -- initial state
  op no-atm : -> Atm                    -- error
  op invalid-operation : -> Atm         -- error
  -- push the deposit button
  bop deposit : Atm -> Atm              -- method
  -- push the withdraw button
  bop withdraw : Atm -> Atm             -- method
  -- input the request for withdraw
  bop request : Nat Atm -> Atm          -- method
  -- put money
  bop put-money : Nat Atm -> Atm        -- method
  -- take money
  bop take-money : Atm -> Atm           -- mothod
  -- set money for output (system operation)
  bop set-money : Nat Atm -> Atm        -- method
  -- put the bank card
  bop put-card : UId Atm -> Atm         -- method
  -- clear all the informations kept in the atm
  bop clear : Atm -> Atm                -- method
  -- get the user ID
  bop user-id : Atm -> UId              -- attribute
  -- get the money that user input
  bop get-input : Atm -> Nat            -- attribute
  -- get the outputed money
  bop get-output : Atm -> Nat           -- attribute
  -- get the request
  bop get-request : Atm -> Nat          -- attribute
  -- get the state of the button
  bop button-status : Atm -> Operation  -- attribute

  bop button : Atm -> Button     {memo} -- projection
  bop card : Atm -> Card         {memo} -- projection
  bop request : Atm -> Request   {memo} -- projection
  bop input : Atm -> Input       {memo} -- projection
  bop output : Atm -> Output     {memo} -- projection

  var ATM : Atm
  var N : Nat
  var U : UId
  var A : AId

  eq button(init-atm(A)) = init-button .
  eq button(invalid-operation) = init-button .
  eq button(deposit(ATM)) = on(button(ATM)) .
  eq button(withdraw(ATM)) = off(button(ATM)) .
  eq button(request(N, ATM)) = button(ATM) .
  eq button(put-money(N, ATM)) = button(ATM) .
  eq button(take-money(ATM)) = button(ATM) .
  eq button(set-money(N, ATM)) = button(ATM) .
  eq button(put-card(U, ATM)) = button(ATM) .
  eq button(clear(ATM)) = init-button .

  eq card(init-atm(A)) = init-card .
  eq card(invalid-operation) = init-card .
  eq card(deposit(ATM)) = card(ATM) .
  eq card(withdraw(ATM)) = card(ATM) .
  eq card(request(N, ATM)) = card(ATM) .
  eq card(put-money(N, ATM)) = card(ATM) .
  eq card(take-money(ATM)) = card(ATM) .
  eq card(set-money(N, ATM)) = card(ATM) .
  eq card(put-card(U, ATM)) = put(U, card(ATM)) .
  eq card(clear(ATM)) = init-card .

  eq request(init-atm(A)) = init-request .
  eq request(invalid-operation) = init-request .
  eq request(deposit(ATM)) = request(ATM) .
  eq request(withdraw(ATM)) = request(ATM) .
  eq request(request(N, ATM)) = put(N, request(ATM)) .
  eq request(put-money(N, ATM)) = request(ATM) .
  eq request(take-money(ATM)) = request(ATM) .
  eq request(set-money(N, ATM)) = request(ATM) .
  eq request(put-card(U, ATM)) = request(ATM) .
  eq request(clear(ATM)) = init-request .

  eq input(init-atm(A)) = init-input .
  eq input(invalid-operation) = init-input .
  eq input(deposit(ATM)) = input(ATM) .
  eq input(withdraw(ATM)) = input(ATM) .
  eq input(request(N, ATM)) = input(ATM) .
  eq input(put-money(N, ATM)) = put(N, input(ATM)) .
  eq input(take-money(ATM)) = input(ATM) .
  eq input(set-money(N, ATM)) = input(ATM) .
  eq input(put-card(U, ATM)) = input(ATM) .
  eq input(clear(ATM)) = init-input .

  eq output(init-atm(A)) = init-output .
  eq output(invalid-operation) = init-output .
  eq output(deposit(ATM)) = output(ATM) .
  eq output(withdraw(ATM)) = output(ATM) .
  eq output(request(N, ATM)) = output(ATM) .
  eq output(put-money(N, ATM)) = output(ATM) .
  eq output(take-money(ATM)) = init-output .
  eq output(set-money(N, ATM)) = put(N, output(ATM)) .
  eq output(put-card(U, ATM)) = output(ATM) .
  eq output(clear(ATM)) = output(ATM) .

  eq user-id(ATM) = get(card(ATM)) .
  eq get-input(ATM) = get(input(ATM)) .
  eq get-output(ATM) = get(output(ATM)) .
  eq get-request(ATM) = get(request(ATM)) .
  eq button-status(ATM) = status(button(ATM)) .
}

-- -------------------------------------------------------------
-- ATM system
-- -------------------------------------------------------------
mod* ATM-SYSTEM {
  -- protecting(BOOL+)
  protecting(ACCOUNT-SYSTEM + ATM-CLIENT)

  *[ System ]*

  op init-sys : -> System                   -- initial state
  -- add an atm to the system
  bop add-atm : AId System -> System        -- method
  -- delete an atm from the system
  bop del-atm : AId System -> System        -- method
  -- add an user account
  bop add-user : UId Nat System -> System   -- method
  -- delete an user account
  bop del-user : UId System -> System       -- method
  -- put the bank card
  bop put-card : AId UId System -> System   -- method
  -- request for withdraw
  bop request : AId Nat System -> System    -- method
  -- put money
  bop put-money : AId Nat System -> System  -- method
  -- take money
  bop take-money : AId System -> System     -- method
  -- deposit operation
  bop deposit : AId System -> System        -- method
  -- withdraw operation
  bop withdraw : AId System -> System       -- method
  -- push the ok button on atm to complete the operation
  bop ok : AId System -> System             -- method
  -- cancel the operation of ATM
  bop cancel : AId System -> System         -- method
  -- get the balance of specified user
  bop balance : UId System -> Nat           -- attribute
  -- projection operator for AccountSys
  bop account-sys : System -> AccountSys  {memo}  -- projection
  -- projection operator for Atm
  bop atm : AId System -> Atm             {memo}  -- projection

  var S : System
  vars A A' : AId
  var U : UId
  var N : Nat

  eq balance(U, S) = balance(U, account-sys(S)) .

  eq account-sys(init-sys) = init-account-sys .
  eq account-sys(add-atm(A, S)) = account-sys(S) .
  eq account-sys(del-atm(A, S)) = account-sys(S) .
  eq account-sys(add-user(U, N, S)) = add(U, N, account-sys(S)) .
  eq account-sys(del-user(U, S)) = del(U, account-sys(S)) .
  eq account-sys(put-card(A, U, S)) = account-sys(S) .
  eq account-sys(request(A, N, S)) = account-sys(S) .
  eq account-sys(put-money(A, N, S)) = account-sys(S) .
  eq account-sys(take-money(A, S)) = account-sys(S) .
  eq account-sys(deposit(A, S)) = account-sys(S) .
  eq account-sys(withdraw(A, S)) = account-sys(S) .
  ceq account-sys(ok(A, S)) = 
       deposit(user-id(atm(A, S)), get-input(atm(A, S)), account-sys(S))
       if (button-status(atm(A, S)) == deposit) and-also
          (user-id(atm(A, S)) =/= unidentified-user) and-also
          (get-input(atm(A, S)) =/= 0) .
  ceq account-sys(ok(A, S)) = 
       withdraw(user-id(atm(A, S)), get-request(atm(A, S)), account-sys(S))
       if (button-status(atm(A, S)) == withdraw) and-also
          (user-id(atm(A, S)) =/= unidentified-user) and-also
          (get-request(atm(A, S)) =/= 0) and-also
          (get-request(atm(A, S)) <=
                 balance(user-id(atm(A, S)), account-sys(S))) .
  ceq account-sys(ok(A, S)) = account-sys(S)
       if user-id(atm(A, S)) == unidentified-user or
          (button-status(atm(A, S)) == deposit and-also
              get-input(atm(A, S)) == 0) or
          (button-status(atm(A, S)) == withdraw and-also
              (get-request(atm(A, S)) == 0 or
              get-request(atm(A, S)) >
                       balance(user-id(atm(A, S)), account-sys(S)))) .
  eq account-sys(cancel(A, S)) = account-sys(S) .

  eq atm(A, init-sys) = no-atm .
  ceq atm(A, add-atm(A', S)) = init-atm(A)
       if A == A' .
  ceq atm(A, add-atm(A', S)) = atm(A, S)
       if A =/= A' .
  ceq atm(A, del-atm(A', S)) = no-atm
       if A == A .
  ceq atm(A, del-atm(A', S)) = atm(A, S)
       if A =/= A .
  eq atm(A, add-user(U, N, S)) = atm(A, S) .
  eq atm(A, del-user(U, S)) = atm(A, S) .
  ceq atm(A, put-card(A', U, S)) = put-card(U, atm(A, S))
       if A == A' .
  ceq atm(A, put-card(A', U, S)) = atm(A, S)
       if A =/= A' .
  ceq atm(A, request(A', N, S)) = request(N, atm(A, S))
       if A == A' .
  ceq atm(A, request(A', N, S)) = atm(A, S)
       if A =/= A' .
  ceq atm(A, put-money(A', N, S)) = put-money(N, atm(A, S))
       if A == A' .
  ceq atm(A, put-money(A', N, S)) = atm(A, S)
       if A =/= A' .
  ceq atm(A, take-money(A', S)) = take-money(atm(A, S))
       if A == A' .
  ceq atm(A, take-money(A', S)) = atm(A, S)
       if A =/= A' .
  ceq atm(A, deposit(A', S)) = deposit(atm(A, S))
       if A == A' .
  ceq atm(A, deposit(A', S)) = atm(A, S)
       if A =/= A' .
  ceq atm(A, withdraw(A', S)) = withdraw(atm(A, S))
       if A == A' .
  ceq atm(A, withdraw(A', S)) = atm(A, S)
       if A =/= A' .
  ceq atm(A, ok(A', S)) = clear(atm(A, S))
       if (A == A') and-also
	  (user-id(atm(A, S)) =/= unidentified-user) and-also
          (button-status(atm(A, S)) == deposit) .
  ceq atm(A, ok(A', S)) = set-money(get-request(atm(A, S)), clear(atm(A, S)))
       if A == A' and-also
          (user-id(atm(A, S)) =/= unidentified-user) and-also
          (button-status(atm(A, S)) ==  withdraw) and-also
          (get-request(atm(A, S)) <=
                       balance(user-id(atm(A, S)), account-sys(S))) .
  ceq atm(A, ok(A', S)) = invalid-operation
       if A == A' and-also
          ((user-id(atm(A, S)) == unidentified-user) or
           ((button-status(atm(A, S)) ==  withdraw) and-also
              (get-request(atm(A, S)) >
                           balance(user-id(atm(A, S)), account-sys(S))))) .
  ceq atm(A, ok(A', S)) = atm(A, S)
       if A =/= A' .
  ceq atm(A, cancel(A', S)) = init-atm(A)
       if A == A' .
  ceq atm(A, cancel(A', S)) = atm(A, S)
       if A =/= A' .
}

-- -------------------------------------------------------------
-- The toplevel of ATM system
-- -------------------------------------------------------------
mod* ATM-SYSTEM-TOPLEVEL {
  protecting(ATM-SYSTEM)

  *[ TopLevel ]*

  op init-tl : -> TopLevel                         -- initial state
  -- add a new atm
  bop add-atm : AId TopLevel -> TopLevel           -- method
  -- delete an atm
  bop del-atm : AId TopLevel -> TopLevel           -- method
  -- create an user account with initial balance
  bop add-user : UId Nat TopLevel -> TopLevel      -- method
  -- delete an user account
  bop del-user : UId TopLevel -> TopLevel          -- method
  -- user "UId" goes to an ATM "AId" and deposit "Nat"
  bop deposit : UId AId Nat TopLevel -> TopLevel   -- method
  -- user "UId" goes to an ATM "AId" and withdraw "Nat"
  bop withdraw : UId AId Nat TopLevel -> TopLevel  -- method
  -- get a balance for the user
  bop balance : UId TopLevel -> Nat         {memo} -- attribute
  -- projection operator for System
  bop system : TopLevel -> System           {memo} -- projection

  var U : UId
  var A : AId
  var N : Nat
  var TL : TopLevel

  eq balance(U, TL) = balance(U, account-sys(system(TL))) .

  eq system(init-tl) = init-sys .
  eq system(add-atm(A, TL)) = add-atm(A, system(TL)) .
  eq system(del-atm(A, TL)) = del-atm(A, system(TL)) .
  eq system(add-user(U, N, TL)) = add-user(U, N, system(TL)) .
  eq system(del-user(U, TL)) = del-user(U, system(TL)) .
  eq system(deposit(U, A, N, TL)) =
     ok(A, put-money(A, N, deposit(A, put-card(A, U, system(TL))))) .
  eq system(withdraw(U, A, N, TL)) =
     take-money(A, ok(A, request(A, N, withdraw(A,
                put-card(A, U, system(TL)))))) .
}

-- -------------------------------------------------------------
-- test for ATM-SYSTEM-TOPLEVEL
-- -------------------------------------------------------------
open ATM-SYSTEM-TOPLEVEL .

  op tl : -> TopLevel .
  ops u1 u2 : -> UId .
  ops ai1 ai2 : -> AId .

red balance(u1, deposit(u1, ai2, 20, add-user(u1, 100, tl))) .
red balance(u1, withdraw(u1, ai1, 20, withdraw(u2, ai2, 30,
            add-user(u1, 100, add-user(u2, 100, tl))))) .
close

-- -------------------------------------------------------------
-- module for behavioural equivalences
-- -------------------------------------------------------------
mod COINDUCTION-REL {
  protecting(ATM-SYSTEM-TOPLEVEL)

-- behavioural equivalence for AccountSys
  op _R[_]_ : AccountSys UId AccountSys -> Bool {coherent}

  vars AS1 AS2 : AccountSys
  var U : UId 

  eq AS1 R[U] AS2 = account(U, AS1) =*= account(U, AS2) . 

-- behavioural equivalence for Atm
  op _R_ : Atm Atm -> Bool {coherent}

  vars A1 A2 : Atm

  eq A1 R A2 = button(A1) =*= button(A2) and
               card(A1) =*= card(A2) and
               request(A1) =*= request(A2) and
               input(A1) =*= input(A2) and
               output(A1) =*= output(A2) .

-- behavioural equivalence for System
  op _R[_,_]_ : System UId AId System -> Bool {coherent}

  vars S1 S2 : System
  var A : AId 

  eq S1 R[U, A] S2 = account-sys(S1) R[U] account-sys(S2) and
                     atm(A, S1) R atm(A, S2) . 

-- behavioural equivalence for TopLevel
  op _R[_,_]_ : TopLevel UId AId TopLevel -> Bool {coherent}

  vars T1 T2 : TopLevel

  eq T1 R[U, A] T2 = system(T1) R[U, A] system(T2) .
}

mod PROOF {
-- organize the proof of the behavioural property
  protecting(COINDUCTION-REL)

  ops a a1 a2 : -> AId
  op tl : -> TopLevel
  ops u u1 u2 : -> UId
  ops n1 n2 n01 n02 m1 m1' m2 m2' m : -> Nat

-- atomic cases    
  eq n1 =/= 0 = true .
  eq n2 =/= 0 = true .
  eq n01 == 0 = true .
  eq n02 == 0 = true .
  eq n1 <= m1 = true .
  eq n01 <= m1 = true .
  eq n1 > m1' = true .
  eq n2 <= m2 = true .
  eq n02 <= m2 = true .
  eq n2 > m2' = true .
  
  op state-of-system : Nat Nat -> TopLevel 
  ops w1w2 w2w1 : AId AId Nat Nat Nat Nat -> TopLevel 
-- the meta-level encoding generating the proof term containing all cases
  op TERM : UId AId AId AId Nat Nat Nat Nat -> Bool
  op TERM1 : UId AId AId AId Nat Nat -> Bool 
  op TERM2 : UId AId AId AId -> Bool 
  op TERM' : AId AId AId -> Bool 
  op RESULT :  -> Bool 

  vars A A1 A2 : AId
  var U : UId 
  vars N1 N2 M1 M2 : Nat 

-- basic assumptions
  eq state-of-system(M1, M2) = add-user(u, m,
                               add-user(u1, M1,
	                       add-user(u2, M2,
                               add-atm(a,
                               add-atm(a1,
                               add-atm(a2, tl)))))) .
	                           
  eq w1w2(A1, A2, N1, N2, M1, M2) =
             withdraw(u1, A1, N1,
             withdraw(u2, A2, N2, state-of-system(M1, M2))) .

  eq w2w1(A1, A2, N1, N2, M1, M2) =
             withdraw(u2, A2, N2,
             withdraw(u1, A1, N1, state-of-system(M1, M2))) .

-- the parameterized proof term  
  eq TERM(U, A, A1, A2, N1, N2, M1, M2) =
       w1w2(A1,A2,N1,N2,M1,M2) R[U, A] w2w1(A1,A2,N1,N2,M1,M2) .

  eq TERM1(U, A, A1, A2, N2, M2) =
         TERM(U, A, A1, A2, n1, N2, m1, M2) and
	 TERM(U, A, A1, A2, n1, N2, m1', M2) and
	 TERM(U, A, A1, A2, n01, N2, m1, M2) .

  eq TERM2 (U, A, A1, A2) =
         TERM1(U, A, A1, A2, n2, m2) and
	 TERM1(U, A, A1, A2, n2, m2') and
	 TERM1(U, A, A1, A2, n02, m2) .
  
  eq TERM'(A, A1, A2) = TERM2(u,  A, A1, A2) and
                        TERM2(u1, A, A1, A2) and
			TERM2(u2, A, A1, A2) .
  eq RESULT = TERM'(a,  a1, a2) and
              TERM'(a,  a1, a1) and
              TERM'(a,  a,  a) and
              TERM'(a1, a1, a2) .
}

select PROOF
-- tram red RESULT .
red RESULT .

eof
--
$Id: atm.mod,v 1.2 2010-07-30 00:47:51 sawada Exp $
