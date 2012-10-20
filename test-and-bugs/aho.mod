-- 飯田です。

-- CafeOBJに同一の仕様を繰り返して読み込ませると、
-- 各moduleはredefineされますが、仕様によっては
-- １回目には読み込みに成功したのに、２回目はエラーが
-- でるものがあります。
-- モジュールのインポートで複雑な事をするとでるようです。

-- 例としてメールの最後に仕様を添付しました。

-- ----
-- 飯田 周作（s_iida@jaist.ac.jp）

-- -------------------------------------------------------------
-- SWITCH
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
  extending(NAT *{ sort Nat -> UId })

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
  protecting(COUNTER)

-- error value
  op counter-not-exist : -> Counter  -- error
}

-- -------------------------------------------------------------
-- Account sytem
-- -------------------------------------------------------------
mod* ACCOUNT-SYSTEM {
  protecting(COUNTER* *{ hsort Counter -> Account,
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
  bop account : UId AccountSys -> Account          -- projection

  vars U U' : UId
  var A : AccountSys
  var N : Nat

  beq account(U, init-account-sys) = no-account .
  bceq account(U, add(U', N, A)) = add(N, init-account(U))
       if U == U' .
  bceq account(U, add(U', N, A)) = account(U, A)
       if U =/= U' .
  bceq account(U, del(U', A)) = no-account
       if U == U' .
  bceq account(U, del(U', A)) = account(U, A)
       if U =/= U' .
  bceq account(U, deposit(U', N, A)) = add(N, account(U, A))
       if U == U' .
  bceq account(U, deposit(U', N, A)) = account(U, A)
       if U =/= U' .
  bceq account(U, withdraw(U', N, A)) = add(-(N), account(U, A))
       if U == U' .
  bceq account(U, withdraw(U', N, A)) = account(U, A)
       if U =/= U' .

  eq balance(U, A) = read(account(U, A)) .
}

-- -------------------------------------------------------------
-- TRIV+
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
-- ATM identification
-- -------------------------------------------------------------
mod! ATM-ID {
  protecting(NAT *{ sort Nat -> AId })
}

-- -------------------------------------------------------------
--  ATM client
-- -------------------------------------------------------------
mod* ATM-CLIENT {
-- importing data and the composing objects
  protecting(ATM-ID +
             SWITCH *{ hsort Switch -> Button,
                       sort Value -> Operation,
                       op init-sw -> init-button,
                       op on -> deposit,
                       op off -> withdraw } +
             CELL(X <= view to USER-ID
                  { sort Elt -> UId,
                    op undefined -> unidentified-user })
                  *{ hsort Cell -> Card,
                     op init-cell -> init-card } +
             CELL(X <= view to NAT
                  { sort Elt -> Nat,
                    op undefined -> 0 })
                  *{ hsort Cell -> Request,
                     op init-cell -> init-request } +
             CELL(X <= view to NAT
                  { sort Elt -> Nat,
                    op undefined -> 0 })
                  *{ hsort Cell -> Output,
                     op init-cell -> init-output } +
             CELL(X <= view to NAT
                  { sort Elt -> Nat,
                    op undefined -> 0 })
                  *{ hsort Cell -> Input,
                     op init-cell -> init-input })

  *[ Atm ]*

  op init-atm : AId -> Atm              -- initial state
  op no-atm : -> Atm          -- error
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

  bop button : Atm -> Button            -- projection
  bop card : Atm -> Card                -- projection
  bop request : Atm -> Request          -- projection
  bop input : Atm -> Input              -- projection
  bop output : Atm -> Output            -- projection

  var ATM : Atm
  var N : Nat
  var U : UId
  var A : AId

  beq button(init-atm(A)) = init-button .
  beq button(deposit(ATM)) = on(button(ATM)) .
  beq button(withdraw(ATM)) = off(button(ATM)) .
  beq button(request(N, ATM)) = button(ATM) .
  beq button(put-money(N, ATM)) = button(ATM) .
  beq button(take-money(ATM)) = button(ATM) .
  beq button(set-money(N, ATM)) = button(ATM) .
  beq button(put-card(U, ATM)) = button(ATM) .
  beq button(clear(ATM)) = init-button .

  beq card(init-atm(A)) = init-card .
  beq card(deposit(ATM)) = card(ATM) .
  beq card(withdraw(ATM)) = card(ATM) .
  beq card(request(N, ATM)) = card(ATM) .
  beq card(put-money(N, ATM)) = card(ATM) .
  beq card(take-money(ATM)) = card(ATM) .
  beq card(set-money(N, ATM)) = card(ATM) .
  beq card(put-card(U, ATM)) = put(U, card(ATM)) .
  beq card(clear(ATM)) = init-card .

  beq request(init-atm(A)) = init-request .
  beq request(deposit(ATM)) = request(ATM) .
  beq request(withdraw(ATM)) = request(ATM) .
  beq request(request(N, ATM)) = put(N, request(ATM)) .
  beq request(put-money(N, ATM)) = request(ATM) .
  beq request(take-money(ATM)) = request(ATM) .
  beq request(set-money(N, ATM)) = request(ATM) .
  beq request(put-card(U, ATM)) = request(ATM) .
  beq request(clear(ATM)) = init-request .

  beq input(init-atm(A)) = init-input .
  beq input(deposit(ATM)) = input(ATM) .
  beq input(withdraw(ATM)) = input(ATM) .
  beq input(request(N, ATM)) = input(ATM) .
  beq input(put-money(N, ATM)) = put(N, input(ATM)) .
  beq input(take-money(ATM)) = input(ATM) .
  beq input(set-money(N, ATM)) = input(ATM) .
  beq input(put-card(U, ATM)) = input(ATM) .
  beq input(clear(ATM)) = init-input .

  beq output(init-atm(A)) = init-output .
  beq output(deposit(ATM)) = output(ATM) .
  beq output(withdraw(ATM)) = output(ATM) .
  beq output(request(N, ATM)) = output(ATM) .
  beq output(put-money(N, ATM)) = output(ATM) .
  beq output(take-money(ATM)) = init-output .
  beq output(set-money(N, ATM)) = put(N, output(ATM)) .
  beq output(put-card(U, ATM)) = output(ATM) .
  beq output(clear(ATM)) = output(ATM) .

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
  protecting(ACCOUNT-SYSTEM + ATM-CLIENT)

  *[ System ]*

  op init-sys : -> System                   -- initial state
  -- add an atm to the system
  bop add-atm : AId System -> System        -- method
  -- delete an atm from the system
  bop del-atm : AId System -> System        -- method
  -- add an user account
  bop add-user : UId Nat System -> System   -- method
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
  bop account-sys : System -> AccountSys    -- projection
  bop atm : AId System -> Atm               -- projection

  var S : System
  vars A A' : AId
  var U : UId
  var N : Nat

  eq balance(U, S) = balance(U, account-sys(S)) .

  beq account-sys(init-sys) = init-account-sys .
  beq account-sys(add-atm(A, S)) = account-sys(S) .
  beq account-sys(del-atm(A, S)) = account-sys(S) .
  beq account-sys(add-user(U, N, S)) = add(U, N, account-sys(S)) .
  beq account-sys(put-card(A, U, S)) = account-sys(S) .
  beq account-sys(request(A, N, S)) = account-sys(S) .
  beq account-sys(put-money(A, N, S)) = account-sys(S) .
  beq account-sys(take-money(A, S)) = account-sys(S) .
  beq account-sys(deposit(A, S)) = account-sys(S) .
  beq account-sys(withdraw(A, S)) = account-sys(S) .
  bceq account-sys(ok(A, S)) = 
       deposit(user-id(atm(A, S)), get-input(atm(A, S)), account-sys(S))
       if button-status(atm(A, S)) == deposit and
          user-id(atm(A, S)) =/= unidentified-user and
          get-input(atm(A, S)) =/= 0 .
  bceq account-sys(ok(A, S)) = 
       withdraw(user-id(atm(A, S)), get-request(atm(A, S)), account-sys(S))
       if button-status(atm(A, S)) == withdraw and
          user-id(atm(A, S)) =/= unidentified-user and
          get-request(atm(A, S)) =/= 0 and
          get-request(atm(A, S)) <=
                 balance(user-id(atm(A, S)), account-sys(S)) .
  bceq account-sys(ok(A, S)) = account-sys(S)
       if user-id(atm(A, S)) == unidentified-user or
          (button-status(atm(A, S)) == deposit and
              get-input(atm(A, S)) == 0) or
          (button-status(atm(A, S)) == withdraw and
              (get-request(atm(A, S)) == 0 or
              get-request(atm(A, S)) >
                       balance(user-id(atm(A, S)), account-sys(S)))) .
  beq account-sys(cancel(A, S)) = account-sys(S) .

  beq atm(A, init-sys) = no-atm .
  bceq atm(A, add-atm(A', S)) = init-atm(A)
       if A == A' .
  bceq atm(A, add-atm(A', S)) = atm(A, S)
       if A =/= A' .
  bceq atm(A, del-atm(A', S)) = no-atm
       if A == A .
  bceq atm(A, del-atm(A', S)) = atm(A, S)
       if A =/= A .
  beq atm(A, add-user(U, N, S)) = atm(A, S) .
  bceq atm(A, put-card(A', U, S)) = put-card(U, atm(A, S))
       if A == A' .
  bceq atm(A, put-card(A', U, S)) = atm(A, S)
       if A =/= A' .
  bceq atm(A, request(A', N, S)) = request(N, atm(A, S))
       if A == A' .
  bceq atm(A, request(A', N, S)) = atm(A, S)
       if A =/= A' .
  bceq atm(A, put-money(A', N, S)) = put-money(N, atm(A, S))
       if A == A' .
  bceq atm(A, put-money(A', N, S)) = atm(A, S)
       if A =/= A' .
  bceq atm(A, take-money(A', S)) = take-money(atm(A, S))
       if A == A' .
  bceq atm(A, take-money(A', S)) = atm(A, S)
       if A =/= A' .
  bceq atm(A, deposit(A', S)) = deposit(atm(A, S))
       if A == A' .
  bceq atm(A, deposit(A', S)) = atm(A, S)
       if A =/= A' .
  bceq atm(A, withdraw(A', S)) = withdraw(atm(A, S))
       if A == A' .
  bceq atm(A, withdraw(A', S)) = atm(A, S)
       if A =/= A' .
  bceq atm(A, ok(A', S)) = clear(atm(A, S))
       if A == A' and
          user-id(atm(A, S)) =/= unidentified-user and
          button-status(atm(A, S)) == deposit .
  bceq atm(A, ok(A', S)) = set-money(get-request(atm(A, S)), clear(atm(A, S)))
       if A == A' and
          user-id(atm(A, S)) =/= unidentified-user and
          button-status(atm(A, S)) ==  withdraw and
          get-request(atm(A, S)) <=
                    balance(user-id(atm(A, S)), account-sys(S)) .
  bceq atm(A, ok(A', S)) = invalid-operation
       if A == A' and
          (user-id(atm(A, S)) == unidentified-user or
          (button-status(atm(A, S)) ==  withdraw and
              (get-input(atm(A, S)) >
                   balance(user-id(atm(A, S)), account-sys(S))))) .
  bceq atm(A, ok(A', S)) = atm(A, S)
       if A =/= A' .
  bceq atm(A, cancel(A', S)) = init-atm(A)
       if A == A' .
  bceq atm(A, cancel(A', S)) = atm(A, S)
       if A =/= A' .
}



