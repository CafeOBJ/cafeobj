-- 飯田さんの ATM のコード自体は問題無いのですが，以下のように編集系のロー
-- ド機能に合わせて同一のモジュールを複数回ロードさせるとエラーとなります．
-- 
--
-- ------------------------------------------------------------------
-- -*- Mode:CafeOBJ -*-

mod* TRIV+ {
  [ Elt ]

  op undefined : -> Elt
}

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

mod* REQUEST {
  protecting(CELL(X <= view to NAT
                  { sort Elt -> Nat,
                    op undefined -> 0 })
                  *{ hsort Cell -> Request,
                     op init-cell -> init-request })
}

mod* OUTPUT {
  protecting(CELL(X <= view to NAT
                  { sort Elt -> Nat,
                    op undefined -> 0 })
                  *{ hsort Cell -> Output,
                     op init-cell -> init-output })
}

mod* INPUT {
  protecting(CELL(X <= view to NAT
                  { sort Elt -> Nat,
                    op undefined -> 0 })
                  *{ hsort Cell -> Input,
                     op init-cell -> init-input })
}

mod! USER-ID {
  protecting(NAT)
  [ Nat < UId ]

  op unidentified-user : -> UId
}


mod* CARD {
  protecting(CELL(X <= view to USER-ID
                  { sort Elt -> UId,
                    op undefined -> unidentified-user })
                  *{ hsort Cell -> Card,
                     op init-cell -> init-card })
}

mod! ON-OFF {
  [ Value ]

  ops on off : -> Value
}

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

mod* BUTTON {
  protecting(SWITCH *{ hsort Switch -> Button,
                       sort Value -> Operation,
                       op init-sw -> init-button,
                       op on -> deposit,
                       op off -> withdraw })
}

mod! ATM-ID {
  [ AId ]
--  protecting(NAT *{ sort Nat -> AId })
}

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

  bop button : Atm -> Button            -- projection
  bop card : Atm -> Card                -- projection
  bop request : Atm -> Request          -- projection
  bop input : Atm -> Input              -- projection
  bop output : Atm -> Output            -- projection

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
