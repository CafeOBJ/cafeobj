-- Date: Fri, 22 Aug 1997 13:11:19 +0300
-- From: Diaconescu Razvan <diacon@stoilow.imar.ro>
-- Message-Id: <9708221011.AA02114@stoilow.imar.ro>
-- To: sawada@sra.co.jp
-- Subject:  still a bug in parsing beh equations 
-- Cc: kokichi@jaist.co.jp, nakagawa@sra.co.jp, s_iida@sra.co.jp
-- Content-Type: text
-- Content-Length: 2846
--
-- Dear Toshimi,
--
-- Unfortunately there is still a bug in parsing beqs related to
-- constants of hidden sorts. An operation : VSORT -> HSORT should be
-- regarded as a "parameterised" constants, so it is OK in beh
-- sentences.
--
-- These are fragments from a specification of a telephone system:

-- --------------------------------------------------------------
-- telephone number
-- --------------------------------------------------------------
mod* NUMBER {
  protecting(NAT * { sort Nat -> Number })

  [ Number < Number* ]

  op tel-not-exist : -> Number*   -- for errors
}

-- --------------------------------------------------------------
-- duration of calls (unit)
-- --------------------------------------------------------------
mod! UNIT {
  protecting(NAT * { sort Nat -> Unit })

  op tel-not-exist : -> Unit   -- for errors
  eq tel-not-exist = 0 .
}

-- --------------------------------------------------------------
-- telephone (client)
-- --------------------------------------------------------------
mod* TELEPHONE {
  protecting(NUMBER + UNIT)

  *[ Tel ]*

  op tel-not-exist : -> Tel         -- for errors
  op init-tel : Number  -> Tel      -- initial state
  bop call : Unit Tel -> Tel        -- method
  bop clear : Tel -> Tel            -- method
  bop unit : Tel -> Unit            -- attribute
  bop number : Tel -> Number*        -- attribute

** ...........................
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

** .................................
  bceq tel(NUM, add-tel(NUM', TS)) = init-tel(NUM) if NUM == NUM' . 
** ...........................................................
}
-- --------------------------------------------
eof
-- I get the following:
--
-- [Error]: behavioural axiom must be constructed from terms of behavioural operators.*
-- failed to evaluate the form:
-- axiom declaration(equation): 
--  lhs = (tel ( NUM , add-tel ( NUM' , TS ) ))
--  rhs = (init-tel ( NUM ))
--  condition = (NUM == NUM')

** returning to top level

-- I think the problem is that init-tel is maybe not considered a bop,
-- but it is a "parameterised" constant, so it should be OK.

-- The principle is very simple, any operation in beh sentences which has
-- h. sorts as arguments should be declared a bop. That's all. Not the
-- coarity is important here but the arity.

-- Razvan
