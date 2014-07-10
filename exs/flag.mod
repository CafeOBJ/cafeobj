-- FILE: /home/diacon/LANG/Cafe/prog/flag.mod
-- CONTENTS: behavioural specification of a flag object featuring
--           object inheritance
-- AUTHOR: Joseph Goguen
-- DIFFICULTY: **

mod NAT' {
  [ Nat ]

  op 0 : -> Nat      
  op s : Nat -> Nat  
}

set accept =*= proof on
-- flag object
mod* FLAG {

  *[ Flag ]*

  bops (up_) (dn_) (rev_) : Flag -> Flag  -- methods
  bop up?_ : Flag -> Bool                 -- attribute

  var F : Flag
  eq up? up F = true .
  eq up? dn F = false .
  eq up? rev F = not up? F .
}

-- proof of (rev rev f) =b= f  
open FLAG .
  var B : Bool
  eq not not B = B .

  op f : -> Flag .

  red (rev rev f) =*= f .
close

-- flag object with counter inheriting the simple flag object
mod* CFLAG {
  protecting(NAT' + FLAG)
  
  *[ CFlag < Flag ]*          -- class inheritance

  op newc : -> CFlag
  bops (up_) (dn_) (rev_) : CFlag -> CFlag
  bop count_ : CFlag -> Nat
  bop up?_ : CFlag -> Nat

  var C : CFlag
  eq count newc = 0 .
  eq up? newc = false .
  eq count up  C = s (count C) .
  eq count dn  C = s (count C) .
  eq count rev C = count C .
}
--
set accept =*= proof off
--
eof
--
$Id: flag.mod,v 1.1.1.1 2003-06-19 08:30:10 sawada Exp $
