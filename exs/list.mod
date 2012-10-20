-- FILE: /home/diacon/LANG/Cafe/prog/list.mod
-- CONTENTS: ADT specification of lists featuring an induction proof
-- AUTHOR: Razvan Diaconescu
-- DIFFICULTY: *

-- lists of naturals
mod! LIST-NAT {
  protecting(NAT)

  [ NList < List ]

  op nil : -> List
  op _._ : Nat List -> NList
  op car_ : NList -> Nat
  op cdr_ : NList -> List

  var L : List
  var N : Nat

  eq car (N . L) = N .
  eq cdr (N . L) = L .
}

-- lists with append function
mod! LISTA {
  protecting(LIST-NAT)
  
  op _+_ : List List -> List

  eq nil + L:List = L .
  eq (N:Nat . L:List) +  L':List = (N . (L + L')) .
}

--> proof of associativity of append (_+_)
open LISTA .
  ops l l' l'' :  -> List .
  ops m n p :  -> Nat .
--> base case
red nil + (l + l') == (nil + l) + l' .
--> induction hypothesis
eq l + (l' + l'') = (l + l') + l'' .
--> conclusion
red (n . l) + (l' + l'') == ((n . l) + l') + l'' .
close

--
eof
--
$Id: list.mod,v 1.1.1.1 2003-06-19 08:30:10 sawada Exp $
