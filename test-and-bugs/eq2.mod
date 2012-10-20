-- *****************
-- **Problem 2.**
-- *****************
-- Here is an example of using record terms in equations:

-- ****************** MY TEST FILE*************
mod TEST
{
  protecting (NAT)
  record Ab {
    a : Nat
    b : Nat
  }
  op one-one : -> Ab
  eq one-one = Ab { a = 1, b = 1 } .
}
open TEST
red a(one-one) .  **> should be 1
red a(Ab { a = 1, b = 1 }) . **> should be 1
-- ***************END OF TEST FILE**********

eof
