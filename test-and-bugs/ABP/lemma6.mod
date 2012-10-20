-- ------------------------------------------------
-- Lemma 6 (If CH2 does not loose an acknowledgement then SENDVER receive it  correctly
--          and RECEIVER does not change its state):
--          If 
--              sndr-rec?(A, msg, b) and
--              not empty?(ch2 A) and get(ch2 A) =  b and
--              rcvr-rec?(A, msg, b)
--          Then 
--              sndr-send?(m(A), msg', not b) and
--              rcvr-send?(m(A), msg, b) 
-- ------------------------------------------------
mod LEMMA6 {
  protecting (ABP)
  op a    : -> Abp
  op msg  : -> Msg
  op msg' : -> Msg
  op b    : -> Bool


  eq ackn(sender a) = rec .
  eq flag(sender a) = b .
  eq msg-send(sender a) = << msg ; b >> .
  eq empty?(ch2 a) = false .
  eq get(ch2 a) =  b .
  eq ackn(receiver a) = rec .
  eq flag(receiver a) = b .
  eq msg-rec(receiver a) = << msg ;  b >> .   
  eq not not b = b .                            -- a lemma in BOOL
}

--> lemma 6: case analysis (there are 2 cases)
open LEMMA6

-- hyp
** eq [2.f] : empty?(ch1 a) = false .
** eq [2.f] : get(ch1 a) = << msg ; b >> .  
** eq [2.t] : empty?(ch1 a) = true .  

-- conclusion
red flag(sender m(a)) == (not b) .            --> it should be true
red msg-rec(sender m(a)) == b .               --> it should be true
red flag(receiver m(a)) ==  b .               --> it should be true
red 1* msg-rec(receiver m(a)) == msg .        --> it should be true
red 2* msg-rec(receiver m(a)) == b .          --> it should be true
close

--> lemma 6: case 1
open LEMMA6

-- hyp
 eq [2.f] : empty?(ch1 a) = false .
 eq [2.f] : get(ch1 a) = << msg ; b >> .  
** eq [2.t] : empty?(ch1 a) = true .  

-- conclusion
red flag(sender m(a)) == (not b) .            --> it should be true
red msg-rec(sender m(a)) == b .               --> it should be true
red flag(receiver m(a)) ==  b .               --> it should be true
red 1* msg-rec(receiver m(a)) == msg .        --> it should be true
red 2* msg-rec(receiver m(a)) == b .          --> it should be true
close

--> lemma 6: case 2
open LEMMA6

-- hyp
** eq [2.f] : empty?(ch1 a) = false .
** eq [2.f] : get(ch1 a) = << msg ; b >> .  
 eq [2.t] : empty?(ch1 a) = true .  

-- conclusion
red flag(sender m(a)) == (not b) .            --> it should be true
red msg-rec(sender m(a)) == b .               --> it should be true
red flag(receiver m(a)) ==  b .               --> it should be true
red 1* msg-rec(receiver m(a)) == msg .        --> it should be true
red 2* msg-rec(receiver m(a)) == b .          --> it should be true
close

