-- ------------------------------------------------
-- Lemma 3 (If CH1 does not loose a new message then RECEIVER receives it  correctly
--          and SENDER does not change its state):
--          If 
--              sndr-rec?(A, msg, b) and
--              not empty?(ch1 A) and get(ch1 A) = << msg ; b >> and
--              rcvr-rec?(A, msg', not b)
--          Then 
--              sndr-send?(m(A), msg, b) and
--              rcvr-send?(m(A), msg, b) 
-- ------------------------------------------------
mod LEMMA3 {
  protecting (ABP)
  op a    : -> Abp
  op msg  : -> Msg
  op msg' : -> Msg
  op b    : -> Bool


  eq ackn(sender a) = rec .
  eq flag(sender a) = b .
  eq msg-send(sender a) = << msg ; b >> .
  eq msg-rec(sender a) = (not b) .
  eq empty?(ch1 a) = false .
  eq get(ch1 a) = << msg ; b >> .
  eq ackn(receiver a) = rec .
  eq flag(receiver a) = (not b) .
  eq msg-send(receiver a) = (not b) .
  eq msg-rec(receiver a) = << msg' ; not b >> .     
  eq not not b = b .                            -- a lemma in BOOL
}

--> lemma 3: case analysis (there are 2 cases)
open LEMMA3

-- hyp
** eq [4.f] : empty?(ch2 a) = false .
** eq [4.f] : get(ch2 a) = not b .  
** eq [4.t] : empty?(ch2 a) = true .


-- conclusion
red flag(sender m(a)) == b .                  --> it should be true
red  1* msg-send(sender m(a)) == msg .        --> it should be true
red msg-rec(sender m(a)) == (not b) .         --> it should be true
red flag(receiver m(a)) ==  b .               --> it should be true
red msg-send(receiver m(a)) ==  b .           --> it should be true
red 1* msg-rec(receiver m(a)) == msg .        --> it should be true
red 2* msg-rec(receiver m(a)) == b .          --> it should be true
close

--> lemma 3: case 1
open LEMMA3

-- hyp
 eq [4.f] : empty?(ch2 a) = false .
 eq [4.f] : get(ch2 a) = not b .  
** eq [4.t] : empty?(ch2 a) = true .


-- conclusion
red flag(sender m(a)) == b .                  --> it should be true
red  1* msg-send(sender m(a)) == msg .        --> it should be true
red msg-rec(sender m(a)) == (not b) .         --> it should be true
red flag(receiver m(a)) ==  b .               --> it should be true
red msg-send(receiver m(a)) ==  b .           --> it should be true
red 1* msg-rec(receiver m(a)) == msg .        --> it should be true
red 2* msg-rec(receiver m(a)) == b .          --> it should be true
close

--> lemma 3: case 2
open LEMMA3

-- hyp
** eq [4.f] : empty?(ch2 a) = false .
** eq [4.f] : get(ch2 a) = not b .  
 eq [4.t] : empty?(ch2 a) = true .


-- conclusion
red flag(sender m(a)) == b .                  --> it should be true
red  1* msg-send(sender m(a)) == msg .        --> it should be true
red msg-rec(sender m(a)) == (not b) .         --> it should be true
red flag(receiver m(a)) ==  b .               --> it should be true
red msg-send(receiver m(a)) ==  b .           --> it should be true
red 1* msg-rec(receiver m(a)) == msg .        --> it should be true
red 2* msg-rec(receiver m(a)) == b .          --> it should be true
close
