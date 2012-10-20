-- ---------------------------------------------------
-- Some notations:
--      sndr?(A,msg,b) <=>
--              flag(sender A) = b and 
--              1* msg-send(sender A) = msg and
--              msg-rec(sender A) = not b
--
--      sndr-send?(A,msg,b) <=>
--              ackn(sender A) = send and 
--              sndr?(A,msg,b)
--
--      sndr-rec?(A,msg,b) <=>
--              ackn(sender A) = rec and 
--              sndr?(A,msg,b)
--
--      rcvr?(A,msg,b) <=>
--              flag(receiver A) =  b and 
--              msg-send(sender A) = b and
--              msg-rec(sender A) =  << msg ; b >>
--
--      rcvr-send?(A,msg,b) <=>
--              ackn(receiver A) = send and
--              rcvr?(A,msg,b)
--
--      rcvr-rec?(A,msg,b) <=>
--              ackn(receiver A) = rec and
--              rcvr?(A,msg,b)
-- ---------------------------------------------------



-- ----------------------------------------------------
-- Remark. Some of the following lemmas requires case analysis. To obtain such a case
--         we have to uncomment some hypothesis and, eventually, some conclusions.
--         Here are the uncommenting rules:
--          1. The hyp. "X.f" will be uncommented/commented iff 
--             the hyp. "X.t" are commented/uncommented, where "X" is the prefix
--             of an equation label.
--          2. The hyp. "*.r" will be uncommented/commented iff 
--             the hyp. "*.s" are commented/uncommented.
--          3. All hyp. with the same label have the same uncomment/comment
--             state at a given moment.
--          4. A hyp. with a comment  "if y" will be uncommented/commented
--             only if the hyp. with the label "[y]"  are uncommented/commented.
--          5. Conventions for labels:
--              2 for "ch1 a"
--              4 for "ch2 a"
--              2' for "ch1 m(a)"
--              4' for "ch2 m(a)"
--              * for both "sender a" and "receiver a"  
--              t for empty?(x) = true, x = 2,2',4,4'
--              f for empty?(x) = false, x = 2,2',4,4'
--              s for ackn(*) = send
--              r for ackn(*) = rec
-- -----------------------------------------------

-- ------------------------------------------------
-- Lemma 1 (The synchronization between SENDER and CH1 is correct):
--          If
--              ackn(sender A) = send 
--          Then 
--              ch1 m(a)) = put(ch1 A, msg-send(sender A))
-- ------------------------------------------------
--> lemma 1
open ABP
op a   : -> Abp .
op msg : -> Msg .
op b   : -> Bool .

eq msg-send(sender a) = << msg ; b >> .
eq ackn(sender a) = send . 

red ch1 m(a) == put(ch1 a, << msg ; b >>) . --> it should be true
close

-- ------------------------------------------------
-- Lemma 2 (SENDER and RECEIVER  do not change their states while 
--          CH1 is loosing a message): 
--   If 
--     sndr?(A, msg, b) and
--     empty?(ch1 A) and
--     rcvr?(A, msg', not b) and
--     (empty?(ch2 A) or (get(ch2 A) = not b))
--   then
--     sndr?(m(A), msg, b) and
--     (empty?(ch1 m(A)) or (get(ch1 m(A)) = << msg ; b >>)) and 
--     rcvr?(m(A), msg', not b) and
--     (empty?(ch2 m(A)) or (get(ch2 m(A)) = not b))
-- ------------------------------------------------

mod LEMMA2 {
  protecting (ABP)
  op a    : -> Abp
  op msg  : -> Msg
  op msg' : -> Msg
  op b    : -> Bool


  eq flag(sender a) = b .
  eq msg-send(sender a) = << msg ; b >> .
  eq msg-rec(sender a) = (not b) .
  eq empty?(ch1 a) = true .
  eq flag(receiver a) = (not b) .
  eq msg-send(receiver a) = (not b) .
  eq msg-rec(receiver a) = << msg' ; not b >> .
}

--> lemma 2: case analysis (there are 6 cases)

open LEMMA2
-- hyp
** eq [*.s] : ackn(sender a) = send .     
** eq [2'.t] : empty?(put(ch1 a, << msg ; b >>)) = true .   ** if *.s
** eq [2'.f] : empty?(put(ch1 a, << msg ; b >>)) = false .  ** if *.s
** eq [*.r] : ackn(sender a) = rec .
** eq [4.t] : empty?(ch2 a) = true .                        ** if *.r            
** eq [4.f] : empty?(ch2 a) = false .                       ** if *.r   
** eq [4.f] : get(ch2 a) =  not b .                         ** if *.r 
** eq [*.r] : ackn(receiver a) = rec .    
** eq [*.s] : ackn(receiver a) = send .       
** eq [4'.f] : empty?(put(ch2 a, not b)) = false .          ** if *.s
** eq [4'.t] : empty?(put(ch2 a, not b)) = true .           ** if *.s


-- conclusion
red flag(sender m(a)) == b .                  --> it should be true
red  1* msg-send(sender m(a)) == msg .        --> it should be true
red msg-rec(sender m(a)) == (not b) .         --> it should be true
** red get(ch1 m(a)) == << msg ; b >> .       --> it should be true if 2'.f
red flag(receiver m(a)) == (not b) .          --> it should be true
red msg-send(receiver m(a)) == (not b) .      --> it should be true
red 1* msg-rec(receiver m(a)) == msg' .       --> it should be true
red 2* msg-rec(receiver m(a)) == (not b) .    --> it should be true
** red get(ch2 m(a)) == (not b) .             --> it should be true if 4'.f
close


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



-- ------------------------------------------------
-- Lemma 4 (The synchronization between RECEIVER and CH2 is correct): 
--          If 
--              ackn(receiver A) = send and
--              not empty?(ch2 m(A))
--          Then 
--              ch2 m(a)) = put(ch1 A, msg-sent(receiver a))
-- ------------------------------------------------
--> lemma 4
open ABP
op a : -> Abp .
op b : -> Bool .

eq msg-send(receiver a) = b .
eq ackn(receiver a) = send . 

red ch2 m(a) == put(ch2 a, b) . --> it should be true
close


-- ------------------------------------------------
-- Lemma 5 (SENDER and RECEIVER  do not change their states while 
--          CH2 is loosing a message): 
--   If 
--     sndr?(A, msg, b) and
--     (empty?(ch1 A) or get(ch1 A) = << msg ; b >>) and
--     rcvr?(A, msg, b) and
--     empty?(ch2 A)
--   then
--     sndr?(m(A), msg, b) and
--     (empty?(ch1 m(A)) or (get(ch1 m(A)) = << msg ; b >>)) and 
--     rcvr?(m(A), msg, b) and
--     (empty?(ch2 m(A)) or (get(ch2 m(A)) = b))
-- ------------------------------------------------

mod LEMMA5 {
  protecting (ABP)
  op a    : -> Abp
  op msg  : -> Msg
  op msg' : -> Msg
  op b    : -> Bool


  eq flag(sender a) = b .
  eq msg-send(sender a) = << msg ; b >> .
  eq msg-rec(sender a) = (not b) .
  eq flag(receiver a) = b .
  eq msg-send(receiver a) = b .
  eq msg-rec(receiver a) = << msg ; b >> .
  eq empty?(ch2 a) = true .
}

--> lemma 5: case analysis (there are 6 cases)

open LEMMA5

-- hyp
** eq [*.r] : ackn(sender a) = rec .   
** eq [*.s] : ackn(sender a) = send .    
** eq [2'.t] : empty?(put(ch1 a, << msg ; b >>)) = true .   ** if *.s
** eq [2'.f] : empty?(put(ch1 a, << msg ; b >>)) = false .  ** if *.s
** eq [*.r] : ackn(receiver a) = rec .    
** eq [2.t] : empty?(ch1 a) = true .                        ** if *.r            
** eq [2.f] : empty?(ch1 a) = false .                       ** if *.r   
** eq [2.f] : get(ch1 a) = << msg ; b >> .                  ** if *.r      
** eq [*.s] : ackn(receiver a) = send .  
** eq [4'.f] : empty?(put(ch2 a, b)) = false .             ** if *.s
** eq [4'.t] : empty?(put(ch2 a, b)) = true .              ** if *.s


-- conclusion
red flag(sender m(a)) == b .                  --> it should be true
red  1* msg-send(sender m(a)) == msg .        --> it should be true
red msg-rec(sender m(a)) == (not b) .         --> it should be true
** red get(ch1 m(a)) == << msg ; b >> .       --> it should be true if 2'.f
red flag(receiver m(a)) ==  b .               --> it should be true
red msg-send(receiver m(a)) ==  b .           --> it should be true
red 1* msg-rec(receiver m(a)) == msg .        --> it should be true
red 2* msg-rec(receiver m(a)) ==  b .         --> it should be true
** red get(ch2 m(a)) == b .                   --> it should be true if 4'.f
close



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



-- -----------------------------------------------------
-- Theorem 1. Suppose
--              flag(sender A) = not flag(receiver A) and that
--              CH1 is fair. 
--          Then there is a natural number n such that 
--              mm(A) = m^n(A) 
--          and
--              flag(sender mm(A)) = flag(receiver mm(A)).
--          Moreover msg-send(sender A) = msg-rec(receiver mm(A)).
-- ------------------------------------------------------
-- Let n be the least natural number such that empty?(ch1 m^{n-1}(A)) = false
-- and ackn(m^{n-1}(receiver A)) = rec. The existence of such a n is given by the
-- fairness assumption . Applying lemma 2 we get 
--    flag(sender m^i(A)) = flag(sender A) and
--    flag(receiver m^i(A)) = flag(receiver A) and
--    msg-send(sender m^i(A)) = msg-send(sender A)
-- for i = 0,...,n-1.
-- Hence 
--    flag(sender m^i(A)) = not flag(receiver m^i(A))
-- for i = 0,...,n-1.
-- Applying lemma 3 we get
--    flag(receiver m^n(A)) = not flag(receiver m^{n-1}(A)) and
--    flag(sender m^n(A)) = flag(sender m^{n-1}(A)) and
--    msg-rec(receiver m^n(A)) = msg-send(sender m^{n-1}(A))
-- and hence 
--    flag(receiver m^n(A)) = flag(sender m^n(A)) and
--     msg-send(sender A) = msg-rec(receiver mm(A)) .
-- The equality mm(A) = m^(A) follows now from the definition
-- of mm.
-- ------------------------------------------------------

-- -----------------------------------------------------
-- Theorem 2. Suppose
--              flag(sender A) = flag(receiver A) and that
--              CH2 is fair. 
--          Then there is a natural number n such that 
--              mm(A) = m^n(A) 
--          and
--              flag(sender mm(A)) = not flag(receiver mm(A)).
-- ------------------------------------------------------
-- Let n be the least natural number such that empty?(ch2 m^{n-1}(A)) = false
-- and ackn(m^{n-1}(sender A)) = rec. The existence of such a n is given by the
-- fairness assumption . Applying lemma 5 we get 
--    flag(sender m^i(A)) = flag(sender A) and
--    flag(receiver m^i(A)) = flag(receiver A)
-- for i = 0,...,n-1.
-- Hence 
--    flag(sender m^i(A)) = flag(receiver m^i(A))
-- for i = 0,...,n-1.
-- Applying lemma 6 we get
--    flag(receiver m^n(A)) = flag(receiver m^{n-1}(A))
--    flag(sender m^n(A)) = not flag(sender m^{n-1}(A))
-- and hence flag(sender m^n(A)) = not flag(receiver m^n(A)).
-- The equality mm(A) = m^(A) follows now from the definition
-- of mm.
-- ------------------------------------------------------



-- ------------------------------------------------------
-- Theorem 3. XABP refines SRP.
-- ------------------------------------------------------
-- The proof follows by applying Theorem 1 and Theorem 2.
-- ------------------------------------------------------

-- ------------------------------------------------------
-- Corollary. ABP refines SRP.
-- ------------------------------------------------------
