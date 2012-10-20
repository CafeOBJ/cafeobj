
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

