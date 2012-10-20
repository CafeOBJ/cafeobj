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
