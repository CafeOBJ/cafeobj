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
eq [*.s]: ackn(sender a) = send .     
eq [2'.t]: empty?(put(ch1 a, << msg ; b >>)) = true .   ** if *.s
eq [2'.f]: empty?(put(ch1 a, << msg ; b >>)) = false .  ** if *.s
eq [*.r]: ackn(sender a) = rec .
eq [4.t]: empty?(ch2 a) = true .                        ** if *.r            
eq [4.f]: empty?(ch2 a) = false .                       ** if *.r   
eq [4.f]: get(ch2 a) =  not b .                         ** if *.r 
eq [*.r]: ackn(receiver a) = rec .    
eq [*.s]: ackn(receiver a) = send .       
eq [4'.f]: empty?(put(ch2 a, not b)) = false .          ** if *.s
eq [4'.t]: empty?(put(ch2 a, not b)) = true .           ** if *.s


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

--> lemma 2 case 1
open LEMMA2

-- hyp
 eq [*.s] : ackn(sender a) = send . 
** eq [1.r] : ackn(sender a) = rec .
** eq [1.r] : ackn(m(sender a)) = send .     
** eq [4.t] : empty?(ch2 a) = true .                        ** if 1.r            
** eq [4.f] : empty?(ch2 a) = false .                       ** if 1.r   
** eq [4.f] : get(ch2 a) = not b .                          ** if 1.r      
 eq [2'.t] : empty?(put(ch1 a, << msg ; b >>)) = true .   ** if *.s
** eq [2'.f] : empty?(put(ch1 a, << msg ; b >>)) = false .  ** if *.s
** eq [*.r] : ackn(receiver a) = rec .
 eq [*.s] : ackn(receiver a) = send .
 eq [4'.f] : empty?(put(ch2 a, not b)) = false .          ** if *.s
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
 red get(ch2 m(a)) == (not b) .             --> it should be true if 4'.f
close


--> lemma 2 case 2
open LEMMA2

-- hyp
 eq [*.s] : ackn(sender a) = send .
** eq [*.r] : ackn(sender a) = rec . 
** eq [4.t] : empty?(ch2 a) = true .                        ** if *.r            
** eq [4.f] : empty?(ch2 a) = false .                       ** if *.r   
** eq [4.f] : get(ch2 a) = not b .                          ** if *.r      
 eq [2'.t] : empty?(put(ch1 a, << msg ; b >>)) = true .   ** if *.s
** eq [2'.f] : empty?(put(ch1 a, << msg ; b >>)) = false .  ** if *.s
** eq [*.r] : ackn(receiver a) = rec .     
 eq [*.s] : ackn(receiver a) = send .       
** eq [4'.f] : empty?(put(ch2 a, not b)) = false .          ** if *.s
 eq [4'.t] : empty?(put(ch2 a, not b)) = true .           ** if *.s


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



--> lemma 2 case 3
open LEMMA2

-- hyp
 eq [*.s] : ackn(sender a) = send .
** eq [*.r] : ackn(sender a) = rec .     
** eq [4.t] : empty?(ch2 a) = true .                        ** if *.r            
** eq [4.f] : empty?(ch2 a) = false .                       ** if *.r   
** eq [4.f] : get(ch2 a) = not b .                          ** if *.r      
** eq [2'.t] : empty?(put(ch1 a, << msg ; b >>)) = true .   ** if *.s
 eq [2'.f] : empty?(put(ch1 a, << msg ; b >>)) = false .  ** if *.s
** eq [*.r] : ackn(receiver a) = rec .       
 eq [*.s] : ackn(receiver a) = send .      
 eq [4'.f] : empty?(put(ch2 a, not b)) = false .          ** if *.s
** eq [4'.t] : empty?(put(ch2 a, not b)) = true .           ** if *.s


-- conclusion
red flag(sender m(a)) == b .                  --> it should be true
red  1* msg-send(sender m(a)) == msg .        --> it should be true
red msg-rec(sender m(a)) == (not b) .         --> it should be true
 red get(ch1 m(a)) == << msg ; b >> .       --> it should be true if 2'.f
red flag(receiver m(a)) == (not b) .          --> it should be true
red msg-send(receiver m(a)) == (not b) .      --> it should be true
red 1* msg-rec(receiver m(a)) == msg' .       --> it should be true
red 2* msg-rec(receiver m(a)) == (not b) .    --> it should be true
 red get(ch2 m(a)) == (not b) .             --> it should be true if 4'.f
close


--> lemma 2 case 4
open LEMMA2

-- hyp
 eq [*.s] : ackn(sender a) = send .
** eq [*.r] : ackn(sender a) = rec .
** eq [*.r] : ackn(m(sender a)) = send .     
** eq [4.t] : empty?(ch2 a) = true .                        ** if *.r            
** eq [4.f] : empty?(ch2 a) = false .                       ** if *.r   
** eq [4.f] : get(ch2 a) = not b .                          ** if *.r      
** eq [2'.t] : empty?(put(ch1 a, << msg ; b >>)) = true .   ** if *.s
 eq [2'.f] : empty?(put(ch1 a, << msg ; b >>)) = false .  ** if *.s
** eq [*.r] : ackn(receiver a) = rec .        
 eq [*.s] : ackn(receiver a) = send .     
** eq [4'.f] : empty?(put(ch2 a, not b)) = false .          ** if *.s
 eq [4'.t] : empty?(put(ch2 a, not b)) = true .           ** if *.s


-- conclusion
red flag(sender m(a)) == b .                  --> it should be true
red  1* msg-send(sender m(a)) == msg .        --> it should be true
red msg-rec(sender m(a)) == (not b) .         --> it should be true
 red get(ch1 m(a)) == << msg ; b >> .       --> it should be true if 2'.f
red flag(receiver m(a)) == (not b) .          --> it should be true
red msg-send(receiver m(a)) == (not b) .      --> it should be true
red 1* msg-rec(receiver m(a)) == msg' .       --> it should be true
red 2* msg-rec(receiver m(a)) == (not b) .    --> it should be true
** red get(ch2 m(a)) == (not b) .             --> it should be true if 4'.f
close

--> lemma 2 case 5
open LEMMA2

-- hyp
** eq [*.s] : ackn(sender a) = send .
 eq [*.r] : ackn(sender a) = rec .   
 eq [4.t] : empty?(ch2 a) = true .                        ** if *.r            
** eq [4.f] : empty?(ch2 a) = false .                       ** if *.r   
** eq [4.f] : get(ch2 a) = not b .                          ** if *.r      
** eq [2'.t] : empty?(put(ch1 a, << msg ; b >>)) = true .   ** if *.s
** eq [2'.f] : empty?(put(ch1 a, << msg ; b >>)) = false .  ** if *.s
 eq [*.r] : ackn(receiver a) = rec .   
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


--> lemma 2 case 6
open LEMMA2

-- hyp
** eq [*.s] : ackn(sender a) = send .
 eq [*.r] : ackn(sender a) = rec .    
** eq [4.t] : empty?(ch2 a) = true .                        ** if *.r            
 eq [4.f] : empty?(ch2 a) = false .                       ** if *.r   
 eq [4.f] : get(ch2 a) =  not b .                         ** if *.r      
** eq [2'.t] : empty?(put(ch1 a, << msg ; b >>)) = true .   ** if *.s
** eq [2'.f] : empty?(put(ch1 a, << msg ; b >>)) = false .  ** if *.s
 eq [*.r] : ackn(receiver a) = rec .      
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
