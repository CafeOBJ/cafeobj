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


--> lemma 5: case 1

open LEMMA5

-- hyp
** eq [*.r] : ackn(sender a) = rec .     
 eq [*.s] : ackn(sender a) = send .    
 eq [2'.t] : empty?(put(ch1 a, << msg ; b >>)) = true .   ** if *.s
** eq [2'.f] : empty?(put(ch1 a, << msg ; b >>)) = false .  ** if *.s
** eq [*.r] : ackn(receiver a) = rec .    
** eq [2.t] : empty?(ch1 a) = true .                        ** if *.r            
** eq [2.f] : empty?(ch1 a) = false .                       ** if *.r   
** eq [2.f] : get(ch1 a) = << msg ; b >> .                  ** if *.r      
 eq [*.s] : ackn(receiver a) = send .               
 eq [*.s] : ackn(m(receiver a)) = rec .        
 eq [4'.f] : empty?(put(ch2 a, b)) = false .             ** if *.s
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
 red get(ch2 m(a)) == b .                  --> it should be true if 4'.f
close



--> lemma 5: case 2

open LEMMA5

-- hyp
** eq [*.r] : ackn(sender a) = rec .  
 eq [*.s] : ackn(sender a) = send .    
 eq [2'.t] : empty?(put(ch1 a, << msg ; b >>)) = true .   ** if *.s
** eq [2'.f] : empty?(put(ch1 a, << msg ; b >>)) = false .  ** if *.s
** eq [*.r] : ackn(receiver a) = rec .   
** eq [2.t] : empty?(ch1 a) = true .                        ** if *.r            
** eq [2.f] : empty?(ch1 a) = false .                       ** if *.r   
** eq [2.f] : get(ch1 a) = << msg ; b >> .                  ** if *.r      
 eq [*.s] : ackn(receiver a) = send .     
** eq [4'.f] : empty?(put(ch2 a, b)) = false .             ** if *.s
 eq [4'.t] : empty?(put(ch2 a, b)) = true .              ** if *.s


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


--> lemma 5: case 3

open LEMMA5

-- hyp
** eq [*.r] : ackn(sender a) = rec .
 eq [*.s] : ackn(sender a) = send .    
** eq [2'.t] : empty?(put(ch1 a, << msg ; b >>)) = true .   ** if *.s
 eq [2'.f] : empty?(put(ch1 a, << msg ; b >>)) = false .  ** if *.s
** eq [*.r] : ackn(receiver a) = rec .    
** eq [2.t] : empty?(ch1 a) = true .                        ** if *.r            
** eq [2.f] : empty?(ch1 a) = false .                       ** if *.r   
** eq [2.f] : get(ch1 a) = << msg ; b >> .                  ** if *.r      
 eq [*.s] : ackn(receiver a) = send .       
 eq [4'.f] : empty?(put(ch2 a, b)) = false .             ** if *.s
** eq [4'.t] : empty?(put(ch2 a, b)) = true .              ** if *.s


-- conclusion
red flag(sender m(a)) == b .                  --> it should be true
red  1* msg-send(sender m(a)) == msg .        --> it should be true
red msg-rec(sender m(a)) == (not b) .         --> it should be true
 red get(ch1 m(a)) == << msg ; b >> .       --> it should be true if 2'.f
red flag(receiver m(a)) ==  b .               --> it should be true
red msg-send(receiver m(a)) ==  b .           --> it should be true
red 1* msg-rec(receiver m(a)) == msg .        --> it should be true
red 2* msg-rec(receiver m(a)) ==  b .         --> it should be true
 red get(ch2 m(a)) == b .                  --> it should be true if 4'.f
close



--> lemma 5: case 4

open LEMMA5

-- hyp
** eq [*.r] : ackn(sender a) = rec .
 eq [*.s] : ackn(sender a) = send .     
** eq [2'.t] : empty?(put(ch1 a, << msg ; b >>)) = true .   ** if *.s
 eq [2'.f] : empty?(put(ch1 a, << msg ; b >>)) = false .  ** if *.s
** eq [*.r] : ackn(receiver a) = rec .     
** eq [2.t] : empty?(ch1 a) = true .                        ** if *.r            
** eq [2.f] : empty?(ch1 a) = false .                       ** if *.r   
** eq [2.f] : get(ch1 a) = << msg ; b >> .                  ** if *.r      
 eq [*.s] : ackn(receiver a) = send .       
** eq [4'.f] : empty?(put(ch2 a, b)) = false .             ** if *.s
 eq [4'.t] : empty?(put(ch2 a, b)) = true .              ** if *.s


-- conclusion
red flag(sender m(a)) == b .                  --> it should be true
red  1* msg-send(sender m(a)) == msg .        --> it should be true
red msg-rec(sender m(a)) == (not b) .         --> it should be true
 red get(ch1 m(a)) == << msg ; b >> .       --> it should be true if 2'.f
red flag(receiver m(a)) ==  b .               --> it should be true
red msg-send(receiver m(a)) ==  b .           --> it should be true
red 1* msg-rec(receiver m(a)) == msg .        --> it should be true
red 2* msg-rec(receiver m(a)) ==  b .         --> it should be true
** red get(ch2 m(a)) == b .                   --> it should be true if 4'.f
close



--> lemma 5: case 5

open LEMMA5

-- hyp
 eq [*.r] : ackn(sender a) = rec .
** eq [*.s] : ackn(sender a) = send .     
** eq [2'.t] : empty?(put(ch1 a, << msg ; b >>)) = true .   ** if *.s
** eq [2'.f] : empty?(put(ch1 a, << msg ; b >>)) = false .  ** if *.s
 eq [*.r] : ackn(receiver a) = rec .    
 eq [2.t] : empty?(ch1 a) = true .                        ** if *.r            
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


--> lemma 5: case 6

open LEMMA5

-- hyp
 eq [*.r] : ackn(sender a) = rec .
** eq [*.s] : ackn(sender a) = send .     
** eq [2'.t] : empty?(put(ch1 a, << msg ; b >>)) = true .   ** if *.s
** eq [2'.f] : empty?(put(ch1 a, << msg ; b >>)) = false .  ** if *.s
 eq [*.r] : ackn(receiver a) = rec .    
** eq [2.t] : empty?(ch1 a) = true .                        ** if *.r            
 eq [2.f] : empty?(ch1 a) = false .                       ** if *.r   
 eq [2.f] : get(ch1 a) = << msg ; b >> .                  ** if *.r      
** eq [*.s] : ackn(receiver a) = send .               
** eq [*.s] : ackn(m(receiver a)) = rec .        
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

