-- ====================================================================
-- ====================================================================
-- counter
mod! COUNTER {
 [ Counter ]
 op 0 : -> Counter .
 op s_ : Counter -> Counter .
}

mod! READERS-WRITERS {
   pr(COUNTER)
   [ Config ]
   op <_,_> : Counter Counter -> Config { constr } .
   -- < readers, writers >
   vars R W : Counter .
   -- possible transitions in transition rules
   trans [+w] : < 0 , 0 > => < 0 , s 0 > .
   trans [+r] : < R , 0 > => < s R , 0 > .
   trans [-r] : < s R , W > => < R , W > .
   trans [-w] : < R, s W > => < R, W > .
}

mod! RW-INV {
   pr(READERS-WRITERS)
   vars R W : Counter .
   -- mutual exclusion invariant
   pred mutualEx_ : Config .
   eq mutualEx < 0 , W > = true .
   eq mutualEx < R , 0 > = true .
   eq mutualEx < s R , s W > = false .
   -- only one writer invariant
   pred oneWt_ : Config .
   eq oneWt < R, 0 > = true .
   eq oneWt < R, s 0 > = true .
   eq oneWt < R, s s W > = false .
   -- both invariants
   pred mutualExAndOneWt_ : Config .
   eq mutualExAndOneWt < R, W > = (mutualEx < R, W >) and (oneWt < R, W >) .
 }

eof
***
open RW-INV
red < 0 , 0 > =(10,2)=>* C:Config .
close

と入力すると，

%RW-INV> red < 0 , 0 > =(10,2)=>* C:Config .
-- reduce in %RW-INV : ((< 0 , 0 >) = ( 10 , 2 ) =>* C):Bool

** Found [state 0] (< 0 , 0 >):Config
   { C:Config |-> (< 0 , 0 >) }

** Found [state 1] (< 0 , (s 0) >):Config
   { C:Config |-> (< 0 , (s 0) >) }

** Found [state 2] (< (s 0) , 0 >):Config
   { C:Config |-> (< (s 0) , 0 >) }

** Found [state 3] (< 0 , 0 >):Config
   { C:Config |-> (< 0 , 0 >) }

** Found [state 4] (< (s (s 0)) , 0 >):Config
   { C:Config |-> (< (s (s 0)) , 0 >) }
-- reached to the max depth.
(false):Bool
(0.000 sec for parse, 10 rewrites(0.000 sec), 10 matches, 4 memo hits)
%RW-INV>

とSystemが返答しますが，これには以下の疑問点があります．

１．答えが見つかったのに，(false):Bool　と返している．
(先日の議論で答えが一つでも見つかれば true とする，としたと理解しています)

２．** Found [state 0] (< 0 , 0 >):Config
   { C:Config |-> (< 0 , 0 >) }
と
** Found [state 3] (< 0 , 0 >):Config
   { C:Config |-> (< 0 , 0 >) }
で同じConfigを返している．

-- ====================================================================
-- ====================================================================
