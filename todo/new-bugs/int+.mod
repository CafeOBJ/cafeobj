-- -*- Mode:CafeOBJ -*-
-- FILE: int*.mod
-- CONTENTS: a specification of integer with the operations of (_+_), (_*_) 
--           proof of commutativity and associativity of (_*_), 
--           together with distributed laws 
-- AUTHORS:  Kokichi Futatsugi
-- DIFFICULTY: ***

mod! BASIC-INT {
  [ Zero NzNat < Nat ]			-- Zero, Non Zero Naturals
  [ NgInt Zero < NpInt ]		-- Negative Integers
  [ NgInt Zero NpInt NzNat Nat < Int ]  -- Non Positive Integers

  op 0 : -> Zero
  op s_ : Nat -> NzNat
  op p_ : NpInt -> NgInt
  op s_ : Int -> Int
  op p_ : Int -> Int 

  eq (s (p (I:Int))) = I .
  eq (p (s (I:Int))) = I .
}

**> We already proved that _+_ is commutative and associative in
**> "int+.mod" file
**> So, we can assume the _+_ is commutative and associative 
**> in the following definition of _*_ over Int

mod! INT* {
  pr (BASIC-INT)
  op _+_ : Int Int -> Int {assoc comm id: 0}
  vars I J : Int 
  -- eq I + 0 = I .  -- we can omit this axiom because of "id: 0"
  eq I + s J = s(I + J) .
  eq I + p J = p(I + J) .

  op -_ : Int -> Int
  eq - 0 = 0 .
  eq - (s I) = p (- I) .
  eq - (p I) = s (- I) .

  op _*_ : Int Int -> Int
  eq 0 * J = 0 .
  eq (s I) * J = J + (I * J) .
  eq (p I) * J = (- J) + (I * J) .
}

**  ------------------------------------
**> the proof of commutativity of (_*_)
**  ------------------------------------

**> First, prove Lemma-4: i * 0 = 0, by induction on i

open INT*
op i : -> Int .
**> base case (i = 0) : 0 * 0 = 0 
red 0 * 0 == 0 .
**> induction hypothesis
eq  i * 0 = 0 .
**> induction step
red (s i) * 0 == 0 .
red (p i) * 0 == 0 .
**> should be true 
**> QED for Lemma 4
close

**> Secondly prove Lemma 5: i * (s j) = i + (i * j), 
**> again by induction on i
open INT*
ops i j : -> Int .
**> base case (i = 0) : 0 * (s j) = 0 + (0 * j) .
red 0 * (s j) == 0 + (0 * j) .

**> induction hypothesis
--> eq  i * (s j) = i + (i * j) .
eq  i * (s j) = i + (i * j) .

**> induction step
red (s i) * (s j) == (s i) + ((s i) * j) .
red (p i) * (s j) == (p i) + ((p i) * j) .
**> should be true 
**> QED for LEMMA 5
close

**> Next prove Lemma 6: i * (p j) = (- i) + (i * j), 
**> again by induction on i
open INT*
ops i j : -> Int .
**> base case (i = 0) : 0 * (p j) = (- 0) + (0 * j) .
red 0 * (p j) == (- 0) + (0 * j) .

**> induction hypothesis
--> eq  i * (p j) = (- i) + (i * j) .
eq  i * (p j) = (- i) + (i * j) .

**> induction step
red (s i) * (p j) == (- (s i)) + ((s i) * j) .
red (p i) * (p j) == (- (p i)) + ((p i) * j) .
**> should be true 
**> QED for LEMMA 6
close

**> Finally, prove commutativity: i * j = j * i
**> by induction on i
open INT*
eq I:Int * 0  =  0  .                     -- lemma 4
eq I:Int * (s J:Int) = I + (I * J) .      -- lemma 5
eq I:Int * (p J:Int) = (- I) + (I * J) .  -- lemma 6

ops i j : -> Int .

**> base case (i = 0) : 0 * j =  j * 0
red 0 * j ==  j * 0 .

**> induction hypothesis
eq i * j = j * i .

**> induction step
red (s i) * j == j * (s i) .
red (p i) * j == j * (p i) .
**> should be true 
**> QED for commutativity of _*_ of INT+
close

**  ------------------------------------------------
**> the proof of distributed law of (_*_) over (_+_)
**  ------------------------------------------------

**> We can assume the _*_ is commutative
mod! INT* {
  pr (BASIC-INT)
  op _+_ : Int Int -> Int {assoc comm idr: 0}
  vars I J : Int 
  -- eq I + 0 = I .  -- we can omit this axiom because of "id: 0"
  eq I + s J = s(I + J) .
  eq I + p J = p(I + J) .

  op -_ : Int -> Int
  eq - 0 = 0 .
  eq - (s I) = p (- I) .
  eq - (p I) = s (- I) .

  op _*_ : Int Int -> Int { comm }    -- comm is already proved
  eq 0 * J = 0 .
  eq (s I) * J = J + (I * J) .
  eq (p I) * J = (- J) + (I * J) .
}

**> Proof of distributed law of (_*_) over (_+_)
**>    (i + j) * k = (i * k) + (j * k)
**> by induction for i

open INT*
--> ops i j k : -> Int .
ops i j k : -> Int .

**> base case (i = 0) : (0 + j) * k =  (0 * k) + (j * k)
red (0 + j) * k ==  (0 * k) + (j * k) .

**> induction hypothesis
--> eq (i + j) * k = (i * k) + (j * k) .
eq (i + j) * k = (i * k) + (j * k) .

**> induction step
red ((s i) + j) * k == ((s i) * k) + (j * k) .
red ((p i) + j) * k == ((p i) * k) + (j * k) .
**> should be true 
**> QED for distributed law of (_*_) over (_+_)
close

**  ------------------------------------
**> the proof of associativity of (_*_)
**  ------------------------------------

**> Proof of the associativity of (_*_)
**>    (i * j) * k = i * (j * k)
**> by induction for i

open INT*
--> assuming the distributed law already proved
eq (X:Int + Y:Int) * Z:Int = (X * Z) + (Y * Z) .  -- this seems to make error

ops i j k : -> Int .
**> base case (i = 0) : (0 * j) * k =  0 * (j * k)
red (0 * j) * k ==  0 * (j * k) .                -- error seems to happen here

**> induction hypothesis
eq (i * j) * k = i * (j * k) .
-- op _*_ : Int Int -> Int { assoc }

**> induction step
red ((s i) * j) * k == (s i) * (j * k) .
red ((p i) * j) * k == (p i) * (j * k) .
**> should be true 
**> QED for associativity of _*_ of INT*
-- close

eof

%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
