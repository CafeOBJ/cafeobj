-- Date: Mon, 29 Sep 1997 19:46:51 +0300 (EET DST)
-- From: Dorel Lucanu <dlucanu@thor.infoiasi.ro>
-- To: Joseph Goguen <goguen@cs.ucsd.edu>
-- cc: diacon@jaist.ac.jp, amori@cs.ucsd.edu, cerioli@disi.unige.it,
--         daia@stoilow.imar.ro, grantm@comlab.ox.ac.uk, grosu@cs.ucsd.edu,
--         h-ishika@jaist.ac.jp, ishisone@sra.co.jp, kokichi@jaist.ac.jp,
--         mitihiro@jaist.ac.jp, n-ume@jaist.ac.jp, nakagawa@sra.co.jp,
--         nmihalac@stoilow.imar.ro, ogata@jaist.ac.jp, s_iida@jaist.ac.jp,
--         sawada@sra.co.jp, vec@funinf.math.unibuc.ro
-- Subject: Vending machines: beh. eq. vs. fairness 
-- In-Reply-To: <199709260420.VAA07547@awk.ucsd.edu>
-- Message-ID: <Pine.LNX.3.95.970929193903.23360A-100000@thor.infoiasi.ro>
-- MIME-Version: 1.0
-- Content-Type: TEXT/PLAIN; charset=US-ASCII
-- Content-Length: 1580

-- Dear all,

-- There exists a very nice reltionship between the behavioural equivalence and
-- fairness property for vending machines (VM). I firstly recall the VM
-- specification (CafeOBJ version):

mod! DATA {
  [ Data ]
  ops coffee tea : -> Data
  op not_ : Data -> Data
  eq not coffee = tea .
  eq not tea = coffee .
}

mod* VM {
  protecting (DATA)
  *[ St ]*
  op init : -> St
  bop out : St -> Data 
  bop m : St -> St
}

-- The relationship is stated by the following

-- Theorem. A model M is fair iff does not exist k such that 
--    (1) m^k(init) *=* m^{k+1}(init) 
-- (by *=* a denoted the beh. eq. on M).

-- The proof of the theorem uses the following 

-- Lemma. If k < l and m^k(init) *=* m^l(init) then m^k(init) *=*
-- m^{l+n(l-k)}(init) for all n >= 0

-- Proof of the lemma. By induction on n. 
-- The basis step n=0 follows directly from the hypothesis.  
-- Inductive step. Assume m^k(init) *=* m^{l+n(l-k)}(init). Then:
-- m^{l+(n+1)(l-k)} =
-- m^{l-k}(m^{l+n(l-k)}(init) *=*
-- m^{l-k}(m^k(init)) =
-- m^l(init) *=*
-- m^k(init)

-- Proof of the theorem. 
-- 1. Let M be a fair model and suppose  that there exists k such that
-- m^k(init) *=* m^{k+1}(init). Applying the lemma we get m^k(init) *=*
-- m^{k+1+n}(init) for all n >= 0. But this means out(m^k(init)) =
-- out(m^{k+1+n}(init)) for all n. Hence M is unfair. Contradiction.

-- 2. Let M be such that (1) does not hold for all k. Suppose M unfair. Then
-- there exists k such that out(m^k(init)) = out(m^{k+n}(init)) for all n >= 0.
-- It is easy to see now that m^k(init) *=* m^{k+1}(init). Contradiction.

-- Now the proof of theorem is complete.

-- Best regards,
-- Dorel.  

