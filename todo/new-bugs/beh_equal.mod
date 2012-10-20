mod! BARE-NAT {
 [ NzNat Zero < Nat ]
 op 0 : -> Zero
 op s_ : Nat -> NzNat
}
mod! TRIV+(X :: TRIV) {
 op err :  -> ?Elt
}

mod* BUF {
 protecting(TRIV+ + EQL)

 *[ Buf ]*

 op init :  -> Buf
 op put : Elt Buf -> Buf   -- {coherent}
 bop get_ : Buf -> ?Elt
 bop take_ : Buf -> Buf
 op empty? : Buf -> Bool  {coherent}

 var E : Elt
 var B : Buf

 eq [1eq] : empty?(init) = true .
 cq [2eq] : empty?(take B) = true if empty?(B) .
 eq [3eq] : empty?(put(E, B)) = false .
 eq [4eq] : empty?(B) = (get(B) = err) .
 bceq [5eq] : take put(E, B) = put(E, take B) if not empty?(B) .
 bceq [6eq] : take(put(E, B)) = B             if empty?(B) .

--  ceq get B = err if empty?(B) .
 cq [7eq] : get put(E, B) = E if empty?(B) .
 cq [8eq] : get put(E, B) = get B if not empty?(B) .
}

mod* BUF-BEQ {
 protecting(BUF + BARE-NAT + EQL)
 -- EQL is imported for using "_=_" predicate
 op _R[_]_ : Buf Nat Buf -> Bool {coherent}
 bop take : Nat Buf -> Buf -- {coherent}
 var N : Nat
 vars B B1 B2 : Buf
 eq [beq1] : take(0, B) = B .
 eq [beq2] : take(s(N), B) = take(N, take B) .
 eq [beq3] : B1 R[N] B2 = (get take(N, B1) = get take(N, B2)) .
}

open (BUF-BEQ + EQL)
ops b1 b1' b2 b2' : -> Buf .
vars B1 B2 : Buf .
op n : -> Nat .
op e : -> Elt .
beq b1  = b2  .
eq empty?(b1)  = true .
eq empty?(b2)  = true .
beq b1' = b2' .
eq empty?(b1') = false .
eq empty?(b2') = false .

** -------------------------------------------------------
eof
** -------------------------------------------------------

CafeOBJ>
-- defining module! BARE-NAT
TRIV+(X)>
-- defining module* BUF
processing input :
c:\localPrograms\cafeobj147rc2-070416\cafeobj147rc2\lib\eql.mod
-- defining module! EQL.._.* done._*........._...
[Warning]: axiom : [4eq] : empty?(B)
    = ((get B) = err)
   contains error operators....
[Warning]: axiom : [7eq] : (get put(E,B))
    = E if empty?(B)
   contains error operators..
[Warning]: axiom : [8eq] : (get put(E,B))
    = (get B) if (not empty?(B))
   contains error operators..*
** system found the operator
 put : Elt Buf -> Buf
 can be declared as coherent.　-- このメッセージをどのような
                               -- アルゴリズムで出しているかは
                               -- 検討事項として残っています．
** system failed to prove =*= is a congruence of BUF done.
BUF(X.TRIV+)>
-- defining module* BUF-BEQ_*....._..
[Warning]: axiom : [beq3] : (B1 R [ N ] B2)
    = ((get take(N,B1)) = (get take(N,B2)))
   contains error operators..*
** system failed to prove =*= is a congruence of BUF-BEQ done.
BUF-BEQ(X.TRIV+)> _*
-- opening module EQL + BUF-BEQ(X.TRIV+).. done.
%EQL + BUF-BEQ(X.TRIV+)> %EQL + BUF-BEQ(X.TRIV+)>
%EQL + BUF-BEQ(X.TRIV+)> %EQL + BUF-BEQ(X.TRIV+)> %EQL +
BUF-BEQ(X.TRIV+)> %EQL + BUF-BEQ(X.TRIV+)> _
%EQL + BUF-BEQ(X.TRIV+)> %EQL + BUF-BEQ(X.TRIV+)> %EQL +
BUF-BEQ(X.TRIV+)> %EQL + BUF-BEQ(X.TRIV+)> %EQL + BUF-BEQ(X.TRIV+)> %EQL
+ BUF-BEQ(X.TRIV+)>

-- 以上まではシステムは仕様を正常に読み込んでいます．
-- ここでシステムに以下のcqを読み込ませます．これは帰納法の仮定です．

cq [ih] : (get(take(n, put(e, B1))) = get(take(n, put(e, B2)))) = true
  if B1 =b= B2 .
[Warning]: axiom : [ih] : ((get take(n,put(e,B1))) = (get
take(n,put(e,B2))))
    = true if (B1 =b= B2)
   contains error operators.

-- その後で以下のbredを実行すると，システムはtrueを返しません．

%EQL + BUF-BEQ(X.TRIV+)> bred put(e, b1') R[s n] put(e, b2') .
*
-- behavioural reduce in %EQL + BUF-BEQ(X.TRIV+) :
   (put(e,b1') R [ (s n) ] put(e,b2')):Bool
((get take(n,put(e,(take b1')))) = (get take(n,put(e,(take b2'))))):Bool

(0.000 sec for parse, 14 rewrites(0.015 sec), 58 matches)

-- これはtrueを返すべきなので，traceを取ってみます．

%EQL + BUF-BEQ(X.TRIV+)> set trace on
%EQL + BUF-BEQ(X.TRIV+)> bred put(e, b1') R[s n] put(e, b2') .
-- behavioural reduce in %EQL + BUF-BEQ(X.TRIV+) :
   (put(e,b1') R [ (s n) ] put(e,b2')):Bool
1>[1] rule: eq [beq3] : (B1:Buf R [ N:Nat ] B2:Buf)
  = ((get take(N,B1)) = (get take(N,B2)))
   { N:Nat |-> (s n), B1:Buf |-> put(e,b1'), B2:Buf |-> put(e,b2') }
1<[1] (put(e,b1') R [ (s n) ] put(e,b2')) --> ((get take((s
n),put(e,b1'))) = (get take((s n),put(e,b2'))))
1>[2] rule: eq [beq2] : take((s N:Nat),B:Buf)
  = take(N,(take B))
   { N:Nat |-> n, B:Buf |-> put(e,b1') }
1<[2] take((s n),put(e,b1')) --> take(n,(take put(e,b1')))
1>[3] apply trial #1
-- rule: bceq [5eq] : (take put(E:Elt,B:Buf))
  = put(E,(take B)) if (not empty?(B))
   { E:Elt |-> e, B:Buf |-> b1' }
2>[3] rule: eq (not A:Bool) = (A xor true)
   { A:Bool |-> empty?(b1') }
2<[3] (not empty?(b1')) --> (empty?(b1') xor true)
2>[4] rule: beq b1' = b2'
   {}
2<[4] b1' --> b2'
2>[5] rule: eq empty?(b2') = false
   {}
2<[5] empty?(b2') --> falsep
2>[6] rule: eq (false xor A:Bool) = A
   { A:Bool |-> true }
2<[6] (false xor true) --> true
1>[7] match success #1
1<[7] (take put(e,b1')) --> put(e,(take b1'))
1>[8] rule: eq [beq2] : take((s N:Nat),B:Buf)
  = take(N,(take B))
   { N:Nat |-> n, B:Buf |-> put(e,b2') }
1<[8] take((s n),put(e,b2')) --> take(n,(take put(e,b2')))
1>[9] apply trial #1
-- rule: bceq [5eq] : (take put(E:Elt,B:Buf))
  = put(E,(take B)) if (not empty?(B))
   { E:Elt |-> e, B:Buf |-> b2' }
2>[9] rule: eq (not A:Bool) = (A xor true)
   { A:Bool |-> empty?(b2') }
2<[9] (not empty?(b2')) --> (empty?(b2') xor true)
2>[10] rule: eq empty?(b2') = false
   {}
2<[10] empty?(b2') --> false
2>[11] rule: eq (false xor A:Bool) = A
   { A:Bool |-> true }
2<[11] (false xor true) --> true
1>[12] match success #1
1<[12] (take put(e,b2')) --> put(e,(take b2'))
1>[13] apply trial #1
-- rule: ceq [ih] : ((get take(n,put(e,B1:Buf))) = (get
take(n,put(e,B2:Buf))))
  = true if (B1 =b= B2)
   { B1:Buf |-> (take b1'), B2:Buf |-> (take b2') }
2>[13] rule: eq (CXU =b= CYU) = #!! (coerce-to-bool
(term-equational-equal cxu cyu))
   { CXU |-> (take b1'), CYU |-> (take b2') }
2<[13] ((take b1') =b= (take b2')) --> false
1>[14] apply trial #1
-- rule: ceq [ih] : ((get take(n,put(e,B1:Buf))) = (get
take(n,put(e,B2:Buf))))
  = true if (B1 =b= B2)
   { B1:Buf |-> (take b2'), B2:Buf |-> (take b1') }
2>[14] rule: eq (CXU =b= CYU) = #!! (coerce-to-bool
(term-equational-equal cxu cyu))
   { CXU |-> (take b2'), CYU |-> (take b1') }
2<[14] ((take b2') =b= (take b1')) --> false
1>[15] rewrite rule exhausted (#1)
((get take(n,put(e,(take b1')))) = (get take(n,put(e,(take b2'))))):Bool

(0.000 sec for parse, 14 rewrites(0.000 sec), 58 matches)

-- 上のtraceから，
-- 2<[13] ((take b1') =b= (take b2')) --> false
-- や
-- 2<[14] ((take b2') =b= (take b1')) --> false
-- でfalseを返すのがおかしいことが分かります．

-- 実際，以下のように
-- %EQL + BUF-BEQ(X.TRIV+)>
-- のレベルで
-- red ((take b1') =b= (take b2')) .
-- を実行しても，
-- bred ((take b1') =b= (take b2')) .
-- を実行しても，
-- システムはtrueを返します．

%EQL + BUF-BEQ(X.TRIV+)> red ((take b1') =b= (take b2')) .
-- reduce in %EQL + BUF-BEQ(X.TRIV+) : ((take b1') =b= (take b2')):Bool

1>[1] rule: beq b1' = b2'
   {}
1<[1] b1' --> b2'
1>[2] rule: eq (CXU =b= CYU) = #!! (coerce-to-bool
(term-equational-equal cxu cyu))
   { CXU |-> (take b2'), CYU |-> (take b2') }
1<[2] ((take b2') =b= (take b2')) --> true

(true):Bool
(0.000 sec for parse, 2 rewrites(0.015 sec), 6 matches)

%EQL + BUF-BEQ(X.TRIV+)> bred ((take b1') =b= (take b2')) .
-- behavioural reduce in %EQL + BUF-BEQ(X.TRIV+) :
   ((take b1') =b= (take b2')):Bool
1>[1] rule: beq b1' = b2'
   {}
1<[1] b1' --> b2'
1>[2] rule: eq (CXU =b= CYU) = #!! (coerce-to-bool
(term-equational-equal cxu cyu))
   { CXU |-> (take b2'), CYU |-> (take b2') }
1<[2] ((take b2') =b= (take b2')) --> true

(true):Bool
(0.000 sec for parse, 2 rewrites(0.000 sec), 6 matches)
%EQL + BUF-BEQ(X.TRIV+)>

-- 以上から，
-- 2<[13] ((take b1') =b= (take b2')) --> false
-- や
-- 2<[14] ((take b2') =b= (take b1')) --> false
-- で何らかの事情でシステムがおかしな動きをしていることが
-- 疑われます．
