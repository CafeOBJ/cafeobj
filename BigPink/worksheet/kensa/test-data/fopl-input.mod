**>
**> FOPL 文入力に関する検査
**>

**> 例として用いる組み込みの NAT をオープンする
open NAT

**> FOPL 文の入力を可能とするため, FOPL-CLAUSE を輸入
protecting(FOPL-CLAUSE)

**> 検査に使用する命題や述語を宣言する.
--> ops p q r : -> Bool .
--> pred P : Nat .
--> pred Q : Nat .
--> pred R : Nat Nat .
--> pred S : Nat Nat .
--> op  a   : -> Nat .

ops p q r : -> Bool .
pred P : Nat .
pred Q : Nat .
pred R : Nat Nat .
pred S : Nat Nat .
op  a   : -> Nat .

**> FOPL 文の入力試験
--> let t1 = (p -> q) -> (q -> r) .
let t1 = (p -> q) -> (q -> r) .

--> let t2 = \A[X2:Nat]\E[Y1:Nat]\A[X1:Nat]\E[Y2:Nat]R(X1,Y1) & S(X2,Y2) .
let t2 = \A[X2:Nat]\E[Y1:Nat]\A[X1:Nat]\E[Y2:Nat]R(X1,Y1) & S(X2,Y2) .

--> let t3 = (\A[X:Nat]P(X) -> (\E[Y:Nat]R(X,Y))) &
-->          (\A[X:Nat]~ P(X) -> ~ (\E[Y:Nat]R(X,Y))) .
let t3 = (\A[X:Nat]P(X) -> (\E[Y:Nat]R(X,Y))) &
         (\A[X:Nat]~ P(X) -> ~ (\E[Y:Nat]R(X,Y))) .
--> let t4 = (\A[X:Nat]P(X) -> (\E[Y:Nat]R(X,Y))) |
-->          (\A[X:Nat]~ P(X) -> ~ (\E[Y:Nat]R(X,Y))) .
let t4 = (\A[X:Nat]P(X) -> (\E[Y:Nat]R(X,Y))) |
         (\A[X:Nat]~ P(X) -> ~ (\E[Y:Nat]R(X,Y))) .

--> let t5 = \A[X:Nat]P(X) -> 
-->                   (\E[Y:Nat](R(X,Y) -> P(a)) & 
-->                             (\A[Z:Nat]R(Y,Z) -> P(X))) .
let t5 = \A[X:Nat]P(X) -> 
                   (\E[Y:Nat](R(X,Y) -> P(a)) & 
                             (\A[Z:Nat]R(Y,Z) -> P(X))) .

**> 入力された FOPL 文の表示
**> t1 : 
-->
show term t1 .
**> t2 : 
-->
show term t2 .
**> t3 :
-->
show term t3 .
**> t4 : 
-->
show term t4
**> t5 : 
-->
show term t5
**
close
--
eof
