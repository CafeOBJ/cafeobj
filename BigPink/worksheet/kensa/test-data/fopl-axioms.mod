**>
**> FOPL 文による公理の宣言機能検査
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

**> FOPL 文による公理宣言.
--> ax[t1]: (p -> q) -> (q -> r) .
ax[t1]: (p -> q) -> (q -> r) .

--> ax[t2]: \A[X2:Nat]\E[Y1:Nat]\A[X1:Nat]\E[Y2:Nat]R(X1,Y1) & S(X2,Y2) .
ax[t2]: \A[X2:Nat]\E[Y1:Nat]\A[X1:Nat]\E[Y2:Nat]R(X1,Y1) & S(X2,Y2) .

--> goal[t3]: (\A[X:Nat]P(X) -> (\E[Y:Nat]R(X,Y))) &
-->          (\A[X:Nat]~ P(X) -> ~ (\E[Y:Nat]R(X,Y))) .
goal[t3]: (\A[X:Nat]P(X) -> (\E[Y:Nat]R(X,Y))) &
          (\A[X:Nat]~ P(X) -> ~ (\E[Y:Nat]R(X,Y))) .
--> goal[t4]: (\A[X:Nat]P(X) -> (\E[Y:Nat]R(X,Y))) |
-->           (\A[X:Nat]~ P(X) -> ~ (\E[Y:Nat]R(X,Y))) .
goal[t4]: (\A[X:Nat]P(X) -> (\E[Y:Nat]R(X,Y))) |
          (\A[X:Nat]~ P(X) -> ~ (\E[Y:Nat]R(X,Y))) .

--> ax[t5] \A[X:Nat]P(X) -> 
-->                 (\E[Y:Nat](R(X,Y) -> P(a)) & 
-->                           (\A[Z:Nat]R(Y,Z) -> P(X))) .
ax[t5]: \A[X:Nat]P(X) -> 
           (\E[Y:Nat](R(X,Y) -> P(a)) & 
                     (\A[Z:Nat]R(Y,Z) -> P(X))) .

**> モジュールを表示し, 上記の公理が正しく受け付けられて
**> いること確認する.
show .
**
close
--
eof
