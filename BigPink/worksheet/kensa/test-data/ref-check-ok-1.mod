**>
**> 詳細化検証機能
**> view が詳細化となっている場合-1
**> 手動で view を定義する．

**> 自然数上のかけ算と足し算の定義されたモジュール TIMES-NAT
mod! TIMES-NAT {
  [ NzNat Zero < Nat ]

  op 0 : -> Zero
  op s_ : Nat -> NzNat
  op _+_ : Nat Nat -> Nat
  op _*_ : Nat Nat -> Nat

  vars M N : Nat 
    
  eq N + s(M) = s(N + M) .
  eq N + 0 = N . 
  eq 0 + N = N .
  eq 0 * N = 0 .
  eq N * 0 = 0 .
  eq N * s(M) = (N * M) + N .
}

**> モノイド
mod* MON {
  [ Elt ]

  op null :  ->  Elt
  op _;_ : Elt Elt -> Elt {assoc idr: null} 
}

**> view の定義
--> モノイドの2項演算を足し算に，
--> 単位元を 0 に写像する．
**>
view plus from MON to TIMES-NAT {
  sort Elt -> Nat, 
  op _;_ -> _+_,  
  op null -> 0 
}

**> 自然数上の足し算はモノイドと解釈できる
**> つまり, 仕様射 plus は，TIMES-NAT が,
**> MON の詳細化を定義するものであることを示す．

--> check refinement plus
check refinement plus
