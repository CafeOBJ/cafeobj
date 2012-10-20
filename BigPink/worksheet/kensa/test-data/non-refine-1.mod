**>
**> 詳細化検証機能
**> view が詳細化とならない場合-1
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
--> モノイドの2項演算をかけ算に
--> 単位元を 1(s(0)) に写像する．
**>
view times from MON to TIMES-NAT {
  sort Elt -> Nat, 
  op _;_ -> _*_,  
  op null -> s(0)
}

**> TIME-NAT で定義されている自然数上のかけ算は，
**> 単位元を 1 としたモノイドを構成するかどうかを見る．
**> つまり, 仕様射 times は，TIMES-NAT が,
**> MON の詳細化を定義するものであるかを調べる．

--> 詳細な情報が欲しいのでフラグを設定する
--> flag(debug-refine,on)
flag(debug-refine,on)
--> ただし，長大なログは望ましくないので，given clause
--> の印字は抑制する
flag(print-given,off)

--> check コマンドの起動
--> check refinement times
check refinement times

