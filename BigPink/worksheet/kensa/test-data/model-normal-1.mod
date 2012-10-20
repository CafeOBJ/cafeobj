**>
**> モデル検査正常終了のケース-1
**> 

set include FOPL-CLAUSE on

**> 整数：
mod! INT*
{
  [ Int ]
  op 0 : -> Int
  op _+_ : Int Int -> Int
  op _-_ : Int Int -> Int
  pred _<=_ : Int Int

  vars M N : Int
  ax M <= M .
  ax 0 <= M & 0 <= N -> 0 <= M + N .
  ax M <= N -> 0 <= N - M .
}

**> 口座の仕様
mod* ACCOUNT
{
  protecting(INT*)
  *[ Account ]*
  -- 初期状態
  op new-account : -> Account
  -- 残高照合
  bop balance : Account -> Int
  -- 預け入れ
  bop deposit : Int Account -> Account
  -- 引き出し
  bop withdraw : Int Account -> Account

  var A : Account    
  vars M N : Int

  eq balance(new-account) = 0 .
  ax 0 <= N -> balance(deposit(N,A)) = balance(A) + N .
  ax ~(0 <= N) -> balance(deposit(N,A)) = balance(A) .
  ax N <= balance(A) -> balance(withdraw(N,A)) = balance(A) - N .
  ax ~(N <= balance(A)) -> balance(withdraw(N,A)) = balance(A) .

}

**> ACCOUNT に関するモデル検査のためのモジュール
**> 保証したい性質は, 述語 P で表現.

mod* PROOF
{
  protecting(ACCOUNT)

  pred P : Account .
  #define P(A:Account) ::= 0 <= balance(A) .
}

**> 反駁エンジンオプションの設定
evq (setq *print-line-limit* 40)
--> auto モードで行う.
option reset
flag(auto,on)

**> PROOF モジュールのオープン
open PROOF

**> モデル検査の実行
--> 述語 P は, 残高(balance) が正であることを述べたもの.
--> これが常に保証されることを検査する.
--> check safety P from new-account
check safety P from new-account
**
close
