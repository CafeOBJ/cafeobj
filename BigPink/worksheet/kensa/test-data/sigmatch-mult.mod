**>
**> 複数の射の自動構成テストのためのモジュール宣言と
**> sigmatch コマンドの起動
**>

-->
--> ベースとなるモジュール ： CONTAINER
-->

mod* CONTAINER(X :: TRIV) 
{
  *[ Container ]*

  op empty : -> Container
  bop store : Elt Container -> Container
  bop val : Container -> Elt
}

-->
--> テスト対象のモジュール : MTEST
--> 
mod* MTEST(X :: TRIV)
{
  *[ H ]*

  op init : -> H
  bop m1   : H Elt -> H
  bop m2   : Elt H -> H
  bop a1   : H -> Elt
  bop a2   : H -> Elt
}

**> sigmatch コマンドの起動
--> sigmatch (CONTAINER) to (MTEST)
-->
sigmatch (CONTAINER) to (MTEST)

