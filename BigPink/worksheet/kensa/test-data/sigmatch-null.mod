**>
**> 射が無い場合のテストのためのモジュール宣言と
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
--> テスト対象のモジュール : ARR
--> 
mod* ARR(X :: TRIV) 
{
  protecting(NAT)
  *[ Arr ]*
  op nil : -> Arr
  bop put : Elt Nat Arr -> Arr
  bop  _[_] : Arr Nat -> Elt
}

**> sigmatch を起動
--> sigmatch (CONTAINER) to (ARR)
-->
sigmatch (CONTAINER) to (ARR)

-->
--> テスト対象のモジュール : BAG
--> 
mod* BAG(X :: TRIV) 
{

  protecting(NAT)
  *[ Bag ]*
  op empty :  -> Bag 
  bop put : Elt Bag -> Bag
  bop take : Elt Bag -> Bag
  bop get : Bag Elt -> Nat
}

**> sigmatch を起動
--> sigmatch (CONTAINER) to (BAG)
-->
sigmatch (CONTAINER) to (BAG)

-->
--> テスト対象のモジュール : COUNTER
--> 
mod* COUNTER {
  protecting(INT)

  *[ Counter ]*

  op init : -> Counter
  bop add : Int Counter -> Counter
  bop read_ : Counter -> Int
}

**> sigmatch を起動
--> sigmatch (CONTAINER) to (COUNTER)
-->
sigmatch (CONTAINER) to (COUNTER)

-->
--> テスト対象のモジュール : BASICSETS
--> 

mod* BASICSETS(X :: TRIV) 
{

  *[ Set ]*

  op empty : -> Set 
  op add   : Elt Set -> Set {coherent}
  bop _in_  : Elt Set -> Bool
}

**> sigmatch を起動
--> sigmatch (CONTAINER) to (BASICSETS)
-->
sigmatch (CONTAINER) to (BASICSETS)







