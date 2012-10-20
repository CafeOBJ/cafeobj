**>
**> 単一の射の自動構成テストのためのモジュール宣言と
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
--> テスト対象のモジュール : BUF
--> 
mod* BUF(X :: TRIV)
{
  *[ Buf ]*
  op init :  -> Buf 
  bop in : Elt Buf -> Buf
  bop val : Buf -> Elt
  bop out : Buf -> Buf
  bop empty? : Buf -> Bool
}

**> sigmatch を起動
--> sigmatch (CONTAINER) to (BUF)
-->
sigmatch (CONTAINER) to (BUF)

-->
--> テスト対象のモジュール : CELL
--> 
mod* CELL(X :: TRIV) 
{
  *[ Cell ]*

  op init-cell : -> Cell
  bop put : Elt Cell -> Cell
  bop get : Cell -> Elt
}

**> sigmatch を起動
--> sigmatch (CONTAINER) to (CELL)
-->
sigmatch (CONTAINER) to (CELL)

-->
--> テスト対象のモジュール : LIST
--> 
mod* LIST(X :: TRIV)  
{

  *[ List ]*

  op nil : -> List   
  op cons : Elt List -> List {coherent}
  bop car : List -> Elt
  bop cdr : List -> List
}

**> sigmatch を起動
--> sigmatch (CONTAINER) to (LIST)
-->
sigmatch (CONTAINER) to (LIST)

-->
--> テスト対象のモジュール : QUEUE
--> 

mod* QUEUE(X :: TRIV) 
{
  *[ Queue ]*
  op empty : -> Queue 
  bop front : Queue -> Elt
  bop enq : Elt Queue -> Queue
  bop deq : Queue -> Queue
}

**> sigmatch を起動
--> sigmatch (CONTAINER) to (QUEUE)
-->
sigmatch (CONTAINER) to (QUEUE)

-->
--> テスト対象のモジュール : STACK
--> 

mod* STACK(X :: TRIV) 
{
  *[ Stack ]*
  op empty : -> Stack
  bop top : Stack -> Elt
  bop push : Elt Stack -> Stack
  bop pop : Stack -> Stack
}

**> sigmatch を起動
--> sigmatch (CONTAINER) to (STACK)
-->
sigmatch (CONTAINER) to (STACK)

**
eof

