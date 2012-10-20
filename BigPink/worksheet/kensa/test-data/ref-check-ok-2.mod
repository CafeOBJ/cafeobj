**>
**> 仕様詳細化検査の試験 - 2
**> 自動生成された射による場合．
**>

**> もとになる仕様：CONTAINER
**> 一般的な「入れ物」を定義したモジュール
**>
mod* CONTAINER(X :: TRIV) 
{
  *[ Container ]*

  -- 空の入れ物
  op empty : -> Container
  -- 要素を入れる
  bop store : Elt Container -> Container
  -- 入れ物の中を見る
  bop val : Container -> Elt

  var E : Elt
  var C : Container
  -- 要素Eを格納した直後に中を見るとEが見える
  eq val(store(E,C)) = E .
}

**>
**> CELL : CONTAINER と同じく一般的な入れ物
**>
mod* CELL(X :: TRIV) 
{
  *[ Cell ]*

  op init-cell : -> Cell
  bop put : Elt Cell -> Cell
  bop get : Cell -> Elt

  var E : Elt
  var C : Cell

  eq get(put(E,C)) = E .
}

**>
**> STACK : 先入れ先だし方式の入れ物
**>
mod* STACK(X :: TRIV) 
{
  *[ Stack ]*
  op empty : -> Stack
  bop top : Stack -> Elt
  bop push : Elt Stack -> Stack
  bop pop : Stack -> Stack
  vars D : Elt   var S : Stack
  eq pop(empty) = empty .
  eq top(push(D,S)) = D .
  beq pop(push(D,S)) = S .
}

**>
**> LIST : リスト構造
**>
mod* LIST(X :: TRIV)  {

  *[ List ]*

  op nil : -> List   
  op cons : Elt List -> List {coherent}
  bop car : List -> Elt
  bop cdr : List -> List
    
  vars E E' : Elt
  var L : List

  eq car(cons(E, L)) = E .
  beq cdr(nil) = nil .
  beq cdr(cons(E, L)) = L .
}

**> それぞれのモジュールについて，CONTAINER との sigmatch を
**> 実行して，射を自動生成する．

--> sigmatch (CONTAINER) to (CELL)
-->
sigmatch (CONTAINER) to (CELL)

--> sigmatch (CONTAINER) to (STACK)
-->
sigmatch (CONTAINER) to (STACK)

--> sigmatch (CONTAINER) to (LIST)
-->
sigmatch (CONTAINER) to (LIST)

