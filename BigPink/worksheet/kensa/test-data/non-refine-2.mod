**>
**> 仕様詳細化検査：詳細化となっていない場合
**> sigmatch による自動構成射による検査：
**>

**>
**> CONTAINER : ベースとする仕様
**> 一般的な「入れ物」を定義したモジュール
**>
mod* CONTAINER(X :: TRIV) 
{
  *[ Container ]*

  op empty : -> Container
  bop store : Elt Container -> Container
  bop val : Container -> Elt

  var E : Elt
  var C : Container

  eq val(store(E,C)) = E .
}

**>
**> Buufer 構造
**>
mod* BUF(X :: TRIV)
{
  *[ Buf ]*
  op init :  -> Buf 
  bop in : Elt Buf -> Buf
  bop val : Buf -> Elt
  bop out : Buf -> Buf
  bop empty? : Buf -> Bool
  var N : Elt   var B : Buf 
  eq empty?(init) = true .
  ceq empty?(out(B)) = true if not empty?(B) .
  eq empty?(in(N,B)) = false .
  ceq val(out(in(N,B))) = N if empty?(B) .
  bceq in(N,B) = B if not empty?(B) .
  bceq out(B) = B if empty?(B) .
}

**>
**> QUEUE 構造
**>
mod* QUEUE(X :: TRIV) 
{
  *[ Queue ]*
  op empty : -> Queue 
  bop front : Queue -> Elt
  bop enq : Elt Queue -> Queue
  bop deq : Queue -> Queue
  vars D E : Elt   var Q : Queue
  beq deq(enq(E,empty)) = empty .
  beq deq(enq(E,enq(D,Q))) = enq(E,deq(enq(D,Q))) .
  eq front(enq(E,empty)) = E .
  eq front(enq(E,enq(D,Q))) = front(enq(D,Q)) .
}

**> 各々のモジュールについて、CONTAINER からの
**> 射を生成する：

--> sigmatch (CONTAINER) to (BUF)
-->
sigmatch (CONTAINER) to (BUF)

--> sigmatch (CONTAINER) to (QUEUE)
-->
sigmatch (CONTAINER) to (QUEUE)



