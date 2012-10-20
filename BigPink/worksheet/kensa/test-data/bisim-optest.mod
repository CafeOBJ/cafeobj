**
** 両模擬関係オペレータの自動生成検査
**

mod* BISIMOP
{
  protecting(NAT)
  [ Elt ]
  -- 隠れソートの宣言
  *[ Bag ]*

  op empty :  -> Bag 
  -- メソッド
  bop put : Elt Bag -> Bag    -- method 
  bop take : Elt Bag -> Bag   -- method
  -- アトリビュート
  bop get : Bag Elt -> Nat    -- attribute

  vars E E' : Elt
  var B : Bag 

  eq get(empty, E) = 0 .
  cq get(put(E, B), E')  =  get(B, E')   if E =/= E' .
  eq get(put(E, B), E)   = s(get(B, E)) . 
  cq get(take(E, B), E') =  get(B, E')   if E =/= E' .
  eq get(take(E, B), E)  = p(get(B, E)) .

}

select BISIMOP

**> _=*=_ が自動生成されているかどうかの確認
**> generic な _=*=_ とオーバロードしていることも確認する:
describe op _=*=_

**> _=*=_ を含む項をパーズして，オペレータがきちんと定義されて
**> いるかどうかを確認する:
parse b1:Bag =*= b1 .
parse put(e:Elt, b1:Bag) =*= put(e, b2:Bag) .
parse take(e:Elt, b1:Bag) =*= take(e, b2:Bag) .

**
eof

