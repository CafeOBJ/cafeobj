**>
**> 両模擬関係試験-1: 公理の自動生成
**> 

**> _=*=_ が合同関係になるケース
**> 公理が自動生成されていなければならない．

mod* BISIM-AX-1 (X :: TRIV) 
{
  *[ H ]*
  op method : Elt H -> H
  bop a1 : H Elt -> Elt
  bop a2 : H Elt Elt -> Elt
  bop a3 : Elt H -> Elt
  bop a4 : Elt H -> Elt
}

**> システムは _=*=_ が congruence であるとメッセージを出しているはず．
**> 実際に公理が追加されているかどうかを show コマンドで調べる．
show BISIM-AX-1

**> 次の例は _=*=_ が合同関係にはならないケース
**> 公理の追加があってはならない．

mod* BISIM-AX-2 (X :: TRIV) 
{
  
  *[ H ]*

  op zero : -> Elt
  op empty :  -> H 
  -- メソッド
  bop put : Elt H -> H    -- method 
  bop take : Elt H -> H   -- method
  -- アトリビュート
  bop get : H Elt -> Elt    -- attribute

  vars E E' : Elt
  var B : H 

  eq get(empty, E) = zero .
  cq get(put(E, B), E')  =  get(B, E')   if E =/= E' .
  eq get(put(E, B), E)   = get(B, E) . 
  cq get(take(E, B), E') =  get(B, E')   if E =/= E' .
  eq get(take(E, B), E)  = get(B, E) .
}

**> show で確認する．
show BISIM-AX-2
