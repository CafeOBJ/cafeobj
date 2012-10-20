**>
**> 両模擬関係試験-1: 公理の自動生成
**> 

**> _=*=_ が合同関係になるケース
**> 公理が自動生成されていなければならない．

mod* BISIM-AX-1 (X :: TRIV) 
{
  protecting(NAT)
  
  *[ Bag ]*

  op empty :  -> Bag 
  op put : Elt Bag -> Bag    
  op take : Elt Bag -> Bag   
  bop get : Bag Elt -> Nat  -- attribute

  vars E E' : Elt
  var B : Bag 

  eq get(empty, E) = 0 .
  cq get(put(E, B), E')  =  get(B, E')   if E =/= E' .
  eq get(put(E, B), E)   = s(get(B, E)) . 
  cq get(take(E, B), E') =  get(B, E')   if E =/= E' .
  eq get(take(E, B), E)  = p(get(B, E)) .
}

**> システムは _=*=_ が congruence であるとメッセージを出しているはず．
**> 実際に公理が追加されているかどうかを show コマンドで調べる．
show BISIM-AX-1

**> 次の例は _=*=_ が合同関係にはならないケース
**> 公理の追加があってはならない．

mod* BISIM-AX-1 (X :: TRIV) 
{
  protecting(NAT)
  
  *[ Bag ]*

  op empty :  -> Bag 
  op put : Elt Bag -> Bag    
  op take : Elt Bag -> Bag   
  bop get : Bag Elt -> Nat  -- attribute
}

**> show で確認する．
show BISIM-AX-2



