-- とりあえず，シグネチャマッチングで検索ができることを当面の目標として，
-- 適当な仕様(The Alternating Bit Protocol)のファイルを添付します．論文に
-- 書く予定の例も基本的には ABP の変形を考えています．例えば，

--   SENDER の仕様でシグネチャマッチングすると RECEIVER もひっかかってし
--   まうが，ABP が正常に一容量バッファ BUF として動くためには，振舞詳細
--   化の検証を行う必要がある．

-- のようなシナリオが考えられます．

-- ABP モジュールは SENDER と RECEIVER でパラメータ化されていますので，ト
-- レーダーへの最初の入力としてこの ABP が与えられるということも考えられ
-- ます．この場合は仕様書にもあるように，トレーダーの方でパラメータ部を切
-- り出して，SENDER と RECEIVER の検索を行うようにしなければなりません．
-- このあたりはまた様子を見て相談／決定しましょう．

-- あと思い付いたことですが，遠隔実行する際には CafeOBJ の振舞仕様のイン
-- ターフェース(メソッド，アトリビュート)と IDLインターフェースの対応が必
-- 要になります．これは将来的に開発する予定の CafeOBJ->IDLコンパイラが面
-- 倒見ることですが，実験段階ではごまかす必要があります．

-- 今回の論文では遠隔実行部は空想で書くつもりでいますので，問題を先送りし
-- てもいいのですが，CafeOBJ仕様を格納するリポジトリや動的呼び出しなどの
-- 方式も含めていいアイディアがあれば教えて下さい．

-- トレーダー仕様書はおいおい更新して行きます．

-- それではよろしくお願いします．

-- そうそう，瀬尾さんは JAIST に来れそうですか？ ダメなようでしたら東京で
-- 澤田さんと一緒に作業してもらおうかと思っています．私は手一杯で東京に行
-- けそうにないです．

-- 森 彰

-- ----------------------------------------------------------------------
mod* DATA {
  protecting (NAT)
  protecting (FOPL-CLAUSE)
  [ Nat < Data, Flag]
  ops on off : -> Flag { constr }
  op not_ : Flag -> Flag
  eq not on = off .
  eq not off = on .
  ax ~(on = off) .
}

mod! QUEUE {
  protecting(DATA)
  [ NeQueue < Queue ]
  op nil : -> Queue 
  op front : NeQueue -> Data
  op enq : Data Queue -> NeQueue
  op deq : NeQueue -> Queue
  vars D E : Data   var Q : Queue
  eq deq(enq(E,nil)) = nil .
  eq deq(enq(E,enq(D,Q))) = enq(E,deq(enq(D,Q))) .
  eq front(enq(E,nil)) = E .
  eq front(enq(E,enq(D,Q))) = front(enq(D,Q)) .
}

mod* SENDER {
  protecting(DATA)
  *[ Sender ]*
  bop bit : Sender -> Flag
  bop val : Sender -> Data
  bop in : Data Flag Sender -> Sender
  op init : -> Sender
  var D : Data   var B : Flag   var S : Sender
  eq bit(init) = on .   -- valid initial state
  ceq val(in(D,B,S)) = D if bit(S) == B . -- new data for right ack
  ceq bit(in(D,B,S)) = not bit(S) if bit(S) == B . -- alternates bit
  bceq in(D,B,S) = S if bit(S) =/= B .  -- stays put for wrong ack
}

mod* RECEIVER {
  protecting(DATA)
  *[ Receiver ]*
  bop bit : Receiver -> Flag
  bop val : Receiver -> Data
  bop get : Data Flag Receiver -> Receiver
  op init : -> Receiver
  var D : Data   var B : Flag   var R : Receiver
  eq bit(init) = on .   -- valid initial state
  ceq val(get(D,B,R)) = D if bit(R) =/= B . -- output value
  ceq bit(get(D,B,R)) = not bit(R) if bit(R) =/= B . -- alternates bit
  bceq get(D,B,R) = R if bit(R) == B . -- stays put for wrong bit
}

mod* ABP (X :: SENDER, Y :: RECEIVER) {
  protecting(QUEUE)
  *[ Abp ]*
  op Init : -> Abp
  op Protocol : Sender Receiver Queue Queue Queue -> Abp {coherent}
  bop In : Data Abp -> Abp
  bop Out : Abp -> Abp
  bop Val : Abp -> Data
  bop Empty? : Abp -> Bool .

  vars D E : Data   var B : Flag   var A : Abp   var S : Sender
  var R : Receiver   vars L L1 L2 : Queue
  beq Init = Protocol(init,init,nil,nil,nil) .
  bceq In(D,Protocol(S,R,L1,L2,enq(B,L)))
       = Protocol(in(D,front(enq(B,L)),S),R,enq(D,L1),
                  enq(not bit(S),L2),deq(enq(B,L)))
       if bit(S) == front(enq(B,L)) .
  beq In(D,Protocol(S,R,enq(E,L1),enq(B,L2),nil))
      = Protocol(S,R,enq(E,L1),enq(B,L2),nil) .
  bceq [ 1 ] : Protocol(S,R,L1,L2,enq(B,L))
               = Protocol(S,R,L1,L2,deq(enq(B,L)))
               if bit(S) =/= front(enq(B,L)) .
  bceq Out(Protocol(S,R,enq(D,L1),enq(B,L2),L))
       = Protocol(S,get(front(enq(D,L1)),front(enq(B,L2)),R),
         deq(enq(D,L1)),deq(enq(B,L2)),enq(not bit(R),L))
       if bit(R) =/= front(enq(B,L2)) .
  bceq [ 2 ] : Protocol(S,R,enq(D,L1),enq(B,L2),L)
               = Protocol(S,R,deq(enq(D,L1)),deq(enq(B,L2)),L)
               if bit(R) == front(enq(B,L2)) .
  beq Out(Protocol(S,R,nil,nil,enq(B,L)))
      = Protocol(S,R,nil,nil,enq(B,L)) .
  beq [ 3 ] : Protocol(S,R,L1,L2,L)
              = Protocol(S,R,enq(val(S),L1),enq(bit(S),L2),L) .
  beq [ 4 ] : Protocol(S,R,L1,L2,L)
              = Protocol(S,R,L1,L2,enq(bit(R),L)) .
  eq Val(Protocol(S,R,L1,L2,L)) = val(R) .
  eq Empty?(Protocol(S,R,L1,L2,L)) = bit(S) == bit(R) .
}

mod* BUF {
  protecting(DATA)
  *[ Buf ]*
  op init :  -> Buf 
  bop in : Data Buf -> Buf
  bop val : Buf -> Data
  bop out : Buf -> Buf
  bop empty? : Buf -> Bool
  var N : Data   var B : Buf 
  eq empty?(init) = true .
  ceq empty?(out(B)) = true if not empty?(B) .
  eq empty?(in(N,B)) = false .
  ceq val(out(in(N,B))) = N if empty?(B) .
  bceq in(N,B) = B if not empty?(B) .
  bceq out(B) = B if empty?(B) .
}

module M1
{
  protecting (DATA)
  *[ E ]*
  op elt : -> E
  bop ar1 : E -> Bool
  bop ar2 : E -> Data
  bop m1  : Bool E Data -> E
}

view X1 from M1 to SENDER
{
  hsort E -> Sender,
  bop ar1 -> bit,
  bop ar2 -> val,
  bop m1(B:Bool, E:E, D:Data) -> in(X:Data, Y:Bool, S:Sender),
  op elt -> init
}

view V1 from SENDER to RECEIVER
{
  hsort Sender -> Receiver,
  bop bit -> bit,
  bop val -> val,
  var D : Data,
  var B : Bool,
  bop in(D,B,S:Sender) -> get(D,B,S:Receiver),
  op init -> init
}


--
eof
--
$Id:
