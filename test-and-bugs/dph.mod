-- To: sawada@sra.co.jp
-- From: Eiko Matsushima <Eiko.Matsushima@unisys.co.jp>
-- Subject: DINNING FILOSOPHER
-- Date: Mon, 20 Oct 1997 11:51:34 +0900
-- Sender: matusima@as.unisys.co.jp
-- Content-Type: text
-- Content-Length: 7368

-- こんにちは、松島＠ユニシスです。

-- CafeOBJ 1.3.1(Roman)でmoduleのdefiningでエラーになる
-- 「食事する哲学者」のサンプルをお送り致します。
-- 1.3.1, CafeOBJ 1.3.1bではOKです。1.4では試していません。
-- ご存知かと思いますが、CafeOBJインタプリタのサンプルに
-- ついている exs/fun.mod も1.3.1(Roman)でエラーになります。

-- ===8< cut here 8<====

-- 「多相的な」空集合

module EMPTY { [ Empty ] op * : -> Empty }

-- 要素の重複を許す、集合
-- _,_ は集合の和で、結合的、可換、単位元は空集合

module MULTISET[X :: TRIV] {
  protecting (EMPTY)
  signature {
    [ Empty Elt < MultiSet ]
    op _,_ : MultiSet MultiSet -> MultiSet { assoc comm id: * }
  }
}

-- プロセスのチャネルの名前
-- _[_:=_] は、名前の中で自由な変数に対して名前を代入する演算

module NAME {
  signature {
    [ Variable < Primitive < Name ]
    op _[_] : Name Name -> Name
    op _[_:=_] : Name Variable Name -> Name
  }
  axioms {
    var X : Variable
    var P : Primitive
    vars L M N : Name
    cq P[X := N] = N if P == X .
    cq P[X := N] = P if not(P == X) .
    eq L[M][X := N] = L[X := N][M[X := N]] .
  }
}

-- プロセスのチャネル
-- ? は入力を表し、! は出力を表す

module CHANNEL {
  protecting (NAME)
  signature {
    [ Channel ]
    ops ? ! : Name -> Channel
    op _[_:=_] : Channel Variable Name -> Channel
  }
  axioms {
    var X : Variable
    vars M N : Name
    eq ?(M)[X := N] = ?(M[X := N]) .
    eq !(M)[X := N] = !(M[X := N]) .
  }
}

view TRIV2CHANNEL from TRIV to CHANNEL { sort Elt -> Channel }

-- チャネルの多重集合

module CHANNELS {
  protecting ((MULTISET * { sort MultiSet -> Channels })[TRIV2CHANNEL])
  signature {
    op _[_:=_] : Channels Variable Name -> Channels
  }
  axioms {
    var N : Name
    var X : Variable
    var C : Channel
    var Cs : Channels
    eq *[X := N] = * .
    cq (C,Cs)[X := N] = (C[X := N]),(Cs[X := N]) if not(Cs == *) .
  }
}

-- プロセス
-- {Cs}; P は、チャネルたち Cs でガードされているプロセス P を表す

module PROCESS {
  protecting (CHANNELS)
  signature {
    [ Unit < Process ]
    op @ : -> Unit
    op {_};_ : Channels Process -> Process
    op _[_:=_] : Process Variable Name -> Process
  }
  axioms {
    var N : Name
    var X : Variable
    var U : Unit
    var P : Process
    var Cs : Channels
    eq {*}; @ = @ .
    eq {*};({Cs}; P) = {Cs}; P .
    eq U[X := N] = U .
    eq ({Cs}; P)[X := N] = {Cs[X := N]};(P[X := N]) .
  }
}

-- プロセスの並行合成
-- 書換え規則で、並行合成されているプロセス間の交信を表している

module COMPOSITION {
  extending (PROCESS)
  signature {
    op _|_ : Process Process -> Process { assoc comm id: @ }
  }
  axioms {
    var X : Variable
    vars M N : Name
    vars Cs Ds : Channels
    vars P Q R : Process
    rl  ({!(N),Cs}; P)|({?(N),Ds}; Q) => ({Cs}; P)|({Ds}; Q) .
    rl  ({!(M[N]),Cs}; P)|({?(M[X]),Ds}; Q) => ({Cs}; P)|({Ds};(Q[X := N])) .
    crl ({!(N),Cs}; P)|({?(N),Ds}; Q)| R =>
        ({Cs}; P)|({Ds}; Q)| R if not(R == @) .
    crl ({!(M[N]),Cs}; P)|({?(M[X]),Ds}; Q)| R =>
        ({Cs}; P)|({Ds};(Q[X := N]))| R if not(R == @) .
    cq  (P | Q)[X := N] = (P[X := N])|(Q[X := N]) if not(P == @ or Q == @).
  }
}

-- 例：食事する哲学者たち

-- 哲学者の人数(最大4人)
-- 理由：4人を超えると、実行に一日かかるから

module NUMBER { [ Num ] ops 1 2 3 4 : -> Num }

-- フォークに対する行為(「持つ」と「置く」)

module ACTION-on-FORK {
  extending (NAME)
  signature {
    ops pickup putdown : -> Primitive
  }
}

-- フォークを表すプロセス
-- 誰かに持たれたら、その人が置くまで、誰も使えない

module FORK {
  extending (PROCESS)
  extending (ACTION-on-FORK)
  signature {
    op x : -> Variable
    op FK : -> Unit
    op fk : -> Process
  }
  axioms {
    var X : Variable
    var N : Name
    eq fk = {?(pickup[x])};{?(putdown[x])}; FK .
    eq {*}; FK = fk .
  }
}

-- 椅子に対する行為(「座る」と「立つ」)

module ACTION-on-SEAT {
  extending (NAME)
  signature {
    ops sitdown getup : -> Primitive
  }
}

-- 椅子を表すプロセス
-- 誰かに座られたら、その人が立つまでは誰も座れない

module SEAT {
  extending (PROCESS)
  extending (ACTION-on-SEAT)
  signature {
    op y : -> Variable
    op ST : -> Unit
    op st : -> Process
  }
  axioms {
    var X : Variable
    var N : Name
    eq st = {?(sitdown[y])};{?(getup[y])}; ST .
    eq {*}; ST = st .
  }
}

-- 哲学者を表すプロセス
-- 席について、フォークを二つ持ちスパゲティを食べる
-- スパゲティを食べ終えたら、フォークを置き、席を離れる
-- ただし、この哲学者は慎み深くなく
-- 空いている席ならば何処にでも座り
-- 空いているフォークならば、たとえ自分から離れていても取りに行く

module PHILOSOPHER {
  extending (PROCESS)
  extending (ACTION-on-FORK)
  extending (ACTION-on-SEAT)
  protecting (NUMBER)
  signature {
    [ Num < Primitive ]
    op PH : -> Unit
    op ph : Num -> Process
  }
  axioms {
    var i : Num
    eq ph(i) = {!(sitdown[i])};
               {!(pickup[i]),!(pickup[i])};
               {!(putdown[i]),!(putdown[i])};
               {!(getup[i])}; PH .
  }
}

-- 食堂
-- アイテムは、フォーク、席、そして哲学者

module DININGROOM {
  extending (COMPOSITION)
  extending (FORK)
  extending (SEAT)
  extending (PHILOSOPHER)
}

-- 実行例
-- 哲学者、フォーク、席の数はそれぞれ 3
-- 哲学者は既に席に着いている
-- 哲学者たちがスパゲティを食べるべく、一斉(?)にフォークを持とうとすると...

open DININGROOM .
op sph : Num -> Process .
var j : Num .
eq sph(j) = ph(j) | st .
let droom = fk | fk | fk | sph(1) | sph(2) | sph(3) .
reduce droom .

-- 次のような結果に終わる
-- 哲学者は1本ずつフォークを持ち、他の哲学者のフォークを睨んでいる
-- 哲学者はフォークが2本持てないから、スパゲティを食べられない

--   {!(pickup[3])};{!(putdown[3]),!(putdown[3])};{!(getup[3])}; PH
-- | {?(putdown[3])}; FK
-- | {!(pickup[2])};{!(putdown[2]),!(putdown[2])};{!(getup[2])}; PH
-- | {?(putdown[2])}; FK
-- | {!(pickup[1])};{!(putdown[1]),!(putdown[1])};{!(getup[1])}; PH
-- | {?(putdown[1])}; FK
-- | {?(getup[1])}; ST
-- | {?(getup[2])}; ST
-- | {?(getup[3])}; ST
-- : Process
-- (0.000 sec for parse, 207 rewrites(37.150 sec), 632 match attempts)
close

-- 今度は、席を一つ少なくする
-- 哲学者の一人は、誰かが食べ終わるまで、席に着くことはできない

open DININGROOM .
let droom = fk | fk | fk | ph(1) | ph(2) | ph(3) | st | st .
reduce droom .

-- 今度は、無事に哲学者全員が食事を終えることができた

--   {*}; PH
-- | {?(sitdown[y])};{?(getup[y])}; ST
-- | {?(sitdown[y])};{?(getup[y])}; ST
-- | {*}; PH
-- | {*}; PH
-- | {?(pickup[x])};{?(putdown[x])}; FK
-- | {?(pickup[x])};{?(putdown[x])}; FK
-- | {?(pickup[x])};{?(putdown[x])}; FK
-- : Process
-- (0.000 sec for parse, 332 rewrites(46.533 sec), 1175 match attempts)
close

-- 本当は
-- let droom = fk | fk | fk | ph(1) | ph(2) | ph(3) | st | st | st .
-- として、droom の値を計算すると deadlock になることを見たいんだけれど、
-- Cafeの実行の癖のせいか、そうすると哲学者が全員食事できてしまう。
-- 全員が席について一斉にフォークを持とうとすると、最初の実行のように
-- deadlock になることを、apply コマンドを使って見せられると思います。

-- ===8< cut here 8<====
