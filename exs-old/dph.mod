** -*- Mode:CafeOBJ -*-
--
-- from Forsdonnet Sample
-- 

-- まず、「多相的な」空集合を定義する。

module EMPTY { [ Empty ] op * : -> Empty }

-- 次に、要素の重複を許す、集合を定義する。
-- <CODE>_,_</CODE> は集合の和で、結合的、可換、単位元は空集合である。

module MULTISET(X :: TRIV) {
  protecting (EMPTY)
  signature {
    [ Empty Elt < MultiSet ]
    op _,_ : MultiSet MultiSet -> MultiSet { assoc comm id: * }
  }
}


-- プロセスのチャネルの名前を定義する。
-- _[_:=_] は、名前の中で自由な変数に対して名前を代入する演算である。
--

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

-- プロセスのチャネルを定義する。
-- ? は入力を表し、! は出力を表す。

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

view TRIV2CHANNEL from TRIV to CHANNEL
{
  sort Elt -> Channel
}

-- チャネルの多重集合を定義する。

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


-- 次にプロセスを定義する。
-- {Cs}; P、チャネルたち Cs でガードされているプロセス P を表す。

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

-- プロセスの並行合成を定義する。
-- 書換え規則で、並行合成されているプロセス間の交信を表している。

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
    trans  ({!(N),Cs}; P)|({?(N),Ds}; Q) => ({Cs}; P)|({Ds}; Q) .
    trans ({!(M[N]),Cs}; P)|({?(M[X]),Ds}; Q) => ({Cs}; P)|({Ds};(Q[X := N])) .
    ctrans ({!(N),Cs}; P)|({?(N),Ds}; Q)| R =>
        ({Cs}; P)|({Ds}; Q)| R if not(R == @) .
    ctrans ({!(M[N]),Cs}; P)|({?(M[X]),Ds}; Q)| R =>
        ({Cs}; P)|({Ds};(Q[X := N]))| R if not(R == @) .
    cq  (P | Q)[X := N] = (P[X := N])|(Q[X := N]) if not(P == @ or Q == @).
  }
}

-- これから、『食事する哲学者たち』を例として定義する。
-- 
-- 哲学者の人数を最大4人とする。

module NUMBER { [ Num ] ops 1 2 3 4 : -> Num }

-- フォークに対する行為(「持つ」と「置く」)を定義する。

module ACTION-on-FORK {
  extending (NAME)
  signature {
    ops pickup putdown : -> Primitive
  }
}

-- フォークを表すプロセスを定義する。
-- 誰かに持たれたら、その人が置くまで、誰も使えない。

module FORK {
  extending (PROCESS)
  extending (ACTION-on-FORK)
  signature {
    op x : -> Variable
    op FK : -> Unit
    op fk : -> Process
  }
  axioms {
    eq fk = {?(pickup[x])};{?(putdown[x])}; FK .
    eq {*}; FK = fk .
  }
}

-- 椅子に対する行為(「座る」と「立つ」)を定義する。

module ACTION-on-SEAT {
  extending (NAME)
  signature {
    ops sitdown getup : -> Primitive
  }
}


-- 椅子を表すプロセスを定義する。
-- 誰かに座られたら、その人が立つまでは誰も座れない。

module SEAT {
  extending (PROCESS)
  extending (ACTION-on-SEAT)
  signature {
    op y : -> Variable
    op ST : -> Unit
    op st : -> Process
  }
  axioms {
    eq st = {?(sitdown[y])};{?(getup[y])}; ST .
    eq {*}; ST = st .
  }
}

-- 哲学者を表すプロセスを定義する。
-- 席について、フォークを二つ持ちスパゲティを食べる。
-- スパゲティを食べ終えたら、フォークを置き、席を離れる。
-- ただし、この哲学者は慎み深くなく空いている席ならば何処にでも座り、
-- 空いているフォークならば、たとえ自分から離れていても取りに行く。

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

-- 食堂を定義する。
-- アイテムは、フォーク、席、そして哲学者。

module DININGROOM {
  extending (COMPOSITION)
  extending (FORK)
  extending (SEAT)
  extending (PHILOSOPHER)
}

-- 実行例<P>
-- 哲学者、フォーク、席の数はそれぞれ 3
-- 哲学者は既に席に着いている
-- 哲学者たちがスパゲティを食べるべく、一斉(?)にフォークを持とうとすると...

open DININGROOM .
op sph : Num -> Process .
var j : Num .
eq sph(j) = ph(j) | st .
let droom = fk | fk | fk | sph(1) | sph(2) | sph(3) .
-- eof

exec droom .
eof
close

-- これを実行すると次のような結果に終わるだろう。
-- 哲学者は1本ずつフォークを持ち、他の哲学者のフォークを睨んでいる。
-- 哲学者はフォークが2本持てないから、スパゲティを食べられない。

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


-- 今度は、席を一つ少なくする。
-- 哲学者の一人は、誰かが食べ終わるまで、席に着くことはできない。

open DININGROOM .
let droom = fk | fk | fk | ph(1) | ph(2) | ph(3) | st | st .
exec droom .
close

-- 今度は、次のように無事に哲学者全員が食事を終えることができるだろう。
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

eof

