-- To: sawada@sra.co.jp
-- cc: ishisone@srapc459.sra.co.jp
-- Subject: BOOL3
-- Date: Thu, 30 Apr 1998 17:03:17 +0900
-- From: Makoto Ishisone <ishisone@srapc459.sra.co.jp>
-- Content-Type: text
-- Content-Length: 1837

-- BOOL3 を使ってテストしてみました。で、brute の項の等価性判定ルーチンに
-- バグを見つけたのですが、ついでにインタプリタのバグらしきものを見つけました。
-- インタプリタは srapc459 にインストールされているやつです。

-- モジュール

mod! BOOL3 {
  [ B3 ]
  ops (_+_) (_*_) : B3 B3 -> B3 { assoc comm }
  ops 0 1 2 : -> B3
  ops and or : B3 B3 -> B3
  op not : B3 -> B3
  ops a b c d : -> B3
    
  vars X Y Z : B3

  eq X + 0 = X .
  eq X + X + X = 0 .
  eq (X + Y) * Z = (X * Z) + (Y * Z) .

  eq X * 0 = 0 .
  eq X * X * X = X .
  eq X * 1 = X .

  eq and(X,Y) = (X * X * Y * Y) + (2 * X * X * Y) +
    (2 * X * Y * Y) + (2 * X * Y) .
  eq or(X, Y) = (2 * X * X * Y * Y) + (X * X * Y) +
    (X * Y * Y) + (X * Y) + (X + Y) .
  eq not(X) = (2 * X) + 1 .
  eq 2 = 1 + 1 .
}

-- において

--     red not(and(a, b)) .

-- を実行すると、

--     (a * b) + (a * b * b) + (a * b * b) + (a * a * b * b) + (a * a * b * b) + 1 : B3

-- という結果が得られます。よく見てみるとこれは a と b に関して非対称ですが、
-- and/or に関する公理は全て対称なのでちょっと変です。で、トレースしてみると、

-- 1>[16] rule: eq AC + X:B3 + X:B3 + X:B3 = AC + 0
--     { AC |-> (a * a * b * b) + (a * b * b) + (a * b) + (a * b), X:B3 |-> 
--        a * b * b }
-- 1<[16] (a * a * b * b) + (a * a * b) + (a * a * b) + (a * b * b) 
--     + (a * b * b) + (a * b) + (a * b) --> (a * a * b * b) + (a * 
--     b * b) + (a * b) + (a * b) + 0

-- のマッチングが変です。上をコンパクトに書き直すと

--     aabb + aab + aab + abb + abb + ab + ab

-- に対して

--     eq X + X + X = 0 .

-- が X = abb でマッチングして、結果が

--     aabb + abb + ab + ab + 0

-- になっています。どうも abb とaab が等価だとして扱われているようです。

-- 							-- ishisone
eof

aabb + aab + aab + abb + abb + ab + ab
