-- From: Michihiro Matumoto <mitihiro@jaist.ac.jp>
-- Date: Wed, 12 Nov 97 17:33:10 JST
-- Message-Id: <9711120833.AA13090@is27e0s04.jaist.ac.jp>
-- To: cafeteria@rascal.jaist.ac.jp
-- Subject: Bug for "sort qualifying" and "red command"
-- Resent-Message-ID: <"1QgSe.A.NhF.JnWa0"@rascal.jaist.ac.jp>
-- Resent-From: cafeteria@rascal.jaist.ac.jp
-- Reply-To: cafeteria@rascal.jaist.ac.jp
-- X-Mailing-List: <cafeteria@ldl.jaist.ac.jp> archive/latest/190
-- X-Loop: cafeteria@ldl.jaist.ac.jp
-- Precedence: list
-- Resent-Sender: cafeteria-request@rascal.jaist.ac.jp
-- Content-Type: text
-- Content-Length: 2108

-- 松本@JAIST です。

--   CafeOBJ system Version 1.4.0(Beta-3) の、"sort qualifying" と、
-- "red command" に関する不具合らしき現象を発見したので報告します。

--   以下のコードを実行します。

-- vvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvv

set auto context on .

mod! AB {
  [ A ]
  op a : -> A

  [ B ]
  op a : -> B
  op b : -> B

  eq b = a .
}

open .
red b == a:B .  --> this must be b == (a):B .

-- ^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^

-- すると、

--  vvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvv

-- %AB> set trace whole on .

-- %AB> red b == a:B .
-- -- reduce in % : b == a:B
-- [1]: b == a:B
-- ---> a == a:B
-- [2]: a == a:B
-- ---> false
-- false : Bool
-- (0.000 sec for parse, 2 rewrites(0.000 sec), 2 match attempts)

-- ^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^

-- と、true になるはずなのに、false になってしまいます。
-- なお、sort qualifying をしないと、以下のようにtrue になります。

-- vvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvv
-- %AB> red b == a .
-- [Warning]: Ambiguous term:
-- * Please select a term from the followings:
-- [1] _==_ :  Cosmos   Cosmos  -> Bool --------------------------
-- _==_:Bool
--   /    \  
--  b:B  a:B
          
-- [2] _==_ :  Cosmos   Cosmos  -> Bool --------------------------
-- _==_:Bool
--   /    \  
--  b:B  a:A
          
-- * Please input your choice (a number from 1 to 2, default is 1)? 1
-- Taking the first as correct.
-- -- reduce in % : b == a
-- [1]: b == a
-- ---> a == a
-- [2]: a == a
-- ---> true
-- true : Bool
-- (1.533 sec for parse, 2 rewrites(0.000 sec), 2 match attempts)

-- ^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^

-- 但し、sort qualifying しない場合、Ambiguous term: の選択で[2]を指定
-- した時も、true になってしまいます。
-- こちらのケースは、sort が違うので、falseになるはずだと思うのですが、
-- 違うのでしょうか？

-- -- 
-- 北陸先端科学技術大学院大学 情報科学研究科 情報システム学専攻
-- 言語設計学講座 二木研究室 博士前期課程 2年
-- 松本 充広 mitihiro@jaist.ac.jp

