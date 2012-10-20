-- From: Michihiro Matumoto <mitihiro@jaist.ac.jp>
-- Date: Mon, 21 Apr 97 23:20:43 JST
-- Message-Id: <9704211420.AA13560@is27e0s04.jaist.ac.jp>
-- To: cafeteria@rascal.jaist.ac.jp
-- Subject: Problem about eq between ground terms.
-- Resent-Message-ID: <"Od8d8B.A.BkD.Ef3Wz"@rascal.jaist.ac.jp>
-- Resent-From: cafeteria@rascal.jaist.ac.jp
-- Reply-To: cafeteria@rascal.jaist.ac.jp
-- X-Mailing-List: <cafeteria@ldl.jaist.ac.jp> archive/latest/135
-- X-Loop: cafeteria@ldl.jaist.ac.jp
-- Precedence: list
-- Resent-Sender: cafeteria-request@rascal.jaist.ac.jp
-- Content-Type: text
-- Content-Length: 2031
-- 
-- 松本@二木研です。
-- 
--   ground term間のeqに関する不具合らしき現象を発見したので報告します。
-- 以前の"Problem between record and ground term ."と似たような現象です
-- が、showをすると、今回はeq "groud"がきちんと登録されています。
-- 
-- (CafeOBJのバージョン)
-- CafeOBJ system Version 1.2.0 + 1.2-patch.tar.gz
-- 
-- (現象)
--   下記コードを実行した時、
-- 
-- vvvvv

mod TEST
{
  protecting (NAT)
  record Ab {
    a : Nat
    b : Nat
  }
  op one-one : -> Ab
  eq [ ground ] : one-one = Ab { a = 1, b = 1 } .
}
select TEST .
red a(one-one) .  **> should be 1
red a(Ab { a = 1, b = 1 }) . **> should be 1

-- ^^^^^
-- 
-- red a(one-one)も1になるはずだが、
-- 
-- vvvvv
--
-- CafeOBJ> in te
-- processing input : ./te.mod
-- defining module TEST..._.* done.
-- reduce in TEST : a(one-one)
-- a(one-one) : Nat
-- (0.000 sec for parse, 0 rewrites(0.000 sec), 1 match attempts)
-- **> should be 1
-- reduce in TEST : a(Ab { (a = 1 , b = 1) })
-- 1 : NzNat
-- (0.000 sec for parse, 1 rewrites(0.017 sec), 3 match attempts)
-- **> should be 1
-- 
-- ^^^^^
-- 
-- となる。
-- なお、eqの代わりにletを使って、
-- 
-- vvvvv
-- 
-- mod TEST
--{
--  protecting (NAT)
--   record Ab {
--    a : Nat
--     b : Nat
--   }
-- }
-- select TEST .
-- let one-one = Ab { a = 1, b = 1 } .
-- red a(one-one) .  **> should be 1
-- red a(Ab { a = 1, b = 1 }) . **> should be 1
-- 
-- ^^^^^
--
-- とすると、
-- 
-- vvvvv
-- 
-- CafeOBJ> in te2
-- -- processing input : ./te2.mod
-- -- defining module TEST.._* done.
-- -- reduce in TEST : a(Ab { (a = 1 , b = 1) })
-- 1 : NzNat
-- (0.000 sec for parse, 1 rewrites(0.017 sec), 3 match attempts)
-- **> should be 1
-- -- reduce in TEST : a(Ab { (a = 1 , b = 1) })
-- 1 : NzNat
-- (0.000 sec for parse, 1 rewrites(0.000 sec), 3 match attempts)
-- **> should be 1
--
-- ^^^^^
-- 
-- と、1になる。
--
-- 
-- 北陸先端科学技術大学院大学 情報科学研究科 情報システム学専攻
-- 言語設計学講座 二木研究室 博士前期課程 2年 在学中
-- （株）PFU 研究所 第4研究室
-- 松本 充広 mitihiro@jaist.ac.jp / michi@pfu.co.jp
eof

