-- 澤田さん

-- 先日電話でご相談したcafeobjのsubsortに関係した奇妙な現象に出会ったので、
-- 参考のためのお送りしておきます。

-- 以下の例で、

--   op 0 : -> Nat
-- と
--   op 0 : -> NatHalt .
-- はshowやdesicribeで見る限りoverloadされた一つのoperatorとして処理されて
-- いるように見えますが、
-- 　parse s 0 .     -- ambiguous
-- のように2つの0があるように見えたり。

-- parse 0:Nat + s 0:Nat . -- parsed
-- red 0:Nat + s 0:Nat .  -- no reduction; no matching
-- のように、parse出来てもmatchされない、といった現象があります。

-- すでにあるsortのsubsortを後から付け加えるというのは、危険である可能性が
-- 高いので、これを禁止するというのが良いのかもしれません。

-- op宣言や、sort宣言を処理するときに、すでにある名前(id)に出会うたびに
-- warnningを発し、危険なものは受け付けない、ということでこの手の問題の多く
-- は解決するように思いますが、いかがでしょうか？

-- 二木

-- =============================================
mod! NAT+ {
  [ Nat]
  op 0 : -> Nat
  op s_ : Nat -> Nat
  op _+_ : Nat Nat -> Nat

  eq 0 +  N:Nat = N .
  eq (s M:Nat) + N:Nat = s(M + N) .
}

-- open NAT+
-- [ NatHalt < Nat ]
-- op 0 : -> NatHalt .

-- parse 0 .       -- can be parsed as a term of the minimum sort 0:NatHalt
-- parse 0:Nat .   -- can be parsed
-- parse s 0 .     -- Ambiguous
-- parse s 0:NatHalt .  -- parsed
-- parse s 0:Nat .   -- parsed

-- parse 0:Nat + s 0:Nat . -- parsed
-- red 0:Nat + s 0:Nat .  -- no reduction; no matching

-- parse 0:NatHalt + s 0:NatHalt . -- parsed
-- red 0:NatHalt + s 0:NatHalt .  -- no reduction; no matching

-- close


mod NAT+test {
ex(NAT+)
[ NatHalt < Nat ]
op 0 : -> NatHalt }

select NAT+test

set debug parse on
**> parse 0 .       -- can be parsed as a term of the minimum sort 0:NatHalt
parse 0 .       -- can be parsed as a term of the minimum sort 0:NatHalt
**> parse 0:Nat .   -- can be parsed
parse 0:Nat .   -- can be parsed
**> parse s 0 .     -- ambiguous
parse s 0 .     -- ambiguous
**> parse s 0:NatHalt .  -- parsed
parse s 0:NatHalt .  -- parsed
**> parse s 0:Nat .   -- parsed
parse s 0:Nat .   -- parsed
**> parse 0:Nat + s 0:Nat . -- parsed
parse 0:Nat + s 0:Nat . -- parsed

set debug rewrite on
**> red 0:Nat + s 0:Nat .  -- no reduction; no matching
red 0:Nat + s 0:Nat .  -- no reduction; no matching

**> parse 0:NatHalt + s 0:NatHalt . -- parsed
parse 0:NatHalt + s 0:NatHalt . -- parsed
**> red 0:NatHalt + s 0:NatHalt .  -- no reduction; no matching
red 0:NatHalt + s 0:NatHalt .

eof
-- =============================================




