**>
**> FOPL-CLAUSE 自動輸入の検査
**>
module R
{
  [E]
  pred Shaves : E E
  op Barber : -> E
  var x : E
  ax Shaves(x,x) | Shaves(Barber, x) .
  ax Shaves(Barber,x) -> ~(Shaves(x,x)) .
}

**> モジュール R に自動的に FOPL-CLAUSE が輸入されているか
**> どうかを, show コマンドでみる.
show R .
