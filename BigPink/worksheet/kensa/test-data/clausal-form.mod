**>
**> 公理の節形式への自動変換検査
**> 

set include FOPL-CLAUSE on

module R
{

  [E]
  pred Shaves : E E
  op Barber : -> E
  var x : E
  ax[ax1]: Shaves(x,x) | Shaves(Barber, x) .
  ax[ax2]: Shaves(Barber,x) -> ~(Shaves(x,x)) .
}

option reset

**> モジュール R 文脈モジュールに設定する
--> select R
select R

**> 反駁システムの初期化
--> db reset
db reset

**> 自動変換されているはずの節集合を見る
--> list axioms
list axioms


