**>
**> Hyper Resolution 検査
**> Otter3.0.5 の例題を CafeOBJ へ変換したもの．
**> 

module! WANG
{ 
  protecting (FOPL-CLAUSE)
  [ E ]

  ops m b k : -> E
  pred p : E E
  ops f g : E -> E

  vars x y z v v1 : E

  ax y = m | p(y,m) | v1 = m | v1 = y | ~ p(y,v1) | ~ p(v1,y).
  ax y = b | ~ p(y,b) | v = b | v = y | ~ p(y,v) | ~ p(v,y).
  ax y = k | y = m | y = b | ~ p(y,k).
  ax y = m | ~ p(y,m) | ~(f(y) = m) .
  ax y = m | ~ p(y,m) | ~(f(y) = y) .
  ax y = m | ~ p(y,m) | p(y,f(y)).
  ax y = m | ~ p(y,m) | p(f(y),y).
  ax y = b | ~ p(y,b) | ~(g(y) = b) .
  ax y = b | p(y,b) | ~(g(y) = y) .
  ax y = b | p(y,b) | p(y,g(y)).
  ax y = b | p(y,b) | p(g(y),y).
  ax y = k | ~(y = m) | p(y,k).
  ax y = k | ~(y = b) | p(y,k).
  ax x = x .
  ax ~(x = y) | y = x .
  ax ~(x = y) | ~(y = z) | x = z .
  ax ~(x = y) | ~ p(x,z) | p(y,z).
  ax ~(x = y) | ~ p(z,x) | p(z,y).
  ax ~(x = y) | f(x) = f(y).
  ax ~(x = y) | g(x) = g(y).
  **

  ax ~(m = b).
  ax ~(b = k).
  ax ~(k = m).
}

**> オプションのリセット
option reset
**> auto モードで実行する．
flag (auto,on)
**> 詳細な統計情報を印字するように設定する．
param (stats-level,4)

open WANG
**> 反駁エンジンの起動
resolve .
close
--
eof
