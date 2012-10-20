**>
**> Binary Resolution の試験
**> Otter 3.05 のサンプルプログラムを CafeOBJ
**> に書き換えたものであり，結果が反駁に成功することは
**> 分かっている．

module ANDREWS
{
  [ E ]
  pred p : E 
  pred q : E
}

open ANDREWS
protecting (FOPL-CLAUSE)

**> 証明したいゴール
goal [GOAL]: (( (\E[x:E] \A[y:E] (p (x) <-> p(y)))
		 <-> ( (\E[u:E] q(u)) <-> (\A[v:E] p(v)))))
	      <->
	      ((\E[w:E]\A[z:E] (q(z) <-> q(w)))
		<->
		  ((\E[x1:E] p(x1)) <-> (\A[x2:E] q(x2)))) .

**> システムのリセット
option reset
db reset
**> binary resolution を用いることを指定
flag(binary-res,on)
flag(process-input,on)
**> ログが長大となるので一部を抑制
flag(print-kept,off)
flag(print-back-sub,off)
evq (setq *print-line-limit* 40)

**> SOS の設定
sos = { GOAL }

**> エンジンの起動
resolve .

close
--
eof


