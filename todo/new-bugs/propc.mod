二木です

 |おしらせいただいた現象をどうしても再現することができませんでした。
 |これはかならず起きる現象なのでしょうか？
 |> PROPC> red not true .
 |> -- reduce in PROPC : (true)
 |> Error: Caught fatal error [memory may be damaged]
 |> Fast links are on: do (si::use-fast-links nil) for debugging
 |> Error signalled by CAFEOBJ-EVAL-REDUCE-PROC.

再現できました．結論からいうと，PROPC + BOOL というmoduleをつくり，そ
こで red を実行した後で，PROPCで red を実行すると，起こるようです．

以下の例を見て下さい．一番目はそれ自体面白い現象の報告にもなっています．
これを見ると，PROPCとBOOLを混在させるのは危険なのでしょうか？

そうであれば，BOOLにPROPCの機能を共に抱かせてしまいそれをBOOLとして
PROPCはなくす方が良いかも知れませんね？

この際，PROPCはいろんなところで必要になる完全な命題論理書き換え系です
から，上のBOOLは完全な書き換え系である必要はありますが．

*** で始まる行は私のコメントです．

%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
PROPC + BOOL> red not not B:Bool .
-- reduce in PROPC + BOOL : not (not B:Bool)
not (not B:Bool) : Bool
(0.000 sec for parse, 0 rewrites(0.390 sec), 4 matches)

*** PROPC + BOOLでは
***	not (not B:Bool) は B:Boolに簡約できない．
*** その理由は以下の通り．

PROPC + BOOL> sh sort Prop
Sort Prop declared in the module PROPC
  - subsort relations :
  
         ?Prop    
           |       
         Prop     
       /        \  
  Identifier  Bool
                   
  
PROPC + BOOL> sh op not_
.............................(not _).............................
  * rank: Prop -> Prop
    - attributes:  { strat: (0 1) prec: 53 }
    - axioms:
      eq not p:Prop = p:Prop xor true
  * rank: Bool -> Bool
    - attributes:  { prec: 53 }
    - axioms:
      eq not true = false
      eq not false = true

PROPC + BOOL> select PROPC
PROPC> red not not B:Bool .
-- reduce in PROPC : ((B:Bool))

*** これは B:Boolに簡約できるはず，しかし以下のようにシステムは暴走す
*** る．

Error: Caught fatal error [memory may be damaged]
Fast links are on: do (si::use-fast-links nil) for debugging
Error signalled by CAFEOBJ-EVAL-REDUCE-PROC.
Broken at PERFORM-REDUCTION.  Type :H for Help.
CHAOS>>


*** 実はこれ以下のようにもっと簡単な例で再現される．

             -- CafeOBJ system Version 1.4.2(b1) --
                built: 1998 Jul 1 Wed 10:59:03 GMT
                      prelude file: std.bin
                               ***
                   1998 Jul 2 Thu 12:15:23 GMT
                         Type ? for help
                               ---
                   uses GCL (GNU Common Lisp)
            Licensed under GNU Public Library License
              Contains Enhancements by W. Schelter
CafeOBJ> select (PROPC + BOOL)
_*
PROPC + BOOL> red not true .
-- reduce in PROPC + BOOL : not true
false : Bool
(0.000 sec for parse, 1 rewrites(0.020 sec), 1 matches)
PROPC + BOOL> select PROPC
PROPC> red not true .
-- reduce in PROPC : (true)
Error: Caught fatal error [memory may be damaged]
Fast links are on: do (si::use-fast-links nil) for debugging
Error signalled by CAFEOBJ-EVAL-REDUCE-PROC.
Broken at PERFORM-REDUCTION.  Type :H for Help.
CHAOS>>

*** 以上



















 |
 |この項の評価は PROPC での簡約で日常的に出現するもので、単純な
 |バグとはとても思えません。
 |トップレベルのスイッチの設定や、`red not true' を実行する前に
 |何を行なったかに影響されている可能性がありますので、申し訳ありませんが、
 |お調べになれる範囲で情報をお知らせいただければ幸いです。
 |あと、すみませんがインタプリタのバージョンもお知らせください。
 |-- sawada@sra.co.jp
 |
