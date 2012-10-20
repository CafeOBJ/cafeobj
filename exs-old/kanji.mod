** -*- Mode:CafeOBJ -*-
-- NOTE: This documentation contains Japanese Kanji characters.
--> 日本語文字を使用した例．たまたま動いているだけということに注意．
--> 何の保証もありません．(ECU コードを使用)．

--  MUST FIX 'variation in id completion for ...'

module 自然数 {
  signature {
    [ 自然数 ]
    op 0 : -> 自然数
    op 後 : 自然数 -> 自然数
    op _足す_ : 自然数 自然数 -> 自然数 {
      assoc comm idr: 0 prec: 3
    }
    op _掛ける_ : 自然数 自然数 -> 自然数 {
      assoc comm idr: (後(0)) prec: 2
    }
  }
  axioms {
    vars m n : 自然数
    eq 後(m) 足す n = 後(m 足す (n)) .
    eq m 掛ける 0 = 0 .
    eq m 掛ける 後(n) = m 掛ける n 足す m .

  }
}

module 整数 {
  protecting (自然数)
  signature {
    [ 自然数 < 整数 ]
    op _足す_ : 整数 整数 -> 整数 {
      assoc comm idr: 0 prec: 3
    }
    op _掛ける_ : 整数 整数 -> 整数 {
      assoc comm idr: (後(0)) prec: 2
    }
    op 負_ : 整数 -> 整数
    op 後 : 整数 -> 整数
    op 前 : 整数 -> 整数
  }
  axioms {
    vars n : 整数
    eq 負 負 n = n .
    eq 負 0 = 0 .
    eq 後(前(n)) = n .
    eq 前(後(n)) = n .
  }
}

module 群 
     principal-sort 要素
{
  [ 要素 ]
  op 単位元 : -> 要素
  op _×_ : 要素 要素 -> 要素 { assoc id: 単位元 }
  op _の逆元 : 要素 -> 要素
  eq (x:要素 の逆元) × x = 単位元 .
  eq x:要素 × (x の逆元) = 単位元 .
}

view 加法群 from 群 to 整数 {
  sort 要素 -> 整数,
  op 単位元 -> 0,
  op _×_ -> _足す_,
  op _の逆元 -> 負_
}

--
eof
**
$Id: kanji.mod,v 1.1.1.1 2003-06-19 08:30:16 sawada Exp $
