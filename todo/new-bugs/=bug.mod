-- From: Razvan Diaconescu <diacon@jaist.ac.jp>
-- Date: Sun, 3 May 98 19:13:33 JST
-- Message-Id: <9805031013.AA04580@is27e0s07.jaist.ac.jp>
-- To: sawada@sra.co.jp
-- Subject:  little bug on =*= ??
-- Content-Type: text
-- Content-Length: 543

-- Dear Toshimi,

-- I find a bit strange that when loading the following module there is
-- no messgage from  CafeOBJ about =*=. Is this a little bug?

mod! UBUF(X :: TRIV) {

  *[ UBuf ]*

  op init :  -> UBuf
  op put : UBuf Elt -> UBuf {coherent}
  bop get_ : UBuf -> Elt
  bop empty? : UBuf -> Bool

  var UB : UBuf
  var E : Elt

  eq empty?(init) = true .
  cq get put(UB, E) = E 
     if not empty?(put(UB, E)) .
}

eof

-- defining module! UBUF
[Warning]: redefining module UBUF _*_*........_..* done.
UBUF(X)>

--
Best regards,
Razvan


