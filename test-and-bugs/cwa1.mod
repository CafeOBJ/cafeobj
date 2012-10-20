-- From: Razvan Diaconescu <diacon@jaist.ac.jp>
-- Date: Wed, 1 Oct 97 07:33:55 GMT
-- Message-Id: <9710010733.AA10513@is27e0s07.jaist.ac.jp>
-- To: sawada@sra.co.jp
-- Subject:  new bug in the implementation of ==>??
-- Content-Type: text
-- Content-Length: 962

-- Dear Toshimi,

-- I think I maybe discovered some bug related to the closed world
-- assumption, but I might be in fact confused. Please let me know what
-- you think about the following problem.

mod! NNAT {
  extending(NAT)

  op _|_ : Nat Nat -> Nat {r-assoc}
  
  vars M N : Nat

  trans N | M => N .
  trans N | M => M .
}

-- The following is a very compact proof score for 3 <= 4 | 4 |5:

-- red ((3 <= ( 4 | 4 | 5 ))  ==> false) == true .

-- It works fine, it gives *false*, which means there is no possible
-- transition which makes 3 <= ( 4 | 4 | 5 ) false, hence for all
-- transitions (i.e., for all non-deterministic choices) 3 <= ( 4 | 4 | 5
-- ) is always true.

-- With the new switch for CWA I hoped to be able to write this just as:

-- set closed world on .
-- red (3 <= ( 4 | 4 | 5 ))  ==> false .

-- But it gives *true*, which is wrong... I saw the trace, it seems the
-- system doesnt do too much in this case (contrasting to the exhaustive
-- computation in the first case).
