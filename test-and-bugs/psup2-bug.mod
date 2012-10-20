-- To: sawada@sra.co.jp
-- Cc: mikami@is.s.u-tokyo.ac.jp, yas@yk.is.noda.sut.ac.jp,
--         joker@sy.is.noda.sut.ac.jp
-- Subject: Re: parser 
-- In-reply-to: Your message of "Tue, 02 Sep 1997 15:12:20 JST."
-- Mime-Version: 1.0 (generated by tm-edit 7.106)
-- Date: Thu, 18 Sep 1997 20:58:31 +0900
-- From: Masaki Ishiguro <masa@mri.co.jp>
-- Content-Type: text/plain; charset=ISO-2022-JP
-- Content-Length: 1733


-- $B_7EDMM(B:

-- $B2<5-$N7o$G$9$,(B,  CafeOBJ system Version 1.3.1(Roman) $B$G;n$7$?$H$3$m(B, 
-- $BF1$8%(%i!<$H$J$j$^$7$?(B.  Version 1.3.b7$B$O@5$7$/F0$/$N$G$9$,(B, $B$=$NHG$K(B
-- $B$O(B psup-unparse-expression $B$,4^$^$l$J$$$?$a(B, $BF1;~$K$D$+$&$3$H$,=PMh$^(B
-- $B$;$s(B. 
-- $B$43NG'D:$1$^$9$G$7$g$&$+(B. 
-- --
-- $B@P9u(B

-- >> To: sawada@sra.co.jp
-- >> Subject: parser

-- >> CafeOBJ$B%Q!<%6$N7o$G$9$,(B, CafeOBJ system Version 1.3.1 $B$G(B 
-- >> psup-image-of-axioms $B$r0J2<$N;EMM$G;H$*$&$H$7$^$7$?$H$3$m(B, $B%(%i!<$H$J$C(B
-- >> $B$F$7$^$$$^$9(B. $BA0$NHG$G$O(B, psup-image-of-axioms $B$NF0:n$r3NG'$7$F$$$?$N(B
-- >> $B$G$9$,(B. $BD4$Y$FD:$1$J$$$G$7$g$&$+(B. 
-- >> 
-- >> ------------------------------------------------------------------
-- >> 
-- >> 
mod TOSET {
  [ Elt ]
  op _<_ : Elt Elt -> Bool
  vars E1 E2 E3 : Elt
  eq E1 < E1 = false .
  cq E1 < E3 = true if (E1 < E2) and (E2 < E3) .
  cq (E1 < E2) or (E2 < E1) = true if E1 =/= E2 .
}

mod NAT' {
  [ Nat ]
  op 0 : -> Nat
  op s : Nat -> Nat
  op _+_ : Nat Nat -> Nat 
  op _<_ : Nat Nat -> Bool
  vars m n : Nat
  eq m + 0 = m .
  eq m + s(n) = s(m + n) .
  eq 0 < s(n) = true .
  eq n < 0 = false .
  eq s(n) < s(m) = n < m .
  
}

view F from TOSET to NAT' {
  sort Elt -> Nat
  op _<_ -> _<_
}
 
-- ------------------------------------------------------------------
--  CafeOBJ> in view-obl
--  -- processing input : ./view-obl.mod
--  -- defining module TOSET..._...* done.
--  -- defining module NAT'......_.....* done.
--  -- defining view F  done.
 
--  CafeOBJ> evq (psup-image-of-axioms "F")
--  Broken at PSUP-IMAGE-OF-AXIOMS.  Type :H for Help.
--  CHAOS>>

