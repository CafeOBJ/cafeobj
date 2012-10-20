-- Return-Path: kokichi@shin.jaist.ac.jp 
-- Received: from srasva.sra.co.jp (root@srasva [133.137.12.2]) by sras75.sra.co.jp (8.6.13/3.4W-sra) with ESMTP id AAA18124 for <sawada@sras75.sra.co.jp>; Thu, 26 Mar 1998 00:39:31 +0900
-- Received: from sranha.sra.co.jp (sranha [133.137.8.8])
-- 	by srasva.sra.co.jp (8.8.7/3.6Wbeta7-srambox) with ESMTP id AAA01491
-- 	for <sawada@srasva.sra.co.jp>; Thu, 26 Mar 1998 00:39:33 +0900 (JST)
-- Received: from sraigw.sra.co.jp (sraigw-hub [133.137.8.14])
-- 	by sranha.sra.co.jp (8.8.7/3.6Wbeta7-sranha) with ESMTP id AAA21819
-- 	for <sawada@sra.co.jp>; Thu, 26 Mar 1998 00:39:30 +0900 (JST)
-- Received: from shin.jaist.ac.jp (shin.jaist.ac.jp [150.65.5.14])
-- 	by sraigw.sra.co.jp (8.8.7/3.6Wbeta7-sraigw) with ESMTP id AAA14192
-- 	for <sawada@sra.co.jp>; Thu, 26 Mar 1998 00:39:22 +0900 (JST)
-- Received: (from kokichi@localhost) by shin.jaist.ac.jp (8.7.5+2.6Wbeta6/3.4W3) id AAA00539; Thu, 26 Mar 1998 00:39:30 +0900
-- Date: Thu, 26 Mar 1998 00:39:30 +0900
-- From: Kokichi Futatsugi <kokichi@shin.jaist.ac.jp>
-- Message-Id: <199803251539.AAA00539@shin.jaist.ac.jp>
-- To: sawada@sra.co.jp
-- cc: diacon@jaist.ac.jp, s_iida@jaist.ac.jp
-- Subject: bugs?
-- Cc: kokichi@jaist.ac.jp
-- Reply-to: kokichi@jaist.ac.jp
-- Content-Type: text
-- Content-Length: 4288

-- Sawada-san,

-- Attached please find a bug report on which I sent e-mail.
-- You might received similar report from Razvan.

-- Kokichi

-- ==================================================================
-- 1. loading the following CafeOBJ code
-- ------------------------------------------------------------------
mod! STRG (X :: TRIV) {
  [ Elt < Strg ]

  op nil :  -> Elt 
  op __ : Strg Strg -> Strg {assoc idr: nil} 
}

mod* POSET {
  [ Elt ]

  op _<=_ : Elt Elt -> Bool 

  vars E1 E2 E3 : Elt

  eq E1 <= E1 = true .
  cq E1 = E2      if (E1 <= E2) and (E2 <= E1) .
  cq (E1 <= E3) = true      if (E1 <= E2) and (E2 <= E3) .
}

mod! I-POSET (Y :: POSET)
  principal-sort 2Tuple {
  protecting(2TUPLE(Y,NAT))

  op _<=_ : 2Tuple 2Tuple -> Bool

  vars E1 E2 : Elt
  vars N1 N2 : Nat 
    
  ceq << E1 ; N1 >> <= << E2 ; N2 >> = true if E1 <= E2 .
  ceq << E1 ; N1 >> <= << E2 ; N2 >> = true
     if ((E1 <= E2) =/= true) and ((E2 <= E1) =/= true) and (N1 <= N2) .
}

mod! STRG-MAPPING (Z :: POSET) {
  protecting ( STRG(Z) + STRG(I-POSET(Z))*{sort Strg -> 2Strg} )

  var E : Elt
  var N : Nat
  var S : Strg
  vars S1 S2 : 2Strg 
 
  op s : 2Tuple -> 2Tuple
  op s : 2Strg -> 2Strg 
    
  op [_] : Elt -> 2Tuple
  op [_] : Strg -> 2Strg 
    
  eq s(<< E ; N >>) = << E ; s(N) >> .
  eq s(S1 S2) =  s(S1) s(S2) .
  
  eq [ E ] = << E ; 1 >> .
  eq [ E S ] = << E ; 1 >> s([ S ]) .
}

-- ==================================================================
-- 2. We get
-- ------------------------------------------------------------------
-- CafeOBJ> in string
-- -- processing input : ./string.mod
-- -- defining module! STRG_*_*..._._* done.
-- -- defining module* POSET..._...* done.
-- -- defining module! I-POSET_*_*..,,,,,,_,,*...._..* done.
-- -- defining module! STRG-MAPPING_*_*.,,,,,,_,,,,,,,,,_,,*,,,,,_,,,*,,,,,_,,,,,,,,,_,,**_*........._...
-- [Error]: No parse for axiom (ignored): 
-- - possible LHS
         
--            [_]:2Strg  
--                |       
--             __:Strg   
--            /       \   
--          E:Elt  S:Strg
                       
         
--  No possible parse for RHS
-- -- failed to evaluate the form:
-- axiom declaration(equation): 
--  lhs = ([ E S ])
--  rhs = (<< E ; 1 >> s ( [ S ] ))

-- ** returning to top level

-- CafeOBJ> select STRG-MAPPING .

-- STRG-MAPPING(Z)> sh .
-- *
-- module! STRG-MAPPING (Z :: POSET)
-- {
--   imports {
--     protecting (STRG(X <= I-POSET(Y <= Z.STRG-MAPPING)) * {sort Strg
--                    -> 2Strg} + STRG(X <= Z.STRG-MAPPING))
--   }
--   signature {
--     op s : 2Strg -> 2Strg
--     op s : 2Strg -> 2Strg
--     op [ _ ] : Strg -> 2Strg
--     op [ _ ] : Strg -> 2Strg
--   }
--   axioms {
--     var E : Elt
--     var N : Nat
--     var S : Strg
--     var S1 : 2Strg
--     var S2 : 2Strg
--     eq s(<< E ; N >>) = << E ; (s N) >> .
--     eq s(S1 S2) = s(S1) s(S2) .
--     eq [ E ] = << E ; 1 >> .
--   }
-- }

-- STRG-MAPPING(Z)> show all sorts .
-- * visible sorts :
--   Elt, Elt < 2Strg Strg
--   2Strg, Elt < 2Strg
--   2Tuple
--   Strg, Elt < Strg

-- STRG-MAPPING(Z)> 

-- ==================================================================
-- 3. But the following should be replied after
-- STRG-MAPPING(Z)> show all sorts .
-- ------------------------------------------------------------------
-- * visible sorts :
--   Elt, Elt < Strg		<--- 
--   2Strg, 2Tuple < 2Strg		<--- 
--   2Tuple,   2Tuple < 2Strg	<--- 
--   Strg, Elt < Strg


-- ==================================================================
-- 4. Wnen get the following similar problem for POSET param!!
-- ------------------------------------------------------------------
-- ...> select ( STRG(POSET) + STRG(I-POSET(POSET))*{sort Strg -> 2Strg} ) .
-- ,,,,,,_,,,,,,,,,_,,*,,,,,_,,,*,,,,,_,,,,,,,,,_,,**_*

-- STRG(X <= I-POSET(Y <= POSET)) * { ... } + STRG(X <= POSET)> show all sorts .
-- * visible sorts :
--   2Strg, Elt < 2Strg
--   Elt, Elt < 2Strg Strg
--   2Tuple
--   Strg, Elt < Strg

-- STRG(X <= I-POSET(Y <= POSET)) * { ... } + STRG(X <= POSET)> 

-- ==================================================================
-- 4. But get no problems for for NAT param!!
-- ------------------------------------------------------------------
-- ...> select ( STRG(NAT) + STRG(I-POSET(NAT))*{sort Strg -> 2Strg} ) .

-- STRG(X <= I-POSET(Y <= NAT)) * { ... } + STRG(X <= NAT)> sh all sorts .
-- * visible sorts :
--   2Strg, 2Tuple < 2Strg
--   2Tuple, 2Tuple < 2Strg
--   Strg, Nat < Strg

-- %%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
