-- From: Razvan Diaconescu <diacon@jaist.ac.jp>
-- Date: Sun, 24 May 98 18:14:40 JST
-- Message-Id: <9805240914.AA02610@is27e0s07.jaist.ac.jp>
-- To: sawada@sra.co.jp
-- Subject:  another parameterization issue
-- Cc: kokichi@jaist.ac.jp, s_iida@jaist.ac.jp
-- Content-Type: text
-- Content-Length: 18044

-- Dear Toshimi,

-- Here is another parameterization problem. This one is actually very
-- subtle and goes to the heart of the our language parameterization
-- mechanism. I think that if we can understand this issue properly and
-- fix it in the system, then this would mean an important step forward
-- for our system.

-- This problem is extracted from the Jewels paper, and it seems the
-- system does not support such kind of specification.

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

mod! I-POSET (Y' :: POSET)
  principal-sort 2Tuple {
  protecting(2TUPLE(Y',NAT))

  op _<=_ : 2Tuple 2Tuple -> Bool

  vars E1 E2 : Elt
  vars N1 N2 : Nat 
    
  ceq << E1 ; N1 >> <= << E2 ; N2 >> = true if E1 <= E2 .
  ceq << E1 ; N1 >> <= << E2 ; N2 >> = true
     if (E1 <= E2 =/= true) and (E2 <= E1 =/= true) and (N1 <= N2) .
}

mod! STRG-MAPPING (Z :: POSET) {
  protecting(STRG(Z) + STRG(I-POSET(Z))* { sort Strg -> 2Strg })
  -- protecting(STRG(Z) +
  --	       STRG(I-POSET(Z){sort Elt -> 2Tuple})* { sort Strg -> 2Strg })

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

-- 
eof

If you have any idea how this can be achieved with the actual system,
please tell us. But I expect that some change/improvement on the
implementation is necessary in order to make such example work.

In order to facilitate the understanding of the module structure of
this example I prepared a eps file with the corresponding *commuting*
diagrams. I attach it at the end of this message.

Best regards,
Razvan
------------------------------------------------------
%!
%%BoundingBox: 47 440 300 737
%%Title: sorting
%%CreationDate: Sat May 23 18:22:21 1998
%%Creator: Tgif-3.0J-p13 by William Chia-Wei Cheng (william@cs.UCLA.edu)

/tgifdict 4 dict def
tgifdict begin

/tgifarrowtipdict 8 dict def
tgifarrowtipdict /mtrx matrix put

/tgifarrowtip
 { tgifarrowtipdict begin
      /dy exch def
      /dx exch def
      /h exch def
      /w exch def
      /y exch def
      /x exch def
      /savematrix mtrx currentmatrix def
      x y translate
      dy dx atan rotate
      0 0 moveto
      w neg h lineto
      w neg h neg lineto
      savematrix setmatrix
   end
 } def

end

%%PageBoundingBox: 47 440 300 737
tgifdict begin
/tgifsavedpage save def

1 setmiterlimit
1 setlinewidth

0 setgray

72 0 mul 72 11.70 mul translate
72 128 div 100.000 mul 100 div dup neg scale

gsave

/tgiforigctm matrix currentmatrix def

% TEXT
0 setgray
/Helvetica findfont [12 0 0 -12 0 0] makefont setfont
   gsave
      196 272 moveto (2TUPLE\(Y',NAT\)) show
   grestore

% POLY/OPEN-SPLINE
0 setgray
gsave
   newpath
      232 256 moveto
      -52 0 atan dup cos 8.000 mul 232 exch sub
      exch sin 8.000 mul 204 exch sub lineto
   tgiforigctm setmatrix
   1 setlinewidth
   stroke
grestore
gsave
   tgiforigctm setmatrix
   newpath
      232 204 8.000 3.000 0 -52 tgifarrowtip
   1 setgray closepath fill
   0 setgray
   newpath
      232 204 8.000 3.000 0 -52 tgifarrowtip
   closepath fill
grestore

% POLY/OPEN-SPLINE
0 setgray
gsave
   newpath
      232 328 moveto
      -52 0 atan dup cos 8.000 mul 232 exch sub
      exch sin 8.000 mul 276 exch sub lineto
   tgiforigctm setmatrix
   1 setlinewidth
   stroke
grestore
gsave
   tgiforigctm setmatrix
   newpath
      232 276 8.000 3.000 0 -52 tgifarrowtip
   1 setgray closepath fill
   0 setgray
   newpath
      232 276 8.000 3.000 0 -52 tgifarrowtip
   closepath fill
grestore

% POLY/OPEN-SPLINE
0 setgray
gsave
   newpath
      136 268 moveto
      0 56 atan dup cos 8.000 mul 192 exch sub
      exch sin 8.000 mul 268 exch sub lineto
   tgiforigctm setmatrix
   1 setlinewidth
   stroke
grestore
gsave
   tgiforigctm setmatrix
   newpath
      192 268 8.000 3.000 56 0 tgifarrowtip
   1 setgray closepath fill
   0 setgray
   newpath
      192 268 8.000 3.000 56 0 tgifarrowtip
   closepath fill
grestore

% POLY/OPEN-SPLINE
0 setgray
gsave
   newpath
      348 268 moveto
      0 -52 atan dup cos 8.000 mul 296 exch sub
      exch sin 8.000 mul 268 exch sub lineto
   tgiforigctm setmatrix
   1 setlinewidth
   stroke
grestore
gsave
   tgiforigctm setmatrix
   newpath
      296 268 8.000 3.000 -52 0 tgifarrowtip
   1 setgray closepath fill
   0 setgray
   newpath
      296 268 8.000 3.000 -52 0 tgifarrowtip
   closepath fill
grestore

% TEXT
0 setgray
/Helvetica findfont [12 0 0 -12 0 0] makefont setfont
   gsave
      204 200 moveto (I-POSET) show
   grestore

% TEXT
0 setgray
/Helvetica findfont [12 0 0 -12 0 0] makefont setfont
   gsave
      352 272 moveto (NAT) show
   grestore

% TEXT
0 setgray
/Helvetica findfont [12 0 0 -12 0 0] makefont setfont
   gsave
      212 344 moveto (2TUPLE) show
   grestore

% TEXT
0 setgray
/Helvetica findfont [12 0 0 -12 0 0] makefont setfont
   gsave
      88 272 moveto (POSET) show
   grestore

% TEXT
0 setgray
/Helvetica findfont [12 0 0 -12 0 0] makefont setfont
   gsave
      96 344 moveto (TRIV) show
   grestore

% TEXT
0 setgray
/Helvetica findfont [12 0 0 -12 0 0] makefont setfont
   gsave
      348 344 moveto (TRIV) show
   grestore

% POLY/OPEN-SPLINE
0 setgray
gsave
   newpath
      108 328 moveto
      -52 0 atan dup cos 8.000 mul 108 exch sub
      exch sin 8.000 mul 276 exch sub lineto
   tgiforigctm setmatrix
   1 setlinewidth
   stroke
grestore
gsave
   tgiforigctm setmatrix
   newpath
      108 276 8.000 3.000 0 -52 tgifarrowtip
   1 setgray closepath fill
   0 setgray
   newpath
      108 276 8.000 3.000 0 -52 tgifarrowtip
   closepath fill
grestore

% POLY/OPEN-SPLINE
0 setgray
gsave
   newpath
      128 340 moveto
      0 80 atan dup cos 8.000 mul 208 exch sub
      exch sin 8.000 mul 340 exch sub lineto
   tgiforigctm setmatrix
   1 setlinewidth
   stroke
grestore
gsave
   tgiforigctm setmatrix
   newpath
      208 340 8.000 3.000 80 0 tgifarrowtip
   1 setgray closepath fill
   0 setgray
   newpath
      208 340 8.000 3.000 80 0 tgifarrowtip
   closepath fill
grestore

% POLY/OPEN-SPLINE
0 setgray
gsave
   newpath
      344 340 moveto
      0 -84 atan dup cos 8.000 mul 260 exch sub
      exch sin 8.000 mul 340 exch sub lineto
   tgiforigctm setmatrix
   1 setlinewidth
   stroke
grestore
gsave
   tgiforigctm setmatrix
   newpath
      260 340 8.000 3.000 -84 0 tgifarrowtip
   1 setgray closepath fill
   0 setgray
   newpath
      260 340 8.000 3.000 -84 0 tgifarrowtip
   closepath fill
grestore

% POLY/OPEN-SPLINE
0 setgray
gsave
   newpath
      364 332 moveto
      -60 0 atan dup cos 8.000 mul 364 exch sub
      exch sin 8.000 mul 272 exch sub lineto
   tgiforigctm setmatrix
   1 setlinewidth
   stroke
grestore
gsave
   tgiforigctm setmatrix
   newpath
      364 272 8.000 3.000 0 -60 tgifarrowtip
   1 setgray closepath fill
   0 setgray
   newpath
      364 272 8.000 3.000 0 -60 tgifarrowtip
   closepath fill
grestore

% POLY/OPEN-SPLINE
0 setgray
gsave
   newpath
      116 260 moveto
      -56 88 atan dup cos 8.000 mul 204 exch sub
      exch sin 8.000 mul 204 exch sub lineto
   tgiforigctm setmatrix
   1 setlinewidth
   stroke
grestore
gsave
   tgiforigctm setmatrix
   newpath
      204 204 8.000 3.000 88 -56 tgifarrowtip
   1 setgray closepath fill
   0 setgray
   newpath
      204 204 8.000 3.000 88 -56 tgifarrowtip
   closepath fill
grestore

% TEXT
0 setgray
/Helvetica findfont [10 0 0 -10 0 0] makefont setfont
   gsave
      148 231 moveto (Y') show
   grestore

% TEXT
0 setgray
/Helvetica findfont [10 0 0 -10 0 0] makefont setfont
   gsave
      156 355 moveto (C1) show
   grestore

% TEXT
0 setgray
/Helvetica findfont [10 0 0 -10 0 0] makefont setfont
   gsave
      292 355 moveto (C2) show
   grestore

% TEXT
0 setgray
/Helvetica findfont [10 0 0 -10 0 0] makefont setfont
   gsave
      236 307 moveto (K) show
   grestore

% TEXT
0 setgray
/Helvetica findfont [10 0 0 -10 0 0] makefont setfont
   gsave
      372 307 moveto (*) show
   grestore

% TEXT
0 setgray
/Helvetica findfont [10 0 0 -10 0 0] makefont setfont
   gsave
      100 307 moveto (*) show
   grestore

% TEXT
0 setgray
/Helvetica findfont [10 0 0 -10 0 0] makefont setfont
   gsave
      156 283 moveto (K1) show
   grestore

% TEXT
0 setgray
/NewCenturySchlbk-Roman findfont [10 0 0 -10 0 0] makefont setfont
   gsave
      320 283 moveto (K2) show
   grestore

% TEXT
0 setgray
/Helvetica findfont [10 0 0 -10 0 0] makefont setfont
   gsave
      408 255 moveto (2TUPLE \(Y',NAT\)) show
   grestore

% TEXT
0 setgray
/Times-Roman findfont [10 0 0 -10 0 0] makefont setfont
   gsave
      408 270 moveto (is a co-limit with ) show
   grestore

% TEXT
0 setgray
/Helvetica findfont [10 0 0 -10 0 0] makefont setfont
   gsave
      492 271 moveto (K,K1,K2) show
   grestore

% TEXT
0 setgray
/Times-Roman findfont [10 0 0 -10 0 0] makefont setfont
   gsave
      408 282 moveto (the co-limiting co-cone) show
   grestore

% TEXT
0 setgray
/Helvetica findfont [12 0 0 -12 0 0] makefont setfont
   gsave
      264 456 moveto (TRIV) show
   grestore

% TEXT
0 setgray
/Helvetica findfont [12 0 0 -12 0 0] makefont setfont
   gsave
      396 456 moveto (STRG) show
   grestore

% TEXT
0 setgray
/Helvetica findfont [12 0 0 -12 0 0] makefont setfont
   gsave
      380 388 moveto (STRG\(I-POSET\(Z\)\)) show
   grestore

% TEXT
0 setgray
/Helvetica findfont [12 0 0 -12 0 0] makefont setfont
   gsave
      172 388 moveto (I-POSET\(Z\)) show
   grestore

% TEXT
0 setgray
/Helvetica findfont [12 0 0 -12 0 0] makefont setfont
   gsave
      396 520 moveto (STRG\(Z\)) show
   grestore

% POLY/OPEN-SPLINE
0 setgray
gsave
   newpath
      408 460 moveto
      48 0 atan dup cos 8.000 mul 408 exch sub
      exch sin 8.000 mul 508 exch sub lineto
   tgiforigctm setmatrix
   1 setlinewidth
   stroke
grestore
gsave
   tgiforigctm setmatrix
   newpath
      408 508 8.000 3.000 0 48 tgifarrowtip
   1 setgray closepath fill
   0 setgray
   newpath
      408 508 8.000 3.000 0 48 tgifarrowtip
   closepath fill
grestore

% POLY/OPEN-SPLINE
0 setgray
gsave
   newpath
      408 440 moveto
      -48 0 atan dup cos 8.000 mul 408 exch sub
      exch sin 8.000 mul 392 exch sub lineto
   tgiforigctm setmatrix
   1 setlinewidth
   stroke
grestore
gsave
   tgiforigctm setmatrix
   newpath
      408 392 8.000 3.000 0 -48 tgifarrowtip
   1 setgray closepath fill
   0 setgray
   newpath
      408 392 8.000 3.000 0 -48 tgifarrowtip
   closepath fill
grestore

% POLY/OPEN-SPLINE
0 setgray
gsave
   newpath
      296 452 moveto
      0 96 atan dup cos 8.000 mul 392 exch sub
      exch sin 8.000 mul 452 exch sub lineto
   tgiforigctm setmatrix
   1 setlinewidth
   stroke
grestore
gsave
   tgiforigctm setmatrix
   newpath
      392 452 8.000 3.000 96 0 tgifarrowtip
   1 setgray closepath fill
   0 setgray
   newpath
      392 452 8.000 3.000 96 0 tgifarrowtip
   closepath fill
grestore

% TEXT
0 setgray
/Helvetica findfont [12 0 0 -12 0 0] makefont setfont
   gsave
      188 520 moveto (POSET) show
   grestore

% POLY/OPEN-SPLINE
0 setgray
gsave
   newpath
      204 508 moveto
      -116 0 atan dup cos 8.000 mul 204 exch sub
      exch sin 8.000 mul 392 exch sub lineto
   tgiforigctm setmatrix
   1 setlinewidth
   stroke
grestore
gsave
   tgiforigctm setmatrix
   newpath
      204 392 8.000 3.000 0 -116 tgifarrowtip
   1 setgray closepath fill
   0 setgray
   newpath
      204 392 8.000 3.000 0 -116 tgifarrowtip
   closepath fill
grestore

% POLY/OPEN-SPLINE
0 setgray
gsave
   newpath
      232 516 moveto
      0 160 atan dup cos 8.000 mul 392 exch sub
      exch sin 8.000 mul 516 exch sub lineto
   tgiforigctm setmatrix
   1 setlinewidth
   stroke
grestore
gsave
   tgiforigctm setmatrix
   newpath
      392 516 8.000 3.000 160 0 tgifarrowtip
   1 setgray closepath fill
   0 setgray
   newpath
      392 516 8.000 3.000 160 0 tgifarrowtip
   closepath fill
grestore

% POLY/OPEN-SPLINE
0 setgray
gsave
   newpath
      244 384 moveto
      0 132 atan dup cos 8.000 mul 376 exch sub
      exch sin 8.000 mul 384 exch sub lineto
   tgiforigctm setmatrix
   1 setlinewidth
   stroke
grestore
gsave
   tgiforigctm setmatrix
   newpath
      376 384 8.000 3.000 132 0 tgifarrowtip
   1 setgray closepath fill
   0 setgray
   newpath
      376 384 8.000 3.000 132 0 tgifarrowtip
   closepath fill
grestore

% POLY/OPEN-SPLINE
0 setgray
gsave
   newpath
      272 460 moveto
      44 -48 atan dup cos 8.000 mul 224 exch sub
      exch sin 8.000 mul 504 exch sub lineto
   tgiforigctm setmatrix
   1 setlinewidth
   stroke
grestore
gsave
   tgiforigctm setmatrix
   newpath
      224 504 8.000 3.000 -48 44 tgifarrowtip
   1 setgray closepath fill
   0 setgray
   newpath
      224 504 8.000 3.000 -48 44 tgifarrowtip
   closepath fill
grestore

% POLY/OPEN-SPLINE
0 setgray
gsave
   newpath
      268 440 moveto
      -48 -44 atan dup cos 8.000 mul 224 exch sub
      exch sin 8.000 mul 392 exch sub lineto
   tgiforigctm setmatrix
   1 setlinewidth
   stroke
grestore
gsave
   tgiforigctm setmatrix
   newpath
      224 392 8.000 3.000 -44 -48 tgifarrowtip
   1 setgray closepath fill
   0 setgray
   newpath
      224 392 8.000 3.000 -44 -48 tgifarrowtip
   closepath fill
grestore

% TEXT
0 setgray
/Helvetica findfont [10 0 0 -10 0 0] makefont setfont
   gsave
      256 423 moveto (*) show
   grestore

% TEXT
0 setgray
/Helvetica findfont [10 0 0 -10 0 0] makefont setfont
   gsave
      256 491 moveto (*) show
   grestore

% TEXT
0 setgray
/Helvetica findfont [10 0 0 -10 0 0] makefont setfont
   gsave
      324 447 moveto (   X) show
   grestore

% TEXT
0 setgray
/Helvetica findfont [10 0 0 -10 0 0] makefont setfont
   gsave
      188 451 moveto (Y') show
   grestore

% TEXT
0 setgray
/Helvetica findfont [10 0 0 -10 0 0] makefont setfont
   gsave
      304 379 moveto (X'') show
   grestore

% TEXT
0 setgray
/Helvetica findfont [12 0 0 -12 0 0] makefont setfont
   gsave
      304 532 moveto (X') show
   grestore

% TEXT
0 setgray
/Helvetica findfont [12 0 0 -12 0 0] makefont setfont
   gsave
      216 568 moveto (I-POSET\(Z\)) show
   grestore

% TEXT
0 setgray
/Helvetica findfont [12 0 0 -12 0 0] makefont setfont
   gsave
      372 568 moveto (STRG\(I-POSET\(Z\)\)) show
   grestore

% TEXT
0 setgray
/Helvetica findfont [12 0 0 -12 0 0] makefont setfont
   gsave
      212 636 moveto (POSET) show
   grestore

% TEXT
0 setgray
/Helvetica findfont [12 0 0 -12 0 0] makefont setfont
   gsave
      392 636 moveto (STRG-MAPPING) show
   grestore

% TEXT
0 setgray
/Helvetica findfont [12 0 0 -12 0 0] makefont setfont
   gsave
      308 708 moveto (STRG\(Z\)) show
   grestore

% POLY/OPEN-SPLINE
0 setgray
gsave
   newpath
      240 624 moveto
      -56 0 atan dup cos 8.000 mul 240 exch sub
      exch sin 8.000 mul 568 exch sub lineto
   tgiforigctm setmatrix
   1 setlinewidth
   stroke
grestore
gsave
   tgiforigctm setmatrix
   newpath
      240 568 8.000 3.000 0 -56 tgifarrowtip
   1 setgray closepath fill
   0 setgray
   newpath
      240 568 8.000 3.000 0 -56 tgifarrowtip
   closepath fill
grestore

% POLY/OPEN-SPLINE
0 setgray
gsave
   newpath
      256 632 moveto
      0 132 atan dup cos 8.000 mul 388 exch sub
      exch sin 8.000 mul 632 exch sub lineto
   tgiforigctm setmatrix
   1 setlinewidth
   stroke
grestore
gsave
   tgiforigctm setmatrix
   newpath
      388 632 8.000 3.000 132 0 tgifarrowtip
   1 setgray closepath fill
   0 setgray
   newpath
      388 632 8.000 3.000 132 0 tgifarrowtip
   closepath fill
grestore

% POLY/OPEN-SPLINE
0 setgray
gsave
   newpath
      288 564 moveto
      0 80 atan dup cos 8.000 mul 368 exch sub
      exch sin 8.000 mul 564 exch sub lineto
   tgiforigctm setmatrix
   1 setlinewidth
   stroke
grestore
gsave
   tgiforigctm setmatrix
   newpath
      368 564 8.000 3.000 80 0 tgifarrowtip
   1 setgray closepath fill
   0 setgray
   newpath
      368 564 8.000 3.000 80 0 tgifarrowtip
   closepath fill
grestore

% POLY/OPEN-SPLINE
0 setgray
gsave
   newpath
      424 572 moveto
      52 0 atan dup cos 8.000 mul 424 exch sub
      exch sin 8.000 mul 624 exch sub lineto
   tgiforigctm setmatrix
   1 setlinewidth
   stroke
grestore
gsave
   tgiforigctm setmatrix
   newpath
      424 624 8.000 3.000 0 52 tgifarrowtip
   1 setgray closepath fill
   0 setgray
   newpath
      424 624 8.000 3.000 0 52 tgifarrowtip
   closepath fill
grestore

% POLY/OPEN-SPLINE
0 setgray
gsave
   newpath
      244 640 moveto
      56 72 atan dup cos 8.000 mul 316 exch sub
      exch sin 8.000 mul 696 exch sub lineto
   tgiforigctm setmatrix
   1 setlinewidth
   stroke
grestore
gsave
   tgiforigctm setmatrix
   newpath
      316 696 8.000 3.000 72 56 tgifarrowtip
   1 setgray closepath fill
   0 setgray
   newpath
      316 696 8.000 3.000 72 56 tgifarrowtip
   closepath fill
grestore

% POLY/OPEN-SPLINE
0 setgray
gsave
   newpath
      356 696 moveto
      -56 64 atan dup cos 8.000 mul 420 exch sub
      exch sin 8.000 mul 640 exch sub lineto
   tgiforigctm setmatrix
   1 setlinewidth
   stroke
grestore
gsave
   tgiforigctm setmatrix
   newpath
      420 640 8.000 3.000 64 -56 tgifarrowtip
   1 setgray closepath fill
   0 setgray
   newpath
      420 640 8.000 3.000 64 -56 tgifarrowtip
   closepath fill
grestore

% TEXT
0 setgray
/Helvetica findfont [10 0 0 -10 0 0] makefont setfont
   gsave
      228 603 moveto (Y') show
   grestore

% TEXT
0 setgray
/Helvetica findfont [10 0 0 -10 0 0] makefont setfont
   gsave
      264 683 moveto (X') show
   grestore

% TEXT
0 setgray
/Helvetica findfont [10 0 0 -10 0 0] makefont setfont
   gsave
      304 627 moveto (Z) show
   grestore

% TEXT
0 setgray
/Helvetica findfont [10 0 0 -10 0 0] makefont setfont
   gsave
      308 559 moveto (X'') show
   grestore

grestore
tgifsavedpage restore
end
%MatchingCreationDate: Sat May 23 18:22:21 1998
