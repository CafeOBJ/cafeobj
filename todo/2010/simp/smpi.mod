mod! VAR{
  [Var]
  ops a b c d e f g h i j k l m n o p q r s t u v w x y z pid np : -> Var .
}

mod! EXP{
  pr(VAR)
  pr(INT)
  [Bool Var Int < Exp]
  op _+_ : Exp Exp -> Exp 
  op _*_ : Exp Exp -> Exp 
  op _-_ : Exp Exp -> Exp 
  op _=_ : Exp Exp -> Exp 
  op _>_ : Exp Exp -> Exp 
  op _<_ : Exp Exp -> Exp 
  op not _ : Exp -> Exp  
  op _and_ : Exp Exp -> Exp 
  op _or_ : Exp Exp -> Exp 
}

mod! PGM{
  pr(EXP)
  [BPgm < Pgm]
  op int_; : Var -> BPgm 
  op _:=_; : Var Exp -> BPgm {prec: 38}
  op if_{_} : Exp Pgm -> BPgm 
  op while_{_} : Exp Pgm -> BPgm
  op end : -> Pgm .
  op __ : Pgm Pgm -> Pgm {assoc prec: 41}
}

mod! STORE{
  pr(VAR)
  ex(INT)
  [Store]
  op na : -> Int .
  op _::_ : Var Int -> Store .
  op init : -> Store .
  op __ : Store Store -> Store {assoc comm id: init prec: 39}
  op in? : Var Store -> Bool .
  op val : Var Store -> Int .
  op update : Var Int Store -> Store .
  vars X Y Z : Var .
  var S : Store .
  vars I J : Int .
  eq in?(X, init) = false .
  eq in?(X, (Y :: I)) = (X == Y) .
  eq in?(X, (Y :: I) S) = (X == Y) or in?(X, S) .
  eq val(X, (X :: I)) = I .
  eq val(X, (X :: I) S) = I .
 ceq val(X, (Y :: I) S) = val(X, S) if (X =/= Y) . 
  eq update(X, I, (X :: J)) = X :: I .
  eq update(X, I, (X :: J) S) = (X :: I) S .
}

mod! SEM-EXP{
  pr(EXP)
  pr(STORE)
  op _[_] : Store Exp -> Int .
  vars A B C : Var .
  vars I J K : Int .
  vars E E1 E2 : Exp .
  var S : Store .
  eq S[A] = val(A, S) .
  eq S[I] = I .
  eq S[E1 + E2] = (S[E1]) + (S[E2])  .
  eq S[E1 - E2] = (S[E1]) - (S[E2]) .
  eq S[E1 * E2] = (S[E1]) * (S[E2]) .
  eq (S[E1 = E2]) = (if (S[E1] ==  S[E2]) then 1 else 0 fi) .
  eq S[E1 > E2] = if (S[E1]) > (S[E2]) then 1 else 0 fi .
  eq S[E1 < E2] = if (S[E1]) < (S[E2]) then 1 else 0 fi .
  eq S[not E] = if (S[E] == 0) then 1 else 0 fi .
  eq S[E1 and E2] = if (S[E1] == 0) or (S[E2] == 0) then 0 else 1 fi .
  eq S[E1 or E2] = if (S[E1] == 0) and (S[E2] == 0) then 0 else 1 fi .
}

-- select SEM-EXP .
-- red (x :: 1) (y :: 2) (z :: 4) [x + y] .
-- red (x :: 1) (y :: 2) (z :: 4) [x + y > z] .
-- red (x :: 1) (y :: 2) (z :: 4) [x + y < z] .

mod! SEM-PGM{
  pr(SEM-EXP)
  pr(PGM)
  [Store < State]
  op __ : State Pgm -> State 
  vars BP BP2 : BPgm .
  vars P P1 P2 : Pgm .
  vars A B C : Var .
  vars I J K : Int .
  vars E E1 E2 : Exp .
  var S : Store .
  trans S end  => S .
  ctrans S (int A ;)  => S            if in?(A,S) .
  ctrans S (int A ;)  =>  (A :: na) S if not in?(A,S) .
  ctrans S A := E ;  => update(A,S[E],S) if in?(A, S) .
   trans S (BP P)  => (S BP) P .
   eq (S (BP P1)) P2 = (S BP) (P1 P2) .
   eq ((S BP) P1) P2 = (S BP) (P1 P2) .
  ctrans S if(E){P1} =>  S P1 if S[E] =/= 0 .
  ctrans S if(E){P1} =>  S    if S[E] == 0 .
  ctrans S (while E { P }) => S (P while E { P }) if S[E] =/= 0 .
  ctrans S (while E { P }) => S                   if S[E] == 0 .
}

-- select SEM-PGM .
-- exec init ( int i ; int x ; i := 100 ; x := 1 ; x := x + 1 ; i := i - 1 ;) .
-- exec init ( int i ;  int x ; x := 1 ; i := 1000 ; while i > 0 { i := i - 1 ; x := x + 2 ; }) .

mod! MPGM{
  pr(PGM)
  op send(_,_); : Var Exp -> BPgm  .
  op recv(_,_); : Var Exp -> BPgm .
  op any : -> Exp .
}

mod! SEM-MPGM{
 pr(MPGM)
 pr(SEM-PGM)
 [State < List]
 op nil : -> List .
 op _|_ : List List -> List {assoc comm prec: 99}
 vars S1 S2 : Store .
 vars P1 P2 : Pgm .
 var L : List .
 vars Dest Source : Exp .
 vars X1 X2 : Var .

 ctrans ((S1 send(X1, Dest);) P1) | ((S2 recv(X2, Source);) P2)  => 
 (S1 P1) | (update(X2, S1[X1], S2) P2) 
 if S1[Dest] == S2[pid] and S1[pid] == S2[Source] .

 ctrans ((S1 send(X1, Dest);) P1) | ((S2 recv(X2, any);) P2)  => 
 (S1 P1) | (update(X2, S1[X1], S2) P2) 
 if S1[Dest] == S2[pid] .
}

mod! SMPI{
 pr(SEM-MPGM)
 op mpirun : Int Pgm -> List .
 op mpirun' : Int Pgm Int -> List .
 vars I J : Int .
 var P : Pgm .
 eq mpirun(I, P) = mpirun'(I, P end, I) .
 ceq mpirun'(I, P, J) = nil if J < 1 .
  eq mpirun'(I, P, 1) = ((pid :: 0) (np :: I)) P .
 ceq mpirun'(I, P, J) = ((pid :: J - 1) (np :: I)) P | mpirun'(I, P, J - 1)
     if J > 1 .
}

mod! TEST{
 pr(SMPI)
 op input : -> List .
 eq input = 
  mpirun(3, 
  if(not(pid = 0)){
    int x ;
    send(pid,0);
    recv(x,0);
  } 
  if(pid = 0){
    int x ; int i ; 
    i := 1 ;
      while (np > i) {
        recv(x,any) ;
        send(x,np - i) ;
        i := i + 1 ;
      }
  } 
) .
}

set clean memo on
open TEST .

--> (1) exec test 

exec input .

--> (2) red _==>!_ test 
--> This search should find the normal form of the above execution (1).

red input ==>! L:List .

close
set clean memo off

--
eof


