** This is based on bobj example
**    www.cs.ucsd.edu/groups/tatami/bobj/vend.html
** adapted to CafeOBJ by sawada@sra.co.jp

** for || construct of BOBJ
mod* PARA-CONFIG(C1 :: TRIV, C2 :: TRIV)
{
  *[ Tuple ]*
  op < _ , _ > : Elt.C1 Elt.C2 -> Tuple { constr }
}

mod* VENDM {
  pr (PARA-CONFIG(INT, QID)*{hsort Tuple -> S})
  bops (Q_) (D_) (T_) (C_) : S -> S 
  bop $_ : S -> Nat 
  bop o_ : S -> Id
  op I : -> S  { constr }
  
  var N : Nat
  var L : Id
  var S : S
  eq I = < 0, 'Hello > .
  eq $ < N, L > = N .
  eq o < N, L > = L .
  eq Q < N, L > = < N + 1, 'Thank-you > .
  eq D < N, L > = < N + 4, 'Thank-you > .
  ceq T < N, L > = < N, 'Please-deposit-more > if N < 4 .
  ceq T < N, L > = < N - 4, 'T > if N >= 4 .
  ceq C < N, L > = < N, 'Please-deposit-more > if N < 6 .
  ceq C < N, L > = < N - 6, 'C > if N >= 6 .
}

mod! LEMMAS
{
  pr(VENDM)
  vars M N : Nat
  var L : Id
  eq N + M >= N = true .
  eq (N + M) - N = M .
  ceq N < M = true if N < M - 1 .
}

select LEMMAS

**> followng 3 should be true
cbred Q Q Q Q < N, L > == D < N, L > .
cbred Q D < N, L > == D Q < N, L > .
cbred Q < 0, 'C > == Q < 0, 'T > .

**> next 3 should be false
cbred < 0, 'C > == < 0, 'T > .
cbred T C < N, L > == C T < N, L > .
cbred Q T < N, L > == Q C < N, L > .

select .

--
eof
