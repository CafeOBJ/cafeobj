"  The data types for the programming language
   from Appendix A, pp.177-
"

module ZZ {
  imports {
    protecting (INT)
  }

  signature {
    op _is_ : Int Int -> Bool
  }
  axioms {
    vars I J K L : Int
    -- -----------------------
    eq I is I = true .
    eq (I + J) is (K + J) = I is K .
    eq (I - J) is (K - J) = I is K .
    cq I is J = false if (I < J) or (J < I) .
    eq I + - I = 0 .
    eq I + - J = - I + - J .
    eq -(I + J) = - I + - J .
    eq 0 * I = 0 .
    eq - I * J = -(I * J) .
    eq I - J = I + - J .
    eq I * (J + K) = (I * J) + (I * K) .
    cq I * J = I + (I * (J - 1)) if 0 < J .
    eq (I + J) * K = (I * K) + (J * K) .

    eq not(I <= J) = J < I .
    eq not(I < J) = J <= I .
    eq I + 1 <= J = I < J .
    eq I < J + 1 = I <= J .
    eq I <= J + -1 = I < J .
    eq I <= J + - K = I + K <= J .
    eq I < J + - K = I + K < J .
    eq I + -1 < J = I <= J .
    eq I <= I = true .
    eq I < I = false .
    cq I < I + J = true if 0 < J .
    eq I + -1 < I = true .
    cq I + J < I = true if J < 0 .
    cq I <= J = true if I < J .
    cq I <= J + 1 = true if I <= J .
    cq I <= J + K = true if (I <= J) and (I <= K) .
    cq I + J <= K + L = true if (I <= K) and (J <= L) .
  }
}

module ARRAY {
  imports {
    protecting (ZZ)
  }
  signature {
    [ Array ]
    op _[_] : Array Int -> Int { prec: 5} 
    op _[_<-_] : Array Int Int -> Array
  }
  axioms {
    var A : Array
    vars I J K : Int 
    -- -----------------------
    eq (A [ I <- J])[I] = J .
    cq (A [ I <- J])[K] = A[K] if not(I is K) .
  }
}

** the programming language: expressions **
module EXP {
  imports {
    protecting (ZZ)
    protecting (QID * { sort Id -> Var })
  }
  signature {
    [ Arvar, Var Int Arcmop < Exp ]
    ops a b c : -> Arvar
    op _+_ : Exp Exp -> Exp { prec: 10 }
    op _*_ : Exp Exp -> Exp { prec: 8 }
    op -_  : Exp -> Exp { prec: 1 } 
    op _-_ : Exp Exp -> Exp { prec: 10 }
    op _[_] : Arvar Exp -> Arcomp { prec: 1 }
  }
}

** the programming languge: tests **
module TST {
  imports {
    protecting (EXP)
  }
  signature {
    [ Bool < Tst ]
    op _<_ : Exp Exp -> Tst { prec: 15 }
    op _<=_ : Exp Exp -> Tst { prec: 15 }
    op _is_ : Exp Exp -> tst { prec: 15 }
    op not_ : Tst -> Tst { prec: 1 }
    op _and_ : Tst Tst -> Tst { prec: 20 }
    op _or_ : Tst Tst -> Tst { prec: 25 }
  }
}

** the programming language: basic programs **
module BPGM {
  protecting (TST)
  signature {
    [ BPgm ]
    op _:=_ : Var Exp -> Bpgm { prec: 20 }
    op _:=_ : Arcomp Exp -> Bpgm { prec: 20 }
  }
}

** semantics of basic programs **

module STORE {
  imports {
    protecting (BPGM)
    protecting (ARRAY)
  }
  signature {
    [ Store ]
    op initial : -> Store
    op _[[_]] : Store Exp -> Int { prec: 65 }
    op _[[_]] : Store Est -> Bool { prec: 65 }
    op _[[_]] : Store Arvar -> Array { prec: 65 }
    op _;_    : Store Bpgm -> Store { prec: 60 }
  }
  axioms {
    var S : Store
    vars X1 X2 : Var
    var I : Int
    vars E1 E2 : Exp
    vars T1 T2 : Tst
    var B : Bool
    vars AV AV' : Arvar
    -- --------------------------
    eq initial [[X1]] = 0 .
    eq S[[I]] = I .
    eq S[[- E1]] = -(S[[E1]]) .
    eq S[[E1 - E2]] = (S[[E1]]) - (S[[E2]]) .
    eq S[[E1 + E2]] = (S[[E1]]) + (S[[E2]]) .
    eq S[[E1 * E2]] = (S[[E1]]) * (S[[E2]]) .
    eq S[[AV[E1]]] = (S[[Av]])[ S[[E1]] ] .

    eq S[[B]] = B .
    eq S[[E1 is E2]] = (S[[E1]]) is (S[[E2]]) .
    eq S[[E1 <= E2]] = (S[[E1]]) <= (S[[E2]]) .
    eq S[[E1 < E2 ]] = (S[[E1]]) < (S[[E2]]) .
    eq S[[not T]] = not(S[[T1]]) .
    eq S[[T1 and T2]] = (S[[T1]]) and (S[[T2]]) .
    eq S[[T1 or T2]] = (S[[T1]]) or (S[[T2]]) .

    eq S ; X1 := E1 [[X1]] = S[[E1]] .
    cq S ; X1 := E1 [[X2]] = S[[X2]] if X1 =/= X2 .
    eq S ; X1 := E1 [[AV]] = S[[AV]] .

    eq S ; AV[E1] := E2 [[AV]]
       = (S[[AV]])[ S[[E1]] <- S[[E2]] ] .
    cq S ; AV[E1] := E2 [[AV']] = S [[AV']] if AV =/= AV' .
    eq S ; AV[E1] := E2 [[X1]] = S [[X1]] .
  }
}

** extended programming languge **
module PGM {
  imports {
    protecting (BPGM) 
  }
  signature {
    [ Bpgm < Pgm ]
    op skip : -> Pgm
    op _;_ : Pgm Pgm -> Pgm { assoc prec: 50 }
    op if_then_else_fi : Tst Pgm Pgm -> Pgm { prec: 40 }
    op while_do_od : Tst Pgm -> Pgm { prec: 40 }
  }
}

module SEM {
  imports {
    protecting (PGM)
    protecting (STORE)
  }
  signature {
    [ Store < EStore ]
    op _;_ : Estore Pgm -> Estore { prec: 60 }
  }

  axioms {
    var S : Store
    var T : Tst
    vars P1 P2 : Pgm
    -- -----------------------------
    eq S ; skip = S .
    eq S ; (P1 ; P2) = (S ; P1) ; P2 .
    cq S ; if T then P1 else P2 fi = S ; P1 if S[[T]] .
    cq S ; if T then P1 else P2 fi = S ; P2 if not(S[[T]]) .
    cq S ; while T do P1 od = (S ; P1) ; while T do P1 od
       if S[[T]] .
    cq S ; while T do P1 od = S if not(S[[T]]) .
  }
}


