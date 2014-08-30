-- ZZ : builtin Integer with some extensions .
--
-- From J.A.Goguen and G. Malcolm "Algebraic semantics of 
-- imperative program", MIT Press.
-- * program codes are converted from OBJ to CafeOBJ
--
"ZZ extends CafeoBJ's built-in representation of the integers with an
 equality predicate, _is_, and with some equations that are useful for
 manipulating inequalities. In paricular, these equations are useful
 as lemmas in the correctness proof given in the book. For example,
 proving that a property is an invariant of a loop often involves showing
 that `if 0 <= s[['X]] then 0 <= s[['X]] + 1' for some store s.
 The equation in ZZ allow this implication to be automatically verified
 by an CafeOBJ reduction, but they are not strong enough to allow all
 properties of integers to be proved by reduction. For instance, they do
 not allow the automatic verification of the implication: `if 0 <= s[['X]]
 then 0 <= s[['X]] + 2'. If this property is needed for a correctnes proof
 of some program, then an appropriate equation will beed to be added as a
 lemma for the proof. In fact, there is not set of equations that can allow
 the automatic verification of all properties of integer expressions which 
 contain indeterminate values such as `s[['X]]'; in other words, first order
 arithmetic is \"undecidable\".
"

module ZZ {
  imports {
    protecting (INT)
  }
  signature {
    "The predicate _is_ is intended to represent equality on integers.
     The reason for introducing a new equality predicate rather then
     using CafeOBJ's builtin equality _==_ is that we want to use 
     integer expressions which indeterminate values in program 
     correctness proofs (cf. Section 2.1.1 of Chapter2). "
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


eof
