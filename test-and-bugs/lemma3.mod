
open TEST

op c : -> Counter.COUNTERH .

op d : -> DCounter .

ops k k1 k2 : -> Nat .

eq val(second(d)) = k1 .

eq val(first(d)) = k2 .

eq k1 * 10 + k2 = k .

eq val(c) = k .


**> Lemma 3 .

**> Presumption .

eq k = 50 .

**> Conclusion

-- red next(c) R dnext(d) .
