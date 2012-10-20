** -*- Mode:CafeOBJ -*-
** an example from J.A.Goguen "Theorem Proving and Algebra"
** tlanslated to CafeOBJ.

module! FADD {
  -- extending (PROPC)
  extending (BOOL)
  -- ops i1 i2 cin p1 p2 p3 p4 p5 cout sout : -> Prop
  ops i1 i2 cin p1 p2 p3 p4 p5 cout sout : -> Bool
  eq p1 = i1 and i2 .
  eq p2 = i1 and cin .
  eq p3 = p1 or p2 .
  eq p4 = cin and i2 .
  eq p5 = cin xor i2 .
  eq cout = p3 or p4 .
  eq sout = i1 xor p5 .
}

**> correctness of cout
-- reduce in FADD : cout <-> (i1 and i2) or (i1 and cin) or (i2 and cin) .
reduce in FADD : cout iff (i1 and i2) or (i1 and cin) or (i2 and cin) .

**> correctness of sout
-- reduce in FADD : sout <-> (not i1 and not i2 and cin) or
--                (not i1 and i2 and not cin) or
--                (i1 and not i2 and not cin) or
--                (i1 and i2 and cin) .

reduce in FADD : sout iff (not i1 and not i2 and cin) or
                (not i1 and i2 and not cin) or
                (i1 and not i2 and not cin) or
                (i1 and i2 and cin) .
--
eof
**
$Id: fadd.mod,v 1.1.1.1 2003-06-19 08:30:16 sawada Exp $
