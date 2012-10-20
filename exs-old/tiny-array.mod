** -*- Mode:CafeOBJ -*-

module! ARRAY(INDEX :: TRIV, VALUE :: TRIV)
     principal-sort Array
{
  signature {
    [ Array ]
    op nilArr : -> Array {constr}	-- empty array
    op put : Elt.INDEX Elt.VALUE Array -> Array 
    op _[_] : Array Elt.INDEX -> Elt.VALUE 
    pred _in_ : Elt.INDEX Array
    op undef : Elt.INDEX -> Elt.VALUE  ** err-op
  }
  axioms {
    var A : Array 
    vars I I' : Elt.INDEX
    var E : Elt.VALUE 
    eq put(I,E,A)[ I ] = E .
    ceq put(I,E,A)[ I' ] = A [ I' ] if I =/= I' .
    eq I in nilArr = false .
    eq I in put(I',E,A) = I == I' or I in A .
    ceq A [ I ] = undef(I) if not I in A .  ** err-eqn
  }
}

provide tiny-array
--
eof
--
$Id: tiny-array.mod,v 1.1.1.1 2003-06-19 08:30:17 sawada Exp $
