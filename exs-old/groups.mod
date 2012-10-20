** -*- Mode:CafeOBJ -*-

module* G {
  signature {
    [ Elt ]
    op _*_ : Elt Elt -> Elt
    op e : -> Elt
    op _-1 : Elt -> Elt {prec 2}
  }
  axioms {
    vars A B C : Elt
    eq A * e = A .
    eq A * A -1 = e .
    eq A * (B * C) = (A * B) * C .
  }
}

module* GL {
  signature {
     [ Elt ]
     op _*_ : Elt Elt -> Elt
     op e : -> Elt
     op _-1 : Elt -> Elt {prec 2}
  }
  axioms {
    vars A B C : Elt 
    eq e * A = A .
    eq A -1 * A = e .
    eq A * (B * C) = (A * B) * C .
  }
}

--
eof
--
$Id: groups.mod,v 1.1.1.1 2003-06-19 08:30:16 sawada Exp $

