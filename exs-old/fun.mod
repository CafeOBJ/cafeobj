** -*- Mode:CafeOBJ -*-
-- A simple functional langage. 
-- From examples of OBJ3 distribution.
--
require tiny-list ./tiny-list
require tiny-array ./tiny-array

** the expressions of Fun
module! EXP
{
  protecting (ARRAY(QID, INT)*{ sort Array -> Env })
  signature {
    [ Int Id < IntExp,
      Bool < BoolExp ]
    ops (_and_) (_or_) : BoolExp BoolExp -> BoolExp 
    op not_ : BoolExp -> BoolExp 
    op _<_ : IntExp IntExp -> BoolExp 
    op _=_ : IntExp IntExp -> BoolExp 
    op if_then_else_endif : BoolExp IntExp IntExp -> IntExp 
    ops (_+_) (_-_) (_*_) : IntExp IntExp -> IntExp 
    op [[_]]_ : IntExp Env -> Int 
    op [[_]]_ : BoolExp Env -> Bool 
   }
   axioms {
    var N : Int         var T : Bool 
    vars E E' : IntExp  vars B B' : BoolExp 
    var I : Id          var V : Env 
    -- ---------------------------------------
    eq [[ N ]] V = N .
    eq [[ I ]] V  = V [ I ] .
    eq [[ E + E' ]] V = ([[ E ]] V) + ([[ E' ]] V) .
    eq [[ E - E' ]] V = ([[ E ]] V) - ([[ E' ]] V) .
    eq [[ E * E' ]] V = ([[ E ]] V) * ([[ E' ]] V) .
    eq [[ T ]] V = T .
    eq [[ E < E' ]] V = ([[ E ]] V) < ([[ E' ]] V) .
    eq [[(E = E')]] V = ([[ E ]] V) == ([[ E' ]] V) .
    eq [[ B and B' ]] V = ([[ B ]] V) and ([[ B' ]] V) .
    eq [[ B or  B' ]] V = ([[ B ]] V) or  ([[ B' ]] V) .
    eq [[ not B ]] V = not([[ B ]] V) .
    eq [[ if B then E else E' endif ]] V 
       = if [[ B ]] V then [[ E ]] V else [[ E' ]] V fi .
  }
}

** the statements of Fun
module! STMT {
  protecting (EXP)
  signature {
    [ Stmt ]
    op _;_ : Stmt Stmt -> Stmt {assoc}
    op _::=_ : Id IntExp -> Stmt 
    op while_do_od : BoolExp Stmt -> Stmt 
    op [[_]]_ : Stmt Env -> Env 
  }
  axioms {
    vars S S' : Stmt    var V : Env 
    var E : IntExp      var B : BoolExp 
    var I : Id 
    -- -----------------------------------------
    eq [[ I ::= E ]] V = put(I,[[ E ]] V, V) .
    eq [[ S ; S' ]] V = [[ S' ]] [[ S ]] V .
    eq [[ while B do S od ]] V 
       = if [[ B ]] V then
            [[ while B do S od ]] [[ S ]] V 
         else V fi .
  }
}

** evaluation of Fun programs
module! FUNCONSTR {
  protecting (STMT)
  protecting (LIST(QID) * { sort List -> IdList, sort NeList -> IdNeList})
  protecting (LIST(INT) * { sort List -> IntList, sort NeList -> IntNeList})
  [ Init ]
  op _initially_ : Id IntExp -> Init {prec: 1}
}

module! FUN {
  protecting ((LIST * {op nil -> nil-init,
		       op (__) -> (_;_)})
	      (FUNCONSTR { sort Elt -> Init })
	      * { sort List -> InitList })
  signature {
    [ Fun ]
    op fun _ _ is vars _ body: _ : Id IdList InitList Stmt -> Fun 
    op [[_::=_]]_ : IdList IntList Env -> Env 
    op [[_]]_ : InitList Env -> Env 
    op [[_]][_]_ : Fun Env IntList -> Env 
    op [[_]]_ : Fun IntList -> Int 
    op wrong#args : -> Env    ** err-op
  }
  axioms {
    vars I F : Id     var Is : IdList 
    var N : Int       var Ns : IntList
    var E : IntExp    var INs : InitList
    var S : Stmt      var V : Env 
    -- -------------------------------------
    eq [[ nil-init ]] V = V .
    eq [[(I initially E); INs ]] V = [[ INs ]] [[ I ::= E ]] V .
    eq [[ I Is ::= N Ns ]] V = [[ (I ::= N) ]] ([[ Is ::= Ns ]] V) .
    eq [[(nil):IdList ::= (nil):IntList ]] V = V .
    eq [[ fun F(Is) is vars nil-init body: S ]][ V ](Ns) = [[ S ]] V .
    eq [[ fun F(Is) is vars INs body: S ]][ V ](Ns) =
          [[ S ]] [[ INs ]] [[ Is ::= Ns ]] V .
    eq [[ fun F(Is) is vars INs body: S ]](Ns) =
          [[ fun F(Is) is vars INs body: S ]][ nilArr ](Ns) [ F ] .
    cq [[ Is ::= Ns ]] V = wrong#args if | Is | =/= | Ns | .  ** err-qn
  }
}

set tram path brute
select FUN
**> pow(n m) finds the nth power of m for positive n or 0
reduce [[ fun 'pow('n 'm) is vars 'pow initially 1 body:
          while 0 < 'n do ('pow ::= 'pow * 'm);('n ::= 'n - 1) od ]](4 2) .
-- tram reduce [[ fun 'pow('n 'm) is vars 'pow initially 1 body:
--          while 0 < 'n do ('pow ::= 'pow * 'm);('n ::= 'n - 1) od ]](4 2) .
reduce [[ fun 'pow('n 'm) is vars 'pow initially 1 body:
	    while 0 < 'n do ('pow ::= 'pow * 'm);('n ::= 'n - 1) od ]](4 2) .
**> should be: 16

**> factorial of n
reduce [[ fun 'fac('n) is vars ('fac initially 1);('i initially 0) body:
          while 'i < 'n do ('i ::= 'i + 1); ('fac ::= 'i * 'fac) od ]](5) .
-- tram reduce [[ fun 'fac('n) is vars ('fac initially 1);('i initially 0) body:
--          while 'i < 'n do ('i ::= 'i + 1); ('fac ::= 'i * 'fac) od ]](5) .
**> should be: 120

**> max finds the maximum of a list of three numbers
reduce [[ fun 'max('a 'b 'c) is vars ('n initially 2);('max initially 'a) body:
          while 0 < 'n do
          ('n ::= 'n - 1); ('x ::= 'b); ('b ::= 'c);
          ('max ::= if 'x < 'max then 'max else 'x endif) od ]](3 123 32) .
-- tram reduce [[ fun 'max('a 'b 'c) is vars ('n initially 2);('max initially 'a) body:
--          while 0 < 'n do
--          ('n ::= 'n - 1); ('x ::= 'b); ('b ::= 'c);
--          ('max ::= if 'x < 'max then 'max else 'x endif) od ]](3 123 32) .
**> should be: 123
--
eof
**
$Id: fun.mod,v 1.1.1.1 2003-06-19 08:30:16 sawada Exp $

