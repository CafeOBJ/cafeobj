** -*- Mode:CafeOBJ -*-
** $Id: mrwl.mod,v 1.16 2014-05-30 02:26:47 sawada Exp $
** system: Chaos
** module: library
** file: mrwl.mod
** -------------------------------------------------------------

**
** METARWL
**
sys:mod! METARWL
      principal-sort Bool
{
  imports {
    protecting (CHAOS:TERM)
    protecting (BOOL)
    protecting (NAT-VALUE)
    protecting (RWL)
  }
  signature {

    ** NOTE: these two predicates are almost obsolate.

    op _=(_)=>_ : *Term* NzNat* *Term* -> *Term* { strat: (0) prec: 51 }
    op _=(_)=>_ suchThat _ : *Term* NzNat* *Term* *Term* -> *Term* { strat: (0) prec: 51 }

    ** new search operators
    op _=(_,_)=>*_ : *Term* NzNat* NzNat* *Term* -> *Term* { strat: (0) prec: 51 }
    op _=(_,_)=>+_ : *Term* NzNat* NzNat* *Term* -> *Term* { strat: (0) prec: 51 }
    op _=(_,_)=>!_ : *Term* NzNat* NzNat* *Term* -> *Term* { strat: (0) prec: 51 }
    op _=(_,_)=>*_ suchThat _: *Term* NzNat* NzNat* *Term* *Term* -> *Term*
      { strat: (0) prec: 51 }
    op _=(_,_)=>+_suchThat_: *Term* NzNat* NzNat* *Term* *Term* -> *Term*
      { strat: (0) prec: 51 }
    op _=(_,_)=>!_suchThat_: *Term* NzNat* NzNat* *Term* *Term* -> *Term*
      { strat: (0) prec: 51 }
    -- suchThat 'state equality opicate'
    op _=(_,_)=>*_withStateEq_ : *Term* NzNat* NzNat* *Term* *Term* -> *Term*
      { strat: (0) prec: 51 }
    op _=(_,_)=>+_withStateEq_ : *Term* NzNat* NzNat* *Term* *Term* -> *Term*
      { strat: (0) prec: 51 }
    op _=(_,_)=>!_withStateEq_ : *Term* NzNat* NzNat* *Term* *Term* -> *Term*
      { strat: (0) prec: 51 }
    op _=(_,_)=>*_suchThat_withStateEq_ : *Term* NzNat* NzNat* *Term* *Term* *Term* -> *Term*
      { strat: (0) prec: 51 }
    op _=(_,_)=>+_suchThat_withStateEq_ : *Term* NzNat* NzNat* *Term* *Term* *Term* -> *Term*
      { strat: (0) prec: 51 }
   op _=(_,_)=>!_suchThat_withStateEq_ : *Term* NzNat* NzNat* *Term* *Term* *Term* -> *Term*
     { strat: (0) prec: 51 }

    ** the followings are handy version of =(,)=>* etc.
    -- 
    op _==>*_ : *Term* *Term* -> *Term* { strat: (0) prec: 51 }
    op _==>+_ : *Term* *Term* -> *Term* { strat: (0) prec: 51 }
    op _==>!_ : *Term* *Term* -> *Term* { strat: (0) prec: 51 }
    op _==>1_ : *Term* *Term* -> *Term* { strat: (0) prec: 51 }
    op _==>*_withStateEq_ : *Term* *Term* *Term* -> *Term* { strat: (0) prec: 51 }
    op _==>+_withStateEq_ : *Term* *Term* *Term* -> *Term* { strat: (0) prec: 51 }
    op _==>!_withStateEq_ : *Term* *Term* *Term* -> *Term* { strat: (0) prec: 51 }
    op _==>1_withStateEq_ : *Term* *Term* *Term* -> *Term* { strat: (0) prec: 51 }

    op _==>1_suchThat_ : *Term* *Term* *Term* -> *Term* { strat: (0) prec: 51 }
    op _==>*_suchThat_ : *Term* *Term* *Term* -> *Term* { strat: (0) prec: 51 }
    op _==>+_suchThat_ : *Term* *Term* *Term* -> *Term* { strat: (0) prec: 51 }
    op _==>!_suchThat_ : *Term* *Term* *Term* -> *Term* { strat: (0) prec: 51 }
    op _==>1_suchThat_ withStateEq_ : *Term* *Term* *Term* *Term* -> *Term*
      { strat: (0) prec: 51 }
    op _==>*_suchThat_withStateEq_ : *Term* *Term* *Term* *Term* -> *Term*
      { strat: (0) prec: 51 }
    op _==>+_suchThat_withStateEq_ : *Term* *Term* *Term* *Term* -> *Term*
      { strat: (0) prec: 51 }
    op _==>!_suchThat_withStateEq_ : *Term* *Term* *Term* *Term* -> *Term*
      { strat: (0) prec: 51 }

    op _=(_)=>*_ : *Term* NzNat* *Term* -> *Term* { strat: (0) prec: 51 }
    op _=(_)=>+_ : *Term* NzNat* *Term* -> *Term* { strat: (0) prec: 51 }
    op _=(_)=>!_ : *Term* NzNat* *Term* -> *Term* { strat: (0) prec: 51 }
    op _=(_)=>*_ withStateEq(_) : *Term* NzNat* *Term* *Term* -> *Term* 
      { strat: (0) prec: 51 }
    op _=(_)=>+_withStateEq(_) : *Term* NzNat* *Term* *Term* -> *Term* 
      { strat: (0) prec: 51 }
    op _=(_)=>!_withStateEq(_) : *Term* NzNat* *Term* *Term* -> *Term*
      { strat: (0) prec: 51 }
    op _=(_)=>*_suchThat_ : *Term* NzNat* *Term* *Term* -> *Term* { strat: (0) prec: 51 }
    op _=(_)=>+_suchThat_ : *Term* NzNat* *Term* *Term* -> *Term* { strat: (0) prec: 51 }
    op _=(_)=>!_suchThat_ : *Term* NzNat* *Term* *Term* -> *Term* { strat: (0) prec: 51 }
    op _=(_)=>*_suchThat_withStateEq_ : *Term* NzNat* *Term* *Term* *Term* -> *Term*
      { strat: (0) prec: 51 }
    op _=(_)=>+_suchThat_withStateEq_ : *Term* NzNat* *Term* *Term* *Term* -> *Term* 
      { strat: (0) prec: 51 }
    op _=(_)=>!_suchThat_withStateEq_ : *Term* NzNat* *Term* *Term* *Term* -> *Term*
      { strat: (0) prec: 51 }

    op _=(,_)=>*_ : *Term* NzNat* *Term* -> *Term* { strat: (0) prec: 51 }
    op _=(,_)=>+_ : *Term* NzNat* *Term* -> *Term* { strat: (0) prec: 51 }
    op _=(,_)=>!_ : *Term* NzNat* *Term* -> *Term* { strat: (0) prec: 51 }
    op _=(,_)=>*_withStateEq_ : *Term* NzNat* *Term* *Term* -> *Term*
      { strat: (0) prec: 51 }
    op _=(,_)=>+_withStateEq_ : *Term* NzNat* *Term* *Term* -> *Term*
      { strat: (0) prec: 51 }
    op _=(,_)=>!_withStateEq_ : *Term* NzNat* *Term* *Term* -> *Term*
      { strat: (0) prec: 51 }
    op _=(,_)=>*_suchThat_ : *Term* NzNat* *Term* *Term* -> *Term* { strat: (0) prec: 51 }
    op _=(,_)=>+_suchThat_: *Term* NzNat* *Term* *Term* -> *Term* { strat: (0) prec: 51 }
    op _=(,_)=>!_suchThat_: *Term* NzNat* *Term* *Term* -> *Term* { strat: (0) prec: 51 }
    op _=(,_)=>*_suchThat_withStateEq_ : *Term* NzNat* *Term* *Term* *Term* -> *Term*
      { strat: (0) prec: 51 }
    op _=(,_)=>+_suchThat_withStateEq_ : *Term* NzNat* *Term* *Term* *Term* -> *Term*
      { strat: (0) prec: 51 }
    op _=(,_)=>!_suchThat_withStateEq_ : *Term* NzNat* *Term* *Term* *Term* -> *Term*
      { strat: (0) prec: 51 }

  }
  axioms {
    var CXU : *Term*
    var CYU : *Term*
    var COND : *Term*
    var MAX-R : NzNat*
    var MAX-D : NzNat*
    var OP : *Term*
    ** 
    eq (CXU ==> CXU) = true .
    eq (CXU ==> CYU) = CXU ==>1 CYU .
    **
    ** older version of `search', for backward compatibiliy
    **
    eq (CXU =( N:NzNat* )=> CYU)
      = term(CXU) =(N)=> term(CYU) .
    eq (CXU =( N:NzNat* )=> CYU suchThat COND)
      = term(CXU) =(N)=> term(CYU) suchThat term(COND) .
    ** 
    **
    -- ==>
    eq (CXU ==>1 CYU) = (CXU =(1,*)=>+ CYU) .
    eq (CXU ==>* CYU) = (CXU =(*,*)=>* CYU) .
    eq (CXU ==>! CYU) = (CXU =(*,*)=>! CYU) .
    eq (CXU ==>+ CYU) = (CXU =(*,*)=>+ CYU) .
    eq (CXU ==>1 CYU suchThat COND) = (CXU =(1,*)=>+ CYU suchThat COND) .
    eq (CXU ==>* CYU suchThat COND) = (CXU =(*,*)=>* CYU suchThat COND) .
    eq (CXU ==>! CYU suchThat COND) = (CXU =(*,*)=>! CYU suchThat COND) .
    eq (CXU ==>+ CYU suchThat COND) = (CXU =(*,*)=>+ CYU suchThat COND) .
    eq (CXU ==>1 CYU withStateEq(OP)) = (CXU =(1,*)=>+ CYU withStateEq(OP)) .
    eq (CXU ==>* CYU withStateEq(OP)) = (CXU =(*,*)=>* CYU withStateEq(OP)) .
    eq (CXU ==>! CYU withStateEq(OP)) = (CXU =(*,*)=>! CYU withStateEq(OP)) .
    eq (CXU ==>+ CYU withStateEq(OP)) = (CXU =(*,*)=>+ CYU withStateEq(OP)) .
    eq (CXU ==>1 CYU suchThat COND withStateEq(OP))
    = (CXU =(1,*)=>+ CYU suchThat COND withStateEq(OP)) .
    eq (CXU ==>* CYU suchThat COND withStateEq(OP))
    = (CXU =(*,*)=>* CYU suchThat COND withStateEq(OP)) .
    eq (CXU ==>! CYU suchThat COND withStateEq(OP))
    = (CXU =(*,*)=>! CYU suchThat COND withStateEq(OP)) .
    eq (CXU ==>+ CYU suchThat COND withStateEq(OP))
    = (CXU =(*,*)=>+ CYU suchThat COND withStateEq(OP)) .

    -- =(NzNat*)=>
    eq (CXU =(MAX-R)=>* CYU) = (CXU =(MAX-R,*)=>* CYU) .
    eq (CXU =(MAX-R)=>! CYU) = (CXU =(MAX-R,*)=>! CYU) .
    eq (CXU =(MAX-R)=>+ CYU) = (CXU =(MAX-R,*)=>+ CYU) .
    eq (CXU =(MAX-R)=>* CYU suchThat COND) = (CXU =(MAX-R,*)=>* CYU suchThat COND) .
    eq (CXU =(MAX-R)=>! CYU suchThat COND) = (CXU =(MAX-R,*)=>! CYU suchThat COND) .
    eq (CXU =(MAX-R)=>+ CYU suchThat COND) = (CXU =(MAX-R,*)=>+ CYU suchThat COND) .
    eq (CXU =(MAX-R)=>* CYU withStateEq(OP)) = (CXU =(MAX-R,*)=>* CYU withStateEq(OP)) .
    eq (CXU =(MAX-R)=>! CYU withStateEq(OP)) = (CXU =(MAX-R,*)=>! CYU withStateEq(OP)) .
    eq (CXU =(MAX-R)=>+ CYU withStateEq(OP)) = (CXU =(MAX-R,*)=>+ CYU withStateEq(OP)) .
    eq (CXU =(MAX-R)=>* CYU suchThat COND withStateEq(OP))
    = (CXU =(MAX-R,*)=>* CYU suchThat COND withStateEq(OP)) .
    eq (CXU =(MAX-R)=>! CYU suchThat COND withStateEq(OP))
    = (CXU =(MAX-R,*)=>! CYU suchThat COND withStateEq(OP)) .
    eq (CXU =(MAX-R)=>+ CYU suchThat COND withStateEq(OP))
    = (CXU =(MAX-R,*)=>+ CYU suchThat COND withStateEq(OP)) .

    -- =(,NzNat*)=>
    eq (CXU =(,MAX-D)=>* CYU) = (CXU =(*,MAX-D)=>* CYU) .
    eq (CXU =(,MAX-D)=>! CYU) = (CXU =(*,MAX-D)=>! CYU) .
    eq (CXU =(,MAX-D)=>+ CYU) = (CXU =(*,MAX-D)=>+ CYU) .
    eq (CXU =(,MAX-D)=>* CYU suchThat COND)
      = (CXU =(*,MAX-D)=>* CYU suchThat COND) .
    eq (CXU =(,MAX-D)=>! CYU suchThat COND)
      = (CXU =(*,MAX-D)=>! CYU suchThat COND) .
    eq (CXU =(,MAX-D)=>+ CYU suchThat COND)
      = (CXU =(*,MAX-D)=>+ CYU suchThat COND) .
    eq (CXU =(,MAX-D)=>* CYU withStateEq(OP))
      = (CXU =(*,MAX-D)=>* CYU withStateEq(OP)) .
    eq (CXU =(,MAX-D)=>! CYU withStateEq(OP))
      = (CXU =(*,MAX-D)=>! CYU withStateEq(OP)) .
    eq (CXU =(,MAX-D)=>+ CYU withStateEq(OP))
      = (CXU =(*,MAX-D)=>+ CYU withStateEq(OP)) .
    eq (CXU =(,MAX-D)=>* CYU suchThat COND withStateEq(OP))
      = (CXU =(*,MAX-D)=>* CYU suchThat COND withStateEq(OP)) .
    eq (CXU =(,MAX-D)=>! CYU suchThat COND withStateEq(OP))
      = (CXU =(*,MAX-D)=>! CYU suchThat COND withStateEq(OP)) .
    eq (CXU =(,MAX-D)=>+ CYU suchThat COND withStateEq(OP))
      = (CXU =(*,MAX-D)=>+ CYU suchThat COND withStateEq(OP)) .

    **
    eq (CXU =(MAX-R, MAX-D)=>* CYU) = (term(CXU) =(MAX-R, MAX-D)=>* term(CYU)) .
    eq (CXU =(MAX-R, MAX-D)=>! CYU) = (term(CXU) =(MAX-R, MAX-D)=>! term(CYU)) .
    eq (CXU =(MAX-R, MAX-D)=>+ CYU) = (term(CXU) =(MAX-R, MAX-D)=>+ term(CYU)) .
    eq (CXU =(MAX-R, MAX-D)=>* CYU suchThat COND) = 
       (term(CXU) =(MAX-R, MAX-D)=>* term(CYU)) .
    eq (CXU =(MAX-R, MAX-D)=>! CYU suchThat COND) = (term(CXU) =(MAX-R, MAX-D)=>! term(CYU) suchThat term(COND)) .
    eq (CXU =(MAX-R, MAX-D)=>+ CYU suchThat COND) = (term(CXU) =(MAX-R, MAX-D)=>+ term(CYU) subhThat term(COND)) .
    **
    eq (CXU =(MAX-R, MAX-D)=>* CYU withStateEq(OP)) = (term(CXU) =(MAX-R, MAX-D)=>* term(CYU) withStateEq(term(OP))) .
    eq (CXU =(MAX-R, MAX-D)=>! CYU withStateEq(OP)) = (term(CXU) =(MAX-R, MAX-D)=>! term(CYU) withStateEq(term(OP))) .
    eq (CXU =(MAX-R, MAX-D)=>+ CYU withStateEq(OP)) = (term(CYU) =(MAX-R, MAX-D)=>+ term(CYU) withStateEq(term(OP))) .
    eq (CXU =(MAX-R, MAX-D)=>* CYU suchThat COND withStateEq(OP))
     = (term(CXU) =(MAX-R, MAX-D)=>* term(CYU) suchThat term(COND) withStateEq(term(OP))) .
    eq (CXU =(MAX-R, MAX-D)=>! CYU suchThat COND withStateEq(OP))
     = (term(CXU) =(MAX-R, MAX-D)=>! CYU suchThat term(COND) withStateEq(term(OP))) .
    eq (CXU =(MAX-R, MAX-D)=>+ CYU suchThat COND withStateEq(OP))
     = (term(CXU) =(MAX-R, MAX-D)=>! term(CYU) suchThat term(COND) withStateEq(term(OP))) .
  }
}

**
provide MRWL
provide mrwl
**
eof
