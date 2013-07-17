** -*- Mode:CafeOBJ -*-
** $Id: rwl.mod,v 1.16 2010-07-30 02:26:47 sawada Exp $
** system: Chaos
** module: library
** file: rwl.mod
** -------------------------------------------------------------
require bool
--
-- NOTE: You may need to modify `setup-rwl' if you change
--       the definition of module TRUTH
--
lispq
(defun setup-rwl ()
  (setq *rwl-module* (eval-modexp "RWL"))
  (final-setup *rwl-module*)
  (with-in-module (*rwl-module*)
    (let* ((nat-star (find-sort-in *rwl-module* "NzNat*"))
           (rwl-op-info (find-operator '("_" "==>" "_") 2 *rwl-module*))
           (rwl-pred (lowest-method* (car (opinfo-methods rwl-op-info))))
           (rwl-op-info2 (find-operator '("_" "=" "(" "_" ")" "=>" "_")
                                        3
                                        *rwl-module*))
           (rwl-pred2 (lowest-method* (car (opinfo-methods rwl-op-info2)))))
      (unless nat-star
        (with-output-panic-message ()
          (princ "could not find sort NzNat*...")
          (break)))
      (unless rwl-pred
        (with-output-panic-message ()
          (princ "could not find ==> operaotr....")
          (break)))
      (unless rwl-pred2
        (with-output-panic-message ()
          (print "could not find =(?)=> operator ....")
          (break)))
      ;;
      (setq *rwl-nat-star-sort* nat-star)
      (setq *rwl-predicate* rwl-pred)
      (setq *rwl-predicate2* rwl-pred2))
    ))

**
** RWL
**
** allow using universal sorts
set sys universal-sort on

** we want to be very explicit here
lispq
(progn 
  (setq *include-bool-save* *include-bool*)
  (setq *include-bool* nil))

sys:mod! RWL
      principal-sort Bool
{
  imports {
    protecting (BOOL)
    protecting (METALEVEL)
  }
  signature {
    -- [ Nat*, Nat < Nat* ]
    [ NzNat*, NzNat < NzNat* ]
    op * : -> NzNat* { constr }
    -- op + : -> Nat* { constr }
    -- op ! : -> Nat* { constr }
    pred _==>_ : *Term* *Term* { strat: (0) prec: 51 }

    ** NOTE: these two predicates are almost obsolate.
    -- kept for backward compatibility.
    -- _=(N:NzNat*)=>_ is equivalent to _=(1,N)=>*_
    pred _=(_)=>_ : *Term* NzNat* *Term* { strat: (0) prec: 51 }
    pred _=(_)=>_ suchThat _ : *Term* NzNat* *Term* *Term* { strat: (0) prec: 51 }

    ** new search operators
    pred _=(_,_)=>*_ : *Term* NzNat* NzNat* *Term* { strat: (0) prec: 51 }
    pred _=(_,_)=>+_ : *Term* NzNat* NzNat* *Term* { strat: (0) prec: 51 }
    pred _=(_,_)=>!_ : *Term* NzNat* NzNat* *Term* { strat: (0) prec: 51 }
    pred _=(_,_)=>*_ suchThat _: *Term* NzNat* NzNat* *Term* *Term*
      { strat: (0) prec: 51 }
    pred _=(_,_)=>+_suchThat_: *Term* NzNat* NzNat* *Term* *Term*
      { strat: (0) prec: 51 }
    pred _=(_,_)=>!_suchThat_: *Term* NzNat* NzNat* *Term* *Term*
      { strat: (0) prec: 51 }
    -- suchThat 'state equality predicate'
    pred _=(_,_)=>*_withStateEq_ : *Term* NzNat* NzNat* *Term* *Term*
      { strat: (0) prec: 51 }
    pred _=(_,_)=>+_withStateEq_ : *Term* NzNat* NzNat* *Term* *Term*
      { strat: (0) prec: 51 }
    pred _=(_,_)=>!_withStateEq_ : *Term* NzNat* NzNat* *Term* *Term*
      { strat: (0) prec: 51 }
    pred _=(_,_)=>*_suchThat_withStateEq_ : *Term* NzNat* NzNat* *Term* *Term* *Term*
      { strat: (0) prec: 51 }
    pred _=(_,_)=>+_suchThat_withStateEq_ : *Term* NzNat* NzNat* *Term* *Term* *Term*
      { strat: (0) prec: 51 }
   pred _=(_,_)=>!_suchThat_withStateEq_ : *Term* NzNat* NzNat* *Term* *Term* *Term*
     { strat: (0) prec: 51 }

    ** the followings are handy version of =(,)=>* etc.
    -- 
    pred _==>*_ : *Term* *Term* { strat: (0) prec: 51 }
    pred _==>+_ : *Term* *Term* { strat: (0) prec: 51 }
    pred _==>!_ : *Term* *Term* { strat: (0) prec: 51 }
    pred _==>1_ : *Term* *Term* { strat: (0) prec: 51 }
    pred _==>*_withStateEq_ : *Term* *Term* *Term* { strat: (0) prec: 51 }
    pred _==>+_withStateEq_ : *Term* *Term* *Term* { strat: (0) prec: 51 }
    pred _==>!_withStateEq_ : *Term* *Term* *Term* { strat: (0) prec: 51 }
    pred _==>1_withStateEq_ : *Term* *Term* *Term* { strat: (0) prec: 51 }

    pred _==>1_suchThat_ : *Term* *Term* *Term* { strat: (0) prec: 51 }
    pred _==>*_suchThat_ : *Term* *Term* *Term* { strat: (0) prec: 51 }
    pred _==>+_suchThat_ : *Term* *Term* *Term* { strat: (0) prec: 51 }
    pred _==>!_suchThat_ : *Term* *Term* *Term* { strat: (0) prec: 51 }
    pred _==>1_suchThat_ withStateEq_ : *Term* *Term* *Term* *Term*
      { strat: (0) prec: 51 }
    pred _==>*_suchThat_withStateEq_ : *Term* *Term* *Term* *Term*
      { strat: (0) prec: 51 }
    pred _==>+_suchThat_withStateEq_ : *Term* *Term* *Term* *Term*
      { strat: (0) prec: 51 }
    pred _==>!_suchThat_withStateEq_ : *Term* *Term* *Term* *Term*
      { strat: (0) prec: 51 }

    pred _=(_)=>*_ : *Term* NzNat* *Term* { strat: (0) prec: 51 }
    pred _=(_)=>+_ : *Term* NzNat* *Term* { strat: (0) prec: 51 }
    pred _=(_)=>!_ : *Term* NzNat* *Term* { strat: (0) prec: 51 }
    pred _=(_)=>*_ withStateEq(_) : *Term* NzNat* *Term* *Term*
      { strat: (0) prec: 51 }
    pred _=(_)=>+_withStateEq(_) : *Term* NzNat* *Term* *Term*
      { strat: (0) prec: 51 }
    pred _=(_)=>!_withStateEq(_) : *Term* NzNat* *Term* *Term*
      { strat: (0) prec: 51 }
    pred _=(_)=>*_suchThat_ : *Term* NzNat* *Term* *Term* { strat: (0) prec: 51 }
    pred _=(_)=>+_suchThat_ : *Term* NzNat* *Term* *Term* { strat: (0) prec: 51 }
    pred _=(_)=>!_suchThat_ : *Term* NzNat* *Term* *Term* { strat: (0) prec: 51 }
    pred _=(_)=>*_suchThat_withStateEq_ : *Term* NzNat* *Term* *Term* *Term*
      { strat: (0) prec: 51 }
    pred _=(_)=>+_suchThat_withStateEq_ : *Term* NzNat* *Term* *Term* *Term*
      { strat: (0) prec: 51 }
    pred _=(_)=>!_suchThat_withStateEq_ : *Term* NzNat* *Term* *Term* *Term*
      { strat: (0) prec: 51 }

    pred _=(,_)=>*_ : *Term* NzNat* *Term* { strat: (0) prec: 51 }
    pred _=(,_)=>+_ : *Term* NzNat* *Term* { strat: (0) prec: 51 }
    pred _=(,_)=>!_ : *Term* NzNat* *Term* { strat: (0) prec: 51 }
    pred _=(,_)=>*_withStateEq_ : *Term* NzNat* *Term* *Term*
      { strat: (0) prec: 51 }
    pred _=(,_)=>+_withStateEq_ : *Term* NzNat* *Term* *Term*
      { strat: (0) prec: 51 }
    pred _=(,_)=>!_withStateEq_ : *Term* NzNat* *Term* *Term*
      { strat: (0) prec: 51 }
    pred _=(,_)=>*_suchThat_ : *Term* NzNat* *Term* *Term* { strat: (0) prec: 51 }
    pred _=(,_)=>+_suchThat_: *Term* NzNat* *Term* *Term* { strat: (0) prec: 51 }
    pred _=(,_)=>!_suchThat_: *Term* NzNat* *Term* *Term* { strat: (0) prec: 51 }
    pred _=(,_)=>*_suchThat_withStateEq_ : *Term* NzNat* *Term* *Term* *Term*
      { strat: (0) prec: 51 }
    pred _=(,_)=>+_suchThat_withStateEq_ : *Term* NzNat* *Term* *Term* *Term*
      { strat: (0) prec: 51 }
    pred _=(,_)=>!_suchThat_withStateEq_ : *Term* NzNat* *Term* *Term* *Term*
      { strat: (0) prec: 51 }

  }
  axioms {
    var CXU : *Term*
    var CYU : *Term*
    var COND : *Term*
    var MAX-R : NzNat*
    var MAX-D : NzNat*
    var PRED : *Term*
    ** 
    eq (CXU ==> CXU) = true .
    ** ceq (CXU ==> CYU) = true if CXU =(*,*)=>* CYU .
    ** now older builtin ==> is just a equivalent with =(1,*)=>*
    ** but there is an equation 'X ==> X = true' so we implement
    ** this by ==>1.
    eq (CXU ==> CYU) = CXU ==>1 CYU .
    **
    ** older version of `search', for backward compatibiliy
    **
    eq (CXU =( N:NzNat* )=> CYU)
      = #!! (rwl-sch-set-result (term-pattern-included-in-cexec (meta-term-term cxu) (meta-term-term cyu) n)) .
    eq (CXU =( N:NzNat* )=> CYU suchThat COND)
      = #!! (rwl-sch-set-result
	       (term-pattern-included-in-cexec (meta-term-term cxu) (meta-term-term cyu) n
		                               (meta-term-term cond))) .
    **
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
    eq (CXU ==>1 CYU withStateEq(PRED)) = (CXU =(1,*)=>+ CYU withStateEq(PRED)) .
    eq (CXU ==>* CYU withStateEq(PRED)) = (CXU =(*,*)=>* CYU withStateEq(PRED)) .
    eq (CXU ==>! CYU withStateEq(PRED)) = (CXU =(*,*)=>! CYU withStateEq(PRED)) .
    eq (CXU ==>+ CYU withStateEq(PRED)) = (CXU =(*,*)=>+ CYU withStateEq(PRED)) .
    eq (CXU ==>1 CYU suchThat COND withStateEq(PRED))
    = (CXU =(1,*)=>+ CYU suchThat COND withStateEq(PRED)) .
    eq (CXU ==>* CYU suchThat COND withStateEq(PRED))
    = (CXU =(*,*)=>* CYU suchThat COND withStateEq(PRED)) .
    eq (CXU ==>! CYU suchThat COND withStateEq(PRED))
    = (CXU =(*,*)=>! CYU suchThat COND withStateEq(PRED)) .
    eq (CXU ==>+ CYU suchThat COND withStateEq(PRED))
    = (CXU =(*,*)=>+ CYU suchThat COND withStateEq(PRED)) .

    -- =(NzNat*)=>
    eq (CXU =(MAX-R)=>* CYU) = (CXU =(MAX-R,*)=>* CYU) .
    eq (CXU =(MAX-R)=>! CYU) = (CXU =(MAX-R,*)=>! CYU) .
    eq (CXU =(MAX-R)=>+ CYU) = (CXU =(MAX-R,*)=>+ CYU) .
    eq (CXU =(MAX-R)=>* CYU suchThat COND) = (CXU =(MAX-R,*)=>* CYU suchThat COND) .
    eq (CXU =(MAX-R)=>! CYU suchThat COND) = (CXU =(MAX-R,*)=>! CYU suchThat COND) .
    eq (CXU =(MAX-R)=>+ CYU suchThat COND) = (CXU =(MAX-R,*)=>+ CYU suchThat COND) .
    eq (CXU =(MAX-R)=>* CYU withStateEq(PRED)) = (CXU =(MAX-R,*)=>* CYU withStateEq(PRED)) .
    eq (CXU =(MAX-R)=>! CYU withStateEq(PRED)) = (CXU =(MAX-R,*)=>! CYU withStateEq(PRED)) .
    eq (CXU =(MAX-R)=>+ CYU withStateEq(PRED)) = (CXU =(MAX-R,*)=>+ CYU withStateEq(PRED)) .
    eq (CXU =(MAX-R)=>* CYU suchThat COND withStateEq(PRED))
    = (CXU =(MAX-R,*)=>* CYU suchThat COND withStateEq(PRED)) .
    eq (CXU =(MAX-R)=>! CYU suchThat COND withStateEq(PRED))
    = (CXU =(MAX-R,*)=>! CYU suchThat COND withStateEq(PRED)) .
    eq (CXU =(MAX-R)=>+ CYU suchThat COND withStateEq(PRED))
    = (CXU =(MAX-R,*)=>+ CYU suchThat COND withStateEq(PRED)) .

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
    eq (CXU =(,MAX-D)=>* CYU withStateEq(PRED))
      = (CXU =(*,MAX-D)=>* CYU withStateEq(PRED)) .
    eq (CXU =(,MAX-D)=>! CYU withStateEq(PRED))
      = (CXU =(*,MAX-D)=>! CYU withStateEq(PRED)) .
    eq (CXU =(,MAX-D)=>+ CYU withStateEq(PRED))
      = (CXU =(*,MAX-D)=>+ CYU withStateEq(PRED)) .
    eq (CXU =(,MAX-D)=>* CYU suchThat COND withStateEq(PRED))
      = (CXU =(*,MAX-D)=>* CYU suchThat COND withStateEq(PRED)) .
    eq (CXU =(,MAX-D)=>! CYU suchThat COND withStateEq(PRED))
      = (CXU =(*,MAX-D)=>! CYU suchThat COND withStateEq(PRED)) .
    eq (CXU =(,MAX-D)=>+ CYU suchThat COND withStateEq(PRED))
      = (CXU =(*,MAX-D)=>+ CYU suchThat COND withStateEq(PRED)) .

    -- =(NzNat*, NzNat*)=>
    eq (CXU =(MAX-R, MAX-D)=>* CYU) = 
      #!! (rwl-sch-set-result
             (rwl-search :term (meta-term-term cxu)
                         :pattern (meta-term-term cyu) :max-result MAX-R
                         :max-depth MAX-D :zero? t)) .
    eq (CXU =(MAX-R, MAX-D)=>! CYU) = 
      #!! (rwl-sch-set-result
             (rwl-search :term (meta-term-term cxu)
                         :pattern (meta-term-term cyu)
                         :max-result MAX-R
                         :max-depth MAX-D :final? t)) .
    eq (CXU =(MAX-R, MAX-D)=>+ CYU) = 
      #!! (rwl-sch-set-result
             (rwl-search :term (meta-term-term cxu)
                         :pattern (meta-term-term cyu)
                         :max-result MAX-R
                         :max-depth MAX-D)) .
    eq (CXU =(MAX-R, MAX-D)=>* CYU suchThat COND) = 
      #!! (rwl-sch-set-result
             (rwl-search :term (meta-term-term cxu) 
                         :pattern (meta-term-term cyu)
                         :max-result MAX-R
                         :max-depth MAX-D :zero? t
			 :cond (meta-term-term cond))) .
    eq (CXU =(MAX-R, MAX-D)=>! CYU suchThat COND) = 
      #!! (rwl-sch-set-result
             (rwl-search :term (meta-term-term cxu)
                         :pattern (meta-term-term cyu)
                         :max-result MAX-R
                         :max-depth MAX-D :final? t
			 :cond (meta-term-term cond))) .
    eq (CXU =(MAX-R, MAX-D)=>+ CYU suchThat COND) = 
      #!! (rwl-sch-set-result
             (rwl-search :term (meta-term-term cxu)
                         :pattern (meta-term-term cyu)
                         :max-result MAX-R
                         :max-depth MAX-D
			 :cond (meta-term-term cond))) .
    -- =(NzNat*, NzNat*)=> withStateEq(*Term*Term/2)
    eq (CXU =(MAX-R, MAX-D)=>* CYU withStateEq(PRED)) = 
      #!! (rwl-sch-set-result
             (rwl-search :term (meta-term-term cxu)
                         :pattern (meta-term-term cyu)
                         :max-result MAX-R
                         :max-depth MAX-D :zero? t :pred PRED)) .
    eq (CXU =(MAX-R, MAX-D)=>! CYU withStateEq(PRED)) = 
      #!! (rwl-sch-set-result
             (rwl-search :term (meta-term-term cxu)
                         :pattern (meta-term-term cyu) :max-result MAX-R
                         :max-depth MAX-D :final? t :pred PRED)) .
    eq (CXU =(MAX-R, MAX-D)=>+ CYU withStateEq(PRED)) = 
      #!! (rwl-sch-set-result
             (rwl-search :term (meta-term-term cxu)
                         :pattern (meta-term-term cyu) :max-result MAX-R
                         :max-depth MAX-D :pred PRED)) .
    eq (CXU =(MAX-R, MAX-D)=>* CYU suchThat COND withStateEq(PRED)) = 
      #!! (rwl-sch-set-result
             (rwl-search :term (meta-term-term cxu)
                         :pattern (meta-term-term cyu) :max-result MAX-R
                         :max-depth MAX-D :zero? t
			 :cond (meta-term-term cond)
	                 :pred (meta-term-term PRED))) .
    eq (CXU =(MAX-R, MAX-D)=>! CYU suchThat COND withStateEq(PRED)) = 
      #!! (rwl-sch-set-result
             (rwl-search :term (meta-term-term cxu)
                         :pattern cyu :max-result MAX-R
                         :max-depth MAX-D :final? t
			 :cond (meta-term-term cond)
                         :pred (meta-term-term PRED))) .
    eq (CXU =(MAX-R, MAX-D)=>+ CYU suchThat COND withStateEq(PRED)) = 
      #!! (rwl-sch-set-result
             (rwl-search :term (meta-term-term cxu)
                         :pattern (meta-term-term cyu) :max-result MAX-R
                         :max-depth MAX-D
			 :cond (meta-term-term cond)
	                 :pred (meta-term-term PRED))) .
  }
}

** setup truth module
lispq
(setup-rwl)
lispq
(setup-tram-bool-modules)
lispq
(init-builtin-universal)
**
set sys universal-sort off
lispq
(setq *include-bool* *include-bool-save*)
**
provide RWL
provide rwl
**
eof
