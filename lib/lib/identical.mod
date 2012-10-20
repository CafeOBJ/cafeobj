** -*- Mode:CafeOBJ -*-
** $Id: identical.mod,v 1.2 2007-01-24 10:03:39 sawada Exp $
** system: Chaos
** module: library
** file: identical.mod
** -------------------------------------------------------------

--
-- NOTE: You may need to modify `setup-identical' if you change
--       the definition of module IDENTICAL
--
lispq
(defun setup-identical ()
  (let ((id-opinfo nil)
	(nid-opinfo nil))
    (setf *IDENTICAL-module* (eval-modexp "IDENTICAL"))
    (with-in-module (*identical-module*)
      (setf id-opinfo (find-operator '("_" "===" "_")
				     2
				     *identical-module*))
      (setf *identical*
	  (lowest-method* (car (opinfo-methods id-opinfo))))
      (setf nid-opinfo (find-operator '("_" "=/==" "_") 2 *identical-module*))
      (setf *nonidentical*
	    (lowest-method* (car (opinfo-methods nid-opinfo))))
      )))

** allow using universal sorts
set sys universal-sort on

** we want to be very explicit here
lispq
(progn 
  (setq $temp2 *include-bool*)
  (setq *include-bool* nil))

**
** IDENTICAL
**
sys:mod! IDENTICAL
      principal-sort Bool
{
  imports {
    protecting (BOOL)
  }
  signature {
    pred _===_ : *Universal* *Universal* { strat: (0) prec: 51 }
    pred _=/==_ : *Universal* *Universal* { strat: (0) prec: 51 }
  }
  axioms {
    var XU : *Universal*
    var YU : *Universal*
    eq XU === YU = #!! (coerce-to-bool (term-is-similar? xu yu)) .
    eq XU =/== YU = #!! (coerce-to-bool (not (term-is-similar? xu yu))) .
  }
}

** setting up
lispq
(setup-identical)
lispq
(setup-tram-bool-modules)
lispq
(init-builtin-universal)
**
set sys universal-sort off
lispq
(setq *include-bool* $temp2)
**
provide IDENTICAL
provide identical
**
eof
