;;;-*-Mode:LISP; Package: CHAOS; Base:10; Syntax:Common-lisp -*-
;;; $Id: glob.lisp,v 1.3 2007-01-24 05:28:44 sawada Exp $
;;;
(in-package :chaos)
#|=============================================================================
			    System:Chaos
			  Module:BigPink
			   File:glob.lisp
=============================================================================|#
#-:chaos-debug
(declaim (optimize (speed 3) (safety 0) #-GCL (debug 0)))
#+:chaos-debug
(declaim (optimize (speed 1) (safety 3) #-GCL (debug 3)))

;;; ***********
;;; FOPL SYNTAX ---------------------------------------------------------------
;;; ***********

#||
;;; t if our logic has two diffrent types of equality.
;; (declaim (type boolean *fopl-two-equalities*))
(defvar *fopl-two-equalities* nil)

;;; primitive built-in modules for supporting inference in FOPL
(defvar *fopl-sentence-module* nil)
(defvar *fopl-clause-form-module* nil)
;;; primitive sorts declared in the aboves.
(defvar *fopl-sentence-sort* nil)
(defvar *var-decl-list-sort* nil)
(defvar *fopl-clause-sort* nil)
(defvar *fopl-sentence-seq-sort* nil)
;;; primitive formula constructors
(defvar *var-decl-list* nil)
(defvar *fopl-and* nil)
(defvar *fopl-or* nil)
(defvar *fopl-imply* nil)
(defvar *fopl-iff* nil)
(defvar *fopl-neg* nil)
(defvar *fopl-forall* nil)
(defvar *fopl-exists* nil)
(defvar *fopl-eq* nil)
(defvar *fopl-beq* nil)
(defvar *fopl-ans* nil)

;;; not used 
(defvar *clause-constructor* nil)
(defvar *clause-constructor2* nil)
(defvar *fopl-sentence-seq* nil)

||#
;;; *******
;;; FORMULA ----------------------------------------------------------------
;;; *******

;;; binds last proccessed list of clause, i.e., return value of
;;; the function `formula->clause-1'
;;; 
(defvar $$raw-clause nil)
(defvar *sk-function-num* nil)
;; (defvar *sk-function-num* 0)
;; (defvar *sk-constant-num* 0)

;;; ******
;;; CLAUSE --------------------------------------------------------------
;;; ******

;;; if non-nil print clause in little bit prettier.
(defvar *clause-pretty-print* nil)

;;; ****************
;;; INFERENCE ENGINE ----------------------------------------------------
;;; ****************

;;; ------------
;;; PROOF SYSTEM
;;; ------------
(declaim (special *current-proof-system*))
(defvar *current-proof-system* nil)	; current module
(defvar *current-psys* nil)		; current psystem
(defvar *given-clause* nil)		; current given clause

(defvar *pn-proof-module* nil)		; built-in for invariance check

(defvar *pn-refinement-check-module* nil)
					; built-in for refinement check

(defvar *pn-no-db-reset* nil)

;;; GOLOBAL DB USED BY ENGINES DURING INFERENCE PROCESS *****************
(defvar .debug-pn-memory. nil)
(declaim (type fixnum .pn-clause-deleted.))
(defvar .pn-clause-deleted. 0)

;;; hash table of all clauses generated so far.
(defvar  *clause-hash* nil)		; from *current-psys*

;;; Set of support (SOS)
(declaim (type list *sos*))
(defvar *sos* nil)			; from *current-psys*

;;; usable clauses
(declaim (type list *usable*))
(defvar *usable* nil)			; from *current-psys*

;;; demodulators
(defvar *demodulators* nil)		; from *current-psys*
(defvar *new-demodulator* nil)

(declaim (type list *passive*))
(defvar *passive* nil)			; from *current-psys*

;;; binds the last clause id given as input.
;;;
(declaim (type fixnum *max-input-id*))
(defvar *max-input-id* 0)

(defvar *hot* nil)
;;;
(defvar *weight-pick-given* nil)
(defvar *weight-purge-gen* nil)
(defvar *weight-terms* nil)

;;; INDEX TABLES for INFERENCES

;;; tables for inference rules
(defvar *clash-pos-literals* (make-hash-table :size 30 :test #'eq))
(defvar *clash-neg-literals* (make-hash-table :size 30 :test #'eq))

;;; tables for subsumption check
(defvar *pos-literals* (make-hash-table :size 30 :test #'eq))
(defvar *neg-literals* (make-hash-table :size 30 :test #'eq))

;;; table for paramodulation into
(defvar *paramod-rules* (make-hash-table :size 30 :test #'eq))

;;; table for from paramodulation from
(defvar *clash-lit-table* (make-hash-table :size 30 :test #'eq))

;;; table for para into/from var
(defvar *parainto-var-rules* (make-hash-table :size 30 :test #'eq))
(defvar *parafrom-var-rules* (make-hash-table :size 30 :test #'eq))

;;; table for back demodulation
(defvar *full-lit-table* (make-hash-table :size 30 :test #'eq))


;;; ----------
;;; PARAMETERS
;;; ----------
(declaim (type fixnum *pn-max-parameters*))
(defparameter *pn-max-parameters* 30)

(defstruct (pn-param (:type list))
  (value -1 :type fixnum)
  (name "" :type simple-string)
  (min -1 :type fixnum)
  (max most-positive-fixnum :type fixnum))

(declaim (type (simple-array * (30)) *pn-parameters*))
(defvar *pn-parameters* (make-array *pn-max-parameters*))

(defmacro pn-parameter (_index)
  `(pn-param-value (aref *pn-parameters* ,_index)))
(defmacro pn-parameter-name (_index)
  `(pn-param-name (aref *pn-parameters* ,_index)))
(defmacro pn-parameter-min (_index)
  `(pn-param-min (aref *pn-parameters* ,_index)))
(defmacro pn-parameter-max (_index)
  `(pn-param-max (aref *pn-parameters* ,_index)))

;;; parameter index

; (defconstant REPORT           0)	; output stats and times every
					; n seconds  
(defconstant MAX-GEN          0)	; stop search after this many
					; generated clauses  
(defconstant MAX-KEPT         1)	; stop search after this many
					; kept clauses  
(defconstant MAX-GIVEN        2)	; stop search after this many
					; given clauses  
; (defconstant MAX-LITERALS     5)	; max # of lits in kept clause
					; (0 -> no limit)  
(defconstant MAX-WEIGHT       3)	; maximum weight of kept clauses 
; (defconstant MAX-DISTINCT-VARS 7)	; max # of variables in kept
					; clause  
(defconstant PICK-GIVEN-RATIO 4)	; pick lightest n times, then
					; pick first  
;(defconstant INTERRUPT-GIVEN  9)	; call interact after this
					; many given cls  
(defconstant DEMOD-LIMIT      5)	; Limit on number of rewrites
					; per clause  
(defconstant MAX-PROOFS       6)	; stop search after this many
					; empty clauses  
;(defconstant MIN-BIT-WIDTH    7)	; minimum field for bit strings 
(defconstant NEG-WEIGHT       8)	; add this value to wight of
					; negative literals  
;(defconstant PRETTY-PRINT-INDENT 9)	; indent for pretty print 
(defconstant STATS-LEVEL      10)	; higher stats-level -> output
					; more statistics  
(defconstant CHANGE-LIMIT-AFTER  11)	; replace reduce-weight-limit 
(defconstant NEW-MAX-WEIGHT      12)	; replace reduce-weight-limit 
;(defconstant HEAT                13)	; maximum heat level 
;(defconstant DYNAMIC-HEAT-WEIGHT 14)	; max weigth of dynamic hot clause 
(defconstant MAX-ANSWERS         13)	; maximum number of answer literals 

;(defconstant FSUB-HINT-ADD-WT    16)	; add to pick-given wt     
;(defconstant BSUB-HINT-ADD-WT    17)	; add to pick-given wt     
;(defconstant EQUIV-HINT-ADD-WT   23)	; add to pick-given wt     
;(defconstant VERBOSE-DEMOD-SKIP  24)	; debugging option   

;(defconstant FSUB-HINT-WT        25)	; pick-given wt     
;(defconstant BSUB-HINT-WT        26)	; pick-given wt     
;(defconstant EQUIV-HINT-WT       27)	; pick-given wt     

;(defconstant AGE-FACTOR          30)	; to adjust the pick-given weight 
;(defconstant DISTINCT-VARS-FACTOR 31)	; to adjust the pick-given weight 
;(defconstant NEW-SYMBOL-LEX-POSITION 32)
(defconstant MAX-SOS 14)
(defconstant MAX-SECONDS      15)	; stop search after this many
(defconstant DYNAMIC-DEMOD-DEPTH 16)
(defconstant DYNAMIC-DEMOD-RHS   17)
;;
(defconstant INV-CHECK-MAX-DEPTH 18)
;;
(defconstant CONTROL-MEMORY-POINT 19)
;;
(defconstant MAX-LITERALS 20)

;;; initialize 
(eval-when (eval load)
  (dotimes (x *pn-max-parameters*)
    (setf (aref *pn-parameters* x)
      (make-pn-param)))

  ;(setf (pn-parameter-name REPORT) "report")
  ;(setf (pn-parameter-min report) -1)
  ;(setf (pn-parameter-max report) most-positive-fixnum)

  (setf (pn-parameter-name MAX-SECONDS) "max-seconds")
  (setf (pn-parameter-min max-seconds) -1)
  (setf (pn-parameter-max max-seconds) most-positive-fixnum)
  
  (setf (pn-parameter-name MAX-GEN) "max-gen")
  (setf (pn-parameter-min max-gen) -1)
  (setf (pn-parameter-max max-gen) most-positive-fixnum)
  
  (setf (pn-parameter-name MAX-KEPT) "max-kept")
  (setf (pn-parameter-min max-kept) -1)
  (setf (pn-parameter-max max-kept) most-positive-fixnum)

  (setf (pn-parameter-name MAX-GIVEN) "max-given")
  (setf (pn-parameter-min max-given) -1)
  (setf (pn-parameter-max max-given) most-positive-fixnum)

  ;(setf (pn-parameter-name MAX-LITERALS) "max-literals")
  ;(setf (pn-parameter-min max-literals) -1)
  ;(setf (pn-parameter-max max-literals) most-positive-fixnum)

  (setf (pn-parameter-name MAX-WEIGHT) "max-weight")
  (setf (pn-parameter-min max-weight) most-negative-fixnum)
  (setf (pn-parameter-max max-weight) most-positive-fixnum)

  ;(setf (pn-parameter-name MAX-DISTINCT-VARS) "max-distict-vars")
  ;(setf (pn-parameter-min max-distinct-vars) -1)
  ;(setf (pn-parameter-max max-distinct-vars) most-positive-fixnum)

  (setf (pn-parameter-name PICK-GIVEN-RATIO) "pick-given-ratio")
  (setf (pn-parameter-min pick-given-ratio) -1)
  (setf (pn-parameter-max pick-given-ratio) most-positive-fixnum)

  ;(setf (pn-parameter-name INTERRUPT-GIVEN) "interrupt-given")
  ;(setf (pn-parameter-min interrupt-given) -1)
  ;(setf (pn-parameter-max interrupt-given) most-positive-fixnum)

  (setf (pn-parameter-name DEMOD-LIMIT) "demod-limit")
  (setf (pn-parameter-min demod-limit) -1)
  (setf (pn-parameter-max demod-limit) most-positive-fixnum)

  (setf (pn-parameter-name MAX-PROOFS) "max-proofs")
  (setf (pn-parameter-min max-proofs) -1)
  (setf (pn-parameter-max max-proofs) most-positive-fixnum)

  ;(setf (pn-parameter-name MIN-BIT-WIDTH) "min-bit-width")
  ;(setf (pn-parameter-min min-bit-width) 1)
  ;(setf (pn-parameter min-bit-width) (* 32 8))
  
  (setf (pn-parameter-name NEG-WEIGHT) "neg-weight")
  (setf (pn-parameter-min neg-weight) most-negative-fixnum)
  (setf (pn-parameter-max neg-weight) most-positive-fixnum)

  ;(setf (pn-parameter-name PRETTY-PRINT-INDENT) "pretty-print-indent")
  ;(setf (pn-parameter-min pretty-print-indent) 0)
  ;(setf (pn-parameter-max pretty-print-indent) 16)

  (setf (pn-parameter-name STATS-LEVEL) "stats-level")
  (setf (pn-parameter-min stats-level) 0)
  (setf (pn-parameter-max stats-level) 4)

  (setf (pn-parameter-name change-limit-after) "change-limit-after")
  (setf (pn-parameter-min change-limit-after) 0)
  (setf (pn-parameter-max change-limit-after) most-positive-fixnum)

  (setf (pn-parameter-name new-max-weight) "new-max-weight")
  (setf (pn-parameter-min new-max-weight) most-negative-fixnum)
  (setf (pn-parameter-max new-max-weight) most-positive-fixnum)

  ;(setf (pn-parameter-name HEAT) "heat")
  ;(setf (pn-parameter-min heat) 0)
  ;(setf (pn-parameter-max heat) 100)

  ;(setf (pn-parameter-name DYNAMIC-HEAT-WEIGHT) "dynamic-heat-weight")
  ;(setf (pn-parameter-min dynamic-heat-weight) most-negative-fixnum)
  ;(setf (pn-parameter-max dynamic-heat-weight) most-positive-fixnum)

  (setf (pn-parameter-name MAX-ANSWERS) "max-answers")
  (setf (pn-parameter-min max-answers) -1)
  (setf (pn-parameter-max max-answers) most-positive-fixnum)
  
  ;(setf (pn-parameter-name FSUB-HINT-ADD-WT) "fsub-hint-add-wt")
  ;(setf (pn-parameter-min fsub-hint-add-wt) most-negative-fixnum)
  ;(setf (pn-parameter-max fsub-hint-add-wt) most-positive-fixnum)

  ;(setf (pn-parameter-name BSUB-HINT-ADD-WT) "bsub-hint-add-wt")
  ;(setf (pn-parameter-min bsub-hint-add-wt) most-negative-fixnum)
  ;(setf (pn-parameter-max bsub-hint-add-wt) most-positive-fixnum)

  ;(setf (pn-parameter-name EQUIV-HINT-ADD-WT) "equiv-hint-add-wt")
  ;(setf (pn-parameter-min equiv-hint-add-wt) most-negative-fixnum)
  ;(setf (pn-parameter-max equiv-hint-add-wt) most-positive-fixnum)

  ;(setf (pn-parameter-name VERBOSE-DEMOD-SKIP) "verbose-demod-skip")
  ;(setf (pn-parameter-min verbose-demod-skip) 0)
  ;(setf (pn-parameter-max verbose-demod-skip) most-positive-fixnum)

  ;(setf (pn-parameter-name FSUB-HINT-WT) "fsub-hint-wt")
  ;(setf (pn-parameter-min fsub-hint-wt) most-negative-fixnum)
  ;(setf (pn-parameter-max fsub-hint-wt) most-positive-fixnum)

  ;(setf (pn-parameter-name BSUB-HINT-WT) "bsub-hint-wt")
  ;(setf (pn-parameter-min bsub-hint-wt) most-negative-fixnum)
  ;(setf (pn-parameter-max bsub-hint-wt) most-positive-fixnum)
  
  ;(setf (pn-parameter-name EQUIV-HINT-WT) "equiv-hint-wt")
  ;(setf (pn-parameter-min equiv-hint-wt) most-negative-fixnum)
  ;(setf (pn-parameter-max equiv-hint-wt) most-positive-fixnum)

  (setf (pn-parameter-name DYNAMIC-DEMOD-DEPTH) "dynamic-demod-depth")
  (setf (pn-parameter-min dynamic-demod-depth) -1)
  (setf (pn-parameter-max dynamic-demod-depth) most-positive-fixnum)

  (setf (pn-parameter-name DYNAMIC-DEMOD-RHS) "dynamic-demod-rhs")
  (setf (pn-parameter-min dynamic-demod-rhs) most-negative-fixnum)
  (setf (pn-parameter-max dynamic-demod-rhs) most-positive-fixnum)

  ;(setf (pn-parameter-name AGE-FACTOR) "age-factor")
  ;(setf (pn-parameter-min age-factor) most-negative-fixnum)
  ;(setf (pn-parameter-max age-factor) most-positive-fixnum)

  ;(setf (pn-parameter-name DISTINCT-VARS-FACTOR) "distinct-vars-factor")
  ;(setf (pn-parameter-min distinct-vars-factor) most-negative-fixnum)
  ;(setf (pn-parameter-max distinct-vars-factor) most-positive-fixnum)

  ;(setf (pn-parameter-name NEW-SYMBOL-LEX-POSITION) "new-symbol-lex-position")
  ;(setf (pn-parameter-min new-symbol-lex-position) 1)
  ;(setf (pn-parameter-max new-symbol-lex-position) (/ most-positive-fixnum 2))

  (setf (pn-parameter-name MAX-SOS) "max-sos")
  (setf (pn-parameter-min max-sos) -1)
  (setf (pn-parameter-max max-sos) most-positive-fixnum)

  (setf (pn-parameter-name INV-CHECK-MAX-DEPTH) "inv-check-max-depth")
  (setf (pn-parameter-min inv-check-max-depth) -1)
  (setf (pn-parameter-max inv-check-max-depth) most-positive-fixnum)

  (setf (pn-parameter-name CONTROL-MEMORY-POINT) "control-memory-point")
  (setf (pn-parameter-min control-memory-point) -1)
  (setf (pn-parameter-max control-memory-point) most-positive-fixnum)

  (setf (pn-parameter-name MAX-LITERALS) "max-literals")
  (setf (pn-parameter-min max-literals) -1)
  (setf (pn-parameter-max max-literals) most-positive-fixnum)
  )


;;; ============================
;;; CONTROLS FLAGS for INFERENCE
;;; ============================
(declaim (type fixnum *pn-max-flags*))
(defparameter *pn-max-flags* 100)

(defstruct (pignose-flag (:type list))
  (value nil)
  (name "" :type simple-string)
  (hook #'identity :type function))

(declaim (type (simple-array * (100)) *pn-control-flags*))
(defvar *pn-control-flags*)
(eval-when (eval load)
  (setq *pn-control-flags*
    (make-array *pn-max-flags*)))

(defmacro pn-flag (flag-index)
  `(pignose-flag-value (aref *pn-control-flags* ,flag-index)))

(defmacro pn-flag-name (flag-index)
  `(pignose-flag-name (aref *pn-control-flags* ,flag-index)))

(defmacro pn-flag-hook (flag-index)
  `(pignose-flag-hook (aref *pn-control-flags* ,flag-index)))

;;; IDEXES
(defconstant sos-queue 0)		; first clause on sos is given clause 
(defconstant sos-stack 1)		; pick last sos clause as given clause 
(defconstant input-sos-first 2)		; use input sos before generated sos 

(defconstant print-given 3)		; print given clauses 
(defconstant print-lists-at-end 4)	; print clause lists at end of run 

(defconstant binary-res 5)		; binary resolution 
(defconstant hyper-res 6)		; hyperresolution 
(defconstant neg-hyper-res 7)		; negatve hyperresolution inf rule 
;(defconstant ur-res 8)			; UR-resolution.
(defconstant para-into 8)		; `into' paramodulation inference rule 
(defconstant para-from 9)		; `from' paramodulation inference rule 
(defconstant demod-inf 10)		; apply demodulation as an inference rule 
 
(defconstant para-from-left 11)		; allow paramodulation from left sides 
(defconstant para-from-right 12)	; allow paramodulation from right sides 
(defconstant para-into-left 13)		; allow paramodulation into
					; left args of =  
(defconstant para-into-right 14)	; allow paramodulation into
					; right args of =  
(defconstant para-from-vars 15)		; allow paramodulation from variables 
(defconstant para-into-vars 16)		; allow paramodulation into variables 
(defconstant para-from-units-only 17)	; from clause must be unit 
(defconstant para-into-units-only 18)	; into clause must be unit 
(defconstant para-skip-skolem 19)	; Skolem function restriction strategy 
(defconstant para-ones-rule 20)		; paramod only into first args of terms 
(defconstant para-all 21)		; paramodulate all occurrences
					; of into term  
;(defconstant detailed-history 23)	; store literal position vectors  
;(defconstant order-history 24)		; Nucleus number first for
					; hyper, UR.  
(defconstant unit-deletion 22)		; unit deletion processing 
(defconstant delete-identical-nested-skolem 23) ; delete clauses containing 
(defconstant sort-literals 24)		; sort literals in pre-process 
(defconstant for-sub 25)		; forward subsumption 
(defconstant back-sub 26)		; back subsumption 
(defconstant factor 27)			; factor during post-process 

;(defconstant demod-history 31)		; build history in demodulation 
(defconstant order-eq 28)		; flip equalities (+ and -) if
					; right arg heavier 
(defconstant eq-units-both-ways 29)	; non-oriented eq units both ways 

(defconstant dynamic-demod 30)		; dynamic addition of demodulators 
(defconstant dynamic-demod-all 31)	; try to make all equalities
					; into demodulators  
(defconstant dynamic-demod-lex-dep 32)	; allow lex-dep dynamic demodulators 
(defconstant back-demod 33)		; back demodulation 
(defconstant kb 34)			; Attempt Knuth-Bendix completion 
(defconstant lrpo 35)			; lexicographic recursive path
					; ordering  
(defconstant lex-order-vars 36)		; consider variables when
					; lex-checking terms  
(defconstant simplify-fol 37)		; attempt to simplify during
					; cnf translation  
(defconstant new-variable-name 38)
(defconstant process-input 39)		; process input usable and sos 
(defconstant quiet 40)
(defconstant very-verbose 41)		; print generated clauses 
(defconstant print-kept 42)		; print kept clauses 
(defconstant print-proofs 43)		; print all proofs found 
(defconstant print-new-demod 44)	; print new demodultors 
(defconstant print-back-demod 45)	; print back demodulated clauses 
(defconstant print-back-sub 46)		; print back subsumed clauses 

(defconstant order-hyper 47)		; ordered hyperresolution
					; (satellites)  
(defconstant propositional 48)		; some propositional
					; optimizations  
;(defconstant atom-wt-max-args 53)	; weight of atom is max of
					; weights of arguments  
;(defconstant term-wt-max-args 54)	; weight of term is max of
					; weights of arguments  
(defconstant AUTO 49)			; select the current AUTO mode
;(defconstant proof-weight 56)		; Calculate proof weight (ancestor bag). 
(defconstant hyper-symmetry-kludge 50)	; Secret flag 
;(defconstant gl-demod 58)		; Delay demodulation. 
(defconstant discard-non-orientable-eq 51) ; Secret flag 
(defconstant discard-xx-resolvable 52)	; Secret flag 
(defconstant back-unit-deletion   53)	; like back demodulation, but
					; for literals  
(defconstant auto2 54)
(defconstant auto1 55)
(defconstant auto3 56)
(defconstant debug-infer 57)
(defconstant debug-binary-res 58)
(defconstant debug-hyper-res 59)
(defconstant debug-neg-hyper-res 60)
(defconstant debug-ur-res 61)
(defconstant debug-para-from 62)
(defconstant debug-para-into 63)
(defconstant universal-symmetry 64)
(defconstant control-memory 65)
(defconstant print-stats 66)
(defconstant print-message 67)
(defconstant unify-heavy 68)
(defconstant trace-demod 69)
(defconstant debug-refine 70)
(defconstant no-demod 71)
(defconstant no-back-demod 72)
(defconstant kb2 73)
(defconstant no-new-demod 74)
;;; new flags
(defconstant prop-res 75)
(defconstant no-junk 76)		; obsolete
(defconstant no-confusion 77)		; obsolete
(defconstant meta-paramod 78)
(defconstant debug-inv-check 79)
(defconstant dist-const 80)
(defconstant debug-dist-const 81)
(defconstant randomize-sos 82)
(defconstant debug-sos 83)
(defconstant put-goal-in-sos 84)
(defconstant check-init-always 85)
;; 
(defconstant ur-res 86)
;;
(defconstant kb3 87)
;;;
(eval-when (eval load)
  (dotimes (x *pn-max-flags*)
    (setf (aref *pn-control-flags* x)
      (make-pignose-flag)))
  (setf (pn-flag-name  sos-queue) "sos-queue")
  (setf (pn-flag-name  sos-stack) "sos-stack")
  (setf (pn-flag-name  input-sos-first) "input-sos-first")
  (setf (pn-flag-name  print-given) "print-given")
  (setf (pn-flag-name  print-lists-at-end) "print-lists-at-end")
  (setf (pn-flag-name  binary-res) "binary-res")
  (setf (pn-flag-name  hyper-res) "hyper-res")
  (setf (pn-flag-name  neg-hyper-res) "neg-hyper-res")
  (setf (pn-flag-name  ur-res) "ur-res")
  (setf (pn-flag-name  para-into) "para-into")
  (setf (pn-flag-name  para-from) "para-from")
  (setf (pn-flag-name  demod-inf) "demod-inf")
  (setf (pn-flag-name  para-from-left) "para-from-left")
  (setf (pn-flag-name  para-from-right) "para-from-right")
  (setf (pn-flag-name  para-into-left) "para-into-left")
  (setf (pn-flag-name  para-into-right) "para-into-right")
  (setf (pn-flag-name  para-from-vars) "para-from-vars")
  (setf (pn-flag-name  para-into-vars) "para-into-vars")
  (setf (pn-flag-name  para-from-units-only) "para-from-units-only")
  (setf (pn-flag-name  para-into-units-only) "para-into-units-only")
  (setf (pn-flag-name  para-skip-skolem) "para-skip-skolem")
  (setf (pn-flag-name  para-ones-rule) "para-ones-rules")
  (setf (pn-flag-name  para-all) "para-all")
  ;(setf (pn-flag-name  detailed-history) "detailed-history")
  ;(setf (pn-flag-name  order-history) "order-history")
  (setf (pn-flag-name  unit-deletion) "unit-deletion")
  (setf (pn-flag-name  delete-identical-nested-skolem)
    "delete-identical-nested-skolem")
  (setf (pn-flag-name  sort-literals) "sort-literals")
  (setf (pn-flag-name  for-sub) "for-sub")
  (setf (pn-flag-name  back-sub) "back-sub")
  (setf (pn-flag-name  factor) "factor")
  ;(setf (pn-flag-name  demod-history) "demod-history")
  (setf (pn-flag-name  order-eq) "order-eq")
  (setf (pn-flag-name  eq-units-both-ways) "eq-units-both-ways")
  ;; (setf (pn-flag-name  demod-linear) "demod-linear")
  ;; (setf (pn-flag-name  demod-out-in) "demod-out-in")
  (setf (pn-flag-name  dynamic-demod) "dynamic-demod")
  (setf (pn-flag-name  dynamic-demod-all) "dynamic-demod-all")
  (setf (pn-flag-name  dynamic-demod-lex-dep) "dynamic-demod-lex-dep")
  (setf (pn-flag-name  back-demod) "back-demod")
  (setf (pn-flag-name  kb) "kb")
  (setf (pn-flag-name  lrpo) "lrpo")
  (setf (pn-flag-name  lex-order-vars) "lex-order-vars")
  (setf (pn-flag-name  simplify-fol) "simplify-fol")
  (setf (pn-flag-name  new-variable-name) "new-variable-name")
  (setf (pn-flag-name  process-input) "process-input")
  (setf (pn-flag-name  quiet) "quiet")
  (setf (pn-flag-name  very-verbose) "very-verbose")
  (setf (pn-flag-name  print-kept) "print-kept")
  (setf (pn-flag-name  print-proofs) "print-proofs")
  (setf (pn-flag-name  print-new-demod) "print-new-demod")
  (setf (pn-flag-name  print-back-demod) "print-back-demod")
  (setf (pn-flag-name  print-back-sub) "print-back-sub")
  (setf (pn-flag-name  order-hyper) "order-hyper")
  (setf (pn-flag-name  propositional) "propositional")
  ;(setf (pn-flag-name  atom-wt-max-args) "atom-wt-max-args")
  ;(setf (pn-flag-name  term-wt-max-args) "term-wt-max-args")
  (setf (pn-flag-name  auto) "auto")
  ;(setf (pn-flag-name  proof-weight) "proof-weight")
  (setf (pn-flag-name  hyper-symmetry-kludge) "hyper-symmetry-kludge")
  ;(setf (pn-flag-name  gl-demod) "gl-demod")
  (setf (pn-flag-name  discard-non-orientable-eq) "discard-non-orientable-eq")
  (setf (pn-flag-name  DISCARD-XX-RESOLVABLE) "discard-xx-resolvable")
  (setf (pn-flag-name  back-unit-deletion) "back-unit-deletion")
  (setf (pn-flag-name  auto2) "auto2")
  (setf (pn-flag-name  auto1) "auto1")
  (setf (pn-flag-name  auto3) "auto3")
  (setf (pn-flag-name debug-infer) "debug-infer")
  (setf (pn-flag-name debug-binary-res) "debug-binary-res")
  (setf (pn-flag-name debug-hyper-res) "debug-hyper-res")
  (setf (pn-flag-name debug-neg-hyper-res) "debug-neg-hyper-res")
  (setf (pn-flag-name debug-ur-res) "debug-ur-res")
  (setf (pn-flag-name debug-para-from) "debug-para-from")
  (setf (pn-flag-name debug-para-into) "debug-para-into")
  (setf (pn-flag-name universal-symmetry) "universal-symmetry")
  (setf (pn-flag-name control-memory) "control-memory")
  (setf (pn-flag-name print-stats) "print-stats")
  (setf (pn-flag-name print-message) "print-message")
  (setf (pn-flag-name unify-heavy) "unify-heavy")
  (setf (pn-flag-name trace-demod) "trace-demod")
  (setf (pn-flag-name debug-refine) "debug-refine")
  (setf (pn-flag-name no-demod) "no-demod")
  (setf (pn-flag-name no-back-demod) "no-back-demod")
  (setf (pn-flag-name kb2) "kb2")
  (setf (pn-flag-name no-new-demod) "no-new-demod")
  (setf (pn-flag-name prop-res) "prop-res")
  (setf (pn-flag-name no-junk) "no-junk")
  (setf (pn-flag-name no-confusion) "no-confusion")
  (setf (pn-flag-name meta-paramod) "meta-paramod") ; meta-paramod
  (setf (pn-flag-hook meta-paramod) 'pn-set-tf-flag)
  (setf (pn-flag-name debug-inv-check) "debug-inv-check")
  (setf (pn-flag-name dist-const) "dist-const")
  (setf (pn-flag-name debug-dist-const) "debug-dist-const")
  (setf (pn-flag-name randomize-sos) "randomize-sos")
  (setf (pn-flag-name debug-sos) "debug-sos")
  (setf (pn-flag-name put-goal-in-sos) "put-goal-in-sos")
  (setf (pn-flag-name check-init-always) "check-init-always")
  (setf (pn-flag-name kb3) "kb3")
  )

;;; OPTION SET DB
;;;
(defvar *pn-option-set* nil)

;;; COMMENTS ON CONTROL FLAGS
;;; THESE ARE STOLEN FROM `OTTER UERS'S MANUAL 3.0.5' (by 
;;; 

;;; BINARY-RES
#|
	default off
	if set, inference rule binary resolution is used to 
	generate new clauses. 
	effected flags
		*factor*    on
		*unit-del*  on
|#

;;; HYPER-RES
#|
	default off
	if set, inference rule (positive) hyper resolution is used to
	generate new clauses.
|#

;;; NEG-HYPER-RES
#|
	default off
	if set, inference rule negative hyper resolution is used
	to generate new clauses.
|#

;;; UR-RES
#|
	default off
	if set, inference rule UR-resolution is used to generate
	new clauses.
|#

;;; PARA-INTO
#|
	default off
	if set, inference rule "paramodulation into the given clause"
	is used to generate new clauses.
|#

;;; PARA-FROM
#|
	default off
	if set, inference rule "paramodulation from the given clause"
	is used to generate new clauses.
|#

;;; PARAMODULATION

;;; PARA-FROM-LEFT
#|
	default set
	if set, paramodulation is allowed from the left sides of
	equality literals.
	applied to both *para-into* and *para-from* inference rules.
|#

;;; PARA-FROM-RIGHT
#|
	default set
	if set, paramodulation is allowed the right sides of
	equality literals.
	applied to both *para-into* and *para-from* inference rules.
|#

;;; PARA-INTO-LEFT
#|
	default set
	if set, paramodulation is allowed into left sides of
	positive and negative literals.
	applied to both *para-into* and *para-from* inference rules.
|#

;;; PARA-INTO-RIGHT
#|
	default set
	if set, paramodulation is allowed into right sides of
	positive and gengative equalities.
	applied to both *para-into* and *para-from* inference rules.
|#

;;; Flags handling generated clauses
;;;-------------------------------------------------------------------------

;;; DETAILED-HISTORY
#|
	default set
	affects the parent lists in clauses that are derived by
	*binary-res*, *para-from* or *para-into*.
	if set, the positions of the unified literals or terms are
	given alog with the IDs of the parents.  
|#	

;;; ORDER-HISTORY
#|
	default off
	affects the order of parent lists in clauses that are derived 
	by hyperresolition, negative hyperresolution, or
	UR-reaolution.
	if set, the nucleus is listed first, and the satellites are
	listed in the order in which the corresponding literals appear
	in the nucleus.
	if the flag is off (or if the clause was derived by some other 
	inference rule), the given clause is listed first.
|#

;;; UNIT-DELETION
#|
	default off
	if set, unit deletion is applied to newly generated clauses.
	this removes a literal from a newly generated clause if 
	the literal is the negation of an instance of a unit clause
	that ocuurs in usable or sos. 
	ex. the second literal of `p(a, x) \| q(a, x)' is removed by 
	the unit `~q(u,v)'; but it is not removed by the unit
	`~q(u,b)', because that unification causes the instantiation of 
	x. 

	all such literals are removed from the newly generated clause,
	even if the reslult is is the empty clauses.
	unit deletion is not useful if all generated clauses are
	units.

|#

;;; FOR-SUB
#|
	default set
	if this flag is set, forward subsumption is applied during
	the processing of newly generated clauses -- delete the new
	clause if it is subsumed by any clause in usable or sos.
|#

;;; BACK-SUB
#|
	default set
	if set, back subsumption is applied during the processing of
	newly kept clauses -- delete all clauses in usable or sos
	that are subsumed by the newly kept clause.
|#

;;; FACTOR
#|
	default off
	if set, factoring is applied in two ways. first, factoring is 
	applied as a simplification rule to newly generated clauses.
	if a generated clause C has factors that subsume C, it is
	replaced with its smallest subsuing factor.
	second, it is applied as an inference rule to newly kept 
	clauses. note that unlike other inference rules, factoring is
	not applied to the given clause; it is applied to a new clause
	as soon as it is kept.
	all factors are generated in an iterative manner.
	if factor is set, a clause with n-literals will not cause
	a clause with fewer than n-literals to be deleted by 
	subsumption.
|#

;;; demodulation and ordering flags
;;; not yet.
;;;-------------------------------------------------------------------------
;;; DEMOD-HISTORY
#|
  default set. 
  if set, when a clause is demodulated, the ID numbers of the 
  demodulators are included in the derivation history of the clause.
|#

;;; ORDER-EQ
#|
  default off
  if set, equations are flipped if the right side is havier than the 
  left. 
|#

;;; EQ-UNIT-BOTH-WAYS
#|
  default off. if set, unit equality clauses (both positive and negative)
  are sometimes stored in both orientations; the action taken depends on
  the flag *order-eq*. if *order-eq* is clear, then whenever a unit,
  say a = b, is processed, b = a is automatically generated and processed.
  if *order-eq* is set, then the reverse equality is generated only if
  the equality cannot be oriented.
|#

;;; DEMOD-LINEAR
#|
   default off.
   if set, terms are demodulation indexing is disabled, and a linear
   search of demodulators are used when rewriting terms.
   with indexing disabled, if more than one demodulator can be applied
   to rewrite a term, then the one whose clause number is lowest is applied;
   this flag is useful when demodulation is used to do "procedual" things.
   with indexing enabled (the default), demodulation is much faster, but
   the order in which demodulators is applied is not under the control
   of the user.
|#

;; DEMOD-OUT-IN
#|
  default off.
  if set, terms are demodulated outside-in, left-to-right. in other words
  the program attempts to rewrite a term before rewriting (left-to-right)
  its subterms. the algorithm is "repeat { rewrite the left-most outer-most 
  rewritable term} untill no more rewriting can be done or the limit is
  reached". (the effect is like a standard reduction in lambda-calculus
  or in cominatory logic.) if this flag is off, terms are demodulated 
  inside-out (all subterms are fully demodulated before attempting to 
  rewrite a term). 
|#

;;; DYNAMIC-DEMOD
#|
  default off. if set, some newly kept equalities are made into demodulators.
  setting this flag automatically sets the flag *order-eq*.
|#

;;; DYNAMIC-DEMOD-ALL
#|
  default off. if set, system attempts to make all newly kept equalities
  into demodulators. setting this flag automatically sets the flags
  *dynamic-demod* and *order-eq*
|#

;;; DYNAMIC-DEMOD-LEX-DEP
#|
  default clear. if set dynamic demodulators may be lex-dependent or
  LRPO-dependent.
|#

;;; BACK-DEMOD
#|
  default clear. if set, back demodulation is applied to demodulators,
  *usable* and *sos* whenever a new demodulator is added.
  back demodulation is delayed until the inference rules are sinished
  generating clauses from the current given clause (delayed untill
  post-process). setting the *back-demod* flag automatically sets the
  flag *order-eq* and *dynamic-demod*.
|#

;;; KNUTH-BENDIX
#|
  default clear. if set, system search will behave like a Knuth-Bendix
  completion procedure. this flag is really a metaflag; its only effect
  is to alter other flags as follows: *para-from* -> on, *para-into* ->on,
  *para-from-left* -> on, *para-from-right* -> off, *para-into-left* ->on,
  *para-into-right* -> off, *para-from-vars* -> on, *eq-unit-both-ways* -> on,
  *dynamic-demod-all* -> on, *back-demod* -> on, *process-input* -> on,
  *lrop* -> on.
|#

;;; LRPO
#|
  default off. this flag affects lex-dependent demodulation and the
  evaluable functions and predicates that perform lexical comparisons.
  if set, then lexical ordering is a total order on terms; variables 
  are lowest in the term order. if this flag is off, then a variable is
  comparable only to another occurrence of the same variable; it is
  not comparable to other variables or to nonvariables.
  if *lrop* set, *lex-order-vars* has no effect on demodulation.
|#

;;; SYMBOL-ELIM
#|
  default off. if set, then new demodulators are oriented, if possible,
  so that function symbols (excluding constants) are eliminated.
  a demodulator can eliminate all occurrences of a function symbol if
  the arguments on the left side are all difference variables and if the
  function symbol of the left side does not occur in the right side.
  ex. the demodulators g(x) = f(x,x) and h(x,y) = f(x,f(y,f(g(x),g(y))))
  eliminate all occurrence of g and h, respectively.
|#

;;; INPUT FLAGS
;;;-------------------------------------------------------------------------

;;; PROCESS-INPUT
#|
  default off. if set, input *usable* and *sos* clauses (including
  clauses from formulainput) are processed as if they had been generated
  by an inference rule.
|#

;;; -----------------------------------
;;; internal flags--invisible to users
;;; -----------------------------------
(declaim (type fixnum *pn-max-internal-flags*))
(defparameter *PN-MAX-INTERNAL-FLAGS*   10)

(defconstant SPECIAL-UNARY-PRESENT 0)
(defconstant DOLLAR-PRESENT        1)
(defconstant LEX-VALS-SET          2)

(declaim (type simple-array *pn-internal-flags*))
(defvar *pn-internal-flags*
    (make-array *pn-max-internal-flags* :initial-element nil))

(defun reset-pn-internal-flags ()
  (dotimes (x *pn-max-internal-flags*)
    (declare (type fixnum x))
    (setf (aref *pn-internal-flags* x) nil)))

(defmacro pn-internal-flag (_index)
  `(aref *pn-internal-flags* ,_index))

;;; ----------
;;; STATISTICS
;;; ----------
(declaim (type fixnum *pn-stat-size*))
(defparameter *pn-stat-size* 50)

(declaim (type (simple-array fixnum (50)) *pn-stats*))
(defvar *pn-stats* (make-array *pn-stat-size*
			       :element-type 'fixnum
			       :initial-element 0))

;;; STATISTICS ACCESSOR
;;;
(defmacro pn-stat (indx) `(the fixnum (aref *pn-stats* ,indx)))
(defmacro pn-stats (indx) `(the fixnum (aref *pn-stats* ,indx)))

(defun reset-infer-statistics ()
  (dotimes (x *pn-stat-size*)
    (setf (aref *pn-stats* x) 0)))

;;; statistics index

(defconstant cl-input 1)
(defconstant cl-generated 2)
(defconstant cl-kept 3)
(defconstant cl-for-sub 4)
(defconstant cl-back-sub 5)
(defconstant cl-tautology 6)
(defconstant cl-given 7)
(defconstant cl-wt-delete 8)
(defconstant rewrites 9)
(defconstant unit-deletes 10)
(defconstant empty-clauses 11)
(defconstant for-sub-sos 12)
(defconstant new-demods 13)
(defconstant cl-back-demod 14)
(defconstant sos-size 15)
(defconstant cl-not-anc-subsumed 16)
(defconstant usable-size 17)
(defconstant demodulators-size 18)
(defconstant init-wall-seconds 19)
(defconstant binary-res-gen 20)
(defconstant hyper-res-gen 21)
(defconstant neg-hyper-res-gen 22)
(defconstant ur-res-gen 23)
(defconstant para-into-gen 24)
(defconstant para-from-gen 25)
(defconstant demod-inf-gen 26)
(defconstant hot-generated 27)
(defconstant hot-kept 28)
(defconstant factor-simplifications 29)
(defconstant hot-size 30)
(defconstant passive-size 31)
(defconstant back-unit-del-gen 32)
(defconstant factor-gen 33)
(defconstant demod-limits 34)

;;; CLOCKS
;;;
(declaim (type fixnum *pn-max-clocks*))
(defparameter *pn-max-clocks* 25)

(declaim (type simple-vector *pn-clocks*))
(defvar *pn-clocks* (make-array *pn-max-clocks*))

(defstruct (pn-clock (:type list))
  (accum 0 :type integer)		; accumlated time
  (curr -1 :type integer))		; time since clock has been turned on

(defmacro clock-start (clock-num)
  `(let ((clock (aref *pn-clocks* ,clock-num)))
     (if (not (= (pn-clock-curr clock) -1))
	 (with-output-chaos-warning ()
	   (format t "clock #~d already on." ,clock-num))
       (setf (pn-clock-curr clock) (get-internal-real-time)))))

(defmacro clock-stop (clock-num)
  `(let ((clock (aref *pn-clocks* ,clock-num)))
     (if (= (pn-clock-curr clock) -1)
	 (with-output-chaos-warning ()
	   (format t "clock #~d already stop." ,clock-num))
       (progn
	 (incf (pn-clock-accum clock)
	       (- (get-internal-real-time) (pn-clock-curr clock)))
	 (setf (pn-clock-curr clock) -1)))))

(defun reset-pn-clocks ()
  (dotimes (x *pn-max-clocks*)
    (let ((clock (aref *pn-clocks* x)))
      (setf (pn-clock-curr clock) -1)
      (setf (pn-clock-accum clock) 0))))

(defmacro pn-clock-value (index)
  `(pn-clock-accum (aref *pn-clocks* ,index)))

(defconstant PN-GLOBAL-RUN-TIME   0)
(defconstant BINARY-TIME          1)
(defconstant HYPER-TIME           2)
(defconstant NEG-HYPER-TIME       3)
(defconstant UR-TIME              4)
(defconstant PARA-INTO-TIME       5)
(defconstant PARA-FROM-TIME       6)

(defconstant PRE-PROC-TIME       7)
(defconstant DEMOD-TIME          8)
(defconstant ORDER-EQ-TIME       9)
(defconstant UNIT-DEL-TIME       10)
(defconstant WEIGH-CL-TIME       11)
(defconstant SORT-LITS-TIME      12)
(defconstant FOR-SUB-TIME        13)
(defconstant DEL-CL-TIME         14)
(defconstant KEEP-CL-TIME        15)
(defconstant CONFLICT-TIME       16)
(defconstant NEW-DEMOD-TIME      17)
(defconstant POST-PROC-TIME      18)
(defconstant BACK-DEMOD-TIME     19)
(defconstant BACK-SUB-TIME       20)
(defconstant FACTOR-TIME         21)
(defconstant FACTOR-SIMP-TIME    22)
(defconstant BACK-UNIT-DEL-TIME  23)
(defconstant print-clause-time   24)

(eval-when (eval load)
  (dotimes (x *pn-max-clocks*)
    (setf (aref *pn-clocks* x)
      (make-pn-clock))))

(declaim (type integer *pn-internal-start-time*))
(defvar *pn-internal-start-time* 0)

(defun pn-start-internal-clock ()
  (setq *pn-internal-start-time*
    (get-internal-run-time)))

(defun pn-internal-run-time ()
  (elapsed-time-in-seconds *pn-internal-start-time*
			    (get-internal-run-time)))

;;; SETUP
;;;
(defvar .pn-ignore-ops. nil)

(defun setup-pignose ()
  (setq .pn-ignore-ops.
    (list *bool-and*
	  *bool-or*
	  *bool-not*
	  *sort-membership*
	  *bool-if*
	  *bool-imply*
	  *bool-iff*
	  *bool-xor*
	  *bool-equal*
	  *beh-equal*
	  *bool-nonequal*
	  *beh-eq-pred*
	  *bool-and-also*
	  *bool-or-else*))
  )

;;; EOF
