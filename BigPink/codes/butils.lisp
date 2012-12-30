;;;-*-Mode:LISP; Package: CHAOS; Base:10; Syntax:Common-lisp -*-
;;; $Id: butils.lisp,v 1.2 2003-11-04 03:11:25 sawada Exp $
;;; 
(in-package :chaos)
#|=============================================================================
System:Chaos
Module:BigPink
File:butils.lisp
=============================================================================|#
#-:chaos-debug
(declaim (optimize (speed 3) (safety 0) #-GCL (debug 0)))
#+:chaos-debug
(declaim (optimize (speed 1) (safety 3) #-GCL (debug 3)))

;;; **************************************************************************
;;; 			    BASIC UTILITY FUNCTIONS
;;; **************************************************************************

;;; function specs
;;; TERM-IS-IDENTICAL : TERM1 TERM2 -> Bool
;;;
(defun term-is-identical (t1 t2)
  (declare (type term t1)
           (type (or term null) t2)
           (values boolean))
  (if (term-type-eq t1 t2)
      (or (term-eq t1 t2)
          (if t2
              (cond ((term-is-application-form? t1)
                     (if (method-w= (term-head t1)
                                    (term-head t2))
                         (let ((subs1 (term-subterms t1))
                               (subs2 (term-subterms t2)))
                           (loop
                             ;; (when (null subs1) (return (null subs2)))
                             (when (null subs1) (return t))
                             (unless (term-is-identical (car subs1)
                                                        (car subs2))
                               (return nil))
                             (setq subs1 (cdr subs1)  subs2 (cdr subs2))))
                       nil))
                    ((term-is-variable? t1) (variable-eq t1 t2))
                    ((term-is-builtin-constant? t1)
                     (term-builtin-equal t1 t2))
                    ((term-is-lisp-form? t1)
                     (and (term-is-lisp-form? t2)
                          (equal (lisp-form-original-form t1)
                                 (lisp-form-original-form t2))))
                    (t (break "unknown type of term ~s" t1 )))))
    ))


;;; TERM-OCCURS-IN : TERM1 TERM2 -> Bool
;;;
(defun term-occurs-in (t1 t2)
  (declare (type term t1 t2)
           (values boolean))
  (or (term-is-identical t1 t2)
      (and (term-is-application-form? t2)
           (dolist (sub (term-subterms t2) nil)
             (when (term-occurs-in t1 sub)
               (return-from term-occurs-in t))))
      ))

;;; OPERATOR-OCCURS-IN : method term -> bool
;;; true if method appears in term.
;;;
(defun operator-occurs-in (meth term)
  (declare (type method meth)
           (type term term)
           (values boolean))
  (cond ((or (term-is-variable? term)
             (term-is-builtin-constant? term)
             (term-is-lisp-form? term))
         (return-from operator-occurs-in nil))
        ((method= meth (term-head term))
         (return-from operator-occurs-in t))
        (t (dolist (sub (term-subterms term))
             (when (operator-occurs-in meth sub)
               (return-from operator-occurs-in t)))
           nil)))

;;; COPY-TERM-REUSING-VARIABLES
;;;
(defun copy-term-reusing-variables (term &optional variables)
  (declare (type term term)
           (list variables)
           (values term))
  (cond ((term-is-variable? term)
         (let ((var (find-if #'(lambda (x) (variable-eq term x)) variables)))
           (if var
               var
             (if variables
                 (with-output-panic-message-n (:p-pn-0010 (list (variable-name term)))
                   ;; (format t "copying term, could not find var ~a"
                   ;;        (variable-name term))
                   (break "type in :q for returning to top-level.")
                   )
               term))))
        ((term-is-application-form? term)
         (@create-application-form-term
          (term-head term)
          (term-sort term)
          (mapcar #'(lambda (x)
                      (copy-term-reusing-variables x
                                                   variables))
                  (term-subterms term))))
        (t (simple-copy-term term))))

(defun allocate-new-term-cell (term)
  (declare (type term term)
           (values term))
  (create-term (term-body term)))

;;; PN-MAKE-NEW-VARIABLE : var -> var
;;;
(let ((gen-var-num 0))
  (declare (type fixnum gen-var-num))
  
  (defun pn-reset-var-num () (setq gen-var-num 0))
  (defun pn-current-var-num () gen-var-num)
  (defun pn-next-var-num () (1+ gen-var-num))

  (defun pn-make-new-variable (var)
    (declare (type term var)
             (values term))
    (let ((vnam (incf gen-var-num)))
      (declare (type fixnum vnam))
      (if (pn-flag new-variable-name)
          (make-variable-term (variable-sort var)
                              vnam
                              vnam)
        (make-variable-term (variable-sort var)
                            vnam
                            (variable-print-name var))))
    )
  
  

  (defun pn-make-var-on-the-fly (sort)
    (let ((name (incf gen-var-num)))
      (declare (type fixnum name))
      (make-variable-term sort
                          name
                          name)))

  )

;;; REPLACE-TERM-VARS (term subst)
;;;
(defun replace-term-vars (term subst)
  (declare (type term term)
           (type list subst)
           (values term))
  (when (term-is-application-form? term)
    (dotimes (x (length (term-subterms term)))
      (declare (type fixnum x))
      (let ((sub (term-arg-n term x)))
        (declare (type term sub))
        (cond ((term-is-variable? sub)
               (let ((new-var (variable-image subst sub)))
                 (when new-var
                   (setf (term-arg-n term x) new-var))))
              (t (replace-term-vars sub subst))))))
  term)

;;; TERM-UNIQUE-VARS

(defun make-term-var-rename-map (term)
  (declare (type term term)
           (values list))
  (let ((vars (term-variables term))
        (subst nil))
    (dolist (v vars)
      (push (cons v (pn-make-new-variable v))
            subst))
    subst))

(defun term-unique-vars (term &optional (dest nil))
  (declare (type term term)
           (type boolean dest)
           (values term list))
  (let ((subst (make-term-var-rename-map term)))
    (if subst
        (if dest
            (values (replace-term-vars term subst)
                    subst)
          (values (apply-subst subst term)
                  subst)))
    (values term nil)))

;;; IS-SKOLEM : method module -> Bool
;;;
(defun is-skolem (meth &optional (module (or *current-module* *last-module*)))
  (declare (type method meth)
           (type module module)
           (values boolean))
  (memq meth (module-skolem-functions module)))

;;; ID-NESTED-SKOLEMS : Term -> Bool
;;; t iff term or any of its subterms have the identical-nested-skolems property.
;;;
(defun id-nested-skolems (term)
  (declare (type term term)
           (values boolean))
  (unless (term-is-application-form? term)
    (return-from id-nested-skolems nil))
  ;;
  (when (is-skolem (term-head term))
    (dolist (sub (term-subterms term))
      (when (operator-occurs-in (term-head term) sub)
        (return-from id-nested-skolems t))))
  (dolist (sub (term-subterms term))
    (when (id-nested-skolems sub)
      (return-from id-nested-skolems t)))
  nil)

;;; IDENT-NESTED-SKOLEMS : Clause -> Bool
;;; t iff any of the terms in clause have the
;;; identical-nested-skolems property.  
;;;
(defun ident-nested-skolems (clause)
  (declare (type clause clause)
           (values boolean))
  (dolist (lit (clause-literals clause))
    (declare (type literal lit))
    (when (id-nested-skolems (literal-atom lit))
      (return-from ident-nested-skolems t)))
  nil)

;;; MAKE-VAR-MAPPING : List[Variables] -> ALIST[(OldVar . NewVar)]
;;;
(defun make-var-mapping (vars)
  (declare (type list vars)
           (values list))
  (let ((new-vars-list nil))
    (dolist (v vars)
      (setq new-vars-list (acons v
                                 (pn-make-new-variable v)
                                 new-vars-list)))
    new-vars-list))

;;; INIT-PN-OPTIONS
;;;
(defun init-pn-options ()
  (declare (values t))
  ;; reset flags
  (dotimes (x *pn-max-flags*)
    (setf (pn-flag x) nil))
  ;; reset initially `on' flags
  ;; (setf (pn-flag sos-queue) t)
  (setf (pn-flag para-from-left) t)
  (setf (pn-flag para-from-right) t)
  (setf (pn-flag para-into-left) t)
  (setf (pn-flag para-into-right) t)
                                        ;(setf (pn-flag detailed-history) t)
  (setf (pn-flag for-sub) t)
  (setf (pn-flag back-sub) t)
                                        ;(setf (pn-flag demod-history) t)
  (setf (pn-flag print-kept) t)
  (setf (pn-flag print-stats) t)
                                        ;(setf (pn-flag demod-history) t)
  (setf (pn-flag print-given) t)
  (setf (pn-flag print-back-sub) t)
  (setf (pn-flag print-new-demod) t)
  (setf (pn-flag print-back-demod) t)
  (setf (pn-flag back-unit-deletion) nil)
  (setf (pn-flag simplify-fol) t)
  (setf (pn-flag print-proofs) t)
  (setf (pn-flag new-variable-name) t)
  (setf (pn-flag print-message) t)
  ;; (setf (pn-flag quiet) t)
  (setf (pn-flag order-hyper) t)
  ;; (setf (pn-flag prop-res) t)
  (setf (pn-flag put-goal-in-sos) t)
  (setf (pn-flag check-init-always) t)
  ;;
  (setf (pn-flag no-junk) nil)
  (setf (pn-flag no-confusion) nil)
  ;;
  (setf (pn-flag meta-paramod) nil)
  ;; (setf (pn-flag randomize-sos) t)
  (setf (pn-flag randomize-sos) nil)
  ;;
  ;; (setf (pn-flag unify-heavy) t) **********
  ;;
  ;; reset parameters
  ;;
  (dotimes (x *pn-max-parameters*)
    (setf (pn-parameter x) -1))
  (setf (pn-parameter demod-limit) 1000)
  (setf (pn-parameter max-weight) most-positive-fixnum)
  (setf (pn-parameter max-given) -1)
  (setf (pn-parameter max-sos) -1)
  (setf (pn-parameter max-seconds) -1)
  (setf (pn-parameter neg-weight) 0)
  (setf (pn-parameter max-kept) -1)
  (setf (pn-parameter max-gen) -1)
  (setf (pn-parameter max-literals) -1)
  (setf (pn-parameter max-proofs) 1)
  (setf (pn-parameter stats-level) 2)
  (setf (pn-parameter pick-given-ratio) -1)
  (setf (pn-parameter change-limit-after) 0)
  (setf (pn-parameter new-max-weight) most-positive-fixnum)
  (setf (pn-parameter max-answers) -1)
  (setf (pn-parameter dynamic-demod-depth) -1)
  (setf (pn-parameter dynamic-demod-rhs) 1)
  (setf (pn-parameter inv-check-max-depth) -1)
  (setf (pn-parameter control-memory-point) 20)
  )

;;; initialize
(eval-when (eval load)
  (init-pn-options))

;;; FIND-PN-FLAG-INDEX : Name -> Index
;;;
(defun find-pn-flag-index (name)
  (declare (type simple-string name)
           (values (or null fixnum)))
  (let ((i 0))
    (declare (type fixnum i))
    (dotimes (x *pn-max-flags*)
      (when (string= name (pn-flag-name x))
        (return-from find-pn-flag-index i))
      (incf i))
    nil))

;;; FIND-PN-PARAMETER-INDEX : Name -> Index
;;;
(defun find-pn-parameter-index (name)
  (declare (type simple-string name)
           (values (or null fixnum)))
  (let ((i 0))
    (declare (type fixnum i))
    (dotimes (x *pn-max-parameters*)
      (when (string= name (pn-parameter-name x))
        (return-from find-pn-parameter-index i))
      (incf i))
    nil))

;;; SAVE-PN-FLAGS
(defun save-pn-flags ()
  (declare (values simple-vector))
  (let ((flg-array (make-array *pn-max-flags*)))
    (dotimes (x *pn-max-flags*)
      (setf (aref flg-array x) (pn-flag x)))
    flg-array))

;;; RESTORE-PN-FLAGS
(defun restore-pn-flags (array)
  (declare (type simple-vector array)
           (values t))
  (dotimes (x *pn-max-flags*)
    (setf (pn-flag x) (aref array x))))

;;; SAVE-PN-PARAMETERS
(defun save-pn-parameters ()
  (declare (values simple-array))
  (let ((para-array (make-array *pn-max-parameters*)))
    (dotimes (x *pn-max-parameters*)
      (setf (aref para-array x) (pn-parameter x)))
    para-array))

;;; RESTORE-PN-PARAMETERS
(defun restore-pn-parameters (array)
  (declare (type simple-vector array)
           (values t))
  (dotimes (x *pn-max-parameters*)
    (setf (pn-parameter x) (aref array x))))

;;; --------------------
;;; OPTION SET UTILITIES
;;; --------------------
(defun find-option-set (name)
  (declare (type simple-string name)
           (values (or option-set null)))
  (find-if #'(lambda (x) (string= name (option-set-name x)))
           *pn-option-set*))

(defun create-option-set (name)
  (declare (type simple-string name))
  (let ((oset (make-option-set :name name)))
    ;; (declare (type option-set oset))
    (let ((flags (save-pn-flags))
          (parameters (save-pn-parameters)))
      (setf (option-set-flags oset) flags)
      (setf (option-set-parameters oset) parameters)
      oset)))

(defun save-option-set (name)
  (declare (type simple-string name))
  (let ((oset (find-option-set name)))
    (when (pn-flag print-message)
      (with-output-msg ()
        (format t "saving options to ~a." name)))
    (if oset
        (progn
          (unless (pn-flag quiet)
            (with-output-chaos-warning ()
              (format t "changing option set ~a" name)))
          (setf (option-set-flags oset) (save-pn-flags))
          (setf (option-set-parameters oset) (save-pn-parameters)))
      (progn (setq oset (create-option-set name))
             (push oset *pn-option-set*)))
    t))

(defun restore-option-set (name)
  (declare (type simple-string name))
  (let ((oset (find-option-set name)))
    (unless oset
      (with-output-chaos-error ('no-opset)
        (format t "no such option set ~a" name)))
    (when (pn-flag print-message)
      (with-output-msg ()
        (format t "restoring options from ~a" name)))
    ;;
    (restore-pn-flags (option-set-flags oset))
    (restore-pn-parameters (option-set-parameters oset))
    t))

(defun show-option-set (name)
  (declare (type simple-string name))
  (let ((oset (find-option-set name)))
    (unless oset
      (with-output-chaos-error ('no-oset)
        (format t "no such option  set ~a" name)))
    (let ((oflags (save-pn-flags))
          (oparams (save-pn-parameters)))
      (restore-option-set name)
      (pr-list-of-flag)
      (print-next)
      (pr-list-of-param)
      (restore-pn-flags oflags)
      (restore-pn-parameters oparams)
      t)))

;;; PR-LIST-OF-FLAG 
;;;
(defun pr-list-of-flag ()
  (let ((*print-indent* 2)
        (flags nil))
    (format t "** PigNose Flags --------------")
    (dotimes (x *pn-max-flags*)
      (unless (equal (pn-flag-name x) "")
        (push x flags)))
    (setq flags (sort flags 
                      #'(lambda (x y)
                          (declare (type fixnum x y))
                          (string< (the simple-string (pn-flag-name x))
                                   (the simple-string (pn-flag-name y))))
                      ))
    (dolist (flag flags)
      (print-next)
      (format t "flag(~a, ~a)"
              (pn-flag-name flag)
              (if (pn-flag flag)
                  "on"
                "off")))))

;;; PR-LIST-OF-PARAM
;;;
(defun pr-list-of-param ()
  (let ((*print-indent* 2)
        (params nil))
    (format t "** PigNose Parameters ---------")
    (dotimes (x *pn-max-parameters*)
      (unless (equal (pn-parameter-name x) "")
        (push x params)))
    (setq params (sort params
                       #'(lambda (x y)
                           (declare (type fixnum x y))
                           (string< (the simple-string (pn-parameter-name x))
                                    (the simple-string (pn-parameter-name y))))))
    (dolist (x params)
      (print-next)
      (format t "param(~a,~d)~35t range ~d .. ~d"
              (pn-parameter-name x)
              (pn-parameter x)
              (pn-parameter-min x)
              (pn-parameter-max x)))))

;;; LIST OF OPTIONS
(defun pr-list-of-option ()
  (if *pn-option-set*
      (with-output-msg ()
        (format t "** PigNose Option Sets -------")
        (dolist (x *pn-option-set*)
          (print-next)
          (princ (option-set-name x))))
    (with-output-msg ()
      (princ "none"))))

;;; ----------------
;;; AUTO-CHANGE-FLAG
;;;
(defun auto-change-flag (index value)
  (declare (type fixnum index)
           (type boolean value))
  (unless (eq (pn-flag index) value)
    (when (pn-flag print-message)
      (with-output-simple-msg ()
        (format t "   dependent: flag(~a, ~a)"
                (pn-flag-name index)
                (if value "on" "off"))))
    (setf (pn-flag index) value)
    (dependent-flags index)))

(defun dependent-flags (index)
  (declare (type fixnum index))
  (when (pn-flag index)
    ;; just set
    (case index
      (#.kb
       (auto-change-flag para-from t)
       (auto-change-flag para-into t)
       (auto-change-flag para-from-left t)
       (auto-change-flag para-from-right nil) 
       (auto-change-flag para-into-left t)
       (auto-change-flag para-into-right nil)
       (auto-change-flag para-from-vars t)
       (auto-change-flag eq-units-both-ways t)
       (unless (pn-flag no-demod)
         (auto-change-flag dynamic-demod-all t))
       (unless (pn-flag no-back-demod)
         (auto-change-flag back-demod t))
       (auto-change-flag process-input t)
       (auto-change-flag lrpo t)
       )
      (#.kb2
       (auto-change-flag para-from t)
       (auto-change-flag para-into t)
       (auto-change-flag para-from-left t)
       (auto-change-flag para-from-right nil) 
       (auto-change-flag para-into-left t)
       (auto-change-flag para-into-right nil)
       (auto-change-flag para-from-vars nil)
       (auto-change-flag eq-units-both-ways t)
       (unless (pn-flag no-demod)
         (auto-change-flag dynamic-demod-all t))
       (unless (pn-flag no-back-demod)
         (auto-change-flag back-demod t))
       (auto-change-flag process-input t)
       (auto-change-flag lrpo t)
       )
      (#.kb3
       (auto-change-flag para-from t)
       (auto-change-flag para-into t)
       (auto-change-flag para-from-left t)
       (auto-change-flag para-from-right nil) 
       (auto-change-flag para-into-left t)
       (auto-change-flag para-into-right nil)
       (auto-change-flag para-from-vars nil)
       (auto-change-flag eq-units-both-ways nil)
       (unless (pn-flag no-demod)
         (auto-change-flag dynamic-demod-all t))
       (unless (pn-flag no-back-demod)
         (auto-change-flag back-demod t))
       (auto-change-flag process-input t)
       (auto-change-flag lrpo t)
       )
      (#.back-demod
       (auto-change-flag dynamic-demod t))
      (#.dynamic-demod-all
       (auto-change-flag dynamic-demod t))
      (#.dynamic-demod
       (auto-change-flag order-eq t))
      (#.binary-res
       (auto-change-flag factor t)
       (auto-change-flag unit-deletion t))
      (#.very-verbose
       (auto-change-flag print-kept t)
       (auto-change-flag print-new-demod t)
       (auto-change-flag trace-demod t))
      #||
      (#.para-all
       (auto-change-flag detailed-history nil))
      ||#
      (#.propositional
       (auto-change-flag sort-literals t)
       (auto-change-flag process-input t)
       (auto-change-flag prop-res nil))
      ((#.auto1 #.auto3)
       (auto-change-flag process-input t)
       (auto-change-flag print-kept nil)
       (auto-change-flag print-new-demod nil)
       (auto-change-flag print-back-demod nil)
       (auto-change-flag print-back-sub nil)
       (auto-change-flag control-memory t)
       (auto-change-param max-sos 500)
       (auto-change-param pick-given-ratio 4)
       (auto-change-param stats-level 2)
       (auto-change-param max-seconds 3600)
       )
      (#.auto2
       (auto-change-flag process-input t)
       (auto-change-flag print-kept nil)
       (auto-change-flag print-new-demod nil)
       (auto-change-flag print-back-demod nil)
       (auto-change-flag print-back-sub nil)
       (auto-change-flag control-memory t)
       (auto-change-param max-sos 500)
       (auto-change-param pick-given-ratio 4)
       (auto-change-param stats-level 2)
       (auto-change-param max-seconds 3600)
       )
      (#.auto
       (auto-change-flag auto1 t))
      #|| flag is obsolete
      (#.build-proof-object
       (auto-change-flag order-history t)
       (auto-change-flag detailed-history t))
      ||#
      (#.back-unit-deletion
       (auto-change-flag unit-deletion t))
      (#.quiet
       (auto-change-flag print-message nil)
       (auto-change-flag print-kept nil)
       (auto-change-flag print-given nil)
       (auto-change-flag print-back-sub nil)
       (auto-change-flag print-new-demod nil)
       (auto-change-flag print-back-demod nil)
       ;; (auto-change-flag print-proofs nil)
       (auto-change-flag print-stats nil)
       (auto-change-flag print-lists-at-end nil)
       (auto-change-flag very-verbose nil)
       )
      (#.no-demod
       (auto-change-flag no-back-demod t)
       (auto-change-flag demod-inf nil)
       (auto-change-flag dynamic-demod nil)
       (auto-change-flag dynamic-demod-all nil)
       (auto-change-flag dynamic-demod-lex-dep nil)
       (auto-change-flag back-demod nil))
      (#.no-back-demod
       (auto-change-flag back-demod nil))
      #||
      (#.no-new-demod
       (auto-change-flag no-back-demod t))
      ||#
      (#.demod-inf
       (auto-change-flag dynamic-demod-all t)
       ;; (auto-change-flag lrpo t)
       )
      ;; 
      ))
  )

;;; AUTO-CHANGE-PARAM
;;;
(defun auto-change-param (index value)
  (declare (type fixnum index value))
  (unless (eql (pn-parameter index) value)
    (when (pn-flag print-message)
      (with-output-simple-msg ()
        (format t "   dependent: param(~a, ~d)."
                (pn-parameter-name index)
                value)))
    (setf (pn-parameter index) value)
    (dependent-params index)))

(defun dependent-params (index)
  index)

;;; MOVE-CLAUSES
;;;
(defun move-from-usable-to-sos (pred)
  (declare (type (function (clause) boolean) pred))
  (let ((new-sos nil)
        (new-usable nil))
    (dolist (c *usable*)
      (if (funcall pred c)
          (progn
            (push c new-sos)
            (setf (clause-container c) :sos))
        (progn
          (push c new-usable)
          (setf (clause-container c) :usable))))
    (setq *usable* (nreverse new-usable))
    (setq *sos* (nreverse new-sos))
    (setf (pn-stat usable-size) (length *usable*))
    (setf (pn-stat sos-size) (length *sos*))
    (when *current-psys*
      (setf (psystem-usable *current-psys*) *usable*)
      (setf (psystem-sos *current-psys*) *sos*))
    ))

;;;
;;;
(defun get-global-list (list)
  (declare (type symbol list)
           (values list))
  (case list
    (:sos *sos*)
    (:usable *usable*)
    (:hot *hot*)
    (t nil)))

;;; PN-CONTROL-MEMORY
;;;
(declaim (type fixnum .next-cotrol-point.)
         (type fixnum .max-weight.))

(defvar .next-control-point. 0)

#||
(defun reset-memory-control ()
  (setq .next-control-point. 0))
||#

(defun reset-memory-control ()
  (setq .next-control-point. (* 20 (the fixnum (length *sos*)))))

(defparameter .max-weight. 500)
(declaim (type (simple-array fixnum (500)) .sos-dist.))
(defvar .sos-dist. (make-array .max-weight. :element-type 'fixnum))

(defun pn-control-memory ()
  (let ((control
         (and (not (= (pn-parameter max-sos) -1))
              #||
              (and (< (pn-parameter max-sos) (pn-stat sos-size))
                   (or (zerop .next-control-point.)
                       (= .next-control-point. (pn-stat cl-given))))
              ||#
              (or (< (pn-parameter max-sos) (pn-stat sos-size))
                  (= .next-control-point. (pn-stat cl-given)))
              )))
    ;;
    (when control
      (unless (= (pn-parameter control-memory-point) -1)
        (setq .next-control-point. (+ (pn-stat cl-given)
                                      (pn-parameter control-memory-point))))
      (let ((size 0))
        (declare (type fixnum size))
        (dotimes (x .max-weight.)
          (setf (aref .sos-dist. x) 0))
        ;;
        (dolist (cl *sos*)
          (let ((cl-weight (clause-pick-weight cl))
                (wt 0))
            (declare (type fixnum wt))
            (if (< cl-weight 0)
                (setq wt 0)
              (if (<= .max-weight. cl-weight)
                  (setq wt (1- .max-weight.))
                (setq wt cl-weight)))
            (incf (aref .sos-dist. wt))
            (incf size)))
        ;;
        (let ((i 0)
              (n 0))
          (declare (type fixnum i n))
          (while (and (< i .max-weight.)
                      (<= (* n 20) size))
            (incf n (aref .sos-dist. i))
            (incf i))
          ;;
          (decf i)
          ;; reset weight limit to i
          (when (or (< i (pn-parameter max-weight))
                    (= 0 (pn-parameter max-weight)))
            (setf (pn-parameter max-weight) i)
            (when (pn-flag print-message)
              (with-output-msg ()
                (format t "resetting weight limit to ~d" i)
                (print-next)
                (format t "sos size = ~d" size))))
          )))
    ))

;;; PN-RUN-TIME
;;;
(defun pn-run-time ()
  (declare (values float))
  (clock-stop pn-global-run-time)
  (let ((seconds (time-in-seconds (pn-clock-value pn-global-run-time))))
    (clock-start pn-global-run-time)
    ;; (format t "~%<~s> seconds.~%" seconds)
    seconds))

;;; CHECK-PN-STOP
;;; should the search be terminated?
;;; returns one of:
;;;  :keep-searching  : should not stop
;;;  :max-given-exit  : stop due to max-given option
;;;  :max-gen-exit    : stop due to max-gen option
;;;  :max-kept-exit   : stop due to max-kept option
;;;  :max-seconds     : stop due to max-seconds option
;;;
(defun check-pn-stop ()
  (let ((given (pn-stat cl-given))
        (gen (pn-stat cl-generated))
        (kept (pn-stat cl-kept))
        (seconds (pn-internal-run-time))
        (stat :keep-searching))
    (declare (type fixnum given gen kept)
             (type single-float seconds)
             (type symbol stat)
             (values symbol))
    (let ((max-given? (pn-parameter max-given))
          (max-gen? (pn-parameter max-gen))
          (max-seconds? (pn-parameter max-seconds))
          (max-kept? (pn-parameter max-kept)))
      (declare (type fixnum max-given? max-gen? max-seconds? max-kept?))
      (if (and (not (= max-given? -1))
               (>= given max-given?))
          (setq stat :max-given-exit)
        (if (and (not (= max-seconds? -1))
                 (>= seconds (float max-seconds?)))
            (setq stat :max-seconds-exit)
          (if (and (not (= max-gen? -1))
                   (>= gen max-gen?))
              (setq stat :max-gen-exit)
            (if (and (not (= max-kept? -1))
                     (>= kept max-kept?))
                (setq stat :max-kept-exit)))))
      stat)))

;;; CHECK-FOR-PROOF : Clause -> Clause
;;; check for `empty clause proof' and `unit conflict' proof.
;;;
(defun check-for-proof (clause list)
  (declare (type clause clause)
           (type symbol list)
           (values (or null clause)))
  (let ((num-lits (num-literals clause))
        (e nil))
    (declare (type fixnum num-lits)
             (type (or null clause) e))
    (cond ((= 0 num-lits)
           (when (pn-flag print-message)
             (format t  "~% ~%** EMPTY CLAUSE__________________________")
             (with-output-simple-msg ()
               (princ " ")
               (print-next)
               (print-clause clause)))
           ;;
           (decf (pn-stat cl-kept))
           (delete-from-list list clause)
           (incf (pn-stat empty-clauses))
           (setq e clause)
           (when (pn-flag print-proofs)
             (print-proof e))
           )
          ;;
          ((= 1 num-lits)
           (let ((cp1 (unit-conflict clause)))
             (dolist (cl cp1)
               (setq e cl)
               (when (pn-flag print-message)
                 (format t  "~% ~%** UNIT CONFLICT_________________________")
                 (with-output-simple-msg ()
                   (princ " ")
                   (print-next)
                   (print-clause e)))
               (when (pn-flag print-proofs)
                 (print-proof e))
               ;;
               (delete-from-list list clause)
               #|| obsolete flag
               (when (pn-flag build-proof-object)
                 (build-proof-object e))
               ||#
               )))
          )
    ;;
    e))

;;; PRINT-PROOF
;;; *TODO*
(defun print-proof (clause)
  (format t  "~% ~%** PROOF ________________________________")
  (with-output-simple-msg ()
    (princ " ")
    (let ((cl-list (clause-all-parents clause)))
      (setq cl-list (cons clause cl-list))
      (setq cl-list
        (sort cl-list #'(lambda (x y) (< (clause-id x) (clause-id y)))))
      (dolist (cl cl-list)
        (print-next)
        (print-clause cl))))
  (format t "~% ~%** ______________________________________~% ~%")

  )

;;; MOVE-AXIOMS-TO-USABLE
;;; 
(defun move-axioms-to-usable (psys)
  (declare (type psystem psys)
           (values t))
  (let ((usable nil)
        (passive (psystem-passive psys)))
    (dolist (cl (psystem-axioms psys))
      (unless (member cl passive :test #'(lambda (x y)
                                           (eq (clause-axiom x)
                                               (clause-axiom y))))
        (setf (clause-container cl) :usable)
        (push cl usable)))
    (setf (psystem-usable psys)
      (nreverse usable))
    (setf (psystem-sos psys) nil)))

;;; CLAUSE-SET-PROPERTY
;;; returns some basic properties of clause set.
;;;
(defun clause-set-property (&optional check-sos-also)
  (declare (type boolean check-sos-also)
           (values symbol symbol symbol symbol fixnum))
  ;; find out some basic properties.
  (let ((propositional? t)
        (horn? t)
        (equality? t)
        (symmetry? t)
        (max-lits? 0))
    (declare (type boolean propositional? horn? equality? symmetry?)
             (type fixnum max-lits?))
    ;; propositional
    (setq propositional?
      (and *usable*
           (every #'propositional-clause? *usable*)))
    (when (and propositional?
               check-sos-also
               *sos*)
      (setq propositional?
        (every #'propositional-clause? *sos*)))
    ;; horn 
    (setq horn?
      (and *usable*
           (every #'horn-clause? *usable*)))
    (when (and horn? check-sos-also *sos*)
      (setq horn? (every #'horn-clause? *sos*)))
    ;; equality
    (setq equality?
      (some #'equality-clause? *usable*))
    (unless equality?
      (when (and check-sos-also *sos*)
        (setq equality?
          (some #'equality-clause? *sos*))))
    ;; symmetry
    (setq symmetry?
      (some #'symmetry-clause? *usable*))
    (unless symmetry?
      (when (and check-sos-also *sos*)
        (setq symmetry?
          (some #'symmetry-clause? *sos*))))
    ;; max literals
    (dolist (c *usable*)
      (let ((i (num-literals c)))
        (setq max-lits? (max max-lits? i))))
    (when check-sos-also
      (dolist (c *sos*)
        (let ((i (num-literals c)))
          (setq max-lits? (max max-lits? i)))))
    ;; returns basic properties
    (values propositional?
            horn?
            equality?
            symmetry?
            max-lits?)))

(defun report-clause-set-props (propositional?
                                horn?
                                equality?
                                symmetry?
                                max-lits?)
  (declare (type boolean propositional? horn? equality? symmetry?)
           (type fixnum max-lits?))
  ;;
  (when (pn-flag print-message)
    (with-output-simple-msg ()
      (princ "[Properties of input clauses]:")
      (print-next)
      (format t " propositional~18t= ~:[no~;yes~]" propositional?)
      (print-next)
      (format t " horn~18t= ~:[no~;yes~]" horn?)
      (print-next)
      (format t " equality~18t= ~:[no~;yes~]" equality?)
      (print-next)
      (format t " symmetry~18t= ~:[no~;yes~]" symmetry?)
      (print-next)
      (format t " max literals~18t= ~d" max-lits?))
    ))

;;; PN-AUTOMATIC-SETTINGS
;;; - do very simple syntactive analysis of the clauses and 
;;;   decide on a simple strategy.
;;; - print a message about the strategy.
;;;
(defun pn-automatic-settings-1 ()
  ;;
  (unless *current-psys*
    (with-output-panic-message-n (:p-pn-0020)
      ;; (format t "system error, no context in PigNose environment.")
      ))
  (move-axioms-to-usable *current-psys*)
  (setf *usable* (psystem-usable *current-psys*))
  (setf *sos* nil)
  #||
  (when *demodulators*
    (with-output-chaos-error ()
      (princ "`demodulators' list is not accepted in auto1 mode.")))
  ||#
  (when *sos*
    (with-output-chaos-error ()
      (princ "`sos' list is not accepted in auto1 mode.")))
  (when (or *weight-pick-given*
            *weight-purge-gen*
            *weight-terms*)
    (with-output-chaos-error ()
      (princ "weight lists not accepted in auto mode.")))

  ;; find out some basic properties.
  ;; all input clauses are in usable; move to sos.
  (multiple-value-bind (propositional?
                        horn?
                        equality?
                        symmetry?
                        max-lits?)
      (clause-set-property)
    ;; report the result
    (report-clause-set-props propositional?
                             horn?
                             equality?
                             symmetry?
                             max-lits?)
    ;;
    (when (pn-flag print-message)
      (with-output-simple-msg ()
        (princ "[selected strategy]:")))
    ;;
    (cond (propositional?
           #||
           (when (pn-flag print-message)
             (with-output-msg ()
               (princ "The clause set is propositional. the stragety will be")
               (print-next)
               (princ "ordered hyperresolution with the propositional")
               (print-next)
               (princ "optimizations, with satellites in sos and nuclei in usable.")))
           ||#
           (auto-change-flag propositional t)
           (auto-change-flag hyper-res t)
           (move-from-usable-to-sos #'positive-clause?))
          ;;
          ((and equality? (= 1 max-lits?))
           #||
           (when (pn-flag print-message)
             (with-output-msg ()
               (princ "All clauses are units, and equality is present; the")
               (print-next)
               (princ "strategy will be knuth-bendix with positive clauses in sos.")))
           ||#
           (auto-change-flag kb t)
           (when (every #'positive-clause? *usable*)
             (when (pn-flag print-message)
               (with-output-msg ()
                 (when (pn-flag print-message)
                   (princ "There is no negative clause, so all clause lists will")
                   (print-next)
                   (princ "be printed at the end of the search."))))
             (auto-change-flag print-lists-at-end t))
           (move-from-usable-to-sos #'positive-clause?))
          ((and (not horn?) (not equality?))
           #||
           (when (pn-flag print-message)
             (with-output-msg ()
               (princ "This is a non-Horn set without equality. The strategy")
               (print-next)
               (princ "will be ordered hyper-res, unit deletion, and factoring,")
               (print-next)
               (princ "with stellites in sos and with nuclei in usable.")))
           ||#
           (auto-change-flag hyper-res t)
           (auto-change-flag factor t)
           (auto-change-flag unit-deletion t)
           (move-from-usable-to-sos #'positive-clause?))
          ;;
          ((and horn? (not equality?))
           #||
           (when (pn-flag print-message)
             (with-output-msg ()
               (princ "This is a Horn set without equality. The strategy will")
               (print-next)
               (princ "be hyperresolution, with satelites in sos and nuclei")
               (print-next)
               (princ "in usable.")))
           ||#
           (auto-change-flag hyper-res t)
           (auto-change-flag order-hyper nil)
           (move-from-usable-to-sos #'positive-clause?))
          ;;
          ((and (not horn?) equality?)
           #||
           (when (pn-flag print-message)
             (with-output-msg ()
               (princ "This is a no-Horn set with equality. The strategy will be")
               (print-next)
               (princ "knuth-bendix, ordered hyper-res, factoring, and unit")
               (print-next)
               (princ "deletion, with positive clauses in sos and nonpositive")
               (print-next)
               (princ "clauses in usable")))
           ||#
           (auto-change-flag kb t)
           (auto-change-flag hyper-res t)
           (auto-change-flag unit-deletion t)
           (auto-change-flag factor t)
           (when symmetry?
             #||
             (when (pn-flag print-message)
               (with-output-msg ()
                 (princ "There is a clause for symmetry of equality, so it is")
                 (print-next)
                 (princ "assumed that equality is fully axiomatized; therefore,")
                 (print-next)
                 (princ "paramodulation is disabled.")))
             ||#
             (when (pn-flag print-message)
               (with-output-msg ()
                 (princ "Paramodulation is disabled, because there is a clause")
                 (print-next)
                 (princ "for symmetry of equality.")))
             (auto-change-flag para-from nil)
             (auto-change-flag para-into nil))
           (move-from-usable-to-sos #'positive-clause?))
          ;;
          ((and horn? equality?)
           #||
           (when (pn-flag print-message)
             (with-output-msg ()
               (princ "This is a Horn set with equality. The strategy will be")
               (print-next)
               (princ "knuth-bendix and hyper-res, with positive clauses in")
               (print-next)
               (princ "sos and non-positive clauses in usable.")))
           ||#
           (auto-change-flag kb t)
           (auto-change-flag hyper-res t)
           (auto-change-flag order-hyper nil)
           (when symmetry?
             #||
             (when (pn-flag print-message)
               (with-output-msg ()
                 (princ "There is a clause for symmetry of equality, so it is")
                 (print-next)
                 (princ "assumed that equality is fully axiomatized; therefore,")
                 (print-next)
                 (princ "paramodulation is disabled.")))
             ||#
             (when (pn-flag print-message)
               (with-output-msg ()
                 (princ "Paramodulation is disabled, because there is a clause")
                 (print-next)
                 (princ "for symmetry of equality.")))
             
             (auto-change-flag para-from nil)
             (auto-change-flag para-into nil))
           (move-from-usable-to-sos #'positive-clause?))
          ;;
          (t (with-output-msg ()
               (princ "Could not find any specific property here..."))) )))

(defun sos-has-pos-non-ground ()
  (dolist (cl *sos*)
    (declare (type clause cl))
    (if (and (positive-clause? cl)
             (not (ground-clause? cl)))
        (return-from sos-has-pos-non-ground t)))
  nil)

(defun pn-automatic-settings-2 ()
  ;;
  (unless *current-psys*
    (with-output-panic-message-n (:p-pn-0020)
      ;;(format t "system error, no context in PigNose env.")
      ))
  (move-axioms-to-usable *current-psys*)
  (setf *usable* (psystem-usable *current-psys*))
  (setf *sos* nil)
  ;;
  #||
  (when *demodulators*
    (with-output-chaos-error ()
      (princ "`demodulators' list is not accepted in auto mode.")))
  ||#
  (when (or *weight-pick-given*
            *weight-purge-gen*
            *weight-terms*)
    (with-output-chaos-error ()
      (princ "weight lists not accepted in auto mode.")))
  ;;
  (if (sos-has-pos-non-ground)
      (with-output-msg ()
        (princ "Sos has positive nongound clause; therefore it is not changed."))
    (progn
      (with-output-msg ()
        (princ "Every positive clause in sos is gound (or sos is empty);")
        (print-next)
        (princ "therefore we move all positive usable clauses to sos.")
        (move-from-usable-to-sos #'positive-clause?))))

  ;; find out some basic properties.
  (multiple-value-bind (propositional? 
                        horn?
                        equality?
                        symmetry?
                        max-lits?)
      (clause-set-property :sos-also)
    ;;
    (report-clause-set-props propositional?
                             horn?
                             equality?
                             symmetry?
                             max-lits?)
    ;;
    (when (pn-flag print-message)
      (with-output-msg ()
        (princ "selected strategy")))
    ;;
    (cond (propositional?
           #||
           (when (pn-flag print-message)
             (with-output-msg ()
               (princ "All clauses are propositional; therefore we set the")
               (print-next)
               (princ "propositional flag and use orderd hyperresolution.")))
           ||#
           (auto-change-flag propositional t)
           (auto-change-flag hyper-res t))
          ((= 1 max-lits?)
           ;; all unit
           #||
           (when (pn-flag print-message)
             (with-output-msg ()
               (princ "setting `pick-given-ration' to 2, because all clauses are units.")))
           ||#
           (auto-change-param pick-given-ratio 2))
          (t
           #||
           (when (pn-flag print-message)
             (with-output-msg ()
               (princ "setting hyper-res, because there are nonunits.")))
           ||#
           (auto-change-flag hyper-res t)

           (when (or equality? (not horn?))
             (when (pn-flag print-message)
               (with-output-msg ()
                 (princ "Setting ur-res, because this is a nonunit set containing")
                 (print-next)
                 (princ "either equality literals or non-Horn clauses.")))
             (auto-change-flag ur-res t))

           (cond (horn?
                  #||
                  (when (pn-flag print-message)
                    (with-output-msg ()
                      (princ "Clearning `order-hyper', because all clases are Horn.")))
                  ||#
                  (auto-change-flag order-hyper nil))
                 (t
                  #||
                  (when (pn-flag print-message)
                    (with-output-msg ()
                      (princ "Setting `factor' and `unit-deletion', because there are non-Horn clauses.")))
                  ||#
                  (auto-change-flag factor t)
                  (auto-change-flag unit-deletion t)))
           ))
    ;;
    (when equality?
      #||
      (when (pn-flag print-message)
        (with-output-msg ()
          (princ "Equality is present, so we set the `knuth-bendix' flag.")))
      ||#
      (auto-change-flag kb t)
      (when (> max-lits? 1)
        #||
        (when (pn-flag print-message)
          (with-output-msg ()
            (princ "As an incomplete hueristic, we paramodulate with units only.")))
        ||#
        (auto-change-flag para-from-units-only t)
        (auto-change-flag para-into-units-only t))
      (when symmetry?
        #||
        (when (pn-flag print-message)
          (with-output-msg ()
            (princ "There is a clause for symmetry of equality, so it is")
            (print-next)
            (princ "assumes that equality is fully axiomatized; therefore,")
            (print-next)
            (princ "paramodulation is disabled.")))
        ||#
        (when (pn-flag print-message)
          (with-output-msg ()
            (princ "Paramodulation is disabled, because there is a clause")
            (print-next)
            (princ "for symmetry of equality.")))

        (auto-change-flag para-from nil)
        (auto-change-flag para-into nil))
      )))


(defun pn-automatic-settings-3 ()
  ;;
  (unless *current-psys*
    (with-output-panic-message-n (:p-pn-0020)
      ;; (format t "system error, no context in PigNose env.")
      ))
  (move-axioms-to-usable *current-psys*)
  (setf *usable* (psystem-usable *current-psys*))
  (setf *sos* nil)
  #||
  (when *demodulators*
    (with-output-chaos-error ()
      (princ "`demodulators' list is not accepted in auto1 mode.")))
  ||#
  (when *sos*
    (with-output-chaos-error ()
      (princ "`sos' list is not accepted in auto mode.")))
  (when (or *weight-pick-given*
            *weight-purge-gen*
            *weight-terms*)
    (with-output-chaos-error ()
      (princ "weight lists not accepted in auto mode.")))

  ;; find out some basic properties.
  ;; all input clauses are in usable; move to sos.
  (multiple-value-bind (propositional?
                        horn?
                        equality?
                        symmetry?
                        max-lits?)
      (clause-set-property)
    ;; report the result
    (report-clause-set-props propositional?
                             horn?
                             equality?
                             symmetry?
                             max-lits?)
    ;;
    (when (pn-flag print-message)
      (with-output-simple-msg ()
        (princ "[selected strategy]:")))
    ;;
    (cond (propositional?
           #||
           (when (pn-flag print-message)
             (with-output-msg ()
               (princ "The clause set is propositional. the stragety will be")
               (print-next)
               (princ "ordered hyperresolution with the propositional")
               (print-next)
               (princ "optimizations, with satellites in sos and nuclei in usable.")))
           ||#
           (auto-change-flag propositional t)
           (auto-change-flag hyper-res t)
           (move-from-usable-to-sos #'positive-clause?))
          ;;
          ((and equality? (= 1 max-lits?))
           #||
           (when (pn-flag print-message)
             (with-output-msg ()
               (princ "All clauses are units, and equality is present; the")
               (print-next)
               (princ "strategy will be knuth-bendix with positive clauses in sos.")))
           ||#
	   ;; (auto-change-flag kb3 t) **************************
	   (auto-change-flag kb2 t)
           (when (every #'positive-clause? *usable*)
             (when (pn-flag print-message)
               (with-output-msg ()
                 (when (pn-flag print-message)
                   (princ "There is no negative clause, so all clause lists will")
                   (print-next)
                   (princ "be printed at the end of the search."))))
             (auto-change-flag print-lists-at-end t))
           (move-from-usable-to-sos #'positive-clause?))
          ((and (not horn?) (not equality?))
           #||
           (when (pn-flag print-message)
             (with-output-msg ()
               (princ "This is a non-Horn set without equality. The strategy")
               (print-next)
               (princ "will be ordered hyper-res, unit deletion, and factoring,")
               (print-next)
               (princ "with stellites in sos and with nuclei in usable.")))
           ||#
           (auto-change-flag hyper-res t)
           (auto-change-flag factor t)
           (auto-change-flag unit-deletion t)
           (move-from-usable-to-sos #'positive-clause?))
          ;;
          ((and horn? (not equality?))
           #||
           (when (pn-flag print-message)
             (with-output-msg ()
               (princ "This is a Horn set without equality. The strategy will")
               (print-next)
               (princ "be hyperresolution, with satelites in sos and nuclei")
               (print-next)
               (princ "in usable.")))
           ||#
           (auto-change-flag hyper-res t)
           (auto-change-flag order-hyper nil)
           (move-from-usable-to-sos #'positive-clause?))
          ;;
          ((and (not horn?) equality?)
           #||
           (when (pn-flag print-message)
             (with-output-msg ()
               (princ "This is a no-Horn set with equality. The strategy will be")
               (print-next)
               (princ "knuth-bendix, ordered hyper-res, factoring, and unit")
               (print-next)
               (princ "deletion, with positive clauses in sos and nonpositive")
               (print-next)
               (princ "clauses in usable")))
           ||#
	   ;; (auto-change-flag kb3 t)
	   (auto-change-flag kb2 t)
           (auto-change-flag hyper-res t)
           (auto-change-flag unit-deletion t)
           (auto-change-flag factor t)
           (when symmetry?
             #||
             (when (pn-flag print-message)
               (with-output-msg ()
                 (princ "There is a clause for symmetry of equality, so it is")
                 (print-next)
                 (princ "assumed that equality is fully axiomatized; therefore,")
                 (print-next)
                 (princ "paramodulation is disabled.")))
             ||#
             (when (pn-flag print-message)
               (with-output-msg ()
                 (princ "Paramodulation is disabled, because there is a clause")
                 (print-next)
                 (princ "for symmetry of equality.")))
             (auto-change-flag para-from nil)
             (auto-change-flag para-into nil))
           (move-from-usable-to-sos #'positive-clause?))
          ;;
          ((and horn? equality?)
           #||
           (when (pn-flag print-message)
             (with-output-msg ()
               (princ "This is a Horn set with equality. The strategy will be")
               (print-next)
               (princ "knuth-bendix and hyper-res, with positive clauses in")
               (print-next)
               (princ "sos and non-positive clauses in usable.")))
           ||#
           (auto-change-flag kb3 t)
           (auto-change-flag hyper-res t)
           (auto-change-flag order-hyper nil)
           (when symmetry?
             #||
             (when (pn-flag print-message)
               (with-output-msg ()
                 (princ "There is a clause for symmetry of equality, so it is")
                 (print-next)
                 (princ "assumed that equality is fully axiomatized; therefore,")
                 (print-next)
                 (princ "paramodulation is disabled.")))
             ||#
             (when (pn-flag print-message)
               (with-output-msg ()
                 (princ "Paramodulation is disabled, because there is a clause")
                 (print-next)
                 (princ "for symmetry of equality.")))

             (auto-change-flag para-from nil)
             (auto-change-flag para-into nil))
           (move-from-usable-to-sos #'positive-clause?))
          ;;
          (t (with-output-msg ()
               (princ "Could not find any specific property here...")))

          )))

;;;
;;; STATISTICS
;;; ==========
(defun output-pn-stats (level)
  (declare (type fixnum level))
  (print-pn-stat level))

(defun print-pn-stat (level &optional (stream *standard-output*))
  (declare (type fixnum level))
  (when (<= level 0)
    (return-from print-pn-stat nil))
  (if (< 2 level)
      (print-pn-stat-detail stream)
    (print-pn-stat-brief stream)))

(defun print-pn-stat-detail (stream)
  (with-output-simple-msg (stream)
    (format t "** PigNose statistics ------------------+")
    (format t "~%|  clauses given~28t~10,'.:d~32t |" (pn-stat cl-given))
    (format t "~%|  clauses generated~28t~10,'.:d~32t |" (pn-stat cl-generated))
    (when (or (pn-flag binary-res)
              (and (pn-flag prop-res)
                   (or (pn-flag hyper-res)
                       (pn-flag neg-hyper-res))))
      (format t "~%|    binary-res generated~28t~10,'.:d~32t |" (pn-stat binary-res-gen)))
    (when (pn-flag hyper-res)
      (format t "~%|    hyper-res generated~28t~10,'.:d~32t |" (pn-stat hyper-res-gen)))
    (when (pn-flag neg-hyper-res)
      (format t "~%|    neg-hyper-res gen.~28t~10,'.:d~32t |"
              (pn-stat neg-hyper-res-gen)))
    (when (pn-flag para-from)
      (format t "~%|    para-from generated~28t~10,'.:d~32t |" (pn-stat para-from-gen)))
    (when (pn-flag para-into)
      (format t "~%|    para-into generated~28t~10,'.:d~32t |" (pn-stat para-into-gen)))
    (when (pn-flag factor)
      (format t "~%|    factors generated~28t~10,'.:d~32t |" (pn-stat factor-gen)))
    (when (pn-flag demod-inf)
      (format t "~%|    demod-inf generated~28t~10,'.:d~32t |" (pn-stat demod-inf-gen)))


    (when (pn-flag ur-res)
      (format t "~%|    ur-res generated~28t~10,'.:d~32t |" (pn-stat ur-res-gen)))

    (when (pn-flag back-unit-deletion)
      (format t "~%|    back unit del. gen.~28t~10,'.:d~32t |" (pn-stat back-unit-del-gen)))
    ;;
    (format t "~%|  demod rewrites~28t~10,'.:d~32t |" (pn-stat rewrites))
    (format t "~%|  clauses wt,lit.sk delete~28t~10,'.:d~32t |"
            (pn-stat cl-wt-delete))
    (format t "~%|  tautologies deleted~28t~10,'.:d~32t |" (pn-stat cl-tautology))
    (format t "~%|  clauses forward subsumed~28t~10,'.:d~32t |"
            (pn-stat cl-for-sub))
    #||
    (when (pn-flag ancestor-subsume)
      (format t "~%|  cl not subsumed due to ancestor_subsume~28t~10,'.:d~32t |"
              (pn-stat cl-not-anc-subsumed)))
    ||#
    (format t "~%|    (subsumed by sos)~28t~10,'.:d~32t |" (pn-stat for-sub-sos))
    (format t "~%|  unit deletions~28t~10,'.:d~32t |" (pn-stat unit-deletes))
    (format t "~%|  factor simplifications~28t~10,'.:d~32t |"
            (pn-stat factor-simplifications))
    (format t "~%|  clauses kept~28t~10,'.:d~32t |" (pn-stat cl-kept))
    (when *hot*
      (format t "~%|    (hot clauses kept)~28t~10,'.:d~32t " (pn-stat hot-kept)))
    (format t "~%|  new demodulators~28t~10,'.:d~32t |" (pn-stat new-demods))
    (format t "~%|  empty clauses~28t~10,'.:d~32t |" (pn-stat empty-clauses))
    (format t "~%|  clauses back demodulated~28t~10,'.:d~32t |" (pn-stat cl-back-demod))
    (format t "~%|  clauses back subsumed~28t~10,'.:d~32t |" (pn-stat cl-back-sub))
    (format t "~%|  usable size~28t~10,'.:d~32t |" (pn-stat usable-size))
    (format t "~%|  sos size~28t~10,'.:d~32t |" (pn-stat sos-size))
    (format t "~%|  demodulators size~28t~10,'.:d~32t |" (pn-stat demodulators-size))
    #||
    (format t "~%|  passive size~28t~10,'.:d~32t |" (pn-stat passive-size))
    (format t "~%|  hot size~28t~10,'.:d~32t |" (pn-stat hot-size))
    ||#
    ;;
    (unless (= 0 (pn-stat demod-limits))
      (format t "~%|  demodulations stopped by limit~28t~10,'.:d~32t |"
              (pn-stat demod-limits)))
    (format t "~%+---------------------------------------+")
    ;;
    ))

(defun print-pn-stat-brief (stream)
  (with-output-simple-msg (stream)
    (format t "** PigNose statistics ------------------+")
    (format t "~%|  clauses given~28t~10,'.:d~32t |" (pn-stat cl-given))
    (format t "~%|  clauses generated~28t~10,'.:d~32t |" (pn-stat cl-generated))
    (format t "~%|  clauses kept~28t~10,'.:d~32t |" (pn-stat cl-kept))
    (format t "~%|  clauses forward subsumed~28t~10,'.:d~32t |"
            (pn-stat cl-for-sub))
    (format t "~%|  clauses back subsumed~28t~10,'.:d~32t |"
            (pn-stat cl-back-sub))
    (format t "~%+---------------------------------------+")
    ))

;;; INFER-CLEAN-UP
;;;
(defun infer-clean-up ()
  #||
  (when (pn-flag print-message)
    (with-output-simple-msg ()
      (format t "**> end of PigNose ----------------------")
      (format t "~% ")))
  ||#
  ;;
  (when *current-psys*
    ;; NOTE: *passive* never changes
    (setf (psystem-usable *current-psys*) *usable*)
    (setf (psystem-sos *current-psys*) *sos*))
  ;;
  (when (pn-flag print-lists-at-end)
    (print-usable-list)
    (print-sos-list)
    (print-passive-list)
    (print-demodulators-list))
  ;;
  (when (pn-flag print-stats)
    (output-pn-stats (pn-parameter stats-level)))
  ;;
  ;;  (clock-stop pn-global-run-time)
  ;;
  (setq *new-demodulator* nil)
  )

;;;
(defun print-usable-list ()
  (format t  "~% ~%** USABLE _______________________________")
  (with-output-simple-msg ()
    (princ " ")
    (dolist (cl *usable*)
      (print-next)
      (print-clause cl)))
  (format t "~% ~%"))

(defun print-sos-list ()
  (format t  "~% ~%** SOS __________________________________")
  (with-output-simple-msg ()
    (princ " ")
    (dolist (cl *sos*)
      (print-next)
      (print-clause cl)))
  (format t "~% ~%"))

(defun print-passive-list ()
  (when *passive*
    (format t  "~% ~%** PASSIVE ______________________________")
    (with-output-simple-msg ()
      (princ " ")
      (dolist (cl *passive*)
        (print-next)
        (print-clause cl)))
    (format t "~% ~%")))

(defun print-demodulators-list (&optional (hash *demodulators*))
  (let ((demods (get-all-demodulators hash t)))
    (when demods
      (format t  "~% ~%** DEMODULATORS _________________________")
      (with-output-simple-msg ()
        (princ " ")
        (dolist (demod demods)
          (print-next)
          (print-demodulator demod))))
    (format t "~% ~%")))

;;;
;;; for debug
;;;
(defun print-sos ()
  (dolist (cl *sos*)
    (print-next)
    (print-clause cl)))
(defun print-usable ()
  (dolist (cl *usable*)
    (print-next)
    (print-clause cl)))

(defun print-literal-entry (data)
  (dolist (ent data)
    (let ((atom (literal-entry-atom ent))
          (lit-cl (literal-clause (literal-entry-literal ent))))
      (princ "atom = ")
      (if (paramod-p atom)
          (princ atom)
        (term-print atom))
      (print-next)
      (princ "clause = ")
      (print-clause lit-cl)
      (print-next))))

(defun show-pos-literals ()
  (with-output-simple-msg ()
    (format t "** dump of *pos-literals*")
    (maphash #'(lambda (x y)
                 (print-next)
                 (format t "key=~s" x)
                 (print-next)
                 (format t "value=")
                 (print-next)
                 ;; (print-literal-entry y)
                 (write y :circle t :array t :pretty t)
                 (print-next)
                 (princ "---"))
             *pos-literals*)
    ))

(defun show-neg-literals ()
  (with-output-simple-msg ()
    (format t "** dump of *neg-literals*")
    (maphash #'(lambda (x y)
                 (print-next)
                 (format t "key=~s" x)
                 (print-next)
                 (format t "value=")
                 (print-next)
                 ;; (print-literal-entry y)
                 (write y :circle t :array t :pretty t)
                 (print-next)
                 (princ "---"))
             *neg-literals*)
    ))

(defun show-clash-pos-literals ()
  (with-output-simple-msg ()
    (format t "** dump of *clash-pos-literals*")
    (maphash #'(lambda (x y)
                 (print-next)
                 (format t "key=~s" x)
                 (print-next)
                 (format t "value=")
                 (print-next)
                 ;; (print-literal-entry y)
                 (write y :circle t :array t :pretty t)
                 (print-next)
                 (princ "---"))
             *clash-pos-literals*)
    ))

(defun show-clash-neg-literals ()
  (with-output-simple-msg ()
    (format t "** dump of *clash-neg-literals*")
    (maphash #'(lambda (x y)
                 (print-next)
                 (format t "key=~s" x)
                 (print-next)
                 (format t "value=")
                 (print-next)
                 ;; (print-literal-entry y)
                 (write y :circle t :array t :pretty t)
                 (print-next)
                 (princ "---"))
             *clash-neg-literals*)
    ))

(defun show-paramod-rules ()
  (with-output-simple-msg ()
    (format t "** dump of *paramod-rules*")
    (maphash #'(lambda (x y)
                 (print-next)
                 (format t "key=~s" x)
                 (print-next)
                 (format t "value=")
                 (print-next)
                 ;; (princ y)
                 (write y :circle t :array t :pretty t)
                 (print-next)
                 (princ "---"))
             *paramod-rules*)))

(defun show-full-lit-table ()
  (with-output-simple-msg ()
    (format t "** dump *full-lit-table*")
    (maphash #'(lambda (x y)
                 (print-next)
                 (format t "key=~s" x)
                 (print-next)
                 (princ "value= ")
                 (print-next)
                 (print-literal-entry y)
                 (print-next)
                 (princ "---"))
             *full-lit-table*)))

(defun show-demodulators (&optional (mod (or *current-module*
                                             *last-module*)))
  (unless mod (return-from show-demodulators nil))
  (with-in-module (mod)
    (let* ((psys (module-proof-system mod))
           (dmod-table (psystem-demodulators psys)))
      (format t "~%** demodulator table:")
      (maphash #'(lambda (x y)
                   (print-next)
                   (format t "key=~s" x)
                   (print-next)
                   (princ "value=")
                   (dolist (z y)
                     (print-next)
                     (print-demodulator z))
                   (print-next)
                   (princ "---"))
               dmod-table))))

;;; REPORT-CLOCK
;;;
(defun print-pn-times (&optional (stream *standard-output*))
  ;;
  (with-output-simple-msg (stream)
    (format t "** run times in seconds -------------------")
    (when (pn-flag binary-res)
      (print-next)
      (format t "binary-res~20t~,3f sec."
              (time-in-seconds (pn-clock-value binary-time))))
    (when (pn-flag hyper-res)
      (print-next)
      (format t "hyper-res-time~20t~,3f sec."
              (time-in-seconds (pn-clock-value hyper-time))))
    (when (pn-flag neg-hyper-res)
      (print-next)
      (format t "neg-hyper-res time~20t~,3f sec."
              (time-in-seconds (pn-clock-value neg-hyper-time))))
    (when (pn-flag para-into)
      (print-next)
      (format t "para-into time~20t~,3f sec."
              (time-in-seconds (pn-clock-value para-into-time))))
    (when (pn-flag para-from)
      (print-next)
      (format t "para-from time~20t~,3f sec."
              (time-in-seconds (pn-clock-value para-from-time))))
    (when (pn-flag back-unit-deletion)
      (print-next)
      (format t "back unit del time~20t~,3f sec."
              (time-in-seconds (pn-clock-value back-unit-del-time))))
    (print-next)
    (format t "pre process time~20t~,3f sec."
            (time-in-seconds (pn-clock-value pre-proc-time)))
    (print-next)
    (format t "  demod time ~20t~,3f sec."
            (time-in-seconds (pn-clock-value demod-time)))
    (print-next)
    (format t "  order equalities~20t~,3f sec."
            (time-in-seconds (pn-clock-value order-eq-time)))
    (print-next)
    (format t "  unit deletion~20t~,3f sec."
            (time-in-seconds (pn-clock-value unit-del-time)))
    (print-next)
    (format t "  factor simplify~20t~,3f sec."
            (time-in-seconds (pn-clock-value factor-simp-time)))
    ;;(format t "  wight cl time~20t,~3f sec."
    ;;	    (time-in-seconds (pn-clock-value weigh-cl-time)))
    ;; (format t "  sort lits time~20t~,3f sec."
    ;;	    (time-in-seconds (pn-clock-value sort-lits-time)))
    (print-next)
    (format t "  forward subsume~20t~,3f sec."
            (time-in-seconds (pn-clock-value for-sub-time)))
    (print-next)
    (format t "  delete cl time~20t~,3f sec."
            (time-in-seconds (pn-clock-value del-cl-time)))
    (print-next)
    (format t "  keep cl time~20t~,3f sec."
            (time-in-seconds (pn-clock-value keep-cl-time)))
    (print-next)
    (format t "  conflict time~20t~,3f sec."
            (time-in-seconds (pn-clock-value conflict-time)))
    (print-next)
    (format t "  new demod time~20t~,3f sec."
            (time-in-seconds (pn-clock-value new-demod-time)))
    (print-next)
    (format t "post process time~20t~,3f sec."
            (time-in-seconds (pn-clock-value post-proc-time)))
    (print-next)
    (format t "  back demod time~20t~,3f sec."
            (time-in-seconds (pn-clock-value back-demod-time)))
    (print-next)
    (format t "  back subsume time~20t~,3f sec."
            (time-in-seconds (pn-clock-value back-sub-time)))
    (print-next)
    (format t "  factor time ~20t~,3f sec."
            (time-in-seconds (pn-clock-value factor-time)))
    (print-next)
    (format t "print clause time~20t~3f sec."
            (time-in-seconds (pn-clock-value print-clause-time)))
    (print-next)
    ))

(defun print-pn-times-brief (&optional (stream *standard-output*))
  ;;
  (with-output-simple-msg (stream)
    (format t "** run times in seconds -------------------")
    (when (pn-flag binary-res)
      (print-next)
      (format t "binary-res~20t~,3f sec."
              (time-in-seconds (pn-clock-value binary-time))))
    (when (pn-flag hyper-res)
      (print-next)
      (format t "hyper-res-time~20t~,3f sec."
              (time-in-seconds (pn-clock-value hyper-time))))
    (when (pn-flag neg-hyper-res)
      (print-next)
      (format t "neg-hyper-res time~20t~,3f sec."
              (time-in-seconds (pn-clock-value neg-hyper-time))))
    (when (pn-flag para-into)
      (print-next)
      (format t "para-into time~20t~,3f sec."
              (time-in-seconds (pn-clock-value para-into-time))))
    (when (pn-flag para-from)
      (print-next)
      (format t "para-from time~20t~,3f sec."
              (time-in-seconds (pn-clock-value para-from-time))))
    (print-next)
    (format t "demod time ~20t~,3f sec."
            (time-in-seconds (pn-clock-value demod-time)))
    (print-next)
    (format t "forward subsume~20t~,3f sec."
            (time-in-seconds (pn-clock-value for-sub-time)))
    (print-next)
    (format t "back subsume time~20t~,3f sec."
            (time-in-seconds (pn-clock-value back-sub-time)))
    (print-next)
    (format t "print clause time~20t~3f sec."
            (time-in-seconds (pn-clock-value print-clause-time)))
    (print-next)
    ))

;;; for debug
(defun report-pn-memory ()
  (with-output-msg ()
    (princ "TABLES:")
    (print-next)
    (princ "*clause-hash") (prin1 *clause-hash*)
    (print-next)
    (princ "*pos-literals*") (prin1 *pos-literals*)
    (print-next)
    (princ "*neg-literals*")(prin1 *neg-literals*)
    (print-next)
    (princ "*clash-pos-literals*") (prin1 *clash-pos-literals*)
    (print-next)
    (princ "*clash-neg-literals*")(prin1 *clash-neg-literals*)
    (print-next)
    (princ "*paramod-rules*")(prin1 *paramod-rules*)
    (print-next)
    (princ "*full-lit-table*")(prin1 *full-lit-table*)
    (print-next)
    (princ "*demodulators*")(prin1 *demodulators*)
    ;; clause counters
    (print-next)
    (format t "- clauses generated so far ~s"
            (psystem-clause-counter *current-psys*))
    (print-next)
    (format t "- clauses deleted ~s" .pn-clause-deleted.)
    (print-next)
    (format t "- sos size = ~s" (length *sos*))
    (print-next)
    (format t "- usable size = ~s" (length *usable*))
    ))

(defparameter *import-fopl-ast*
    (%import* :protecting (%modexp* "FOPL-CLAUSE")))

(defun include-FOPL (&optional (module *current-module*))
  (when *include-fopl*
    (unless (assq *fopl-sentence-module*
                  (module-all-submodules module))
      (with-in-module (module)
        (eval-import-modexp *import-fopl-ast*))))
  )

;;; EOF
