;;;-*-Mode:LISP; Package: CHAOS; Base:10; Syntax:Common-lisp -*-
;;;
;;; Copyright (c) 2000-2014, Toshimi Sawada. All rights reserved.
;;;
;;; Redistribution and use in source and binary forms, with or without
;;; modification, are permitted provided that the following conditions
;;; are met:
;;;
;;;   * Redistributions of source code must retain the above copyright
;;;     notice, this list of conditions and the following disclaimer.
;;;
;;;   * Redistributions in binary form must reproduce the above
;;;     copyright notice, this list of conditions and the following
;;;     disclaimer in the documentation and/or other materials
;;;     provided with the distribution.
;;;
;;; THIS SOFTWARE IS PROVIDED BY THE AUTHOR 'AS IS' AND ANY EXPRESSED
;;; OR IMPLIED WARRANTIES, INCLUDING, BUT NOT LIMITED TO, THE IMPLIED
;;; WARRANTIES OF MERCHANTABILITY AND FITNESS FOR A PARTICULAR PURPOSE
;;; ARE DISCLAIMED.  IN NO EVENT SHALL THE AUTHOR BE LIABLE FOR ANY
;;; DIRECT, INDIRECT, INCIDENTAL, SPECIAL, EXEMPLARY, OR CONSEQUENTIAL
;;; DAMAGES (INCLUDING, BUT NOT LIMITED TO, PROCUREMENT OF SUBSTITUTE
;;; GOODS OR SERVICES; LOSS OF USE, DATA, OR PROFITS; OR BUSINESS
;;; INTERRUPTION) HOWEVER CAUSED AND ON ANY THEORY OF LIABILITY,
;;; WHETHER IN CONTRACT, STRICT LIABILITY, OR TORT (INCLUDING
;;; NEGLIGENCE OR OTHERWISE) ARISING IN ANY WAY OUT OF THE USE OF THIS
;;; SOFTWARE, EVEN IF ADVISED OF THE POSSIBILITY OF SUCH DAMAGE.
;;;
(in-package :chaos)
#|=============================================================================
                                    System:CHAOS
                                   Module:thstuff
                                File:bool-term.lisp
 =============================================================================|#
#-:chaos-debug
(declaim (optimize (speed 3) (safety 0) #-GCL (debug 0)))
#+:chaos-debug
(declaim (optimize (speed 1) (safety 3) #-GCL (debug 3)))

(defvar *debug-bterm* nil)
;;;=============================================================================
;;; Utilities to support investigating big boolean term of xor-and normal form.
;;;=============================================================================

;;; *********
;;; TERM HASH
;;; *********
(declaim (type fixnum bterm-hash-size))
(defconstant bterm-hash-size 1001)

(let ((.bterm-hash. nil)
      (bvar-num 0))
  (declare (type fixnum bvar-num))
  
  (defun clear-bterm-memo-table ()
    (dotimes (x bterm-hash-size)
      (setf (svref .bterm-hash. x) nil)))

  (defun bterm-hash ()
    .bterm-hash.)
  
  (defun bterm-hash-ref (index)
    (declare (type fixnum index))
    (svref .bterm-hash. index))

  (defun dump-bterm-hash ()
    (with-in-module ((get-context-module))
      (dotimes (x bterm-hash-size)
        (let ((ent (svref .bterm-hash. x)))
          (when ent
            (format t "~%(~d): " x)
            (let ((*print-indent* (+ *print-indent* 2)))
              (dolist (elt ent)
                (print-next)
                (term-print-with-sort (car elt))
                (princ " |-> ")
                (term-print-with-sort (cdr elt)))))))))

  (defun reset-bvar () 
    (setq bvar-num 0)
    (unless .bterm-hash.
      (setq .bterm-hash. (alloc-svec bterm-hash-size)))
    (clear-bterm-memo-table))

 (defun make-bterm-variable ()
   (let ((varname (intern (format nil "P-~d" (incf bvar-num)))))
     (make-variable-term *bool-sort* varname)))

  (defun get-hashed-bterm-variable (term)
    (let ((val (hash-term term))
          (var nil))
      (declare (type fixnum val))
      (let* ((ind (mod val bterm-hash-size))
             (ent (svref .bterm-hash. ind)))
        (setq var (cdr (assoc term ent :test #'term-is-similar?)))
        (if var
            var
          (progn
            (setf var (make-bterm-variable))
            (setf (svref .bterm-hash. ind) (cons (cons term var) ent))
            var)))))

  )

;;; =======================================================================
;;; ABSTRACTED representation of a _xor_-_and_ normal form of boolean term.

;;; ABS-BTERM:
;;; abstracted boolean term.
;;; each non _and_ or _xor_ boolean sub-term is abstracted by a
;;; variable. 
(defstruct (abst-bterm (:print-function print-abst-bterm))
                                        ; by variables
  (term nil)                            ; the original term
  (subst nil)                           ; list of substitution 
                                        ; or instance of abst-bterm(for _and_ abstraction)
  )

(defstruct (abst-and (:include abst-bterm)))

(defun print-abst-bterm (bt stream &rest ignore)
  (declare (ignore ignore))
  (with-in-module ((get-context-module))
    (princ ":abt[" stream)
    (let ((*print-indent* (+ 2 *print-indent*))
          (num 0))
      (declare (type fixnum *print-indent* num))
      (dolist (sub (abst-bterm-subst bt))
        (print-next nil *print-indent* stream)
        (format stream "(~d) " (incf num))
        (if (abst-bterm-p sub)
            (print-abst-bterm sub stream)
          (progn
            (let ((var (car sub))
                  (term (cdr sub)))
              (term-print-with-sort var)
              (princ " |-> ")
              (term-print-with-sort term))))))
    (princ " ]" stream)))

;;;
(defun find-bvar-subst (var bterm)
  (declare (type abst-bterm bterm))
  (dolist (sub (abst-bterm-subst bterm))
    (if (abst-bterm-p sub)
        (find-bvar-subst var sub)
      (when (variable= var (car sub))
        (return-from find-bvar-subst (cdr sub)))))
  nil)

;;;
;;; abstract-boolen-term : bool-term -> abst-bterm
;;; 

;;; xtract-xor-subterms : term
;;; returns ac subterms of the given term iff the top op is _xor_
(defun xtract-xor-subterms (term)
  (let ((args (if (method= (term-head term) *bool-xor*)
                  (list-ac-subterms term *bool-xor*)
                nil)))
    args))

;;; xtract-and-subterms : term
;;; returns ac subterms of the given term iff the top op is _and_
(defun xtract-and-subterms (term)
  (if (method= (term-head term) *bool-and*)
      (list-ac-subterms term *bool-and*)
    nil))

(defun make-and-abstraction (term subterms)
  (let ((subst nil))
    (dolist (sub subterms)
      (push (cons (get-hashed-bterm-variable sub) sub) subst))
    (make-abst-and :term term :subst (nreverse subst))))

(defun abstract-boolean-term (term)
  (let ((bterm (make-abst-bterm :term term))
        (xor-subs (xtract-xor-subterms term))
        (subst nil))
    ;; reset variable number & term hash
    (reset-bvar)
    (if xor-subs
        ;; top operator is _xor_
        ;; we further decompose by _and_
        (dolist (xs xor-subs)
          (let ((as (xtract-and-subterms xs)))
            (if as 
                (push (make-and-abstraction xs as) subst)
              (push (cons (get-hashed-bterm-variable xs) xs) subst))))
      ;; top operator is not xor
      (let ((as (xtract-and-subterms term)))
        (when as
          (push (make-and-abstraction term as) subst))))
    (setf (abst-bterm-subst bterm) (nreverse subst))
    bterm))

;;;
;;; make-bterm-representation : bterm -> boolen term
;;; from bterm make a concrete representation of abstracted boolean term
;;;
(defun make-and-representation (abst-and)
  (declare (type abst-and abst-and))
  (let ((repre (make-right-assoc-normal-form *bool-and*
                                             (mapcar #'car (abst-and-subst abst-and)))))
    (update-lowest-parse repre)
    repre))

(defun make-xor-representation (bterm)
  (declare (type abst-bterm bterm))
  (let ((repre (make-right-assoc-normal-form *bool-xor*
                                             (mapcar #'(lambda (x) (if (abst-and-p x)
                                                                       (make-and-representation x)
                                                                     (car x)))
                                                     (abst-bterm-subst bterm)))))
    (update-lowest-parse repre)
    repre))

(defun make-bterm-representation (bterm)
  (let ((subst (abst-bterm-subst bterm)))
    ;; no _xor nor _and_ ops in original term
    (unless subst
      (return-from make-bterm-representation (abst-bterm-term bterm)))
    ;; sole _and_ term.
    (when (and (null (cdr subst))
               (abst-and-p (car subst)))
      (return-from make-bterm-representation (make-and-representation (car subst))))
    ;; _xor_ normal form
    (make-xor-representation bterm)))

;;; ===========================================================================================
;;; PRINTERS
;;; abst-bterm printers

;;; simple-print-bterm : bterm -> void
(defun simple-print-bterm (bterm)
  (declare (type abst-bterm bterm))
  (let ((aterm (make-bterm-representation bterm)))
    (term-print-with-sort aterm)))

;;; print-bterm-tree : bterm -> void
(defun print-bterm-tree (bterm &optional (mode :vertical))
  (declare (type abst-bterm bterm)
           (ignore mode))               ; for NOW ** TODO for :vertical
  (let ((aterm (make-bterm-representation bterm)))
    (print-term-graph aterm *chaos-verbose*)))

;;; print-abs-bterm : bterm &key mode
;;; mode :simple print term representation
;;;      :tree   print term representation as vertical tree structure
;;;      :horizontal print term representation horizontal tree structure
;;; also shows a substitution used for abstruction.
;;;
(defun print-abs-bterm (bterm &key (mode :simple))
  (case mode
    (:simple (simple-print-bterm bterm))
    (:tree   (print-bterm-tree bterm))
    (:horizontal (print-bterm-tree bterm :horizontal))
    (otherwise
     (with-output-chaos-error ('invalid-mode)
       (format t "Invalid print mode ~a." mode))))
  ;; shows substitution
  (format t "~%, where")
  (dolist (subst (abst-bterm-subst bterm))
    (format t "~%~4T~A |-> " (variable-name (car subst)))
    (term-print-with-sort (cdr subst)))
  )

;;; ===========================================================================================
;;; RESOLVER
;;; computes possible solutions (assignments) which makes abstracted boolean term to be 'true.'
;;;

;;; assign-tf 
;;; make all posssible variable substitutions with the domain {'true' ,'false'}.
;;;
(defun make-tf-combination (rows columns)
  (let ((assignment nil)
        (subst (make-array (list rows columns))))
    (flet ((change-parity ()
             (if (is-true? assignment)
                 (setq assignment *bool-false*)
               (setq assignment *bool-true*))))
      (dotimes (c columns)
        (setq assignment nil)
        (let ((cycle (expt 2 c)))
          (dotimes (r rows)
            (if (not assignment)
                (setq assignment *bool-true*)
              (if (= 0 (mod r cycle))
                  (change-parity)))
            #||
            (when *debug-bterm*
              (format t "~%cycle=~d, columns=~d, row=~d: ~s" cycle c r (if (is-true? assignment)
                                                                           "true"
                                                                         "false")))
            ||#
            (setf (aref subst r c) assignment))))
      subst)))

(defun assign-tf (list-vars)
  (let* ((columns (length list-vars))
         (rows (expt 2 columns))
         (assignments (make-tf-combination rows columns))
         (l-subst nil))
    (dotimes (r rows)
      (let ((subst nil))
        (dotimes (c columns)
          (push (cons (nth c list-vars) (aref assignments r c)) subst))
        (push (nreverse subst) l-subst)))
    (when *debug-bterm*
      (with-in-module ((get-context-module))
        (let ((num 0))
          (dolist (sub (reverse l-subst))
            (format t "~%(~d): " (incf num))
            (print-substitution sub)))))
    (nreverse l-subst)))

;;;
;;; resolve-abst-bterm : bterm
;;; retuns a list of substitution which makes bterm to be true.
;;;
(defun resolve-abst-bterm (bterm &optional (module (get-context-module)))
  (declare (type abst-bterm bterm))
  (let* ((abst-term (make-bterm-representation bterm))
         (variables (term-variables abst-term))
         (list-subst (assign-tf variables))
         (answers nil))
    (dolist (subst list-subst)
      (let ((target (substitution-image-cp subst abst-term)))
        (reset-reduced-flag target)
        (when *debug-bterm*
          (with-in-module ((get-context-module))
            (format t "~%[resolver_target] ")
            (term-print-with-sort target)
            (print-next)
            (format t "~% mod = ~a" *current-module*)
            (print-next)
            (print-method-brief (term-head target))
            (print-next)
            (format t " str: ~a" (method-rewrite-strategy (term-head target)))))
        (setq target (reducer-no-stat target module :red))
        (when *debug-bterm*
          (with-in-module ((get-context-module))
            (format t "~% --> ")
            (term-print-with-sort $$term)))
        (when (is-true? $$term)
          (push subst answers))))
    answers))

;;; try-resolve-boolean-term : term -> Values (abst-bterm List(substitution))
;;;
(defvar *abst-bterm* nil)
(defvar *abst-bterm-representation* nil)

(defun try-resolve-boolean-term (term module)
  (unless (sort= (term-sort term) *bool-sort*)
    (with-output-chaos-warning ()
      (format t "Given term is not of sort Bool. Ignored.")
      (return-from try-resolve-boolean-term nil)))
  (!setup-reduction module)
  (with-in-module (module)
    (reset-reduced-flag term)
    (let ((target (reducer-no-stat term module :red)))
      ;; abstract
      (let ((bterm (abstract-boolean-term target)))
        (setq *abst-bterm* bterm)
        (setq *abst-bterm-representation*
          (make-bterm-representation bterm))
        (let ((*print-indent* (+ 2 *print-indent*)))
          (format t "~%** Abstracted boolean term:")
          (with-in-module (module)
            (print-next)
            (term-print-with-sort *abst-bterm-representation*)
            (print-term-graph *abst-bterm-representation* *chaos-verbose*)
            (format t "~%  where")
            (let ((*print-indent* (+ 2 *print-indent*)))
              (dolist (var (term-variables *abst-bterm-representation*))
                (let ((mapping (find-bvar-subst var bterm)))
                  (unless mapping
                    (with-output-chaos-error ('internal-err)
                      (format t "Could not find the mapping of variable ~a." (variable-name var))))
                  (print-next)
                  (term-print-with-sort var)
                  (princ " |-> ")
                  (term-print-with-sort mapping))))
            ;; find answers
            (let ((ans (resolve-abst-bterm bterm module)))
              (cond (ans
                     (format t "~%** The following assignment(s) can make the term 'true'.")
                     (let ((num 0))
                       (declare (type fixnum num))
                       (let ((*print-indent* (+ 2 *print-indent*)))
                         (dolist (sub ans)
                           (print-next)
                           (format t "(~d): " (incf num))
                           (print-substitution sub)))))
                    (t
                     (format t "~%** No solution was found.")))
              (values bterm ans))))))))

;;;
(defun binspect-in-goal (goal-name preterm)
  (let* ((goal-node (get-target-goal-node goal-name))
         (context-module (goal-context (ptree-node-goal goal-node)))
         (target (do-parse-term* preterm context-module)))
    (try-resolve-boolean-term target context-module)))

(defun binspect-in-module (mod-name preterm)
  (multiple-value-bind (target context-module)
      (do-parse-term* preterm mod-name)
    (try-resolve-boolean-term target context-module)))

;;; TOP LEVEL FUNCTION
;;; binspect-in
(defun binspect-in (mode goal-or-module-name preterm)
  (cond ((eq mode :citp)
         (binspect-in-goal goal-or-module-name preterm))
        (t 
         (binspect-in-module goal-or-module-name preterm))))

;;; EOF
