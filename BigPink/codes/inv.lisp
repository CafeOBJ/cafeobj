;;;-*-Mode:LISP; Package: CHAOS; Base:10; Syntax:Common-lisp -*-
;;;
;;; Copyright (c) 2000-2015, Toshimi Sawada. All rights reserved.
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
;;;
(in-package :chaos)
#|=============================================================================
                            System:Chaos
                          Module:BigPink
                           File:inv.lisp
=============================================================================|#
#-:chaos-debug
(declaim (optimize (speed 3) (safety 0) #-GCL (debug 0)))
#+:chaos-debug
(declaim (optimize (speed 1) (safety 3) #-GCL (debug 3)))

;;;
;;; Automatic Checking of Invariance of Predicate on Object.
;;;

;;; if no-nil, we are called with `check safety ...'
(declaim (special .pn-check-safety.))
(defvar .pn-check-safety. nil)

;;; INV-CHECK-SYSTEM
;;;
(defstruct (inv-check-system)
  (module nil :type (or null module))   ; context module
  (sort nil :type (or null sort*))      ; sort of object
  (predicate nil :type (or null method)) ; predicate representing invariance
  (initial-state nil :type (or null term)) ; initial state constant term
  (object nil :type term)               ; term representing target object
  (methods nil :type list)              ; methods w.r.t. hidden sort
  (goals nil :type list)                ; goals to be proved
  (conditions nil :type list)           ; filed goals
  (after-loop 0 :type fixnum)           ; loop start point
  (after-num  0 :type fixnum))

(defun pn-get-meth-unique (module opname)
  (declare (type module module)
           (type list opname)
           (values method))
  (with-in-module (module)
    (let* ((parsedop (parse-op-name opname))
           (ops (find-qual-operators parsedop module))
           (op nil))
      (unless ops
        (with-output-chaos-error ('no-op)
          (format t "no such operator with name ~s" opname)))
      (when (cdr ops)
        (with-output-chaos-error ('amb-op)
          (format t "more than one operators with name ~s" opname)))
      ;;
      (dolist (meth (opinfo-methods (car ops)))
        (unless (method-is-error-method meth)
          (setq op meth)
          (return)))
      op)))

(defun make-term-pat (method)
  (declare (type method method))
  (make-term-with-sort-check method
                             (mapcar #'(lambda (x)
                                         (make-variable-term x
                                                             (gensym "_V")))
                                     (method-arity method))))

(defun make-inv-check-context (methods hole target-pattern)
  (let ((res nil))
    (dolist (method methods)
      (let ((kernel-pat nil))
        (setq kernel-pat
          (make-term-with-sort-check
           method
           (mapcar #'(lambda (x)
                       (if (not (sort-is-hidden x))
                           (make-variable-term x
                                               (gensym "_V"))
                         (progn
                           (unless (sort= x (term-sort target-pattern))
                             (with-output-chaos-error ('no-sort-match)
                               (princ "unmatched hidden sorts")
                               ))
                           hole)))
                   (method-arity method))))
        (push
         (if (term-is-variable? target-pattern)
             kernel-pat
           (apply-subst (list (cons hole kernel-pat)) target-pattern))
         res)))
    ;;
    (when (pn-flag debug-inv-check)
      (with-output-simple-msg ()
        (format t "** check contexts:")
        (dolist (tp res)
          (print-next)
          (term-print tp))))
    ;;
    res))
    
(defun make-inv-check-contexts (methods hole target-patterns)
  (let ((res nil))
    (dolist (tpat target-patterns)
      (setq res
        (nconc res
               (make-inv-check-context methods hole tpat))))
    res))

(defun pn-expand-macro (term module)
  (if (module-macros module)
      (let ((pat-string 
             (with-output-to-string (stream)
               (let ((*print-with-sort* t))
                 (term-print term stream)))))
        (simple-parse-from-string pat-string))
    term))  

(defun make-pn-inv-check-pat (predicate
                              target-pat
                              &key (make-condition nil)
                                   (print-msg *error-output*)
                                   (make-imply nil))
  (let ((hole nil)
        (hypo-pat nil)
        (hole-subst nil)
        ;; (method-pat nil)
        (conc-pat nil)
        (check-pat nil)
        )
    ;;
    (setq hypo-pat
      (make-term-with-sort-check predicate
                                 (mapcar #'(lambda (x)
                                             (let ((var (make-variable-term
                                                         x
                                                         (gensym "_V"))))
                                               (when (sort-is-hidden x)
                                                 (push var hole))
                                               (if make-imply
                                                   make-imply
                                                 var)))
                                         (method-arity predicate))))
    (when (cdr hole)
      (with-output-chaos-error ('too-many-holes)
        (princ "predicate pattern has too many hidden context")))
    (setq hole
      (if make-imply
          make-imply
        (car hole)))
    (setq hole-subst (list (cons hole target-pat)))
    (setq conc-pat (apply-subst hole-subst hypo-pat))

    ;; make check pattern
    (if make-imply
        (setq check-pat
          (make-term-with-sort-check
           *fopl-imply*
           (list hypo-pat conc-pat)))
      (setq check-pat conc-pat)
      )
    ;; bound free variables
    (normalize-quantifiers check-pat)
    ;;
    (when print-msg
      (let ((*print-indent* 7))
        (if (stringp print-msg)
            (setq print-msg
              (with-output-to-string (stream)
                (if make-condition
                    (format stream "~%~a: " make-condition)
                  (format stream "~%goal: "))
                (term-print check-pat stream)))
          (progn
            (if make-condition
                (format print-msg "~%~a: " make-condition)
              (format print-msg "~%goal: "))
            (term-print check-pat print-msg)))))
    
    ;; negate
    (unless make-condition
      (setq check-pat
        (make-term-with-sort-check *fopl-neg*
                                   (list check-pat))))
    ;; expand macro
    (setq check-pat (pn-expand-macro check-pat *current-module*))

    ;; translate to clause form
    ;; (formula->clause-1 check-pat (module-proof-system *current-module*))
    (values check-pat print-msg)
    ))

(defun cl-member-test (c1 c2)
  (eq (clause-axiom c1)
      (clause-axiom c2)))

(defun setup-inv-check-db (module goal preset-sos preset-passive)
  (when (or (pn-flag auto)
            (pn-flag auto1)
            (pn-flag auto2)
            (pn-flag auto3))
    ;; in auto mode, 
    ;; essentially we need not do anything,
    ;; but make sure to force `db-reset', because new axioms
    ;; are added implicitly.
    (let ((psys nil))
      (clear-all-index-tables)
      (reset-module-proof-system module)
      (setq psys (module-proof-system module))
      (setf (psystem-passive psys) preset-passive)
      (return-from setup-inv-check-db nil)))
  ;;
  ;; manual mode
  ;;
  ;; implicitly perform db reset.
  (let ((psys nil))
    (clear-all-index-tables)
    (reset-module-proof-system module)
    (setq psys (module-proof-system module))
    ;; (setf (psystem-sos psys) preset-sos)
    ;; (setf (psystem-passive psys) preset-passive)
    ;; reset SOS
    (let ((sos nil)
          (usable nil)
          (passive nil)
          (sos-pre? preset-sos)
          ;; (passive-pre? preset-passive)
          (put-goal-in-sos? nil))
      (when (memq :system-goal preset-sos)
        (setq preset-sos (delete :system-goal preset-sos :test #'eq))
        (setq put-goal-in-sos? t))
      (dolist (cl (psystem-axioms psys))
        (cond ((eq (clause-axiom cl) goal)
               ;; generated goal
               (if put-goal-in-sos?
                   (progn
                     (setf (clause-container cl) :sos)
                     (push cl sos))
                 ;; put the goal into usable
                 (progn
                   (setf (clause-container cl) :usable)
                   (push cl usable)))
               )
              ;; the following cases treat non-goal
              (sos-pre?
               (if (member cl preset-sos :test #'cl-member-test)
                   (progn
                     (setf (clause-container cl) :sos)
                     (push cl sos))
                 (if (member cl preset-passive :test #'cl-member-test)
                     (progn
                       (setf (clause-container cl) :passive)
                       (push cl passive))
                   (progn
                     (setf (clause-container cl) :usable)
                     (push cl usable)))))
              (t
               (if (member cl preset-passive :test #'cl-member-test)
                   (progn
                     (setf (clause-container cl) :passive)
                     (push cl passive))
                 (if (positive-clause? cl)
                     (progn
                       (setf (clause-container cl) :sos)
                       (push cl sos))
                   (progn
                     (setf (clause-container cl) :usable)
                     (push cl usable)))))))
      ;;
      (setf (psystem-sos psys) (reverse sos))
      (setf (psystem-passive psys) (reverse passive))
      (setf (psystem-usable psys) (reverse usable))
      )
    ))

;;; PERFORM-INV-CHECK
;;; prepare run-time env of PigNose and invoke it.
;;;
(defun perform-inv-check (module
                          predicate
                          target-pat
                          conditions
                          additional-conds
                          &key dont-negate
                               type
                               hole)
  (declare (type module module)
           (type method predicate)
           (type term target-pat)
           (type list conditions)
           (values symbol))
  (let ((ret-code nil)
        (preset-sos nil)
        (preset-passive nil)
        (*pn-no-db-reset* t)
        )
    (declare (special *pn-no-db-reset*))
    (when (module-proof-system module)
      (setq preset-sos (psystem-sos (module-proof-system module)))
      (setq preset-passive (psystem-passive (module-proof-system module)))
      )
    (initialize-module *pn-proof-module*)
    (import-module *pn-proof-module* :protecting module)
    (prepare-for-parsing *pn-proof-module*)
    (setf (module-op-lex *pn-proof-module*) (module-op-lex module))
    (with-in-module (*pn-proof-module*)
      (let ((inv-check-pat nil)
            (goal nil)
            (ax nil)
            (flags (save-pn-flags))
            (parameters (save-pn-parameters)))
        ;; make goal
        (setq inv-check-pat
          (make-pn-inv-check-pat predicate
                                 target-pat
                                 :make-condition dont-negate
                                 :make-imply (if (and (eq type :from)
                                                      hole)
                                                 hole
                                               nil)))
        (setq goal
          (make-rule :lhs inv-check-pat
                     :rhs *bool-true*
                     :condition *bool-true*
                     :labels nil
                     :behavioural nil
                     :type :pignose-axiom))

        ;; NOTE: we may need ......................
        ;; the goal is added as an axiom.
        (check-axiom-error-method *current-module*
                                  goal
                                  t)
        (add-axiom-to-module *current-module* goal)
        
        ;; pre conditions
        (dolist (a (append conditions additional-conds))
          (setq ax
            (make-rule :lhs a
                       :rhs *bool-true*
                       :condition *bool-true*
                       :labels nil
                       :behavioural nil
                       :type :pignose-axiom))
          (check-axiom-error-method *current-module*
                                    ax
                                    t)
          (add-axiom-to-module *current-module* ax))

        ;;
        (set-needs-rule)
        (compile-module *current-module*)
        ;;
        ;; invoke PigNose //////
        ;;               ......
        (unless (or (pn-flag auto)
                    (pn-flag auto2)
                    (pn-flag auto3)
                    (pn-flag binary-res)
                    (pn-flag hyper-res)
                    (pn-flag neg-hyper-res)
                    (pn-flag para-from)
                    (pn-flag para-into)
                    (pn-flag demod-inf))
          (with-output-simple-msg ()
            (princ "** NO inference rules are specified.")
            (print-next)
            (princ "system will use `auto' mode."))
          (setq preset-sos nil)
          ;; (setq preset-passive nil)
          (auto-change-flag auto t)
          (auto-change-flag universal-symmetry t))
        ;; only interest the first proof
        (setf (pn-parameter max-proofs) 1)
        ;; 
        (setup-inv-check-db *current-module* goal preset-sos preset-passive)
        ;; do resolve
        (setq ret-code (do-resolve *current-module*))
        ;; restore flags&parameters
        (restore-pn-flags flags)
        (restore-pn-parameters parameters)
        ))
    ;;
    ret-code ))


;;; DO-INVARIANCE-CHECK
;;; the working horse of invariance check.
;;;
(defun do-invariance-check (check-sys type)
  (let ((module (inv-check-system-module check-sys))
        (pred (inv-check-system-predicate check-sys))
        (init-state (inv-check-system-initial-state check-sys))
        (object (inv-check-system-object check-sys))
        (sort (inv-check-system-sort check-sys))
        (success nil)
        (skip-l (inv-check-system-after-loop check-sys))
        (skip-num (inv-check-system-after-num check-sys)))
    (with-in-module (module)
      (case type
        ((:from :of)
         (let* ((ret-code nil)
                (loops -1)
                (max-loops (pn-parameter inv-check-max-depth))
                (target-patterns nil)
                (fail nil)
                (next-goals nil)
                (failed-goals nil)
                (hole (make-variable-term sort
                                          (gensym "_hole")))
                (subst-pat (list
                            (cons hole
                                  (or object init-state))))
                
                (do-skip nil)
                )
           ;; set initial target pattern:
           ;; hole will be substituted by real target.
           (setf (inv-check-system-goals check-sys)
             (list hole))
           ;;
           (catch 'inv-check-fail
             (loop
               (setq target-patterns (inv-check-system-goals check-sys))
               (unless target-patterns
                 ;; we've done without failure.
                 (setq success t)
                 (return))
               ;; check depth limit
               (incf loops)
               (when (and (not (= -1 max-loops))
                          (> loops max-loops))
                 (with-output-msg ()
                   (format t "stopping invariance check due to `inv-check-max-depth'")
                   (return nil)))
               ;;
               (let ((num 0)            ; case # of current depth (loops).
                     (cur-conditions nil)
                     (cur-cond nil))
                 ;; initialy, cur-conditions contains all of the goals
                 ;; to be checked for the current depth.
                 (setq cur-conditions
                   (mapcar #'(lambda (x)
                               (apply-subst subst-pat x))
                           target-patterns))
                 (do* ((targets target-patterns (cdr targets))
                       (target-pat (car targets) (car targets))
                       (reals cur-conditions (cdr reals))
                       (real-target (car reals) (car reals))
                       (hypo-str nil nil))
                     ((endp targets))
                   ;; all not-yet tested goals are used for additional
                   ;; hypothesis of the current goal,i.e. real-target.
                   (setq cur-conditions (remove real-target cur-conditions))
                   (setq cur-cond
                     (mapcar #'(lambda (x)
                                 (multiple-value-bind (pat pat-str)
                                     (make-pn-inv-check-pat pred
                                                            x
                                                            :make-condition "hypo"
                                                            :print-msg ""
                                                            :make-imply nil)
                                   (push pat-str hypo-str)
                                   pat))
                             cur-conditions))
                   ;; print start message
                   (let ((*standard-output* *error-output*))
                     (format t "~%==========")
                     (format t "~%case #~d-~d: " loops (incf num))
                     (term-print real-target)
                     (format t "~%----------")
                     ;;
                     #||
                     (with-output-simple-msg ()
                       (format t "loops=~a, num=~a, skip-l=~a, skip-num=~a"
                               loops num skip-l skip-num))
                     ||#
                     ;;
                     (if (or (< loops skip-l)
                             (and (= loops skip-l)
                                  (< num skip-num)))
                         (with-output-simple-msg ()
                           (format t "** will skip real proof")
                           (setq do-skip t))
                       (setq do-skip nil))
                     
                     #||
                     (dolist (c cur-conditions)
                       (terpri)
                       (princ "hypo: ")
                       (let ((*print-indent* 7))
                         (term-print c)))
                     ||#
                     (dolist (pst (reverse hypo-str))
                       (princ pst))
                     )
                   ;; do the check
                   (setq ret-code
                     (if do-skip
                         :skip-exit
                       (perform-inv-check module
                                          pred
                                          real-target
                                          ;; previous
                                          (inv-check-system-conditions check-sys)
                                          ;; current
                                          cur-cond
                                          :hole hole
                                          :type (if (zerop loops)
                                                    :of
                                                  type)))
                     )
                   
                   ;;
                   (when (eq type :from)
                     (setq subst-pat nil))
                   ;;
                   (let ((*standard-output* *error-output*))
                     (if (eq ret-code :max-proofs-exit)
                         ;; success
                         (progn
                           (when (zerop loops)
                             (push (if (eq type :from)
                                       (make-variable-term sort (gensym "_KV"))
                                     target-pat)
                                   next-goals))
                           (format t "~%** success"))
                       ;; fail
                       (progn
                         (if do-skip
                             (format t "~%** SKIPPING...")
                           (format t "~%** fail"))
                         (setq fail t)
                         ;; reachability check from intial state
                         (when (and init-state
                                    (eq type :of)
                                    (or (not do-skip)
                                        (pn-flag check-init-always)))
                           (let ((target (apply-subst (list (cons hole init-state))
                                                      target-pat)))
                             (terpri)
                             (princ "** check with the initial state : ")
                             (term-print target)
                             (setq ret-code
                               (perform-inv-check module
                                                  pred
                                                  target
                                                  (inv-check-system-conditions
                                                   check-sys)
                                                  cur-cond
                                                  :type type))
                             (unless (eq :max-proofs-exit ret-code)
                               (with-output-simple-msg ()
                                 (princ "** fail!")
                                 (print-next)
                                 (princ "trying to find a counter example: "))
                               ;;
                               (setq ret-code
                                 (perform-inv-check module
                                                    pred
                                                    target
                                                    (inv-check-system-conditions
                                                     check-sys)
                                                    cur-cond
                                                    :type type
                                                    :dont-negate "ax")
                                 )
                               (when (eq :max-proofs-exit ret-code)
                                 (with-output-simple-msg ()
                                   (princ "** found a counter example!")
                                   (print-next)
                                   (princ "initial state can reach to a hazardous state.")
                                   ))
                               (setq success nil)
                               (throw 'inv-check-fail nil)
                               )
                             (with-output-simple-msg ()
                               (princ "** ok, it's safe."))
                             ))
                         
                         ;; next-goals accumurates base context patterns
                         ;; for generating goals of the next loop (depth).
                         (push target-pat next-goals)
                         ;; put the failed goal back to condition
                         ;; this will be used as hyphthesis of the
                         ;; next goal (sibling).
                         (push real-target cur-conditions)
                         )
                       ))
                   )
                 ;; end for all current target,i.e., the current depth.
                 (if (or fail (zerop loops))
                     ;; found at least one failure case, or we've just done
                     ;; for initial base case.
                     (progn
                       (setq next-goals (nreverse next-goals))
                       (setq failed-goals (nconc failed-goals next-goals))
                       (setf (inv-check-system-goals check-sys)
                         (make-inv-check-contexts (inv-check-system-methods
                                                   check-sys)
                                                  hole
                                                  next-goals))
                       (setf (inv-check-system-conditions check-sys)
                         (nconc (inv-check-system-conditions check-sys)
                                (mapcar
                                 #'(lambda (x)
                                     (make-pn-inv-check-pat pred
                                                            x
                                                            :make-condition
                                                            "adding axiom"
                                                            :print-msg *error-output*
                                                            :make-imply nil))
                                 cur-conditions)))
                       )
                   ;; success
                   (setf (inv-check-system-goals check-sys) nil))
                 ;;
                 (setq next-goals nil)
                 )                      ; done for this level
               ;;
               )                        ; done for all
             )
           ;;
           #||
           (when (and success (eq type :of) init-state)
             ;; we must check reachability 
             (setq success nil)
             (let ((*standard-output* *error-output*))
               (format t "~%==============================")
               (format t "~%** start reachability check **")
               (format t "~%------------------------------"))
             (dolist (pat failed-goals (setq success t))
               (let ((target (apply-subst (list (cons hole init-state))
                                          pat)))
                 (setq ret-code
                   (perform-inv-check module
                                      pred
                                      target
                                      (inv-check-system-conditions check-sys)
                                      nil))
                 (let ((*standard-output* *error-output*))
                   (if (eq ret-code :max-proofs-exit)
                       (format t "~%*** success")
                     (progn
                       (format t "~%** fail")
                       (return nil))))))
             )
           ||#
           ;;
           (unless success
             (if .pn-check-safety.
                 (format *error-output*
                         "~%** Failed to prove safety of ~{~a~}.~% ~%"
                         (method-symbol pred))
               (format *error-output*
                       "~%** Failed to prove ~{~a~} is invariant.~% ~%"
                       (method-symbol pred)))
             (return-from do-invariance-check nil))
           ;; success!!
           (if .pn-check-safety.
               (format *error-output*
                       "~%** Predicate ~{~a~} is safe!!~% ~%"
                       (method-symbol pred))
             (format *error-output*
                     "~%** Predicate ~{~a~} is invriant!!~% ~%"
                     (method-symbol pred)))
           t
           ))
        ;;
        (otherwise
         ;; TODO
         )
        )
      )
    ))

;;; PN-CHECK-INVARIANCE : InputArgs -> Void
;;; args ::= '( op ["of" term] [{"from"|"with"} op] [ "after" <num>])'

(defun parse-pn-check-command (args)
  (declare (type list args))
  (let ((pred-name nil)
        (type nil)
        (init-name nil)
        (object-pat nil)
        (loop-after 0)
        (loop-after-sub 0)
        (args-list args)
        (e nil))
    ;; get predicate-name
    (loop
      (unless args-list (return nil))
      (setq e (pop args-list))
      (when (member e '("of" "from" "with" "after"
                        ":of" ":from" ":with" ":after")
                    :test #'equal)
        (return nil))
      (push e pred-name))
    ;; get object pattern if any
    (when (member e '("of" ":of") :test #'equal)
      (setq type :of)
      (loop
        (unless args-list (return nil))
        (setq e (pop args-list))
        (when (member e '("from" "with" "after"
                          ":from" ":with" ":after")
                      :test #'equal)
          (return nil))
        (push e object-pat)))
    ;; get initial pattern or target pattern if any.
    (unless type
      (when (member e '("from" ":from") :test #'equal)
        (setq type :from))
      (when (member e '("with" ":with") :test #'equal)
        (setq type :with)))
    (when (member e '(":from" ":with" "from" "with")
                  :test #'equal)
      (loop
        (unless args-list (return nil))
        (setq e (pop args-list))
        (when (member e '("after" ":after") :test #'equal)
          (return nil))
        (push e init-name)))
    (when (member e '("after" ":after") :test #'equal)
      (let ((pos 0))
        (setq e (pop args-list))
        (multiple-value-setq (loop-after pos)
          (parse-integer e :junk-allowed t))
        (unless (integerp loop-after)
          (with-output-chaos-error ('invalid-arg)
            (format t "invalid `after' agument : ~s" e)))
        (if (and (< pos (length e)))
            (progn
              (setq e (subseq e (1+ pos)))
              (setq loop-after-sub (read-from-string e))
              (unless (integerp loop-after-sub)
                (format t "invalid `after' argument : ~s" e)))
          (setq loop-after-sub 1))
        ))
    (values (nreverse pred-name)
            (nreverse object-pat)
            (nreverse init-name)
            loop-after
            loop-after-sub
            type)
    ))

    
(defun pn-check-invariance (args)
  (declare (type list args))
  (let ((target-module (get-context-module)))
    (declare (type module target-module))
    (compile-module target-module)
    (multiple-value-bind (pred-name object-pat init-name loop-after
                          loop-after-sub
                          type)
        (parse-pn-check-command args)
      (unless (and pred-name type (or init-name object-pat))
        (with-output-chaos-error ('invalid-args)
          (format t "insufficient args for check : ~{~s~}" args)))
      (let ((predicate (pn-get-meth-unique target-module
                                           pred-name))
            (init-method (if init-name
                             (pn-get-meth-unique target-module
                                                 init-name)
                           nil))
            (object (if object-pat
                        (simple-parse target-module object-pat)
                      nil))
            (hsort nil)
            (check-sys nil))
        (declare (type fixnum loop-after loop-after-sub))
        ;;
        (unless (sort= (method-coarity predicate)
                       *bool-sort*)
          (with-output-chaos-error ('invalid-op)
            (princ "operator is not a predicate:")
            (print-chaos-object predicate)))
        (when init-method
          (unless (sort-is-hidden (method-coarity init-method))
            (with-output-chaos-error ('ivalid-op)
              (princ "the value of operator ")
              (print-chaos-object init-method)
              (print-next)
              (princ "is not hidden sort, only hidden valued oprators are meaningful.")
              )))
        ;;
        (when (and object (term-ill-defined object))
          (return-from pn-check-invariance nil))
        ;;
        (when init-method
          (unless (member (method-coarity init-method)
                          (method-arity predicate))
            (with-output-chaos-error ('invalid-op)
              (princ "given predicate and operator don't match."))))
        ;;
        (when (and init-method object)
          (unless (eq (method-coarity init-method)
                      (method-coarity (term-head object)))
            (with-output-chaos-error ('invalid-pat)
              (princ "given pattern does not match with init value.")
              (print-next)
              (princ "init value : ")(print-chaos-object init-method)
              (print-next)
              (princ "pattern    : ")(term-print object))))
        ;;
        (setq hsort
          (if init-method
              (method-coarity init-method)
            (method-coarity (term-head object))))
        ;;
        ;; prepare initial inv-check-system
        ;;
        (setq check-sys
          (make-inv-check-system 
           :module target-module
           :sort hsort
           :predicate predicate
           :initial-state (if init-method
                              (make-term-pat init-method)
                            nil)
           :object object
           :after-loop loop-after
           :after-num loop-after-sub))
        ;;
        (setf (inv-check-system-methods check-sys)
          (nreverse
           (remove-if-not #'(lambda (x)
                              (sort= hsort (method-coarity x)))
                          (module-beh-methods target-module))))
        ;;
        ;; do check
        ;;
        (let ((start-time (get-internal-real-time))
              (grand-total ""))
          (declare (type integer start-time)
                   (type simple-string grand-total))
          ;;
          (do-invariance-check check-sys type)
          ;;
          (setq grand-total
            (format nil "~,3f sec"
                    (elapsed-time-in-seconds start-time
                                             (get-internal-real-time))))
          (unless *chaos-quiet*
            (when (pn-flag print-stats)
              (with-output-simple-msg ()
                (format t "(grand total time ~a)" grand-total)))))))))

;;; PN-CHECK-SAFETY
;;;
(defun pn-check-safety (args)
  (declare (type list args))
  (let ((.pn-check-safety. t))
    (pn-check-invariance args)))

;;; EOF
