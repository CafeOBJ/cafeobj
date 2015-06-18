;;;-*- Mode:LISP; Package:CHAOS; Base:10; Syntax:Common-lisp -*-
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
#|==============================================================================
                               System: CHAOS
                              Module: thstuff
                           File: eval-apply.lisp
==============================================================================|#
#-:chaos-debug
(declaim (optimize (speed 3) (safety 0) #-GCL (debug 0)))
#+:chaos-debug
(declaim (optimize (speed 1) (safety 3) #-GCL (debug 3)))

;;; *****
;;; START
;;; *****

(defun eval-start-command (ast)
  (do-eval-start-th (%start-target ast) (get-context-module)))

(defun do-eval-start-th (pre-term &optional context)
  (catch 'apply-context-error
    (let ((mod (if context
                   (eval-modexp context)
                 (get-context-module))))
      (if (or (null mod) (modexp-is-error mod))
          (if (null mod)
              (with-output-chaos-error ('invalid-module)
                (princ "no module expression provided and no current module."))
            (with-output-chaos-error ('invalid-module)
              (format t "incorrect module expression: ~a" context)))
        (if pre-term
            (with-in-module (mod)
              (prepare-for-parsing *current-module*)
              (cond ((or (equal pre-term '("$$term"))
                         (equal pre-term '("$$subterm")))
                     (let ((target nil))
                       (catch 'term-context-error
                         (setq target (get-bound-value (car pre-term))))
                       (unless target
                         (return-from do-eval-start-th nil))
                       (when (eq mod (get-context-module))
                         (setq $$action-stack nil))
                       (reset-reduced-flag target)
                       (reset-target-term target *current-module* mod)))
                    (t 
                     (let ((*parse-variables* nil))
                       (let ((res (simple-parse *current-module*
                                                pre-term
                                                *cosmos*)))
                         (when (term-is-an-error res)
                           (return-from do-eval-start-th nil))
                         (when (eq (get-context-module) mod)
                           (setq $$action-stack nil))
                         (reset-target-term res *current-module* mod))))))
          ;; try use $$term
          (progn
            (when (or (null $$term) (eq 'void $$term))
              (with-output-chaos-warning ()
                (format t "no target term is given!")
                (return-from do-eval-start-th nil)))
            (check-apply-context mod)
            (when (eq (get-context-module) mod)
              (setq $$action-stack nil))
            (reset-reduced-flag $$term)
            (reset-target-term $$term (get-context-module) mod))))
      (when (command-final) (command-display))
      t)))

;;; ******
;;; CHOOSE
;;; ******

(defun eval-choose-command (ast)
  (unless $$subterm (setq $$subterm $$term))
  (unless $$subterm
    (with-output-chaos-warning ()
      (format t "no target term is specified yet.")
      (print-next)
      (princ "please set the target term by `start' command.")
      (return-from eval-choose-command nil)))
  (let ((selectors (%choose-selectors ast)))
    (when (eq selectors ':top)
      (setq $$subterm $$term)
      (setq $$selection-stack nil)
      (return-from eval-choose-command nil))
    (with-in-module ((get-context-module))
      (multiple-value-bind (subterm-sort subterm)
          (compute-selection $$subterm selectors)
        (declare (ignore subterm-sort))
        (push selectors $$selection-stack)
        (setq $$subterm subterm)))))

;;; *************
;;; INSPECT-TERM
;;; *************
(defun eval-inspect-term-command (&optional ast)
  (declare (ignore ast))
  (unless $$subterm (setq $$subterm $$term))
  (unless $$subterm
    (with-output-chaos-warning ()
      (format t "no target term is specified yet.")
      (print-next)
      (princ "please set the target term by `choose' command.")
      (return-from eval-inspect-term-command nil)))
  (inspect-term $$subterm))

;;; *****
;;; APPLY
;;; *****

(defvar *-applied-* nil)
(defvar *-inside-apply-all-* nil)

;;; top-level evaluator

(defun eval-apply-command (ast)
  (let ((action (%apply-action ast))
        (rule-spec (%apply-rule-spec ast))
        (substitution (%apply-substitution ast))
        (where-spec (%apply-where-spec ast))
        (selectors (%apply-selectors ast)))
    (catch 'apply-context-error
      (if (eq action :help)
          (apply-help)
        (progn
          ;; check some evaluation env
          (when (or (null $$term) (eq 'void $$term))
            (with-output-chaos-error ('invalid-term)
              (princ "term to be applied is not defined.")
              ))
          (unless (get-context-module)
            (with-output-chaos-error ('no-context-module)
              (princ "no current module.")))
          ;; real work begins here ------------------------------
          (with-in-module ((get-context-module))
            (multiple-value-bind (subterm-sort subterm)
                (compute-selection $$term selectors)
              (setq *-applied-* t)
              (case action
                (:reduce                ; full reduction on selections.
                 (!setup-reduction *current-module*)
                 (let ((*rewrite-semantic-reduce*
                        (module-has-behavioural-axioms *current-module*))
                       (*rewrite-exec-mode* nil))
                   (term-replace subterm (@copy-term subterm))
                   (reset-reduced-flag subterm)
                   (rewrite subterm *current-module*)))
                (:breduce
                 (!setup-reduction *current-module*)
                 (let ((*rewrite-semantic-reduce* nil)
                       (*rewrite-exec-mode* nil))
                   (term-replace subterm (@copy-term subterm))
                   (reset-reduced-flag subterm)
                   (rewrite subterm *current-module*)))
                (:exec
                 (!setup-reduction *current-module*)
                 (let ((*rewrite-semantic-reduce*
                        (module-has-behavioural-axioms *current-module*))
                       (*rewrite-exec-mode* t))
                   (term-replace subterm (@copy-term subterm))
                   (reset-reduced-flag subterm)
                   (rewrite subterm *current-module*)))
                ;;
                (:print                 ; print selections.
                 (format t "~%term ")
                 (disp-term subterm)
                 (format t "~&tree form")
                 (print-term-tree subterm))
                (:apply                 ; apply specified rule.
                 (setq *-applied-* nil)
                 (let* ((actrule (compute-action-rule rule-spec
                                                      substitution
                                                      selectors))
                        (*-inside-apply-with-extensions-*
                         (and
                          (let ((arlhs (rule-lhs actrule)))
                            (and (term-is-application-form? arlhs)
                                 (method-is-associative (term-head arlhs)))))))
                   (if (eq :within where-spec)
                       (let ((*-inside-apply-all-* t))
                         (catch 'apply-all-quit
                           (@apply-all actrule subterm-sort subterm)))
                     (@apply-rule actrule subterm-sort subterm)))
                 (when *-applied-*
                   (update-lowest-parse $$term)
                   (when (nth 2 rule-spec) ; reverse order
                     (setq $$term (@copy-term $$term)))
                   (reset-target-term $$term *current-module* *current-module*))) ; end :apply
                (t (with-output-panic-message ()
                     (format t "unknown apply action : ~a" action)
                     (chaos-error 'unknown-action))))
              ;;
              (unless *-applied-*
                (with-output-chaos-warning ()
                  (princ "rule not applied")))
              ;;
              (command-final)
              (command-display))))))))

(defvar *copy-conditions*)
(declaim (special *copy-conditons*))
(defvar *apply-debug* nil)

(defun @apply-one-rule (rule sort term)
  (when *apply-debug*
    (princ "* @apply-one-rule : rule = ")
    (print-chaos-object rule)
    (format t "~%- sort = ") (print-sort-name sort)
    (format t "~&- term = ") (term-print term))
  (let ((*self* term))
    (let ((cond (rule-condition rule)))
      (if (or *reduce-conditions* (is-true? cond))
          (let ((lhs (rule-lhs rule)))
            (if (term-is-variable? lhs)
                (multiple-value-bind (gs sub no eeq)
                    (@matcher lhs (@copy-term term) :match) ; why?
                  (declare (ignore gs))
                  (when eeq (setq sub nil))
                  (unless (or no
                              (and (not (is-true? cond))
                                   (not (is-true?
                                         (!normalize-term
                                          (@copy-term
                                           (substitution-image! sub cond)))))))
                    (setq *-applied-* t)
                    (term-replace-dd-simple term
                                            (@copy-term
                                             (substitution-image! sub
                                                                  (rule-rhs rule))))))
              (let ((*copy-conditions* t))
                (let ((res (apply-one-rule-no-simplify rule term)))
                  (when res
                    (term-replace-dd-simple term
                                            (@copy-term term))
                    (setq *-applied-* t))
                  )))
            term)
        ;; "recurse" on condition
        (let ((lhs (rule-lhs rule))
              (rhs (rule-rhs rule)))
          (multiple-value-bind (gs sub no eeq)
              (@matcher lhs (@copy-term term) :match)
            (declare (ignore gs))
            (when eeq (setq sub nil))
            (unless no
              (setq *-applied-* t)
              (format t "~%shifting focus to condition")
              (force-output)
              (let ((cond-inst (@copy-term (substitution-image! sub cond)))
                    (rhs-inst
                     (@copy-term (substitution-image! sub rhs))))
                (setq $$action-stack
                  (cons
                   (list $$term term rule cond-inst rhs-inst sort)
                   $$action-stack))
                (setq $$term cond-inst)
                (when *-inside-apply-all-*
                  (format t "~%-- applying rule only at first position found: ")
                  (term-print term)
                  (force-output)
                  (throw 'apply-all-quit nil))))))))))

;;; APPLY-ONE-RULE-NO-SIMPLIFY (rule term)
;;;

(defun apply-one-rule-no-simplify (rule term)
  (when *apply-debug*
    (with-output-simple-msg ()
      (princ "[apply]: rule = ")
      (print-chaos-object rule)
      (print-next)
      (princ " term = ")
      (print-chaos-object term)))
  (block the-end
    (let ((condition nil)
          next-match-method
          ;; (*do-unify* t)
          (*self* term))
      (multiple-value-bind (global-state subst nomatch Eequal)
          (funcall (rule-first-match-method rule) (rule-lhs rule) term)
        (when nomatch (return-from the-end nil))
        (when *apply-debug*
          (format t "~%[apply-one-rule] : ")
          (format t "~%  subst = ")
          (print-substitution subst)
          (format t "~%  Eequal = ~a" eequal))
        ;; technical assignation related to substitution$image
        (when Eequal (setq subst nil))
        ;; the condition must be checked
        (block try-rule
          (catch 'rule-failure
            (when (is-true? (setq condition (rule-condition rule)))
              ;; there is no condition
              (term-replace-dd-simple term
                                      (if (rule-is-builtin rule)
                                          (multiple-value-bind (newterm success)
                                              (funcall (lisp-form-function
                                                        (rule-rhs rule)) subst)
                                            (if success
                                                newterm
                                              (return-from try-rule nil)))
                                        ;; note that the computation of the substitution
                                        ;; made a copy of the rhs.
                                        (substitution-image!
                                         subst
                                         (rule-rhs rule))))
              (return-from the-end t))))
        ;; if the condition is not trivial, we enter in a loop
        ;; where one try to find a match such that the condition 
        ;; is satisfied
        (setf next-match-method (rule-next-match-method rule))
        (loop
          (when nomatch (return))       ; exit from loop
          (block try-rule
            (catch 'rule-failure
              (when (is-true?
                     (let (($$cond (substitution-image
                                    ;; want to avoid recopying the whole
                                    (if *copy-conditions*
                                        (mapcar #'(lambda (x)
                                                    (cons (car x)
                                                          (@copy-term (cdr x))))
                                                subst)
                                      subst)
                                    condition)))
                       (!normalize-term $$cond)))
                ;; the condition is satisfied
                (term-replace-dd-simple
                 term
                 (if (rule-is-builtin rule)
                     (multiple-value-bind (newterm success)
                         (funcall (lisp-form-function (rule-rhs rule)) subst)
                       (if success
                           newterm
                         (return-from try-rule nil)))
                   (substitution-image! subst (rule-rhs rule))))
                (return-from the-end t)))
            )                           ; block try-rule
          ;; else, try another ...
          (multiple-value-setq (global-state subst nomatch)
            (funcall next-match-method global-state))
          )                             ; end loop
        ;; In this case there is no match at all and the rule does not apply
        (return-from the-end nil)))))

(defun @apply-rule (rule sort term)
  (if (and *-inside-apply-with-extensions-*
           (term-is-application-form? term)
           (method-is-of-same-operator (term-head (rule-lhs rule))
                                       (term-head term)))
      (@apply-rule-with-extensions rule sort term)
    (@apply-one-rule rule sort term)))

(defun @apply-rule-with-extensions (rule sort term)
  (let ((top (term-head (rule-lhs rule))))
    (if (method-is-associative top)
        (let ((is-applied nil)
              (is-AC (method-is-commutative top)))
          (when (@test-rule rule term)
            (@apply-one-rule rule sort term)
            (setq is-applied *-applied-*))
          (unless is-applied
            (dolist (r (if is-AC
                           (compute-AC-extension rule top)
                         (compute-A-extensions rule top)))
              (when (and r (@test-rule r term))
                (@apply-one-rule r sort term)
                (setq is-applied *-applied-*)
                (return)))))
      ;; only hit this case if top of rule lhs wasn't associative
      (@apply-one-rule rule sort term)))
  nil)

;;;
;;; @apply-all
;;;
(defun @apply-all (rule sort term)
  (if (term-is-variable? term)
      (when (@test-rule rule term) (@apply-rule rule sort term))
    (if (@test-rule rule term)
        (@apply-rule rule sort term)
      (if (term-is-application-form? term)
          (mapc #'(lambda (s x) (@apply-all rule s x))
                (method-arity (term-head term))
                (term-subterms term)))))
  nil)

;;;
;;; apply-print-rule
;;;
(defun apply-print-rule (x)
  (unless x
    (format t "~%That dosen't make sense as a rule specification.")
    (return-from apply-print-rule t))
  (let* ((act (get-apply-action x))
         (rule-spec (if (eq act :apply)
                        (parse-rule-spec x))))
    ;;
    (if (eq :reduce act)
        (format t "~%special rule for reduction of a selected subterm.")
      (if (eq :print act)
          (format t "~%special rule to print-the selected subterm.")
        (progn
          (when (or (eq :error rule-spec) (null rule-spec))
            (format t "~%That doesn't make sense as a rule specification.")
            (return-from apply-print-rule t))
          (let ((num (cadr rule-spec))
                (mod (car rule-spec))
                (rev (caddr rule-spec)))
            (format t "~&rule ~a" num)
            (when rev (format t  " (reversed)"))
            (if (equal "" mod)
                (format t " of the last module")
              (format t " of module ~a" mod))
            (multiple-value-bind (rule module)
                (compute-action-rule rule-spec nil)
              (with-in-module (module)
                (format t "~&  ")
                (print-chaos-object rule)
                (when (and rev (or (rule-is-builtin rule)
                                   (eq (axiom-type rule) :rule)))
                  (format t "~%This rule cannot be applied reversed."))
                (when (and (get-context-module)
                           (not (rule-is-builtin rule)))
                  (format t "~%(This rule rewrites up.)"))))))))
    t))

;;; EOF
