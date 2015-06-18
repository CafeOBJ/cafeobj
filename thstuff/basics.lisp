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
                              File: basics.lisp
==============================================================================|#
#-:chaos-debug
(declaim (optimize (speed 3) (safety 0) #-GCL (debug 0)))
#+:chaos-debug
(declaim (optimize (speed 1) (safety 3) #-GCL (debug 3)))

;;; === Common Basic Functions for APPLY family
;;;     ------------------------------------------------------------------------

;;; *****
;;; UTILS
;;; *****

(defun check-apply-context (mod)
  (unless (check-$$term-context mod)
    (with-output-chaos-warning ()
      (format t "the target term : ")
      (print-chaos-object $$term)
      (print-next)
      (format t "isn't proper in the context : ")
      (print-chaos-object mod)
      (print-next)
      (format t "please re-`start' with supplying new one!")
      (throw 'apply-context-error nil))))

(defun command-display ()
  (if $$action-stack
      (format t "~%-- condition(~s) " (length $$action-stack))
    (format t "~&result "))
  (disp-term $$term))

(defun command-final ()
  (when $$action-stack
    ;; $$action-stack == list of
    ;;      ($$term term rule condition rhs-instance sort)
    ;;         0      1   2      3          4
    (if (term-is-similar? $$term *bool-true*)
        (progn
          (command-display)
          (format t "~%-- condition is satisfied, applying rule")
          (format t "~&-- shifiting focus back to previous context")
          (let ((cur (car $$action-stack)))
            (setq $$term (car cur))
            (term-replace (nth 1 cur) (nth 4 cur))
            (setq $$action-stack (cdr $$action-stack)))
          t)
      (if (term-is-similar? $$term *bool-false*)
          (progn
            (command-display)
            (format t "~%-- condition is not satisfied, rule not applied")
            (format t "~&-- shifting focus back to previous context")
            (setq $$term (caar $$action-stack))
            (setq $$action-stack (cdr $$action-stack))
            t)
        nil))))

(defun disp-term (x)
  (with-in-module ((get-context-module))
    (term-print x)
    (princ " : ")
    (print-sort-name (term-sort x) *current-module*)))

(defun disp-term* (x)
  (term-print x)
  (princ " : ")
  (print-sort-name (term-sort x) *current-module*))

;;;
;;; apply-help
;;;
(defun apply-help ()
  (format t "~%Apply a selected rule, possibly with an instantiation,")
  (format t " to selected subterm(s).")
  (format t "~&Syntax:")
  (format t "~&  apply { reduction | red | print | bred | exec | <RuleSpec> [ <VarSubst> ] }")
  (format t "~&        { at | within } <Selectors>")
  (format t "~&  <RuleSpec>  ::= [ + | - ] [<ModId>.]<RuleId>")
  (format t "~&  <RuleId>    ::= <Natural> | <Identifier>")
  (format t "~&  <VarSubst>  ::= with <Variable> = <Term> { , <Variable> = <Term> }*")
  (format t "~&  <Selectors> ::= top | term | subterm | <Selector> { of <Selector> }* .")
  (format t "~&  <Selector>  ::= (<Natural>+) | `[' <Natural> [ .. <Natural> ] `]' |")
  (format t "~&                  `{' <Natural> {, <Natural>}* `}'")
  )

;;; *******************
;;; COMPUTING SELECTION
;;; *******************

(defun str-to-int (x)
  (if (equal "" x)
      0
    (read-from-string x)))

(defun !make-right-associative (method subs)
  (if (null (cdr subs)) (car subs)
    (make-right-assoc-normal-form method subs)))

;;; <OccurSelection>
;;; ________________
(defun compute-occur-selection (sort term occs)
  (let ((cursrt sort) (cur term))
    (dolist (i occs)
      (if (and (<= 0 i) (<= i (length (term-subterms cur))))
          (unless (zerop i)
            (setq cursrt (nth (1- i) (method-arity (term-head cur))))
            (setq cur (nth (1- i) (term-subterms cur))))
        (with-output-chaos-warning ()
          (format t "no such occurrenct, occurrence ~a is not correct for term :"
                  occs)
          (print-next)
          (term-print term)
          (print-next)
          (format t "ignoring it.")
          (return-from compute-occur-selection (values sort term)))))
    (values cursrt cur) ))

;;; <SubseqSelection>
;;; _________________
;;; compute-subseq-selection : sort term m n
;;;
;;; <SubseqSelection> ::= [ m .. n ] | [ m ]
;;;  - case [ m ]  --> [ m .. m ]
;;;
(defun compute-subseq-selection (sort term m1 n1)
  (let ((m (1- m1))                     ; *note* sequence specifier is 1 origin.
        (n (1- n1)))
    (if (term-is-variable? term)
        (with-output-chaos-warning ()
          (format t "found variable in selection of subsequence selection : ")
          (term-print term)
          (values sort term))
      (let ((method (term-head term)))
        ;; [ ... ] is meaningful only for associative operators.
        (if (method-is-associative method)
            (let ((lst (list-assoc-subterms term method)))
              (if (and (<= m n) (<= 1 m1) (<= n1 (length lst)))
                  (if (or (< 1 m1) (< n1 (length lst)))
                      (let ((res (!make-right-associative
                                  method
                                  (subseq lst m (1+ n)))))
                        (term-replace term
                                      (!make-right-associative
                                       method
                                       (append (subseq lst 0 m)
                                               (list res)
                                               (subseq lst (1+ n)))))
                        (values (car (method-arity method)) res))
                    (values sort term))
                (with-output-chaos-warning ()
                  (format t "selection [~a .. ~a] is out of range for term :~%    "
                          m1 n1)
                  (term-print term)
                  (print-next)
                  (format t "selected the whole subterms instead.")
                  (values sort term)
                  )))
          (with-output-chaos-warning ()
            (format t "found non-associative operator in selection of subsequence slection : ~%    ")
            (print-chaos-object method)
            (values sort term)))))))

;;; <SubsetSelection>
;;; _________________

(defun compute-subset-selection (sort term occs)
  (if (term-is-variable? term)
      (with-output-chaos-warning ()
        (format t "found variable in subset selection ~a: " occs)
        (term-print term)
        (print-next)
        (format t "ignoring the selection and select whole subterms instead.")
        (values sort term))
    (let ((method (term-head term)))
      (if (and (method-is-associative method)
               (method-is-commutative method))
          (let ((lst (list-AC-subterms term method)))
            (let ((len (length lst))
                  (sel nil)
                  (rest nil)
                  (err nil))
              (dolist (i occs)
                (let ((n (1- i)))
                  (if (and (<= 0 n) (< n len))
                      (let ((tl (nthcdr n lst)))
                        (when (car tl) (push (car tl) sel))
                        (rplaca tl nil))
                    (push i err))))
              (dolist (x lst) (when x (push x rest)))
              (when err
                (with-output-chaos-warning ()
                  (princ "found out of range in selection of subterms")
                  (print-next)
                  (format t "ignoring these selections : ~a" err)))
              (if (null rest)
                  (values sort term)
                (let ((res (!make-right-associative method (nreverse sel))))
                  (term-replace
                   term
                   (!make-right-associative method (cons res (reverse rest))))
                  (values (car (method-arity method)) res)
                  ))))
        (with-output-chaos-warning ()
          (princ "subset selection is meaningful only for associative and commuteative operators,")
          (print-next)
          (format t "but : ")
          (print-chaos-object method)
          (princ " is not.")
          (print-next)
          (princ "ignoreing the selection and select whole subterms instead.")
          (values sort term))) )))

;;; compute-set-ocs
;;;  ("{" "1" "," "2" "," "4" "}") --> (1 2 4)
;;;
(defun compute-set-ocs (x)
  (let ((res nil)
        (val nil))
    (setq x (cdr x))
    (do ((elt x (cddr elt)))
        ((endp elt) (nreverse res))
      (setq val (str-to-int (car elt)))
      (pushnew val res))))

;;; top-level interface
;;; *******************
(defvar *selection-target* nil)
(declaim (special *selection-target*))

(defun compute-selection (tm sel)
  (let ((*selection-target* tm))
    (!compute-selection *cosmos*
                        tm
                        (if (consp sel)
                            (if (equal (car (last sel)) ".")
                                (butlast sel)
                              sel)
                          sel))))

;;; !compute-selection
;;; the main computing selections
;;;
(defun !compute-selection (sort tm sel)
  ;; no selection
  (unless sel (return-from !compute-selection
                (if (not (term-eq $$term *selection-target*))
                    (values sort *selection-target*)
                  (values sort $$term))))
  ;; whole term
  (when (memq sel '(:term :top))
    (return-from !compute-selection (values sort $$term)))
  ;; subterm
  (when (eq sel :subterm)
    (if $$subterm
        (return-from !compute-selection (values sort $$subterm))
      (progn
        (with-output-chaos-warning ()
          (format t "no subterm is specified yet, please `choose' some.")
          (print-next)
          (format t "selected the whole term."))
        (values sort $$term))))
  ;; 
  (!compute-selection-aux sort tm (cons (car sel) (cadr sel))))

(defun !compute-selection-aux (sort tm sel)
  (unless sel (return-from !compute-selection-aux
                (if (not (term-eq *selection-target* $$term))
                    (values sort *selection-target*)
                  (values sort $$term))))
  ;; <Selection> of <Selection>
  (when (equal "of" (car sel))
    (return-from !compute-selection-aux
      (!compute-selection-aux sort tm (cdr sel))))
  ;; 
  (case-equal (caar sel)
              ("("
               ;; occur selection
               (when (equal ")" (cadr (car sel)))
                 (return-from !compute-selection-aux
                   (!compute-selection-aux sort tm (cdr sel))))
               (multiple-value-bind (s1 t1)
                   (!compute-selection-aux sort tm (cdr sel))
                 (return-from !compute-selection-aux
                   (compute-occur-selection s1 t1
                                            (mapcar #'str-to-int (cadr (car sel)))))))
              ("["
               ;; subseq selection { [ m .. n ] | [ m ] }
               (let ((i1 (str-to-int (cadr (car sel)))))
                 (multiple-value-bind (s1 t1)
                     (!compute-selection-aux sort tm (cdr sel))
                   (compute-subseq-selection s1
                                             t1
                                             i1
                                             (if (equal "]" (nth 2 (car sel)))
                                                 ;; case [ m ]
                                                 i1 
                                               ;; case [ m .. n ]
                                               (str-to-int (cadr (nth 2 (car sel)))))))))
              ("{"
               ;; subset selection
               (multiple-value-bind (s1 t1)
                   (!compute-selection-aux sort tm (cdr sel))
                 (compute-subset-selection s1 t1 (compute-set-ocs (car sel)))))
              (t (break "SNARK: !compute-selection"))))

;;; **************
;;; Utils on TERMS 
;;; **************

(defun @copy-list-term-using-list-var (term-list list-new-var)
  (declare (type list term-list list-new-var)
           (values list list))
  (let ((v-image nil)
        (list-copied-term nil))
    (values (mapcar #'(lambda (term)
                        (cond ((term-is-variable? term)
                               (if (setq v-image
                                     (cdr (assoc term list-new-var
                                                 :test #'variable-equal)))
                                   v-image
                                 (let ((new-var (variable-copy term)))
                                   (declare (type term new-var))
                                   (setf list-new-var (acons term new-var
                                                             list-new-var))
                                   new-var
                                   )))
                              ((term-is-builtin-constant? term) term)
                              ((term-is-lisp-form? term) term)
                              (t (multiple-value-setq (list-copied-term list-new-var)
                                   (@copy-list-term-using-list-var
                                    (term-subterms term)
                                    list-new-var))
                                 (make-applform (term-sort term)
                                                (term-head term)
                                                list-copied-term))))
                    term-list)
            list-new-var)))

;;; @COPY-TERM-USING-VARIABLE : term List[variable] -> term
;;;
(defun @copy-term-using-variable (term list-new-var)
  (declare (type term term)
           (type list list-new-var)
           (values term))
  (multiple-value-bind (res list-new-var-res)
      (@copy-list-term-using-list-var (list term) list-new-var)
    (declare (ignore list-new-var-res)
             (type list res))
    (car res)))

#||
(defun @copy-term (term)
  (simple-copy-term term))
||#

(defun @copy-term (term)
  (let ((vars (term-variables term)))
    ;; (print vars)
    (if vars
        (@copy-term-using-variable term nil)
      (simple-copy-term term))))

(defun @matcher (pat term type)
  (if (term-is-variable? pat)
      (if (sort<= (term-sort term) (variable-sort pat)
                  (module-sort-order *current-module*))
          (values nil (list (cons pat term)) nil nil)
        (values nil nil t nil))
    (if (term-is-lisp-form? pat)
        (values nil nil t nil)
      (if (eq type :match)
          (first-match pat term)
        (first-unify pat term)))))

(defun @test-rule-direct (rul term type)
  (multiple-value-bind (gs sub no eeq)
      (@matcher (axiom-lhs rul) term type)
    (declare (ignore gs sub eeq))
    (null no)))

(defvar *-inside-apply-with-extensions-* nil)

(defun @test-rule (rule term &optional (type :match))
  (multiple-value-bind (gs sub no-match eeq)
      (@matcher (axiom-lhs rule) term type)
    (declare (ignore gs sub eeq))
    (if (and no-match
             (and *-inside-apply-with-extensions-*
                  (not (or (term-is-variable? term)
                           (term-is-builtin-constant? term)))
                  (method-is-of-same-operator (term-head (axiom-lhs rule))
                                              (term-head term))))
        (@test-rule-extensions rule term type)
      (null no-match))))

(defun @make-ac-pattern (top term)
  (let ((newvar (make-variable-term *cosmos* 'ac-pat)))
    (make-right-assoc-normal-form top
                                  (cons newvar
                                        (list-assoc-subterms
                                         term
                                         (term-head term))))))
(defun @make-a-patterns (top term)
  (let ((new-var1 (make-variable-term *cosmos* 'a-pat1))
        (new-var2 (make-variable-term *cosmos* 'a-pat2)))
    (list (make-right-assoc-normal-form top
                                        (cons new-var1
                                              (list-assoc-subterms
                                               term
                                               (term-head term))))
          (make-right-assoc-normal-form top
                                        (append
                                         (list-assoc-subterms
                                          term
                                          (term-head term))
                                         (list new-var1)))
          (make-right-assoc-normal-form top
                                        (list new-var2
                                              term
                                              new-var1)))))

(defun @pat-match (pat term &optional (type :match))
  (multiple-value-bind (gs sub no-match eeq)
      (@matcher pat term type)
    (declare (ignore gs eeq))
    (unless no-match
      (return-from @pat-match (values t sub)))
    (if (and (term-is-application-form? term)
             (term-is-application-form? pat)
             (method-is-of-same-operator (term-head pat)
                                         (term-head term)))
        (let ((top (term-head pat)))
          (if (method-is-associative top)
              (dolist (npat (if (method-is-commutative top)
                                (list (@make-ac-pattern top pat))
                              (@make-a-patterns top pat))
                        (values nil nil))
                (when (and npat
                           (progn
                             (multiple-value-setq (gs sub no-match eeq)
                               (@matcher npat term type))
                             (null no-match)))
                  (return (values t sub))))
            (values nil nil))))))

;;;
;;; FOR :=
;;;
(declaim (special *m-pattern-subst*))

(defun match-m-pattern (pat term)
  (multiple-value-bind (res subst)
      (@pat-match pat term)
    (when res
      (dolist (sub subst)
        (push sub *m-pattern-subst*))
      (return-from match-m-pattern t))
    nil))

(defun @test-rule-extensions (rule term type)
  (let ((top (term-head (axiom-lhs rule))))
    (if (method-is-associative top)
        (dolist (r (if (method-is-commutative top)
                       (compute-AC-extension rule top)
                     (compute-A-extensions rule top))
                  nil)
          (when (and r (@test-rule-direct r term type))
            (return t)))
      nil)))

;;; *********************
;;; VARIABLE SUBSTITUTION
;;; *********************

;;; COMPUTE-VARIABLE-SUBSTITUTION
;;;
(defun compute-variable-substitution (rule substtoks)
  ;; rule just for vars
  (let ((vars (union (term-variables (axiom-lhs rule))
                     (union (term-variables (axiom-rhs rule))
                            (term-variables (axiom-condition rule)))))
        (sub nil)
        varnm
        trmtoks
        avar
        aterm)
    (with-in-module ((get-context-module))
      (loop (when (null substtoks) (return))
        ;; <varid> = <term>
        (setq varnm (cadr substtoks))
        (setq trmtoks (nth 3 substtoks))
        (setq avar (find-if #'(lambda (x) (equal (string (variable-name x))
                                                 varnm))
                            vars))
        (setq aterm (simple-parse *current-module*
                                  trmtoks
                                  *cosmos*))
        (if (and avar (not (term-is-an-error aterm)))
            (progn
              (if (not (is-in-same-connected-component
                        (term-sort aterm)
                        (variable-sort avar)
                        *current-sort-order*))
                  (with-output-chaos-warning ()
                    (princ "sort of term is incompatible with variable sort")
                    (print-next)
                    (format t "variable ~a:" (string (variable-name avar)))
                    (print-sort-name (variable-sort avar))
                    (print-next)
                    (princ "term ")
                    (print-chaos-object aterm)
                    (princ ":")
                    (print-sort-name (term-sort aterm)))
                (push (cons avar aterm) sub)))
          (with-output-chaos-error ('invalid-subst)
            (unless avar
              (format t "No such variable in rule: ~s" varnm)
              (print-next)
              (princ "specified substitution contains an error")
              )))
        (setq substtoks (cddddr substtoks))))
    sub))

;;; **********************
;;; FINDING MATCHING RULES
;;; **********************

(defstruct found-pattern
  rule-num
  direction
  rule
  subst
  extra
  occur)

(defun get-subterm-pos (term pos)
  (let ((cur term))
    (when pos
      (dolist (p pos)
        (let ((rp (1- p)))
          (when (>= rp 0)
            (setq cur (term-arg-n cur rp)))
          (unless cur
            (with-output-panic-message ()
              (format t "could not find subterm at pos ~d" pos)
              (format t "~% target was ")
              (term-print term)
              (break "wow!")
              (chaos-error 'panic))))))
    cur))

(defun find-matching-rules-all (what target module &optional (type :match) (start-pos nil))
  (with-in-module (module)
    (when start-pos
      (setq target (get-subterm-pos target start-pos)))
    (find-matching-rules-all* what target module type start-pos)))

(defun find-matching-rules-all* (what target module type pos)
  (let ((result (find-matching-rules what target module type)))
    (dolist (r result)
      (setf (found-pattern-occur r) pos))
    (dotimes (x (length (term-subterms target)))
      (let ((r (find-matching-rules-all* what
                                         (term-arg-n target x)
                                         module
                                         type
                                         (append pos (list (1+ x))))))
        (when r (setq result (nconc result r)))))
    ;;
    result))

(defun find-matching-rules (what target module &optional (type :match))
  (with-in-module (module)
    (let* ((*module-all-rules-every* t)
           (rules (get-module-axioms *current-module* t))
           (res nil))
      (do* ((rls rules (cdr rls))
            (rule (car rls) (car rls))
            (num 1 (1+ num)))
          ((endp rls))
        (when (or (eq what :rule) (eq what :+rule))
          (multiple-value-bind (match subst)
              (@pat-match (axiom-lhs rule) target type)
            (when match
              (push (make-found-pattern :rule-num num
                                        :direction :+rule
                                        :rule rule
                                        :subst subst
                                        :extra (compute-extra-variables
                                                rule
                                                :+rule))
                    res))))
        (when (and (or (eq what :rule) (eq what :-rule))
                   (not (eq (axiom-type rule) :rule))
                   (not (rule-is-builtin rule)))
          (multiple-value-bind (match subst)
              (@pat-match (axiom-rhs rule) target type)
            (when match
              (push (make-found-pattern :rule-num num
                                        :direction :-rule
                                        :rule rule
                                        :subst subst
                                        :extra (compute-extra-variables
                                                rule
                                                :-rule))
                    res)))))
      (nreverse res))))

(defun compute-extra-variables (rule direction)
  (let ((lhs (axiom-lhs rule))
        (rhs (axiom-rhs rule))
        (condition (axiom-condition rule)))
    (when (eq direction ':-rule)
      (setq lhs rhs)
      (setq rhs lhs))
    (let* ((lvars (term-variables lhs))
           (rvars (union (term-variables rhs)
                         (term-variables condition))))
      (nset-difference rvars lvars))))

;;; EOF
