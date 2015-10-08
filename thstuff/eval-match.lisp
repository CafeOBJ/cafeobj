;;;-*- Mode:LISP; Package:CHAOS; Base:10; Syntax:Common-lisp -*-
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
(in-package :chaos)
#|==============================================================================
                               System: CHAOS
                              Module: thstuff
                           File: eval-match.lisp
==============================================================================|#
#-:chaos-debug
(declaim (optimize (speed 3) (safety 0) #-GCL (debug 0)))
#+:chaos-debug
(declaim (optimize (speed 1) (safety 3) #-GCL (debug 3)))

;;; DESCRIPTION ----------------------------------------------------------------
;;; evaluators of match, find commands.
;;; *NOTE* `find <what>' is just the alias of `match it to <what>' .
;;;

;;; ******
;;; MATCH
;;; ******

(defun eval-match-command (ast)
  (let ((type (%match-type ast))
        (target (case (%match-target ast)
                  (:top $$term)
                  (:subterm $$subterm)
                  (:it (if $$subterm
                           $$subterm
                         $$term))
                  (t (let* ((*parse-variables* nil)
                            (parsed (with-in-module ((get-context-module))
                                      (simple-parse *current-module*
                                                    (%match-target ast)
                                                    *cosmos*))))
                       (if (sort<= (term-sort parsed)
                                   *syntax-err-sort*
                                   *chaos-sort-order*)
                           nil
                         parsed))))))
    ;;
    (when (or (null target) (eq target 'void))
      (if (symbolp (%match-target ast))
          (with-output-chaos-warning ()
            (princ "no target term is specified, please `start' or `choose'.")))
      (return-from eval-match-command nil))
    ;;
    (if (symbolp (%match-pattern ast))
        (find-rewrite-rules target (%match-pattern ast) type)
      (perform-match target (%match-pattern ast) type))))

(defun find-rewrite-rules (target what &optional (type :match))
  (if *find-all-rules*
      (find-rewrite-rules-all target what type)
    (find-rewrite-rules-top target what type)))

(defun find-rewrite-rules-top (target what &optional (type :match))  
  (let* ((real-target (supply-psuedo-variables target))
         (patterns (find-matching-rules what real-target (get-context-module) type)))
    (unless patterns
      (with-in-module ((get-context-module))
        (format t "~%no rules found for term : ")
        (term-print target))
      (return-from find-rewrite-rules-top nil))
    ;; report the result
    (format t "~%== matching rules to term : ")
    (with-in-module ((get-context-module))
      (let ((*fancy-print* nil))
        (term-print target))
      (dolist (pat patterns)
        (let ((num (found-pattern-rule-num pat))
              (direction (found-pattern-direction pat))
              (rule (found-pattern-rule pat))
              (subst (found-pattern-subst pat))
              (extra (found-pattern-extra pat)))
          (print-next)
          (if (eq direction :-rule)
              (princ "-")
            (princ "+"))
          (print-mod-name *current-module*)
          (if (rule-labels rule)
              (format t ".{ ~D " num)
            (format t ".~D" num))
          (dolist (label (rule-labels rule))
            (print-check)
            (princ "| ")
            (princ (string label)))
          (when (rule-labels rule)
            (princ " }"))
          (princ " is ")
          (print-axiom-brief rule *standard-output* nil t)
          (format t "~% substitution : ")
          (let ((*print-indent* (+ *print-indent* 4)))
            (print-substitution subst))
          (when extra
            (format t "~% extra variables : ")
            (format t "~{~a~^ ~}" (mapcar #'(lambda (x) (string (variable-name x)))
                                          extra))))))))

(defun find-rewrite-rules-all (target what &optional (type :match))  
  (let* ((real-target (supply-psuedo-variables target))
         (patterns (find-matching-rules-all what real-target (get-context-module) type)))
    (unless patterns
      (with-in-module ((get-context-module))
        (format t "~%no rules found for term : ")
        (term-print target))
      (return-from find-rewrite-rules-all nil))
    ;; report the result
    (format t "~%== matching rules to term : ")
    (with-in-module ((get-context-module))
      (let ((*fancy-print* nil))
        (term-print target))
      (dolist (pat patterns)
        (let ((num (found-pattern-rule-num pat))
              (direction (found-pattern-direction pat))
              (rule (found-pattern-rule pat))
              (subst (found-pattern-subst pat))
              (extra (found-pattern-extra pat))
              (pos (found-pattern-occur pat)))
          (print-next)
          (princ "* at posotion:")
          (format t "(~{~d~^ ~}), " pos)
          (let ((*print-indent* (+ 2 *print-indent*)))
            ;;
            (if (eq direction :-rule)
                (princ "-")
              (princ "+"))
            (print-mod-name *current-module*)
            (if (rule-labels rule)
                (format t ".{ ~D " num)
              (format t ".~D" num))
            (dolist (label (rule-labels rule))
              (print-check)
              (princ "| ")
              (princ (string label)))
            (when (rule-labels rule)
              (princ " }"))
            ;;
            (princ " is")
            (print-next)
            (print-axiom-brief rule *standard-output* nil t)
            (format t "~& substitution : ")
            (let ((*print-indent* (+ *print-indent* 4)))
              (print-substitution subst))
            (when extra
              (format t "~& extra variables : ")
              (format t "~{~a~^ ~}" (mapcar #'(lambda (x) (string (variable-name x)))
                                            extra)))))))))

;;; moved to 'meta.lisp'
;;; (defvar *use-choose-match* nil)

(defun perform-match (target pre-pattern &optional (type :match))
  (let ((real-target (if (eq type :match)
                         (supply-psuedo-variables target)
                       target)))
    (let ((first-match-meth (if (eq type :match)
                                (if *use-choose-match*
                                    nil
                                  '@matcher)
                              'first-unify))
          (next-match-meth (if (eq type :match)
                               (if *use-choose-match*
                                   nil
                                 'next-match)
                             'next-unify)))
      (with-in-module ((get-context-module))
        (let* ((*parse-variables* (mapcar #'(lambda (x)
                                              (cons (variable-name x) x))
                                          (term-variables target)))
               (pattern (simple-parse *current-module*
                                      pre-pattern
                                      *cosmos*)))
          (when (sort<= (term-sort pattern)
                        *syntax-err-sort* *chaos-sort-order*)
            (return-from perform-match nil))
          ;;
          (when (and *use-choose-match*
                     (eq type :match))
            (let ((meth (choose-match-method real-target *bool-true* nil)))
              (setf first-match-meth (car meth))
              (setf next-match-meth (cdr meth))))
          ;; ---- first match 
          (multiple-value-bind (global-state subst no-match e-equal)
              (funcall first-match-meth pattern real-target)
            (when no-match
              (if (eq type :match)
                  (format t "~%-- no match")
                (format t "~%-- no unify"))
              (return-from perform-match nil))
            (if (eq type :match)
                (format t "~%-- match success.")
              (format t "~%-- unify success."))
            (when e-equal
              (format t "~%-- given terms are equational equal.")
              (return-from perform-match nil))
            (format t "~% substitution : ")
            (let ((*print-indent* (+ *print-indent* 4)))
              (print-substitution subst))
            ;; ---- next matches
            (block end
              (multiple-value-setq (global-state subst no-match)
                (funcall next-match-meth global-state))
              (while (not no-match)
                (cond ((y-or-n-p-wait #\y 20 ">> More? [y/n] : ")
                       (if (eq type :match)
                           (format t "~%-- match success : ")
                         (format t "~%-- unify success : "))
                       (let ((*print-indent* (+ 4 *print-indent*)))
                         (format t "~% * substitution : ")
                         (print-substitution subst))
                       (print-next))
                      (t (return-from end)))
                (multiple-value-setq (global-state subst no-match)
                  (funcall next-match-meth global-state)))
              (if (eq type :match)
                  (format t "~%-- No more match")
                (format t "~%-- No more unify")))))))))

;;; EOF
