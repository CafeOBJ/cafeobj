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
                                File: base.lisp
==============================================================================|#

(defparameter .case-module-true.  (%module-decl* "true-dummy" :object :user nil))
(defparameter .case-module-false. (%module-decl* "false-dummy" :object :user nil))
(defparameter .case-true-axiom.   (%axiom-decl* :equation '(":case_true") :LHS '("true") nil nil))
(defparameter .case-false-axiom.  (%axiom-decl* :equation '(":case_false") :LHS '("false") nil nil))

(defun perform-case-reduction (ast)
  (let ((bool-term (%scase-bool-term ast))
        (module (%scase-module ast))
        (name (%scase-name ast))
        (body (parse-module-elements (%scase-body ast)))
        (goal-term (%scase-goal-term ast)))
    ;; prepare modules
    (setf (%module-decl-name .case-module-true.) (concatenate 'string name "-#T"))
    (setf (%module-decl-name .case-module-false.) (concatenate 'string name "-#F"))
    ;; (push (%import* :including (parse-modexp module)) body)
    (push (%import* :including module) body)
    (setf (%axiom-decl-lhs .case-true-axiom.) bool-term)
    (setf (%module-decl-elements .case-module-true.) (append body (list .case-true-axiom.)))
    (setf (%axiom-decl-lhs .case-false-axiom.) bool-term)
    (setf (%module-decl-elements .case-module-false.) (append body (list .case-false-axiom.)))
    ;;
    (let ((org-mod (eval-modexp module))
          (true-mod (eval-ast .case-module-true.))
          (false-mod (eval-ast .case-module-false.)))
      (when (modexp-is-error org-mod)
        (with-output-chaos-error ('no-such-module)
          (format t "No such module or invalid module expression ~s" module)))

      ;; CASE TRUE
      (with-in-module (true-mod)
        (compile-module *current-module*)
        ;; 
        (with-output-simple-msg ()
          (format t "===================~%")
          (format t ">>* CASE: true *<<~%")
          (format t "==================="))
        (perform-reduction* goal-term true-mod :red))

      ;; CASE FALSE
      (with-in-module (false-mod)
        (compile-module *current-module*)
        ;; 
        (with-output-simple-msg ()
          (format t "===================~%")
          (format t ">>* CASE: false *<<~%")
          (format t "==================="))
        (perform-reduction* goal-term false-mod :red)))))



;;; EOF
                          
