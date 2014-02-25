;;;-*- Mode:LISP; Package:CHAOS; Base:10; Syntax:Common-lisp -*-
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
    (push (%import* :including (parse-modexp module)) body)
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
	  		  
