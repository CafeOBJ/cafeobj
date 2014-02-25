;;;-*- Mode:LISP; Package:CHAOS; Base:10; Syntax:Common-lisp -*-
;;; $Id: trans-com.lisp,v 1.3 2010-06-21 07:23:00 sawada Exp $
(in-package :chaos)
#|==============================================================================
				 System: CHAOS
				Module: cafeobj
			      File: trans-com.lisp
==============================================================================|#
#-:chaos-debug
(declaim (optimize (speed 3) (safety 0) #-GCL (debug 0)))
#+:chaos-debug
(declaim (optimize (speed 1) (safety 3) #-GCL (debug 3)))

;;; == DESCRIPTION =============================================================
;;; Translators from CafeOBJ toplevel command to Chaos script language.
;;; ----------------------------------------------------------------------------

;;; *****************************
;;; REDUCE/EXEC/PARSE/TEST-REDUCE
;;; *****************************
(defun parse-in-context-modexp-with-term (e)
  (let (modexp
	preterm)
    (if (= 4 (length e)) 
	(progn
	  (setq modexp (parse-modexp (cadr (cadr e))))
	  (setq preterm (nth 2 e)))
	(progn
	  (setq modexp nil)
	  (setq preterm (nth 1 e))))
    (values modexp preterm)))

;;; "reduce" [ "in" <Modexp> ":" ] <Term> . 
;;;
(defun process-reduce-command (e &rest ignore)
  (declare (ignore ignore))
  (multiple-value-bind (modexp preterm)
      (parse-in-context-modexp-with-term e)
    (%reduce* preterm modexp ':red)))

;;; "execute" [ "in" <Modexp> ":" ] <Term> .
;;;
(defun process-exec-command (e &rest ignore)
  (declare (ignore ignore))
  (multiple-value-bind (modexp preterm)
      (parse-in-context-modexp-with-term e)
    (%reduce* preterm modexp ':exec)))

(defun process-exec+-command (e &rest ignore)
  (declare (ignore ignore))
  (multiple-value-bind (modexp preterm)
      (parse-in-context-modexp-with-term e)
    (%reduce* preterm modexp ':exec+)))

;;; "bred" [ "in" <Modexp> ":" ] <Term> .
;;;
(defun process-bred-command (e &rest ignore)
  (declare (ignore ignore))
  (multiple-value-bind (modexp preterm)
      (parse-in-context-modexp-with-term e)
    (%reduce* preterm modexp ':bred)))
;;; "parse" [ "in" <Modexp> ":" ] <Term> .
;;;
(defun process-parse-command (e &rest ignore)
  (declare (ignore ignore))
  (multiple-value-bind (modexp preterm)
      (parse-in-context-modexp-with-term e)
    (%parse* preterm modexp)))

;;; "test {reduce | exec | bred} "
;;;  [ "in" <Modexp> ":" ] <Term> :expect <Term> .
;;;
(defun process-test-reduction (e &rest ignore)
  (declare (ignore ignore))
  (let ((mode-spec (second e))
	(mode nil))
    (case-equal mode-spec
      (("exec" "execute") (setq mode :exec))
      (("reduce" "red") (setq mode :red))
      (("behavioural-reduce" "bred") (setq mode :bred))
      (t (with-output-chaos-error ('invalid-op)
	   (format t "invalid `test' command option ~S" mode))
	 ))
    (setq e (cddr e))
    (let ((modexp nil)
	  (preterm nil)
	  (expect nil))
      (cond ((and (consp (car e)) (equal "in" (caar e)))
	     (setf modexp (parse-modexp (second (car e))))
	     (setf preterm (second e))
	     (setf expect (fourth e)))
	    (t (setf modexp nil)
	       (setf preterm (first e))
	       (setf expect (third e))))
      (%test-reduce* preterm expect modexp mode))))

;;;
;;; PROCESS-TRAM-COMMAND
;;;
(defun process-tram-command (inp &rest ignore)
  (declare (ignore ignore))
  (let ((args (cadr inp))
	(command nil))
    (case-equal (car inp)
      (("red" "reduce") (setq command :reduce))
      (("exec" "execute") (setq command :execute))
      (("compile") (setq command :compile))
      (("reset") (setq command :reset))
      (otherwise (with-output-chaos-error ()
		   (format t "unknown tram command ~a" (car inp)))))
    (if (eq command :compile)
	(let ((debug nil))
	  (loop
	   (case-equal (car args)
	     (("-a" "-all" "-e" "-exec")
	      (setq command :compile-all)
	      (setq args (cdr args)))
	     (("-d" "-debug")
	      (setq debug t)
	      (setq args (cdr args)))
	     (t (return nil))))
	  (%make-tram :command command :modexp args :debug debug))
	(multiple-value-bind (modexp preterm)
	    (parse-in-context-modexp-with-term inp)
	  (%make-tram :command command :modexp modexp :term preterm)))))
	  
;;; PROCESS-AUTOLOAD-COMMAND
(defun process-autoload-command (inp &rest ignore)
  (declare (ignore ignore))
  (let ((mod-name (car inp))
	(file (cadr inp)))
    (%autoload* mod-name file)
    ))

    
;;; CBREAD :
;;; cbred [in <Modexp> : ] LHS = RHS .
;;;
(defun process-cbred-command (toks &rest ignore)
  (declare (ignore ignore))
  (multiple-value-bind (modexp preterm)
      (parse-in-context-modexp-with-term toks)
    (let ((lhs nil)
	  (rhs nil))
      ;;
      (loop (when (or (null preterm)
		      (member (car preterm)
			      '("=" "=b=" "==") :test #'equal))
	      (return))
	(push (car preterm) lhs)
	(setq preterm (cdr preterm)))
      (setq lhs (nreverse lhs))
      (setq rhs (cdr preterm))
      (unless (and lhs rhs)
	(with-output-chaos-error ('invalid-command-form)
	  (princ "cbred: syntax error: ")
	  (princ toks)))
      (%cbred* modexp lhs rhs)
      )))

;;;
;;; LOOK UP
;;;
(defun parse-in-context-modexp-with-name (e)
  (let (modexp
	name)
    (setq e (cddr e))
    (if (cdr e)
	(progn
	  (setq modexp (parse-modexp (second (first e))))
	  (setq name (second e)))
	(progn
	  (setq modexp nil)
	  (setq name (first e))))
    (values modexp name)))

(defun process-look-up-command (e &rest ignore)
  (declare (ignore ignore))
  (multiple-value-bind (modexp name)
      (parse-in-context-modexp-with-name e)
    (%look-up* name modexp)))

;;; CASE
;;; scase (<Term>) in (<Modexp>) as <Name> { ... } : <GoalTerm> .
;;; ("scase" "(" ("1" "==" "2") ")" "in" "(" ("NAT") ")" "as" "NAT-C1" "{" <ModElements> "}" ":" ("1" "==" "2") ".") 
;;;     0    1         2        3    4   5     6     7   8      9      10      11        12  13        14
(defun process-case-command (expr &rest ignore)
  (declare (ignore ignore))
  (let ((case-term (nth 2 expr))
	(modexpr (parse-modexp (nth 6 expr)))
	(name (nth 9 expr))
	(body (nth 11 expr))
	(goal (nth 14 expr)))
    (when (atom body) 
      (setq body nil)
      (setq goal (nth 13 expr)))
    (%scase* case-term modexpr name body goal)))

;;; EOF
