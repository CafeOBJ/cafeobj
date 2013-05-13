;;;-*-Mode:LISP; Package: CHAOS; Base:10; Syntax:Common-lisp -*-
;;; $Id: commands.lisp,v 1.2 2003-11-04 03:11:25 sawada Exp $
;;;
(in-package :chaos)
#|=============================================================================
			     System:Chaos
			    Module:BigPink
			  File:commands.lisp
=============================================================================|#
#-:chaos-debug
(declaim (optimize (speed 3) (safety 0) #-GCL (debug 0)))
#+:chaos-debug
(declaim (optimize (speed 1) (safety 3) #-GCL (debug 3)))

;;;			   ****************
;;;			   PigNose Commands
;;;			   ****************

;;; ==================
;;; COMMAND SYNTAX ADT
;;; ==================

;;; fax Term .
;;; ----------
(defterm fax (%ast)
  :visible (sentence
	    behavioural
	    &optional goal label)
  :eval eval-fax)

;;; input should be
;;; <command> ([ label ]: ( <term> ).
;;; <command> ::= "fax" | "bfax" | "goal" | "bgoal"
;;;
(defun pignose-process-fax-proc (input)
  (declare (type list input)
	   (values list))
  (let ((lhs nil)
	(label nil))
    (setq lhs (second input))
    (when (and (not (equal (first lhs) "("))
	       (equal (first lhs) "[")
	       (equal (third lhs) "]")
	       (equal (fourth lhs) ":"))
      (setf label (list (intern (string (second lhs)))))
      (setf lhs (nthcdr 4 lhs)))
  (%fax* lhs
	 (char= #\b (char (first input) 0))
	 nil
	 label))
  )

(defun pignose-eval-fax-proc (input)
  (declare (type list input)
	   (values t))
  (eval-ast (pignose-process-fax-proc input)))

(defun pignose-process-goal-proc (input)
  (declare (type list input)
	   (values list))
  (let ((lhs nil)
	(label nil))
    (setq lhs (second input))
    (when (and (not (equal (first lhs) "("))
	       (equal (first lhs) "[")
	       (equal (third lhs) "]")
	       (equal (fourth lhs) ":"))
      (setf label (list (intern (string (second lhs)))))
      (setf lhs (nthcdr 4 lhs)))
    (%fax* lhs
	   (char= #\b (char (first input) 0))
	   t
	   label)
    ))

(defun pignose-eval-goal-proc (input)
  (declare (type list input)
	   (values t))
  (eval-ast (pignose-process-goal-proc input)))

;;; sos = "{" . "," ..."}"
;;; also used for passive = ....
;;; passive ....
;;; ----------------------
(defterm sos (%script)
  :visible (operation
	    clause-list
	    type)			; :sos or :passive
  :eval eval-sos)

;;; pre-args ::= "sos" "=" "{" <real-args> "}"
(defun pignose-eval-sos-proc (pre-args)
  (declare (type list pre-args)
	   (values t))
  (let ((args nil)
	(op nil)
	(ast nil)
	(type (if (equal (first pre-args) "sos")
		  :sos
		:passive)))
    (declare (type list args ast)
	     (type symbol op))
    (case-equal (the simple-string (second pre-args))
		("=" (setq op :set))
		("+" (setq op :add))
		("-" (setq op :delete))
		(t (with-output-chaos-error ('internal)
		     (format t "sos op given ivalid op ~a" (second pre-args)))))
    (setq pre-args (cdddr pre-args))
    (dolist (a pre-args)
      (unless (equal "," a)
	(push a args)))
    (pop args)				; pop last "}"
    (setq ast (%sos* op (nreverse args) type))
    (eval-ast ast)))

;;; db reset
(defterm pndb (%script)
  :visible (arg)
  :eval eval-pndb)

(defun pignose-eval-db-proc (inp)
  ;; (declare (ignore inp))
  (eval-ast (%pndb* (cadr inp))))

;;; clause <term> .
(defterm clause-print (%script)
  :visible (term)
  :eval eval-clause-show)

;;; "clause" <term>
;;;
(defun pignose-eval-clause-proc (inp)
  (declare (type list inp)
	   (values t))
  (eval-ast (%clause-print* (cadr inp))))

;;; resolve
(defterm resolve (%script)
  :visible (arg)
  :eval eval-resolve)

(defun pignose-eval-resolve-proc (inp)
  (declare (type list inp))
  (let ((ast (%resolve* (cadr inp))))
    (eval-ast ast)))

;;; demod
(defterm demod (%script)
  :visible (term &optional module mode return-text)
  :eval perform-demodulation)

(defun pignose-eval-demod-proc (inp &rest ignore)
  (declare (type list inp) (ignore ignore))
  (multiple-value-bind (modexp preterm)
      (parse-in-context-modexp-with-term inp)
    (eval-ast (%demod* preterm modexp :red))))

;;; save-option name
(defterm save-option (%script)
  :visible (name)
  :eval pn-eval-save-option)

;;; list { axioms | axiom | sos | usable | demod }
;;;
(defterm pn-list (%script)
  :visible (arg)
  :eval eval-pn-list)

;;; ("list" arg)
(defun pignose-eval-list-proc (inp)
  (declare (type list inp))
  (let ((arg (cadr inp))
	(ast nil))
    (declare (type t arg)
	     (type list ast))
    (case-equal arg
       (("axioms" "axiom") (setq arg :axiom))
       ("sos" (setq arg :sos))
       ("usable" (setq arg :usable))
       ("passive" (setq arg :passive))
       (("flag" "flags") (setq arg :flag))
       (("param" "params" "parameters")(setq arg :param))
       (("option" "options") (setq arg :option))
       (("demod" "demodulator" "demodulators") (setq arg :demod))
       (t (with-output-chaos-error ('invalid-list-option)
	    (format t "invalid list option ~a" arg))))
    (setq ast (%pn-list* arg))
    (eval-ast ast)))

;;; option reset
(defterm pn-option (%script)
  :visible (command &optional name)
  :eval eval-pn-option)

(defun pignose-eval-save-option-proc (inp)
  (declare (type list inp))
  (let ((name (second inp)))
    (declare (type t name))
    (when (equal name ".")
      (with-output-chaos-warning ()
	(format t "option name `.' is not allowed.")
	(return-from pignose-eval-save-option-proc nil)))
    (eval-ast (%pn-option* :save name))
    ))
  
(defun pignose-eval-option-proc (inp)
  (declare (type list inp))
  (let* ((arg (second inp))
	 (arg-1 (first arg)))
    (declare (type t arg arg-1))
    (cond ((equal arg-1 "=")
	   (let ((name (second arg)))
	     (unless name
	       (with-output-chaos-error ('insuf-arg)
		 (princ "insufficient arguments to option command")))
	     (eval-ast (%pn-option* :restore name))))
	  ((or (equal arg-1 ".")
	       (equal arg-1 "reset"))
	   (eval-ast (%pn-option* :reset)))
	  (t (with-output-chaos-error ('inv-arg)
	       (format t "invalid argument to option command ~{~a~}" arg)))
	  )
    ))

;;; flag(name, value)
;;;
(defterm pn-set-flag (%script)
  :visible (name value)
  :eval eval-pn-set-flag)

(defun pignose-eval-flag-proc (inp)
  (declare (type list inp))
  (let ((name (third inp))
	(value (fifth inp)))
    (eval-ast (%pn-set-flag* name value))))

;;; param(name, value)
;;;
(defterm pn-assign (%script)
  :visible (name value)
  :eval eval-pn-assign)

(defun pignose-eval-param-proc (inp)
  (let ((name (third inp))
	(value (fifth inp)))
    (eval-ast (%pn-assign* name value))))

;;; sigmatch '(' M1 ')' 'to' '(' M2 ')'
;;;    0      1  2  3    4    5  6   7
;;;
(defterm sigmatch (%script)
  :visible (mod1 mod2)
  :eval eval-pn-sigmatch)

(defun pignose-eval-sigmatch-proc (inp)
  (declare (type list inp))
  (eval-ast (pignose-process-sigmatch inp)))

(defun pignose-process-sigmatch (inp)
  (declare (type list inp))
  (let ((mod1 (parse-modexp (nth 2 inp)))
	(mod2 (parse-modexp (nth 6 inp))))
    (%sigmatch* mod1 mod2)))

;;; lex [in <MODEXP>] : '(' op1, ..., *, opn ')'
(defterm pn-lex (%script)
  :visible (				; module : TODO***
	    ops)
  :eval eval-pn-lex)

(defun pignose-eval-lex-proc (inp)
  (declare (type list inp)
	   (values t))
  (let ((ops nil)
	(ast nil))
    (dolist (elt (cddr inp))		; skip "lex" "("
      (unless (equal "," elt)
	(push elt ops)))
    (pop ops)				; last ")"
    (setq ast (%pn-lex* (nreverse ops)))
    (eval-ast ast)))
      

;;; =============================
;;; TOP LEVEL COMMANDS EVALUATORS
;;; =============================

;;; EVAL-FAX
(defun eval-fax (ast)
  (declare (type list ast))
  (let ((sentence (%fax-sentence ast))
	(behavioural (%fax-behavioural ast))
	(label (%fax-label ast))
	(goal? (%fax-goal ast)))
    (I-miss-current-module eval-fax)
    ;; include fopl-clause unless already be imported.
    (include-fopl)
    ;;
    (prepare-for-parsing *current-module*)
    (let ((sort *cosmos*)
	  (*parse-variables* nil)
	  (*parse-lhs-attr-vars* nil)
	  (*lhs-attrid-vars* nil)
	  (real-lhs nil)
	  (ax nil))
      (let ((parsed-sentence (simple-parse *current-module*
					   sentence
					   sort)))
	(when (term-ill-defined parsed-sentence)
	  (with-output-chaos-error ('invalid-formula)
	    (princ "no parse for FOPL formula")
	    (print-next)
	    (princ sentence)))
	(unless (sort<= (term-sort parsed-sentence)
			*fopl-sentence-sort*
			(module-sort-order *current-module*))
	  (with-output-chaos-error ('invalid-formula)
	    (princ "sort of axiom must be (subsort of) FoplSentence.")
	    (print-next)
	    (princ sentence)))
	#||
	(if goal?
	    (setq real-lhs
		 (make-term-with-sort-check *fopl-neg*
					    (list parsed-sentence)))
	  (setq real-lhs parsed-sentence))
	||#
	(setq real-lhs parsed-sentence)
	;;
	(setq ax (make-pignose-axiom real-lhs
				     :behavioural behavioural
				     :label label
				     :type (if goal?
					       :pignose-goal
					     :pignose-axiom)))
	(check-axiom-error-method *current-module*
				  ax
				  t)
	(add-axiom-to-module *current-module* ax)
	(set-needs-rule)
	ax))))

;;; reset
(defun eval-pndb (ast)
  (declare (ignore ast))
  (unless *current-module*
    (with-output-chaos-error ('no-context)
      (princ "no context (current) module is set!")))
  ;;
  (pn-db-reset))

;;; EVAL-SOS
;;;
(defun eval-sos (ast)
  (flet ((is-nat (tok)
	   (and (stringp tok)
		(every #'digit-char-p tok))))
    (let ((args (%sos-clause-list ast))
	  (op (%sos-operation ast))
	  (type (%sos-type ast))
	  (real-set nil)
	  (psys nil)
	  (put-sysgoal-in-sos nil))
      (unless *current-module*
	(with-output-chaos-error ('no-context)
	  (princ "no context (current) module is set!")))
      (with-in-module (*current-module*)
	(auto-db-reset *current-module*)
	(setq psys (module-proof-system *current-module*))
	#||
	(unless psys
	  (with-output-chaos-error ('no-psys)
	    (princ "no proof system prepared, do `db reset' first!"))
	  )
	||#
	;;
	(setq args (flatten-list args))
	(dolist (arg args)
	  (cond ((is-nat arg)
		 (let ((cid nil)
		       (clause nil))
		   (setq cid (read-from-string arg))
		   (setq clause
		     (get-clause cid
				 (psystem-clause-hash psys)))
		   (unless clause
		     (with-output-chaos-error ('unvalid-clause-id)
		       (format t "no such claus with Id ~d." cid)))
		   (push clause real-set)))
		((null arg)		; setting empty
					; do nothing
		 )
		(t (let ((label (intern arg))
			 (cl-list nil))
		     (declare (type symbol label)
			      (type list cl-list))
		     (if (and (eq label '|:SYSTEM-GOAL|)
			      (eq type :sos))
			 (setq put-sysgoal-in-sos t)
		       (progn
			 (setq cl-list (find-clause label psys))
			 (if cl-list
			     (dolist (cl cl-list)
			       (push cl real-set))
			   ;; assume let variable
			   (let ((val (get-bound-value arg)))
			     (unless val
			       (with-output-chaos-error ('unboud)
				 (format t "could not find let variable ~a" arg)))
			     (setq val
			       (copy-term-reusing-variables val
							    (term-variables val)))
			     ;; convert to clause form.
			     (unless (and
				      (is-valid-formula? val
							 *current-module*)
				      (check-fopl-syntax val))
			       (with-output-chaos-error ('invalid-formula)
				 (princ "specified term is not valid as formula.")
				 (term-print val)))
			     (dolist (cl (formula->clause-1 val psys))
			       (push cl real-set)))))))))
	  )
	;;
	(dolist (cl (if (eq type :sos)
			(psystem-sos psys)
		      (psystem-passive psys)))
	  (setf (clause-container cl) nil))
	;;
	(case op
	  (:set (if (eq type :sos)
		    (setf (psystem-sos psys) (nreverse real-set))
		  (setf (psystem-passive psys) (nreverse real-set))))
	  (:add (if (eq type :sos)
		    (setf (psystem-sos psys)
		      (union (psystem-sos psys)
			     (nreverse real-set)
			     :test #'clause-equal))
		  (setf (psystem-passive psys)
		    (union (psystem-passive psys)
			   (nreverse real-set)
			   :test #'clause-equal))))
	  (:delete (if (eq type :sos)
		       (setf (psystem-sos psys)
			 (set-difference (psystem-sos psys)
					 (nreverse real-set)
					 :test #'clause-equal))
		     (setf (psystem-passive psys)
		       (set-difference (psystem-passive psys)
				       (nreverse real-set)
				       :test #'clause-equal)))
		   (when put-sysgoal-in-sos
		     (setq put-sysgoal-in-sos nil)))
	  )
	;;
	(if (eq type :sos)
	    (dolist (cl (psystem-sos psys))
	      (setf (clause-container cl) :sos))
	  (dolist (cl (psystem-passive psys))
	    (setf (clause-container cl) :passive)))

	;; setting sos/passive implies initial value of usable slot.
	(dolist (cl (psystem-usable psys))
	  (setf (clause-container cl) nil))
	(setf (psystem-usable psys)
	  (set-difference (psystem-axioms psys)
			  (append (psystem-passive psys)
				  (psystem-sos psys))
			  :test #'clause-equal))
	(dolist (cl (psystem-usable psys))
	  (setf (clause-container cl) :usable))
	;; we sort sos usable in 
	;; *NOT YET*
	(setf (psystem-sos psys)
	  (sort (psystem-sos psys)
		#'(lambda (x y)
		    (< (clause-id x) (clause-id y)))))
	(setf (psystem-usable psys)
	  (sort (psystem-usable psys)
		#'(lambda (x y)
		    (< (clause-id x) (clause-id y)))))
	(setf (psystem-passive psys)
	  (sort (psystem-passive psys)
		#'(lambda (x y)
		    (< (clause-id x) (clause-id y)))))
	;;
	(when put-sysgoal-in-sos
	  (push :system-goal (psystem-sos psys)))
	;;
	psys
	))))

;;; EVAL-CLAUSE-SHOW
;;;
(defun eval-clause-show (ast)
  (let ((pre-term (%clause-print-term ast)))
    (unless *current-module*
      (with-output-chaos-error ('no-context)
	(princ "no context module is given.")))
    (prepare-for-parsing *current-module*)
    #||
    (unless (module-proof-system *current-module*)
      (with-output-chaos-error ('no-psys)
	(princ "no proof system prepared, do `db reset' first!")))
    ||#
    (auto-db-reset *current-module*)
    (with-in-module (*current-module*)
      (let* ((*parse-variables* nil)
	     (term (simple-parse *current-module* pre-term *cosmos*)))
	(when (or (null (term-sort term))
		  (sort<= (term-sort term)
			  *syntax-err-sort* *chaos-sort-order*))
	  (return-from eval-clause-show nil))
	(when *mel-sort*
	  (!setup-reduction *current-module*)
	  (setq term (apply-sort-memb term *current-module*)))
	(unless (check-fopl-syntax term)
	  (with-output-chaos-error ('invalid-formula)
	    (princ "specified term is not valid as formula.")
	    (term-print term)))
	(dolist (cl (formula->clause-1 term
				       (module-proof-system *current-module*)))
	  (print-next)
	  (print-clause cl *standard-output*)))
      )))

;;; EVAL-PN-LIST
;;;
(defun eval-pn-list (ast)
  (let ((arg (%pn-list-arg ast))
	(psys nil))
    (unless (memq arg '(:flag :param :option))
      (unless *current-module*
	(with-output-chaos-error ('no-context)
	  (princ "no context (current) module is set.")))
      (auto-db-reset *current-module*)
      (setq psys (module-proof-system *current-module*))
      (unless psys
	(with-output-panic-message ()
	  (princ "could not construct proof system!"))))
    ;;
    (case arg
      (:axiom
       (with-proof-context (*current-module*)
	 (format t  "~% ~%** MODULE AXIOMS in CLAUSAL FORM ________")
	 (with-output-simple-msg ()
	   (princ " ")
	   (dolist (cl (psystem-axioms psys))
	     (print-next)
	     (print-clause cl *standard-output*)))
	 ))
      (:sos
       (with-proof-context (*current-module*)
	 (print-sos-list)
	 #||
	 (dolist (cl (psystem-sos psys))
	   (print-next)
	   (print-clause cl *standard-output*))
	 ||#
	 ))
      (:usable
       (with-proof-context (*current-module*)
	 (print-usable-list)
	 #||
	 (dolist (cl (psystem-usable psys))
	   (print-next)
	   (print-clause cl *standard-output*))
	 ||#
	 ))
      (:passive
       (with-proof-context (*current-module*)
	 (print-passive-list)))
      
      (:flag
       (pr-list-of-flag))
      (:param
       (pr-list-of-param))
      (:option
       (pr-list-of-option))
      (:demod
       (with-proof-context (*current-module*)
	 (print-demodulators-list)
	 #||
	 (dolist (cl (psystem-demods psys))
	   (print-next)
	   (print-clause cl *standard-output*))
	 ||#
	 ))
      (otherwise
       (with-output-chaos-error ('invalid)
	 (format t "internal error, unknown list option ~a" arg)))
      )))

;;; EVAL-RESOLVE
;;;
(defun eval-resolve (ast)
  (unless *current-module*
    (with-output-chaos-error ('no-context)
      (princ "no context (current module) is set!"))
    )
  (let ((out-file (%resolve-arg ast)))
    (if (and out-file (not (equal out-file ".")))
	(with-open-file (stream out-file :direction :output
			 :if-exists :append :if-does-not-exist :create)
	  (let ((*standard-output* stream))
	    (do-resolve (if *open-module*
			    *last-module*
			  *current-module*))))
      (do-resolve (if *open-module*
		      *last-module*
		    *current-module*)))))

(defun do-resolve (mod)
  (let ((time1 nil)
	(time2 nil)
	(time-for-run nil)
	(ret-code nil))
    (setq time1 (get-internal-run-time))
    (setq ret-code
      (infer-main mod))
    (setq time2 (get-internal-run-time))
    (setq time-for-run
      (format nil "~,3f sec"
	      (elapsed-time-in-seconds time1 time2)))
    (unless *chaos-quiet*
      (when (pn-flag print-stats)
	(with-output-simple-msg ()
	  (format t "(total run time ~a)" time-for-run))))
    ret-code))

;;; EXTENSIONS OF "SHOW"/"DESCRIBE" COMMAND.
;;;
(defun pignose-show-clause (cl-id &optional (desc nil) (all nil))
  (declare (ignore all))
  (unless *current-module*
    (with-output-chaos-error ('no-context)
      (princ "no context (current) module is set!")))
  (with-in-module (*current-module*)
    (let ((psys (module-proof-system *current-module*)))
      (let ((clauses (find-clause cl-id psys)))
	(cond (desc
	       (dolist (cl clauses)
		 (print-next)
		 (when (clause-formula cl)
		   (princ "-- clause derived from formula:")
		   (print-next)
		   (term-print (clause-formula cl))
		   (print-next))
		 (print-clause cl *standard-output*)))
	      (t			; show
	       (dolist (cl clauses)
		 (print-next)
		 (print-clause cl *standard-output*))
	       ))))))

;;; 
;;; SET-FLAG/CLEAR-FLAG
;;;
(defun eval-pn-set-flag (ast)
  (let ((name (%pn-set-flag-name ast))
	(given-value (%pn-set-flag-value ast))
	(value nil))
    (let ((index (find-pn-flag-index name)))
      (unless index
	(with-output-chaos-error ('no-such-flag)
	  (format t "no such flag name ~s" name)))
      (when (or (equal given-value "on")
		(equal given-value "set"))
	(setq value t))
      (when (pn-flag print-message)
	(with-output-msg ()
	  (format t "setting flag ~s to ~s" name given-value)))
      (setf (pn-flag index) value)
      (dependent-flags index)
      ;; run hook
      (funcall (pn-flag-hook index) value)
      )))

;;; SHOW-OPTION
;;;
(defun pignose-show-option (name)
  (show-option-set name))

;;; ASSIGN
;;;
(defun eval-pn-assign (ast)
  (let ((name (%pn-assign-name ast))
	(given-value (%pn-assign-value ast))
	(index nil)
	(value nil))
    (setq index (find-pn-parameter-index name))
    (unless index
      (with-output-chaos-error ('no-such-param)
	(format t "no such parameter name ~s" name)))
    (if (integerp given-value)
	(setq value given-value)
      (when (stringp given-value)
	(setq value (parse-integer given-value :junk-allowed t))))
    (unless (integerp value)
      (with-output-chaos-error ('invalid-value)
	(format t "invalid parameter value ~s" given-value)))
    (let ((min (pn-parameter-min index))
	  (max (pn-parameter-max index)))
      (when (< value min)
	(with-output-chaos-error ('out-of-range)
	  (format t "given value ~d is too small, minimun value allowed is ~d"
		  value min)))
      (when (> value max)
	(with-output-chaos-error ('out-of-range)
	  (format t "given value ~d is too large, maximum value allowed is ~d"
		  value max)))
      (when (pn-flag print-message)
	(with-output-msg ()
	  (format t "setting parameter ~s to ~d."
		  name value)))
      (setf (pn-parameter index) value)
      )))
  
;;; option reset
;;;
(defun eval-pn-option (ast)
  (let ((command (%pn-option-command ast))
	(name (%pn-option-name ast)))
    (case command
      (:reset (init-pn-options))
      (:save (save-option-set name))
      (:restore (restore-option-set name))
      )))

;;; DEMOD
(defun perform-demodulation (ast)
  (let ((preterm (%demod-term ast))
	(modexp (%demod-module ast))
	(mode (%demod-mode ast))
	(result-as-text (%demod-return-text ast)))
    (perform-demodulation* preterm modexp mode result-as-text)))

(defun perform-demodulation* (preterm &optional modexp mode (result-as-text nil))
  ;; (setq $$trials 1)
  (let ((*consider-object* t)
	(*rewrite-exec-mode* (eq mode :exec))
	(*rewrite-semantic-reduce* nil)
	sort
	time1
	time2
	(time-for-parse nil)
	(time-for-reduction nil)
	(number-matches nil))
    (let ((mod (if modexp 
		   (eval-modexp modexp)
		   *last-module*)))
      (unless (eq mod *last-module*)
	(clear-term-memo-table *term-memo-table*))
      (if (or (null mod) (modexp-is-error mod))
	  (if (null mod)
	      (with-output-chaos-error ('no-context)
		(princ "no module expression provided and no selected(current) module.")
		)
	      (with-output-chaos-error ('no-such-module)
		(princ "incorrect module expression, no such module ")
		(print-chaos-object modexp)
		))
	  (progn
	    (context-push-and-move *last-module* mod)
	    (with-in-module (mod)
	      (auto-db-reset mod))
	    (with-proof-context (mod)
	      (when *auto-context-change*
		(change-context *last-module* mod))
	      (!setup-reduction mod)
	      (setq $$mod *current-module*)
	      (setq sort *cosmos*)
	      (when *show-stats* (setq time1 (get-internal-run-time)))
	      (setq *rewrite-semantic-reduce*
		    (and (eq mode :red)
			 (module-has-behavioural-axioms mod)))
	      ;;
	      (let* ((*parse-variables* nil)
		     (term (simple-parse *current-module* preterm sort)))
		(when (or (null (term-sort term))
			  (sort<= (term-sort term) *syntax-err-sort* *chaos-sort-order*))
		  (return-from perform-demodulation* nil))
		(when *rewrite-stepping* (setq *steps-to-be-done* 1))
		(when *show-stats*
		  (setq time2 (get-internal-run-time))
		  (setf time-for-parse
			(format nil "~,3f sec"
				;; (/ (float (- time2 time1)) internal-time-units-per-second)
				(elapsed-time-in-seconds time1 time2)
				)))
		(unless *chaos-quiet*
		  (fresh-all)
		  (flush-all)
		  (if *rewrite-exec-mode*
		      (princ "-- execute in ")
		      (if (eq mode :red)
			  (princ "-- demodulate in ")
			  (princ "-- behavioural demodulate in "))
		      )
		  (print-simple-mod-name *current-module*)
		  (princ " : ")
		  (let ((*print-indent* (+ 4 *print-indent*)))
		    (term-print term))
		  (flush-all))
		;; ******** 
		(reset-target-term term *last-module* mod)
		;; ********
		(setq $$matches 0)
		(setq time1 (get-internal-run-time))
		(let ((*rule-count* 0))
		  (let ((res nil))
		    (catch 'rewrite-abort
		      #||
		      (if (sort<= (term-sort term) *fopl-sentence-sort*
				  *current-sort-order*)
			  (dolist (sub (term-subterms term))
			    (unless (term-is-variable? sub)
			      (demod-atom sub)))
			(setq res (demod-atom term)))
		      ||#
		      (setq res (demod-atom term))
		      )
		    (unless res (setq res $$term))
		    ;;
		    (when *mel-sort*
		      (setq res (apply-sort-memb res
						 mod))
		      (when res
			(setq $$term res)))
		    ;;
		    (setq time2 (get-internal-run-time))
		    (setf time-for-reduction
			  (format nil "~,3f sec"
				  ;; (/ (float (- time2 time1))
				  ;;     internal-time-units-per-second)
				  (elapsed-time-in-seconds time1 time2)))
		    (setf number-matches $$matches)
		    (setq $$matches 0)
		    (setq $$norm res)
		    ;; print out the result.
		    (if result-as-text
			(let ((red-term
			       (with-output-to-string (s)
				 (let ((*standard-output* s)
				       (*print-indent* (+ *print-indent* 2)))
				   (term-print res)
				   (print-check)
				   (princ " : ")
				   (print-sort-name (term-sort res)
						    *current-module*))
				 s
				 ))
			      (stat
			       (if *show-stats*
				   (concatenate
				    'string
				    (format nil
					    "~%(~a for parse, ~s rewrites(~a), ~d matches"
					    time-for-parse
					    *rule-count*
					    time-for-reduction
					    number-matches)
				    (if (zerop *term-memo-hash-hit*)
					(format nil ")~%")
					(format nil ", ~d memo hits)~%"
						*term-memo-hash-hit*)))
				   "")))
			  (return-from perform-demodulation* (values red-term stat)))
			(progn
			  (let ((*print-indent* (+ *print-indent* 2)))
			    (fresh-all)
			    (term-print res)
			    (print-check 0 3)
			    (princ " : ")
			    (print-sort-name (term-sort res)
					     *current-module*))
			  (when *show-stats*
			    (format t "~%(~a for parse, ~s rewrites(~a), ~d matches"
				    time-for-parse
				    *rule-count*
				    time-for-reduction
				    number-matches)
			    (if (zerop *term-memo-hash-hit*)
				(format t ")~%")
				(format t ", ~d memo hits)~%"
					*term-memo-hash-hit*)))
			  (flush-all)))
		    ))
		))
	    (context-pop-and-recover))))))

;;; SIGMATCH
(defun eval-pn-sigmatch (ast)
  (let ((mod1 (eval-modexp (%sigmatch-mod1 ast)))
	(mod2 (eval-modexp (%sigmatch-mod2 ast)))
	(views nil))
    (when (or (null mod1) (modexp-is-error mod1))
      (with-output-chaos-error ('no-such-module)
	(princ "no such module: ")
	(print-modexp (%sigmatch-mod1 ast))))
    (when (or (null mod2) (modexp-is-error mod2))
      (with-output-chaos-error ('no-such-module)
	(princ "no such module: ")
	(print-modexp (%sigmatch-mod2 ast))))
    (setq views (sigmatch mod1 mod2))
    ;; 
    (if views
	(princ views)
      (princ "( )"))
    ))
    
;;; LEX
(defun eval-pn-lex (ast)
  (unless *current-module*
    (with-output-chaos-error ('no-context)
      (princ "no context(current) module is specified.")))
  (compile-module *current-module*)
  (with-in-module (*current-module*)
    (let ((optokens (%pn-lex-ops ast))
	  (prec-list nil))
      (dolist (e optokens)
	(cond ((equal e '("*"))
	       (push :* prec-list))
	      ((equal e '("SKOLEM"))
	       (push :skolem prec-list))
	      (t (let ((parsedop (parse-op-name e)))
		   (multiple-value-bind (ops mod)
		       (resolve-operator-reference parsedop)
		     (with-in-module (mod)
		       (dolist (opinfo ops)
			 (dolist (meth (reverse (opinfo-methods opinfo)))
			   (push meth prec-list))))))
		 )
	      ))
      ;;
      (unless (memq :* prec-list)
	(push :* prec-list))
      (unless (memq :skolem prec-list)
	(push :skolem prec-list))
      (setq prec-list (nreverse prec-list))
      ;;
      (setf (module-op-lex *current-module*) prec-list)
      )))
    

;;; EOF
