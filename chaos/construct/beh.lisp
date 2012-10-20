;;;-*- Mode:LISP; Package:CHAOS; Base:10; Syntax:Common-lisp -*-
;;; $Id: beh.lisp,v 1.8 2010-07-30 00:46:00 sawada Exp $
(in-package :chaos)
#|==============================================================================
				 System: Chaos
			       Module: construct
				 File: beh.lisp
==============================================================================|#
#-:chaos-debug
(declaim (optimize (speed 3) (safety 0) #-GCL (debug 0)))
#+:chaos-debug
(declaim (optimize (speed 1) (safety 3) #-GCL (debug 3)))

;;; == DESCRIPTION =============================================================
;;; stuff supporting proof in behavioural specification.
;;;
(defstruct (beh-stuff (:print-function print-beh-stuff))
  (hs          nil)			; hidden sort
  (attributes  nil)			; list of attributes
  (methods     nil)			; list of methods
  (axioms      nil)			; axioms generated.
  (theorem    nil)			; ceq t =*= t' = true
					; if attr(t,d) == attr(t',d) and ...
  (assumptions nil)			; eq attr(`t,`d) = attr(`t',`d)
  (targets     nil)			; list of terms to be evaluated to true
					;   method(`d,`t) =*= method(`d,`t')
  )

(defun print-beh-stuff (obj stream &rest ignore)
  (declare (ignore ignore)
	   (type beh-stuff obj)
	   (type stream stream)
	   (values t))
  (let ((*standard-output* stream))
    (print-next)
    (format t "Hidden sort : ")
    (print-chaos-object (beh-stuff-hs obj))
    (print-next)
    (format t "axioms : ")
    (let ((*print-indent* (+ *print-indent* 2)))
      (dolist (ax (beh-stuff-axioms obj))
	(print-next)
	(print-chaos-object ax)))
    (print-next)
    (format t "theorem : ")
    (let ((*print-indent* (+ *print-indent* 2)))
      (print-next)
      (print-chaos-object (beh-stuff-theorem obj)))
    (print-next)
    (format t "assumptions : ")
    (let ((*print-indent* (+ *print-indent* 2)))
      (dolist (as (beh-stuff-assumptions obj))
	(print-next)
	(print-chaos-object as)))
    (print-next)
    (format t "targets :")
    (let ((*print-indent* (+ 2 *print-indent*)))
      (dolist (tg (beh-stuff-targets obj))
	(print-next)
	(print-chaos-object tg)))
    ))

;;; (defvar *beh-debug* nil)

(defun construct-beh-stuff (module)
  (declare (type module module)
	   (values list))
  (setf (module-beh-stuff module) nil)	; reset to initial.
  (let ((methods (module-beh-methods module))
	(attributes (module-beh-attributes module)))
    (declare (type list methods attributes))
    (unless (and attributes
		 (or (some #'(lambda (x) (eq module (method-module x)))
			   methods)
		     (some #'(lambda (x) (eq module (method-module x)))
			   attributes)))
      (return-from construct-beh-stuff nil))
    ;; 
    (let ((beh-list nil)
	  (beh nil))
      (declare (type list beh-list))
      (dolist (s (module-all-sorts module))
	(when (and (sort-is-hidden s)
		   (not (or (sort= s *huniversal-sort*)
			    (sort= s *hbottom-sort*))))
	  (setq beh (make-beh-stuff :hs s))
	  ;; 
	  (dolist (m methods)
	    (let ((c (find-if #'(lambda (x) (sort-is-hidden x)) (method-arity m))))
	      (when (sort= c s)
		(push m (beh-stuff-methods beh)))))
	  ;;
	  (dolist (attr attributes)
	    (let ((as (dolist (x (method-arity attr))
			(when (sort-is-hidden x) (return x)))))
	      (when (sort= as s)
		(push attr (beh-stuff-attributes beh)))))
	  ;;
	  (when (beh-stuff-attributes beh)
	    (push beh beh-list))

	  #||
	  (if (or (null (beh-stuff-methods beh))
		  (null (beh-stuff-attributes beh)))
	      (progn
		(unless (beh-stuff-methods beh)
		  (with-output-chaos-warning ()
		    (princ "there are no methods defined on hidden sort ")
		    (print-sort-name s module)))
		(unless (beh-stuff-attributes beh)
		  (with-output-chaos-warning ()
		    (princ "there are no attributes defined on hidden sort ")
		    (print-sort-name s module))))
	      (push beh beh-list))
	  ||#
	  ))
      ;;
      (add-beh-equivalence module beh-list)
      ;;
      (setf (module-beh-stuff module) beh-list))))
  
(defun add-beh-equivalence (module beh-list)
  (declare (type module module)
	   (type list beh-list)
	   (values t))
  ;;
  ;; for each hidden sort with its methods/attributes
  ;;
  (dolist (hma beh-list)
    (let ((hs (beh-stuff-hs hma))	; hidden sort
	  (methods (beh-stuff-methods hma)) ; methods
	  (attributes (beh-stuff-attributes hma)) ; attributes
	  (var-num 0)
	  cond
	  hvars
	  pvars
	  (th-rhs-args nil)
	  hs-pos
	  lhs-args
	  rhs-args
	  lhs
	  rhs
	  ax)
      (declare (type fixnum var-num))
      ;;
      (setq hvars (list (make-variable-term hs '|hs1|)
			(make-variable-term hs '|hs2|)))
      (setq pvars (list (make-pvariable-term hs '|`phs-1|)
			  (make-pvariable-term hs '|`phs-2|)))
      #||
      (setq pvars (list (make-variable-term hs '|phs-1|)
			(make-variable-term hs '|phs-2|)))
      ||#
      ;; cond (hs1 =*= hs2)
      (setq cond (make-term-with-sort-check *beh-equal* hvars))
      ;;
      (dolist (attr attributes)
	(let ((arity (method-arity attr)))
	  ;; first, make general axiom for each attributes.
	  ;; ceq attr(t,d) = attr(t',d) if t =*= t'.
	  ;; *NOTE* This is redundant, seems useless.
	  ;;        we omit this now. Mon Mar  9 23:05:16 JST 1998
	  ;;
	  (setq hs-pos (position-if #'(lambda (x) (sort-is-hidden x))
				    arity))
	  (setq lhs-args
		(mapcar #'(lambda (x)
			    (if (sort-is-hidden x)
				(car hvars)
				(make-variable-term x
						    (intern (format nil
								    "vs~D"
								    (incf
								     var-num))))
				))
			arity))
	  (setq rhs-args (copy-list lhs-args))
	  (setf (nth hs-pos rhs-args) (cadr hvars))
	  ;; lhs : attr(t,d)
	  (setq lhs (make-term-with-sort-check attr lhs-args))
	  ;; rhs : attr(t',d)
	  (setq rhs (make-term-with-sort-check attr rhs-args))
	  ;; ax  : ceq attr(t,d) = attr(t',d) if t =*= t'.
	  ;; *NOTE* we don't introduce this now, see the above note.
	  #||--------------------omit-------------------
	  (setq ax
		(check-axiom-error-method module
					  (make-rule :lhs lhs
						     :rhs rhs
						     :condition cond
						     :type ':equation
						     ;; :kind ':beh-equiv
						     )))
	  ;; we can always introcude this axiom.
	  (adjoin-axiom-to-module module ax)
	  (push ax (beh-stuff-axioms hma))
	  -----------------------omit------------------ ||#
	  ;;
	  ;; make assumption used for prove congruence relation at the later stage.
	  ;; eq attr(t,d) = attr(t',d)
	  ;; NOTE: uses psuedo constants.
	  ;;
	  (push (list lhs rhs) th-rhs-args)
	  (setq lhs-args
		(mapcar #'(lambda (x)
			    (if (sort-is-hidden x)
				(car pvars)
			      (make-pvariable-term x
						   (intern (format nil
								     "`pvs~D"
								     (incf var-num)))
						     )
			      #||
			      (make-variable-term x
						  (intern (format nil
								  "vs~D"
								  (incf var-num))))
			      ||#
			      ))
			arity))
	  (setf rhs-args (copy-list lhs-args))
	  (setf (nth hs-pos rhs-args) (cadr pvars))
	  (setq lhs (make-term-with-sort-check attr lhs-args))
	  (setq rhs (make-term-with-sort-check attr rhs-args))
	  (setq ax
		(check-axiom-error-method module
					  (make-rule :lhs lhs
						     :rhs rhs
						     :condition *bool-true*
						     :type ':equation
						     :kind ':beh-equiv-assumpt)))
	  (push ax (beh-stuff-assumptions hma))

	  ))
      ;;
      ;; make theorem to be proved
      ;;

      ;; ceq t =*= t' = true if attr(t,d) == attr(t',d) and ...
      ;;
      (when attributes
	(setq rhs			; conjunction of each attr(t,d) == attr(t',d).
	      (reduce #'(lambda (x y)
			  (make-term-with-sort-check *bool-and*
						     (list x y)))
		      (mapcar #'(lambda (z)
				  (make-term-with-sort-check *bool-equal* z))
			      th-rhs-args)))
	(setq ax
	      (check-axiom-error-method module
					(make-rule :lhs cond
						   :rhs *bool-true*
						   :condition rhs ; *bool-true*
						   :type ':equation
						   ;; :kind ':beh-equiv-theorem
						   )))
	(setf (beh-stuff-theorem hma) ax)	
	)
      ;; make terms to be evaluated to true in proof.
      (when methods
	;; for each methods
	(dolist (bmeth methods)
	  (let* ((marity (method-arity bmeth))
		 (mhpos (position-if #'(lambda (x) (sort-is-hidden x)) marity)))
	    (setq lhs-args
		  (mapcar #'(lambda (x)
			      (if (sort-is-hidden x)
				  (car pvars)
				(make-pvariable-term x
				(intern (format nil
								       "`bpvs~D"
								       (incf
									var-num))))
				#||
				(make-variable-term x
						    (intern (format nil
								    "bvs~D"
								    (incf
								     var-num))))
				||#
				))
			  marity))
	    (setq rhs-args (copy-list lhs-args))
	    (setf (nth mhpos rhs-args) (cadr pvars))
	    (Setq lhs (make-term-with-sort-check bmeth lhs-args))
	    (setq rhs (make-term-with-sort-check bmeth rhs-args))
	    (push (make-term-with-sort-check *beh-equal* (list lhs rhs))
		  (beh-stuff-targets hma)))))
      )))

;;;
;;; now defined in globals.lisp
;;; (declaim (special *beh-proof-in-progress*))
;;; (defvar *beh-proof-in-progress* nil)

#||
(let ((.beh-proof-mod-num. 0))
  (defun make-beh-proof-mod-name ()
    ;; (format nil " % % -~d" (incf .beh-proof-mod-num.))
    " % % " ))
||#

(defun make-beh-proof-mod-name () " % % " )

(defmacro dont-believe-=*=-proof ()
  `(and *used==* (not *accept-system-proof*)))

(defun try-beh-proof-in (module)
  (unless (module-beh-stuff module)
    (return-from try-beh-proof-in nil))
  (unless (eq module *top-level-definition-in-progress*)
    (return-from try-beh-proof-in nil))
  (when *beh-proof-in-progress* (return-from try-beh-proof-in nil))
  (let ((proved nil)
	(fail nil)
	(*beh-proof-in-progress* t)
	(*auto-context-change* nil)
	(*used==* nil))
    (declare (special *auto-context-change*)
	     (special *used==*))
    ;; first open the module
    (let* ((proof-mod-nam (normalize-modexp (make-beh-proof-mod-name)))
	   (proof-mod (let ((*chaos-quiet* t))
			(create-renamed-module module proof-mod-nam))))
      (setf (module-type proof-mod) :system)
      ;; ** strong assumption **
      ;; opened module is compiled & has just the same beh-to-be-proved!!!!
      (with-in-module (proof-mod)
	(let ((ths (module-beh-stuff proof-mod)))
	  (declare (type list ths))
	  ;; for each beh-stuff
	  (dotimes (t-pos (length ths))
	    (declare (type fixnum t-pos))
	    (let ((th (nth t-pos ths)))
	      (when (beh-stuff-theorem th)
		(let ((*chaos-quiet* t)
		      (*chaos-verbose* nil))
		  (declare (special *chaos-verbose* *chaos-quiet*))
		  ;; add theorem
		  (adjoin-axiom-to-module proof-mod
					  (check-axiom-error-method
					   proof-mod
					   (beh-stuff-theorem th)))
		  (dolist (as (beh-stuff-assumptions th))
		    (adjoin-axiom-to-module proof-mod
					    (check-axiom-error-method
					     proof-mod
					     as)))
		  (set-needs-rule proof-mod)
		  (compile-module proof-mod)
		  )
		;;
		(when *chaos-verbose*
		  (with-output-simple-msg ()
		    (format t "~&>> start trial proof : ")
		    (print-chaos-object (beh-stuff-theorem th))
		    (print-next)
		    (princ "* bases : ")
		    (dolist (as (beh-stuff-assumptions th))
		      (print-next)
		      (print-chaos-object as))
		    (force-output)))
		;; try proof
		(let ((failed nil))
		  (dolist (tm (beh-stuff-targets th))
		    (when *chaos-verbose*
		      (with-output-simple-msg ()
			(print-next)
			(princ "* case : ")
			(print-chaos-object tm)
			(force-output)))
		    ;; do the proof
		    (beh-rewrite tm proof-mod)
		    ;;
		    (when *chaos-verbose*
		      (print-next)
		      (princ "    -> ") (term-print tm))
		    (unless (is-true? tm)
		      (setq failed t)
		      (when *chaos-verbose*
			(with-output-simple-msg ()
			  (print-next)
			  (princ "==> fail!")))
		      (return))
		    (when *chaos-verbose*
		      (with-output-simple-msg ()
			(print-next)
			(princ "==> success!")))
		    )
		  (if failed
		      (progn (setq fail t) (return))
		    (push t-pos proved))
		  )))
	    ;; done for a beh-stuff
	    )
	  ;; done for each beh-stuff
	  ))
      (clean-up-module proof-mod)		; dont need no more 
      ;; 
      ;; (eval-close-module)
      )
    ;; we assert proved theorem in module
    (let ((real-ths (module-beh-stuff module)))
      (if fail
	  (with-output-simple-msg ()
	    (format t "~&** system failed to prove =*= is a congruence of ")
	    (print-mod-name module *standard-output* t t))
	  (with-in-module (module)
	    (with-output-simple-msg ()
              (if (dont-believe-=*=-proof)
		  (format t "~&** system judged \"=*=\" is a congruence of ")
		(format t "~&** system already proved \"=*=\" is a congruence of "))
	      (print-mod-name module *standard-output* t t)
	      (print-next)
	      ;;
	      (when (dont-believe-=*=-proof)
		(princ "** NOTE: in the proof process, an equality")
		(print-next)
		(princ " test (== or =/= with variable/constant on one side)")
		(print-next)
		(princ " was performed. Because system does not run case analysis,")
		(print-next)
		(princ " this judgement can be wrong.")
		(print-next)
		(princ " Please look into the proof process by loading ")
		(print-mod-name module *standard-output* t t)
		(princ " again")
		(print-next)
		(princ " after the two commands of")
		(print-next)
		(princ "     set verbose on ")
		(print-next)
		(princ "     set trace whole on ")
		(print-next)
		(princ " If you are sure that the proof is correct,")
		(print-next)
		(princ " you can add the following axiom(s):")))
	    (dolist (pos proved)
	      (let ((th (nth pos real-ths)))
		(when (or *chaos-verbose* *used==*)
		  (with-output-simple-msg ()
		    (if (not (dont-believe-=*=-proof))
			(format t "~&>> adding axiom : ")
		      (format t "~&ceq "))
		    (print-chaos-object (beh-stuff-theorem th))
		    (princ " . ")))
		(print-next)
		(unless (dont-believe-=*=-proof)
		  (adjoin-axiom-to-module module
					  (check-axiom-error-method
					   module
					   (beh-stuff-theorem th)))
		  )
		))
	    (set-needs-rule module)
	    )))
    ))

(defun beh-rewrite (term mod)
  (let (($$term term)
	(*rule-count* 0)
	(*perform-on-demand-reduction* t)
	(*rewrite-semantic-reduce* (module-has-behavioural-axioms mod)))
    (declare (special $$term)
	     (special *rewrite-semantic-reduce*))
    (rewrite term mod)))

;;; EOF
