;;;-*-Mode:LISP; Package: CHAOS; Base:10; Syntax:Common-lisp -*-
;;; $Id: tram.lisp,v 1.4 2010-08-04 04:37:34 sawada Exp $
(in-package :chaos)
#|=============================================================================
			     System:CHAOS
			     Module:tram
			    File:tram.lisp
=============================================================================|#
#-:chaos-debug
(declaim (optimize (speed 3) (safety 1) #-GCL (debug 1)))
#+:chaos-debug
(declaim (optimize (speed 1) (safety 3) #-GCL (debug 3)))

#+:allegro
(declaim (optimize (speed 1) (safety 3)))
	 
;;; TRAM INTERFACE ============================================================

(defvar *tram-last-module* nil)

;;; ******************
;;; INTERPROCESS COMM.         ________________________________________________
;;; ******************

(declaim (special *tram-process*))
(defvar *tram-process* nil)		; pair (in-stream . out-stream)

;;; debug flags
;;; (defvar *on-tram-debug* nil)

(defun on-tram-debug ()
  (setq *on-tram-debug* t))

(defun off-tram-debug ()
  (setq *tram-process* nil)
  (setq *on-tram-debug* nil))

;;;
(defvar *tram_in_file* nil)
(defvar *tram_out_file* nil)

(defun run-tram-process-if-need ()
  (unless *tram-process*
    (run-tram-process)))

#+:GCL
(defun get-process-id () (si::getpid))

#+:CMU
(defun get-process-id () (unix::unix-getpid))

#+(or :Excl :allegro)
(defun get-process-id () (random (get-universal-time)))

#+:CLISP
(defun get-process-id () (random (get-universal-time)))

#-(or :GCL :CMU :Excl :allegro CLISP)
(defun get-process-id () ())

(defun tram-get-id (prefix)
  (concatenate 'string
	       (the simple-string (string prefix))
	       (the simple-string (format nil "~d" (get-process-id)))))

(defun run-tram-process ()
  (declare (optimize (safety 2) #-GCL (debug 2)))
  ;;
  (when *tram-process*
    (kill-tram-process))
  (setq *tram-process* nil)
  ;;
  (when *on-tram-debug*
    (setq *tram-process* (cons *standard-input* *standard-output*))
    (return-from run-tram-process t))
  (let ((in-file (tram-get-id "/tmp/from-tram"))
	(out-file (tram-get-id "/tmp/to-tram"))
	(in-stream nil)
	(out-stream nil))
    ;; invoke compiler
    ;; *tram-path*    : path to tram compiler
    ;;                  set by `set tram path' command, default "tram".
    ;; *tram-options* : other optional arguments
    ;;                  set by `set tram options', default "".
    (unless #+:GCL (zerop
		    (si::system (concatenate 'string
					     *tram-path*
					     " "
					     *tram-options*
					     (format nil
						     " -server ~a ~a"
						     out-file in-file))))
	    #+:CMU (ext:run-program
		    *tram-path*
		    (if (equal *tram-options* "")
			(list "-server" out-file in-file)
			(list "-server" out-file in-file *tram-options* ))
		    :input t
		    :output t
		    )
	    #+(or :EXCL :allegro)
	    (zerop
	     (excl:shell (concatenate 'string
				      *tram-path*
				      " "
				      *tram-options*
				      (format nil
					      " -server ~a ~a"
					      out-file in-file))))
	    #+CLISP (null
		     (ext::shell (concatenate 'string
				   *tram-path*
				   " "
				   *tram-options*
				   (format nil
					   " -server ~a ~a"
					   out-file in-file)))) 
	    #+MCL nil
	    ;;
	    (with-output-chaos-error ('tram-fail)
	      (format t "failed to invoke TRAM compiler")
	      (when *last-module*
		(context-pop-and-recover))
	      ))

    ;;
    (setq *tram_in_file* in-file
	  *tram_out_file* out-file)
    
    #||
    ;; wait for a while untill i/o files are prepared
    (dotimes (x 30)
      x
      (sleep 1)
      (when (probe-file in-file) (return nil)))
     ||#

    ;; try open streams
    (setq out-stream (open out-file
			   :direction :output
			   :if-does-not-exist nil
			   :if-exists :overwrite))
    (setq in-stream (open in-file :direction :input :if-does-not-exist nil))
    ;;
    ;;
    (unless (and in-stream out-stream)
      (with-output-chaos-error ('tram-fail)
	(format t "failed to open TRAM I/O streams")
	(when *last-module*
	  (context-pop-and-recover))
	))
    (setq *tram-process* (cons in-stream out-stream))
    ))

(defun kill-tram-process ()
  (setq *tram-last-module* nil)
  (if *on-tram-debug*
      (setq *tram-process* nil)
      ;; this will terminate TRAM compiler (I hope).
      (progn
	(unless (eq (car *tram-process*) *standard-input*)
	  (when (car *tram-process*)
	    (close (car *tram-process*))))
	(unless (eq (cdr *tram-process*) *standard-output*)
	  (when (cdr *tram-process*)
	    (close (cdr *tram-process*))))
	(setq *tram-process* nil))))

;;;
;;; body is executed with *standard-output* bound to output stream.
;;; 
(defmacro with-output-to-tram ((ignore) &body body)
  ` (let ((*standard-output* (cdr *tram-process*)))
      (prog1
	  (progn ,@body)
	(force-output *standard-output*))))

;;; send simple string then wait the answer.
;;; used for `compile', `reduce'.
(defparameter tram-eof-value :tram-eof)

(defmacro tram-send-and-wait (tram send-form)
  ` (progn
      (princ ,send-form (cdr ,tram))
      (terpri (cdr ,tram))
      (force-output (cdr ,tram))
      (wait-tram-answer ,tram)
      ))

(defun wait-tram-answer (&optional (tram *tram-process*))
  (when *on-tram-debug*
    (fresh-line)
    (princ "INPUT TRAM ANSWER> ")
    (force-output)
    (return-from wait-tram-answer (read)))
  ;;
  (let ((res nil)
	(limit 120))			; 120 sec would be enough.
    (declare (ignore limit))
    #||
    ;; wait untill some input comes
    (loop
     ;; `listen' could be used here, but I'm not sure that
     ;; GCL recognizes named pipes are interactive streams...
     (sleep 1)
     (decf limit)
     (when (<= limit 0)
       (return-from wait-tram-answer nil))
     ;;
     (let ((val (peek-char nil (car tram) nil tram-eof-value)))
       (unless (eq val tram-eof-value) (return nil))))
    ;;
    ||#
    (setq res (read (car tram) nil tram-eof-value))
    (if (eq res tram-eof-value)
	nil
	res)))

;;; --------
;;; BUILT-IN
;;; --------

;;; ----
;;; TERM
;;; ----

(defun trs-term-to-tram-term (term)
  (if term
      (case (trs-term-type term)
	(:var (trs-term-head term))
	(:builtin-value term)
	(:lisp term)
	(:glisp term)
	(:op (cons (trs-term-head term)
		   (mapcar #'(lambda (sub)
			       (trs-term-to-tram-term sub))
			   (trs-term-subterms term)))))
      nil))

;;;
(defun tram-term-to-chaos (trs tram-term)
  (let ((res nil))
    (with-in-module ((trs$module trs))
      (cond ((consp tram-term)
	     (case (car tram-term)
	       (:builtin-value		; built-in constant
		(make-bconst-term (map-trs-sort-to-chaos (third tram-term)
							 trs)
				  (second tram-term)))
	       (otherwise
		;; application form
		(let ((op-name (car tram-term)))
		  (let ((hd (trs-rev-op-name op-name trs))
			(*consider-object* nil)
			(subs nil))
		    (dolist (s (cdr tram-term))
		      (push (tram-term-to-chaos trs s) subs))
		    (setq res (make-applform-simple (method-coarity hd)
						    hd
						    (nreverse subs)))
		    (update-lowest-parse res)
		    res)))))
	    (t (with-output-panic-message ()
		 (format t "Unkonwn TRAM term ~s is returned.~
~%  This can happen if signature is not regular..."
			 tram-term)
		 (when *last-module*
		   (context-pop-and-recover))
		 (chaos-error 'tram-panic)))))))

;;; construct token sequence of term tram-term in a form
;;; suitable for parsing in Chaos term parser.
;;;
(defun tram-make-term-tok-seq (trs tram-term)
  (with-in-module ((trs$module trs))
    (re-make-tram-tok-seq trs tram-term)))

(defun re-make-tram-tok-seq (trs tram-term)
  ;; we assume terms of list forms are operator application form,
  ;; atoms are builtin constants.
  (let ((res nil))
    (cond ((consp tram-term)
	   ;; application form
	   (let ((op-name (car tram-term)))
	     (let ((hd (trs-rev-op-name op-name trs))
		   (op nil))
	       (setq op (method-operator hd))
	       (cond ((not (operator-is-mixfix op))
		      (let ((subs (cdr tram-term)))
			(dolist (sym (operator-symbol op))
			  (push (string sym) res))
			(if subs
			    (progn
			      (push "(" res)
			      (let ((flg nil))
				(dolist (i subs)
				  (if flg (push "," res) (setq flg t))
				  (dolist (s (re-make-tram-tok-seq trs i))
				    (push s res)))
				(push ")" res))
			      #||
			      (setq res (nconc (nreverse res)
					       (flatten-list (nreverse args))
					       (list ")")))
			      ||#
			      (setq res (nreverse res)))
			    res)))
		     (t (let ((subs (cdr tram-term)))
			  (push "(" res)
			  (dolist (i (operator-token-sequence op))
			    ;; (when prv (push " " res))
			    ;; (setq prv t)
			    (cond ((eq i t)
				   (dolist (s (re-make-tram-tok-seq trs (car subs)))
				     (push s res))
				   (setq subs (cdr subs)))
				  (t (push i res))))
			  (push ")" res)
			  (nreverse res)))))))
	  (t tram-term))))

;;; construct form of term as string
;;;
(defun tram-re-make-term-form (trs tram-term)
  (with-in-module ((trs$module trs))
    (with-output-to-string (str)
      (let ((*standard-output* str))
	(re-print-tram-term trs tram-term)
	str))))

(defun re-print-tram-term (trs tram-term)
  ;; we assume terms of list forms are operator application form,
  ;; atoms are builtin constants.
  (cond ((consp tram-term)
	 ;; application form
	 (let ((op-name (car tram-term)))
	   (let ((hd (trs-rev-op-name op-name trs))
		 (op nil))
	     (setq op (method-operator hd))
	     (cond ((not (operator-is-mixfix op))
		    (let ((subs (cdr tram-term)))
		      (format t "~{~a~^ ~}" (operator-symbol op))
		      (when subs
			(princ "(")
			(let ((flg nil))
			  (dolist (i subs)
			    (if flg (princ ",") (setq flg t))
			    (re-print-tram-term trs i)))
			(princ ")"))))
		   (t (let ((subs (cdr tram-term))
			    (prv nil))
			(princ "(")
			(dolist (i (operator-token-sequence op))
			  (if (null prv)
			      (setq prv t)
			      (princ " "))
			  (cond ((eq i t)
				 (re-print-tram-term trs (car subs))
				 (setq subs (cdr subs)))
				(t (princ i))))
			(princ ")")))))))
	(t (princ tram-term))))

;;; ------
;;; AXIOMS
;;;-------

;;;
;;; MAKE-TRAM-RULES
;;;

(defun make-tram-rules (trs &optional all)
  (let ((rules nil)
	(mod (trs$module trs))
	(*module-all-rules-every* t))
    (declare (special *module-all-rules-every*))
    (with-in-module (mod)
      (let ((own-axs (module-own-axioms-ordered mod nil))
	    (imp-axs (module-imported-axioms mod nil)))
	  (dolist (x own-axs)
	    (when (or (memq (axiom-type x)
			    '(:equation :pignose-axiom :pignose-goal))
		      all)
	      (let ((rule (make-tram-rule x trs)))
		(when rule (push rule rules)))))
	  (dolist (x imp-axs)
	    (when (or (memq (axiom-type x)
			    '(:equation :pignose-axiom :pignose-goal))
		      all)
	      (let ((rule (make-tram-rule x trs)))
		(when rule (push rule rules)))))))
    (nreverse rules)))

(defvar *tram-inhibit-rwl-predicates* nil)

(defun make-tram-rule (ax trs)
  (when (rule-is-builtin ax)
    (return-from make-tram-rule nil))
  (unless (term-is-applform? (axiom-lhs ax))
    (return-from make-tram-rule nil))
  (let ((lhs-top (term-head (axiom-lhs ax))))
    #||
    (when (memq (method-module lhs-top) *tram-builtin-modules*)
      (return-from make-tram-rule nil))
    (when (or (eq lhs-top *bool-if*)
	      (eq lhs-top *bool-equal*)
	      (eq lhs-top *beh-eq-pred*)
	      (eq lhs-top *bool-nonequal*)
	      (when *tram-inhibit-rwl-predicates*
		(or (eq lhs-top *rwl-predicate*)
		    (eq lhs-top *rwl-predicate2*)))
	      )
      (return-from make-tram-rule nil))
    ||#
    ;; NAT INT, STRING etc...
    (let ((rhs (axiom-rhs ax)))
      (when (term-is-lisp-form? rhs)
	(return-from make-tram-rule nil)))
    (when (eq lhs-top *bool-if*)
      (return-from make-tram-rule nil))
    ;;
    ;;
    (when (eq lhs-top *rwl-predicate*)
      (when (some #'(lambda (x)
		      (or (sort= x *cosmos*)
			  (sort= x *universal-sort*)
			  (sort= x *huniversal-sort*)))
		  (mapcar #'(lambda (x) (term-sort x))
			  (term-subterms (axiom-lhs ax))))
	(return-from make-tram-rule nil)))
    ;;
    (trs-rule-to-tram-rule (get-trs-axiom ax trs))))

(defun trs-rule-to-tram-rule (rule)
  (let ((lhs (trs-term-to-tram-term (trs-axiom-lhs rule)))
	(rhs (trs-term-to-tram-term (trs-axiom-rhs rule)))
	(cond (trs-term-to-tram-term (trs-axiom-condition rule)))
	(vars (mapcar #'(lambda (x)
			  (list (trs-term-head x)
				(trs-term-sort x)))
		      (trs-term-variables (trs-axiom-lhs rule)))))
    (list* vars
	   lhs
	   rhs
	   (if cond
	       (list `((,cond (|true/0|))))
	       nil))
    ))

(defun tram-make-sem-axioms (trs)
  (let ((axs nil))
    (dolist (x (trs$sem-axioms trs))
      (let ((ax (trs-rule-to-tram-rule (get-trs-axiom x trs))))
	(when ax (push ax axs))))
    (nreverse axs)))

(defun make-tram-term (term trs)
  (cond ((term-is-variable? term) (variable-name term))
	((term-is-builtin-constant? term)
	 (list ':builtin-value (term-builtin-value term)
	       (map-chaos-sort-to-trs-or-panic (term-sort term) trs)))
	((term-is-simple-lisp-form? term)
	 (list ':lisp (lisp-form-original-form term)))
	((term-is-general-lisp-form? term)
	 (list ':glisp (lisp-form-original-form term)))
	((term-is-application-form? term)
	 (let ((head (term-head term)))
	   (let ((name (map-chaos-op-to-trs head trs)))
	     (unless name
	       (break "PANIC!!!!!!!! ~s" (method-symbol head))
	       ) ; this should not happen.
	     ;;
	     (cons name (mapcar #'(lambda (sub)
				    (make-tram-term sub trs))
				(term-subterms term))))))))

;;;*****************************************************************************
;;; BUILT-IN-OPERATORS
;;;-----------------------------------------------------------------------------
(defparameter tram-bool-sort-name (make-trs-sort-name *bool-sort*))
(defun tram-?bool-sort-name (so)
  (make-trs-sort-name (the-err-sort *bool-sort* so)))

(defparameter tram-sort-id-sort-name (make-trs-sort-name *sort-id-sort*))
(defun tram-?sort-id-sort-name (so)
  (make-trs-sort-name (the-err-sort *sort-id-sort* so)))

;;; ---------------
;;; if-then-else-fi
;;; ---------------
(defparameter tram-if-then-else-op-template
  `(|if_then_else_fi| (dummy sort sort) sort (1 0)))

;;;--------------------------
;;; sort membership predicate
;;; _:_
;;;--------------------------
(defparameter tram-sort-memb-op-template
  `(|_:is_| (sort ,tram-sort-id-sort-name) ,tram-bool-sort-name (1 2 0))
  ;; `(|_:_| (sort ,tram-sort-id-sort-name) ,tram-bool-sort-name (1 2 0))
  )

;;; ------------------
;;; SEMANTIC-RELATIONS
;;; ------------------
(defparameter tram-equal-op-template
  `(|_==_| (sort sort) ,tram-bool-sort-name (1 2 0)))

(defparameter tram-nequal-op-template
  `(|_=/=_| (sort sort) ,tram-bool-sort-name (1 2 0)))

(defparameter tram-bequal-op-template
  `(|_=b=_| (sort sort) ,tram-bool-sort-name (1 2 0)))

(defparameter tram-rwl-trans-op-template
  `(|_==>_| (sort sort) ,tram-bool-sort-name (1 2 0)))

(defparameter tram-rwl-aux-trans-op-template
  `(|_=\\(_\\)=>_| (sort |?Nat*.RWL| sort) ,tram-bool-sort-name (2 0)))

;;; ------
;;; EQUALS
;;; ------

(defparameter xif-op-template
  `(|!if| (,tram-bool-sort-name) ,tram-bool-sort-name (1 0)))

(defparameter eq-op-template
  `(|==-aux| (sort sort) ,tram-bool-sort-name (1 2 0)))

(defparameter neq-op-template
  `(|=/=-aux| (sort sort) ,tram-bool-sort-name (1 2 0)))

;;;
;;; MAKE BUILT-IN OPERATORS
;;;

(defun tram-make-built-in-operators (trs)
  (let* ((error-sorts (get-trs-error-sorts trs))
	 (mod (trs$module trs))
	 (so (module-sort-order mod))
	 (rwl? (or (eq mod *rwl-module*)
		   (module-includes-rwl mod)))
	(ops nil))
    ;; !if
    (push (copy-tree xif-op-template) ops)
    #|| redundant, only error operators are enougth.
    ;; if-then-else-fi for ordinal top sorts
    (dolist (sort (get-trs-top-sorts trs))
      (let ((if-then-op (copy-tree tram-if-then-else-op-template))
	    (sort-name (map-chaos-sort-to-trs-or-panic sort trs)))
	(setf (second if-then-op) (list (tram-?bool-sort-name so)
					sort-name
					sort-name))
	(setf (third if-then-op) sort-name)
	(push if-then-op ops)))
    ||#
    ;; internal equality procs.
    (dolist (sort error-sorts ops)
      (let* ((if-then-op (copy-tree tram-if-then-else-op-template))
	     (sort-memb-op (copy-tree tram-sort-memb-op-template))
	     (equal-op (copy-tree tram-equal-op-template))
	     (nequal-op (copy-tree tram-nequal-op-template))
	     (bequal-op (if (sort-is-hidden sort)
			    (copy-tree tram-bequal-op-template)
			    nil))
	     (trans-op (if rwl?
			   (copy-tree tram-rwl-trans-op-template)
			   nil))
	     (trans-aux-op (if rwl?
			       (copy-tree tram-rwl-aux-trans-op-template)
			       nil))
	     (eq-aux-op (copy-tree eq-op-template))
	     (neq-aux-op (copy-tree neq-op-template))
	     (sort-name (map-chaos-sort-to-trs-or-panic sort trs)))
	;; if-then-else-fi
	(setf (second if-then-op)
	      (list (tram-?bool-sort-name so) sort-name sort-name)
	      (third if-then-op)
	      sort-name)
	(push if-then-op ops)
	;; sort membership; must consider renaming of builtin sorts
	;; TODO.
	(setf (second sort-memb-op) (list sort-name
					  tram-sort-id-sort-name))
	(push sort-memb-op ops)

	;; _==_
	(setf (second equal-op) (list sort-name sort-name))
	(push equal-op ops)
	;; _=/=_
	(setf (second nequal-op) (list sort-name sort-name))
	(push nequal-op ops)
	;; _=b=_
	(when bequal-op
	  (setf (second bequal-op) (list sort-name sort-name))
	  (push bequal-op ops))

	;; ==>
	(when trans-op
	  (setf (second trans-op) (list sort-name sort-name))
	  (push trans-op ops))
	;; =()=>
	(when trans-aux-op
	  (setf (second trans-aux-op)
		(list sort-name
		      (map-chaos-sort-to-trs-or-panic (the-err-sort
						       *rwl-nat-star-sort* so)
						      trs
						      t)
		      sort-name))
	  (push trans-aux-op ops))
	
	;; ==-aux
	(setf (second eq-aux-op)
	      (list sort-name sort-name))
	(push eq-aux-op ops)
	;; =/=-aux
	(setf (second neq-aux-op)
	      (list sort-name sort-name))
	(push neq-aux-op ops)))
    ))

(defun tram-make-built-in-axioms (trs)
  (let ((top-sorts (get-trs-error-sorts trs))
	(mod (trs$module trs))
	(axs nil))
    (push `(()
	    (|!if| (|true/0|))
	    (|true/0|)
	    )
	  axs)
    (push `(()
	    (|!if| (|false/0|))
	    (|false/0|)
	    )
	  axs)
    ;;
    (dolist (sort top-sorts)
      (let ((trs-sort (map-chaos-sort-to-trs-or-panic sort trs t)))
	;; if true then x else y fi
	(push ` (((X ,trs-sort) (Y ,trs-sort))
		 (|if_then_else_fi| (|true/0|) X Y)
		 X)
		axs)
	(push ` (((X ,trs-sort) (Y ,trs-sort))
		 (|if_then_else_fi| (|false/0|) X Y)
		 Y)
		axs)
	;; ==(X,Y) = !if(==-aux(X,Y))
	(push `(((X ,trs-sort) (Y ,trs-sort))
		(|_==_| X Y)
		(|!if| (|==-aux| X Y)))
	      axs)
	(when (sort-is-hidden sort)
	  ;; =b=(X,Y) = !if(==-aux(X,Y))
	  (push `(((X ,trs-sort) (Y ,trs-sort))
		  (|_=b=_| X Y)
		  (|!if| (|==-aux| X Y)))
		axs))
	;; ==-aux(X,Y) = true if X == Y
	(push `(((X ,trs-sort) (Y ,trs-sort))
		(|==-aux| X Y)
		(|true/0|)
		((X Y)))
	      axs)
	;; =/=(X,Y) = !if(=/=-aux(X,Y))
	(push `(((X ,trs-sort) (Y ,trs-sort))
		(|_=/=_| X Y)
		(|!if| (|=/=-aux| X Y)))
	      axs)
	;; =/=-aux(X,Y) = false if X == Y
	(push `(((X ,trs-sort) (Y ,trs-sort))
		(|=/=-aux| X Y)
		(|false/0|)
		((X Y)))
	      axs)
	;; !if(==-aux(X,Y)) = false
	(push `(((X ,trs-sort) (Y ,trs-sort))
		(|!if| (|==-aux| X Y))
		(|false/0|))
	      axs)
	;; !if(=/=-aux(X,Y)) = true
	(push `(((X ,trs-sort) (Y ,trs-sort))
		(|!if| (|=/=-aux| X Y))
		(|true/0|))
	      axs)
	(when (or (eq mod *rwl-module*)
		  (module-includes-rwl mod))
	  ;; X ==> X = true
	  (push `(((X ,trs-sort))
		  (|_==>_| X X)
		  (|true/0|))
		axs)
	  ;; X ==> Y = true if X =(*)=> Y
	  (push `(((X ,trs-sort) (Y ,trs-sort))
		  (|_==>_| X Y)
		  (|true/0|)
		  (((|_=\\(_\\)=>_| X (*/0) Y)
		    (|true/0|))))
		axs)
	  )
	))
    ;; simulates sort membership
    (dolist (sort (trs$sorts trs))
      (unless (memq (sort-module sort) *kernel-hard-wired-builtin-modules*)
	(let ((trs-sort (map-chaos-sort-to-trs-or-panic sort trs t)))
	  (push ` (((X ,trs-sort))
		   ;; (|_:_| X ,(make-sort-id-term sort))
		   (|_:is_| X ,(make-sort-id-term sort))
		   (|true/0|))
		  axs))))
    ;;
    axs))

(defun make-sort-id-term (sort)
  ;;   (setq sort (get-original-sort sort))	; <<<>>>
  (let ((id (string (sort-id sort)))
	(module (sort-module sort)))
    (if (or (eq module *rwl-module*)
	    (memq (sort-module sort) *tram-builtin-modules*))
	(list (intern (concatenate 'string id "/0")))
	(list (intern (concatenate 'string id "/0?SortId.CHAOS:PARSER"))))))

;;;
;;; TRAM-COMPILE-CHAOS-MODULE
;;;
(defun tram-compile-chaos-module (&optional all?
					    (module (or *current-module*
							*last-module*))
					    debug)
  ;;
  (unless debug (run-tram-process-if-need))
  ;;
  (compile-module module)
  ;;
  (let ((trs (get-module-trs module))
	(*print-circle* nil)
	(*print-case* :downcase)
	(*print-pretty* nil)
	;; (*print-escape* t)
	)
    ;; (declare (special *print-circle* *print-case* *print-pretty*))
    ;;
    (setq *tram-last-module* nil)
    ;;
    (with-output-to-tram (*tram-process*)
      (tram-send-initialize trs)
      (tram-send-use module)
      (tram-send-sort-decls trs)
      (tram-send-sort-relations trs)
      (tram-send-op-decls trs)
      (tram-send-built-in-ops trs)
      ;; (tram-send-sem-axioms trs)
      (tram-send-rule-decls trs all?)
      (tram-send-built-in-axioms trs))
    ;;
    (multiple-value-bind (res error)
	;; (tram-send-compile trs)
	(tram-send-compile)
      (unless error
	(if all?
	    (setf (trs$tram trs) :all)
	    (setf (trs$tram trs) :eq))
	(setq *tram-last-module* module)
	)
      (values res error))))

;;;
;;; TRAM-REDUCE
;;;
(defvar *tram-raw-res* nil)
(defun tram-reduce (mod pre-term &optional all)
  (let ((term nil)
	(error nil))
    (compile-module mod)
    (with-in-module (mod)
      (let ((*parse-variables* nil))
	(setq term (simple-parse mod pre-term *cosmos*))
	(when (or (null (term-sort term))
		  (sort<= (term-sort term)
			  *syntax-err-sort*
			  *chaos-sort-order*))
	  (chaos-error 'syntax-error))
	;;
	(unless *chaos-quiet*
	  (fresh-line)
	  (if all
	      (princ "-- execute in ")
	      (princ "-- reduce in "))
	  (print-mod-name mod)
	  (princ " : ")
	  (let ((*print-indent* (+ 4 *print-indent*)))
	    (term-print term))
	  (force-output))
	))
    ;;
    (let ((trs (get-module-trs mod))
	  (exec? nil)
	  (need-compile? nil))
      ;; compile module if need
      (unless (eq *tram-last-module* mod)
	(setq need-compile? t))
      (case (trs$tram trs)
	(:all (unless all
		(setq exec? nil)
		(setq need-compile? t)))
	(:eq (when all
	       (setq exec? t)
	       (setq need-compile? t)))
	(otherwise
	 (setq exec? all)
	 (setq need-compile? t)))
      (when need-compile?
	(multiple-value-bind (comp-res err)
	    (tram-compile-chaos-module exec? mod)
	  (when err
	    (return-from tram-reduce
	      (values comp-res :error-on-compile)))
	  ))
      ;; send reduce
      (multiple-value-setq (*tram-raw-res* error)
	(tram-send-reduce term trs))
      ;; (setq res (tram-re-make-term-form trs raw-res))
      ;; (setq res (tram-make-term-tok-seq trs raw-res))
      (if error
	  (values *tram-raw-res* :error-on-reduce)
	  (values (list (tram-term-to-chaos trs (car *tram-raw-res*))
			(cadr *tram-raw-res*))
		  nil))
      )))

;;; **********************
;;; TRAM COMPILER COMMANDS
;;; **********************

(defparameter _tram_init_command_ '(|init|))
(defparameter _tram_use_command_ '|use|)
(defparameter _tram_sort_decl_command_ '|sort|)
(defparameter _tram_sort_order_decl_command_ '|sort-order|)
(defparameter _tram_op_decl_command_ '|op|)
(defparameter _tram_rule_decl_command_ '|rule|)
(defparameter _tram_compile_command_ '(|compile|))
(defparameter _tram_reduce_command_ '|reduce|)

;;;
;;; followings assume called in the body of 
;;; `with-output-to-tram'
;;;

(defun tram-send-initialize (&rest ignore)
  (declare (ignore ignore))
  (princ _tram_init_command_)
  (terpri)				; just for now readability reason
  )

(defun tram-send-use (module)
  (let ((const-modules (cons (cons module :dummy)
			     (get-module-dependency module))))
    (let ((use-modules nil))
      ;; check NUMBER family
      (cond ((assq *z-float* const-modules)
	     (push *z-float* use-modules))
	    ((assq *z-float-value* const-modules)
	     (push *z-float-value* const-modules)))
      ;; 
      (cond ((assq *z-rat* const-modules)
	     (push *z-rat* use-modules))
	    ((assq *z-int* const-modules)
	     (push *z-int* use-modules))
	    ((assq *z-nat* const-modules)
	     (push *z-nat* use-modules))
	    ((assq *z-nznat* const-modules)
	     (push *z-nznat* use-modules))
	    ((assq *z-rat-value* const-modules)
	     (push *z-rat-value* const-modules))
	    ((assq *z-int-value* const-modules)
	     (push *z-int-value* use-modules))
	    ((assq *z-nat-value* const-modules)
	     (push *z-nat-value* use-modules))
	    ((assq *z-nznat-value* const-modules)
	     (setq *z-nznat-value* use-modules)))
      ;; check CHARACTER family
      (cond ((assq *z-char* const-modules)
	     (push *z-char* use-modules))
	    ((assq *z-char-value* const-modules)
	     (push *z-char-value* use-modules)))
      ;; check QID
      ;; we simulates Identifier by using brute built-in QID also.
      (when (or (assq *z-qid* const-modules)
		(assq *identifier-module* const-modules))
	(push *z-qid* use-modules))

      ;; check STRING
      (when (assq *z-string* const-modules)
	(push *z-string* use-modules))
      (dolist (x (nreverse use-modules))
	(format t "(~a ~a)" _tram_use_command_ (module-name x))
	(terpri))
      )))

(defun tram-send-sort-decls (trs)
  (format t "(~a ~{~s~^ ~})" _tram_sort_decl_command_
	  (mapcar #'cdr
		  (remove-if #'(lambda (x)
				 (and (not (err-sort-p (car x)))
				      (memq (sort-module (car x))
					    *tram-builtin-modules*)))
			     (trs$sort-name-map trs)))))

(defun tram-send-sort-relations (trs)
  (when (trs$sort-graph trs)
    (let ((real-graph nil)
	  )
      (setq real-graph
	    (remove-if #'(lambda (x)
			   (and (memq (sort-module (map-trs-sort-to-chaos (car x) trs))
				      *tram-builtin-modules*)
				(memq (sort-module (map-trs-sort-to-chaos (cadr x) trs))
				      *tram-builtin-modules*)))
		       (trs$sort-graph trs)))
      (when real-graph
	(format t "(~a ~{~s~^ ~})" _tram_sort_order_decl_command_
		real-graph)
	(terpri))))
  (let ((errsorts (trs$err-sorts trs))
	)
    (when errsorts
      (format t "(~a ~{~s~^ ~})" _tram_sort_order_decl_command_
	      errsorts)
      (terpri))))

(defun tram-send-op-decls (trs)
  (flet ((!make-op-info (minfo)
	   (list* (car minfo)
		  (cadr minfo)
		  (caddr minfo)
		  (let ((attrs nil)
			(strat nil))
		    (dolist (attr (nthcdr 3 minfo)
			     (cons strat (if attrs
					     (list (nreverse attrs))
					     nil)))
		      (if (consp attr)
			  (case (car attr)
			    ((:id :idr)
			     (push (list (car attr)
					 (trs-term-to-tram-term
					  (cadr attr)))
				   attrs))
			    (:strat
			     (setq strat (cadr attr))
			     (when strat
			       (unless (eql 0 (car (last strat)))
				 (setq strat
				       (append strat '(0)))))
			     )
			    (otherwise (push attr attrs)))
			  (push attr attrs))))
		  )))
    ;;
    (dolist (op (mapcar #'cdr
			(remove-if #'(lambda (x)
				       (and (not (sort= (method-coarity (car x))
							*sort-id-sort*))
					    (memq (method-module (car x))
						  *tram-builtin-modules*)))
				   (trs$op-info-map trs))))
      (when (setq op (!make-op-info op))
	(format t "(~a ~{~s~^ ~})" _tram_op_decl_command_ op)
	(terpri)))
    ;; 
    (dolist (meth (module-error-methods (trs$module trs)))
      (let ((op (make-trs-op-info meth trs)))
	(when op
	  (setq op (!make-op-info op))
	  (format t "(~a ~{~s~^ ~})" _tram_op_decl_command_ op)
	  (terpri))))
    ))

(defun tram-send-rule-decls (trs &optional all)
  (let ((rules (make-tram-rules trs all))
	)
    (dolist (rule rules)
      (format t "(~a ~{~s~^ ~})" _tram_rule_decl_command_ rule)
      (terpri))))

(defun tram-send-built-in-ops (trs)
  (when (assq *truth-module* (module-all-submodules (trs$module trs)))
    (dolist (opdecl (tram-make-built-in-operators trs))
      (format t "(~a ~{~s~^ ~})" _tram_op_decl_command_ opdecl)
      (terpri))))

(defun tram-send-built-in-axioms (trs)
  (when (assq *truth-module* (module-all-submodules (trs$module trs)))
    (dolist (ax (tram-make-built-in-axioms trs))
      (format t "(~a ~{~s~^ ~})" _tram_rule_decl_command_ ax)
      (terpri))))

(defun tram-send-sem-axioms (trs)
  (dolist (ax (tram-make-sem-axioms trs))
    (format t "(~a ~{~s~^ ~})" _tram_rule_decl_command_ ax)
    (terpri)))
  
(defun tram-send-stat-switch (&rest ignore)
  (declare (ignore ignore))
  (with-output-to-tram (*tram-process*)
    (if *show-stats*
	(princ "(stat on)")
	(princ "(stat off)"))
    (terpri)))

(defun check-tram-error (result)
  (and (stringp result)
       (let ((elts (parse-with-delimiter result #\Space)))
	 (equal (car elts) "error"))))

(defun tram-send-compile (&rest ignore)
  (declare (ignore ignore))
  (let ((res nil)
	(stat nil)
	(error nil))
    (tram-send-stat-switch)
    (setq res
	  (tram-send-and-wait *tram-process*
			      _tram_compile_command_))
    (setq error (check-tram-error res))
    (when (and *show-stats* (not error))
      (setq stat
	    (wait-tram-answer *tram-process*)))
    (values (list res stat) error)
  ))

(defun tram-send-reduce (term trs)
  (let ((trs-term (make-tram-term term trs))
	(res nil)
	(stat nil)
	(error nil))
    (tram-send-stat-switch)
    (setq res
	  (tram-send-and-wait *tram-process*
			      (format nil "(~a ~s)" _tram_reduce_command_
				      trs-term)))
    (setq error (check-tram-error res))
    (when (and *show-stats* (not error))
      (setq stat
	    (wait-tram-answer *tram-process*)))
    (values (list res stat) error)
    ))

;;; EOF
