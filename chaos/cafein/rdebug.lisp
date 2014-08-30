;;;-*-Mode:LISP; Package: CHAOS; Base:10; Syntax:Common-lisp -*-
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
#|=============================================================================
				  System:CHAOS
				 Module:cafein
				File:rdebug.lisp
=============================================================================|#
#-:chaos-debug
(declaim (optimize (speed 3) (safety 0) #-GCL (debug 0)))
#+:chaos-debug
(declaim (optimize (speed 1) (safety 3) #-GCL (debug 3)))

;;;*****************************************************************************
;;;		      REWRITING WITH TRACE, STEP
;;;*****************************************************************************

;;; APPLY-ONE-RULE-DBG
;;;-----------------------------------------------------------------------------
;;; returns true iff the rule has been sucessfully apply. Note that
;;; in this case "term" is also modified.
;;;
(defvar *cafein-current-rule* nil)
(defvar *cafein-current-subst* nil)
;;;
(defun print-trace-in ()
  (format *trace-output* "~&~d>[~a] " *trace-level* (1+ *rule-count*)))

(defun print-trace-out ()
  (format *trace-output* "~&~d<[~a] " *trace-level* *rule-count*))

(defun cafein-pattern-match (pat term)
  (declare (type term pat term)
	   (values (or null t)))
  (if (term-is-variable? pat)
      (if (sort<= (term-sort term) (variable-sort pat)
		  (module-sort-order *current-module*))
	  term
	  nil)
      (if (term-is-lisp-form? pat)
	  nil
	  (multiple-value-bind (gs sub no-match eeq)
	      (first-match pat term)
	    (declare (ignore gs sub eeq))
	    (unless no-match
	      (return-from cafein-pattern-match term))
	    (if (term-is-application-form? term)
		(dolist (sub (term-subterms term) nil)
		  (let ((match (cafein-pattern-match pat sub)))
		    (when match
		      (return-from cafein-pattern-match match))))
		nil)
	    nil))))
	     
(defvar *matched-to-stop-pattern* nil)

(defun check-stop-pattern (term)
  (declare (type term term)
	   (values (or null t)))
  (when *rewrite-stop-pattern*
    (when (eq term *matched-to-stop-pattern*)
      (return-from check-stop-pattern nil))
    (let ((matched (cafein-pattern-match *rewrite-stop-pattern* term)))
      (if matched
	  (let ((*standard-output* *trace-output*))
	    (setq *matched-to-stop-pattern* term)
	    (if (eq matched term)
		(progn
		  (format t "~&>> term matches to stop pattern: ")
		  (let ((*print-indent* (+ *print-indent* 8)))
		    (term-print *rewrite-stop-pattern*))
		  (format t "~&<< will stop rewriting")
		  )
		(progn
		  (format t "~&>> subterm : ")
		  (let ((*print-indent* (+ *print-indent* 8)))
		    (term-print matched))
		  (format t "~&   of term : ")
		  (let ((*print-indent* (+ *print-indent* 8)))
		    (term-print $$term))
		  (format t "~&   matches to stop pattern: ")
		  (let ((*print-indent* (+ *print-indent* 8)))
		    (term-print *rewrite-stop-pattern*))
		  (format t "~&<< will stop rewriting")
		  ))
	    (force-output))
	  ;;
	  (unless *rewrite-stepping*
	    (setq *matched-to-stop-pattern* nil))))))
	    
(defun apply-one-rule-dbg (rule term)
  (declare (type axiom rule)
	   (type term term)
	   (values (or null t))
	   )
  ;; check stop pattern
  (check-stop-pattern term)
  ;; apply rule
  (setq *cafein-current-rule* rule)
  (if (block the-end
	(let* ((condition nil)
	       cur-trial
	       next-match-method
	       (*trace-level* (1+ *trace-level*))
	       (*print-indent* *print-indent*)
	       (*self* term))
	  (multiple-value-bind (global-state subst no-match E-equal)
	      (funcall (rule-first-match-method rule) (rule-lhs rule) term)
	    (incf $$matches)
	    (setq *cafein-current-subst* subst)
	    (when no-match (return-from the-end nil))
	    
	    ;;
	    (unless (beh-context-ok? rule)
	      (return-from the-end nil))
	    
	    ;; technical assignation related to substitution-image.
	    (when E-equal (setq subst nil))

	    ;; match success -------------------------------------
	    ;; then, the condition must be checked
	    (block try-rule
	      (catch 'rule-failure
		(when (and (is-true? (setq condition (rule-condition rule)))
			   (null (rule-id-condition rule)))
		  ;; there is no condition --
		  ;; rewrite term.
		  (when (or $$trace-rewrite
			    (rule-trace-flag rule))
		    (let ((*print-with-sort* t))
	 	      (print-trace-in)
		      (princ "rule: ")
		      (let ((*print-indent* (+ 2 *print-indent*)))
			(print-axiom-brief rule))
		      (let ((*print-indent* (+ 4 *print-indent*)))
			(print-next)
			(print-substitution subst))
		      ))
		  (term-replace-dd-dbg
		   term
		   ;; note that the computation of the substitution
		   ;; made a copy of the rhs.
		   (substitution-image-simplifying subst
						   (rule-rhs rule)))
		  (return-from the-end t))))

	    ;; if the condition is not trivial, we enter in a loop
	    ;; where one try to find a match such that the condition 
	    ;; is satisfied.
	    (setf next-match-method (rule-next-match-method rule))
	    (loop (when no-match
		    (when (or $$trace-rewrite
			      (rule-trace-flag rule))
		      (print-trace-in)
		      (format t "rewrite rule exhausted (#~D)" cur-trial)
		      (force-output))
		    (return))
		  ;;
		  (unless (beh-context-ok? rule)
		    (return-from the-end nil))
		  ;;
		  (setq *cafein-current-subst* subst)
		  ;;
		  (when (or $$trace-rewrite
			    (rule-trace-flag rule))
		    (let ((*print-with-sort* t))
		      (setq cur-trial $$trials)
		      (incf $$trials)
		      (print-trace-in)
		      (format t "apply trial #~D" cur-trial)
		      (print-next)
		      (princ "-- rule: ")
		      (let ((*print-indent* (+ 2 *print-indent*)))
			(print-axiom-brief rule))
		      (let ((*print-indent* (+ 4 *print-indent*)))
			(print-next)
			(print-substitution subst))
		      (force-output)))
		  (block try-rule
		    (catch 'rule-failure
		      (if (and (or (null (rule-id-condition rule))
				   (rule-eval-id-condition subst
							   (rule-id-condition rule)))
			       (is-true?
				(let (($$cond (substitution-image subst condition))
				      (*rewrite-exec-mode*
				       (if *rewrite-exec-condition*
					   *rewrite-exec-mode*
					   nil)))
				  ;; no simplyfing since probably wouldn't pay
				  (if *rewrite-semantic-reduce*
				      (normalize-term-with-bcontext $$cond)
				      (normalize-term $$cond))
				  $$cond)))
			  ;; the condition is satisfied
			  (progn
			    (when (or $$trace-rewrite
				      (rule-trace-flag rule))
			      (print-trace-in)
			      (format t "match success #~D" cur-trial))
			    (term-replace-dd-dbg
			     term
			     (substitution-image-simplifying subst
							     (rule-rhs rule)))
			    (return-from the-end t))
			  nil)))
		  
		  ;; else, try another ...
		  (multiple-value-setq (global-state subst no-match)
		    (progn
		      (incf $$matches)
		      (funcall next-match-method global-state)
		      ))
		  
		  );; end loop
	    
	    ;; In this case there is no match at all and the rule does not apply.
	    (return-from the-end nil))))
      ;; applied a rule.
      t
      ;; else no rule was applied
      (if *matched-to-stop-pattern*
	  (if *rewrite-stepping*
	      nil
	      (progn
		(setq *matched-to-stop-pattern* nil)
		(throw 'rewrite-abort $$term)))
	  nil)
      ))

(defun term-replace-dd-dbg (old new)
  (declare (type term old new)
	   (values term))
  ;;
  (incf *rule-count*)

  (when *matched-to-stop-pattern*
    (unless *rewrite-stepping*
      (setq *matched-to-stop-pattern* nil)
      (throw 'rewrite-abort $$term)))
  
  ;; Enter STEPPER if need
  (when *rewrite-stepping* (cafein-stepper old new))
  (setq *matched-to-stop-pattern* nil)
  
  ;; Trace output
  (when (or $$trace-rewrite
	    (rule-trace-flag *cafein-current-rule*))
    (let ((*print-with-sort* t))
      (print-trace-out)
      (let ((*print-indent* (+ 4 *print-indent*)))
	(term-print old)
	(print-check 0 5)
	(princ " --> ")
	;; (print-check)
	(term-print new))
      (unless $$trace-rewrite-whole (terpri))))
  ;; trace whole
  (if $$trace-rewrite-whole
      (let ((*print-with-sort* t)
	    (*fancy-print* t))
	(if $$cond
	    (progn
	      (format t "~&[~a(cond)]: " *rule-count*)
	      (let ((*print-indent* (+ 2 *print-indent*)))
		(term-print $$cond)
		(print-next)
		(let ((res (term-replace old new)))
		  (print-check 0 5)
		  (princ " --> ")
		  (let ((*print-indent* (+ 2 *print-indent*)))
		    ;; (print-check)
		    (term-print $$cond))
		  res)))
	    (progn
	      (format t "~&[~a]: " *rule-count*)
	      (let ((*print-indent* (+ 2 *print-indent*)))
		(term-print $$term))
	      (print-next)
	      (let ((res (term-replace old new)))
		(print-check 0 5)
		(princ "---> ")
		(let ((*print-indent* (+ 2 *print-indent*)))
		  ;; (print-check)
		  (term-print $$term))
		res))))
      (term-replace old new))
  ;;
  ;; check rewrite count limit
  (when (and *rewrite-count-limit*
	     (<= *rewrite-count-limit* *rule-count*))
      (format *error-output* "~&>> aborting rewrite due to rewrite count limit (= ~d) <<"
	      *rewrite-count-limit*)
      (throw 'rewrite-abort $$term))
  ;;
  $$term)

;;;
;;; STEPPER
;;;

(defparameter cafein-stepper-procs
  '(((":go" ":g" "go" "g") . cafein-go-step-proc)
    (("n" ":n" "next" ":next") . cafein-next-step-proc)
    (("c" ":c" "cont" "continue" ":cont" ":continue")
     . cafein-continue-step-proc)
    (("abort" "a" ":a" ":abort") . cafein-abort-step-proc)
    (("stop" ":stop") . cafein-stop-at-proc)
    (("rwt" "rewrite" ":rwt" ":rewrite")
     . cafein-rewrite-count-limit-proc)
    ;;
    (("r" ":r" "rule" ":rule") . cafein-step-show-rule-proc)
    (("s" ":s" "subst" ":subst")
     . cafein-step-show-subst-proc)
    (("l" ":l" "limit" ":limit") . cafein-show-rewrite-limit)
    (("p" ":p" "pattern" ":pattern") . cafein-show-stop-pattern)
    ;;
    (("match" "unify") . cafeobj-eval-match-proc)
    (("lisp" "ev" "eval") . cafeobj-eval-lisp-proc)
    (("lispq" "lisp-quiet" "evq" "cafeobj-eval-quiet") . cafeobj-eval-lisp-q-proc)
    (("show" "sh") . cafeobj-eval-show-proc)
    (("set") . cafeobj-eval-set-proc)
    (("describe" "desc") . cafeobj-eval-show-proc)
    (("help" "?" ":?" ":help" "h" ":h") . cafein-stepper-help-proc)
    (("pwd") . cafeobj-eval-pwd-proc)
    (("cd") . cafeobj-eval-cd-proc)
    (("ls") . cafeobj-eval-ls-proc)
    (("!") . cafeobj-eval-shell-proc)
    ))

(defun cafein-stepper (term &optional new-term)
  (declare (ignore new-term)
	   (type term term)
	   (values t))
  ;; first check stop pattern or steps to be done....
  (if *matched-to-stop-pattern*
      (progn
	(setq *matched-to-stop-pattern* nil)
	(setq *steps-to-be-done* nil)
	(with-output-simple-msg ()
	  (princ ">> stop because matches stop pattern.")))
      (progn
	(when *steps-to-be-done*
	  (decf (the fixnum *steps-to-be-done*)))
	(when (and *steps-to-be-done* (> (the fixnum *steps-to-be-done*) 0))
	  (return-from cafein-stepper nil))
	(unless *steps-to-be-done* (return-from cafein-stepper nil))))
  ;;
  ;; print current term
  (format t "~&>> stepper term: ")
  (term-print term)
  ;; prompt command
  (catch 'cafein-stepper-exit
    (loop
     (block next-loop
       (with-chaos-top-error ()
	 (with-chaos-error ()
	   (let ((inp (get-step-command)))
	     (unless (listp inp) (return-from next-loop))
	     ;; QUIT 
	     (when (member (car inp) '("eof" "q" ":q" "quit" ":quit" eof) :test #'equal)
	       (step-off)
	       (return-from cafein-stepper nil))
	     ;;
	     (let* ((key (car inp))
		    (proc (find-if #'(lambda (elt)
				       (member key (car elt) :test #'equal))
				   cafein-stepper-procs)))
	       (if proc
		   (funcall (cdr proc) inp)
		   (progn
		     (with-output-chaos-warning ()
		       (format t "unknow step command ~a." inp)
		       (print-next)
		       (format t "type :? for help."))))))))))))
    
(defvar *step-commands* nil)

(defun get-step-command ()
  (let ((.reader-ch. 'space)
	(*reader-input* *reader-void*)
	(*old-context* nil)
	(top-level? (at-top-level)))
    (with-chaos-top-error ()
      (with-chaos-error ()
	(when top-level?
	  (format t "~&STEP[~D]? " *rule-count*)
	  (force-output))
	(reader 'step-commands *step-commands*)))))

(eval-when (:execute :load-toplevel)
  (setq *step-commands*
	'((step-commands
	   (:one-of

	    ;; end of step (just stop now).
	    #-CMU (#\^D)
	    #+CMU (#\)
	    (eof)
	    ((:+ q |:q|))

	    ;; continue rewriting and exit from stepping mode.
	    ((:+ c |:c| continue |:continue|))

	    ;; stop pattern
	    ((:+ stop |:stop|) :top-term)
	    
	    ;; rewrite limit
	    ((:+ rwt rewrite |:rwt| |:rewrite|) :symbol)
	    
	    ;; step to next
	    ((:+ n |:n| next |:next|))

	    ;; step N step
	    ((:+ g go |:g| |:go|) :int)
	    
	    ;; abort
	    ((:+ a |:a| abort |:abort|))
	    
	    ;; show infos
	    ((:+ r |:r| |:rule| rule))
	    ((:+ s |:s| subst |:subst|))
	    ((:+ p |:p| pattern |:pattern|))
	    ((:+ l |:l| limit |:limit|))
	    
	    ;; some useful top level commands
	    ((:+ match unify) (:seq-of :term) to (:seq-of :term) |.|)
	    ((:+ lisp ev eval evq lispq)
	     (:call (read)))
	    ((:+ show sh set describe desc)
	     (:seq-of :top-opname))
	    ;;
	    (cd :symbol)
	    #-(or GCL LUCID CMU) (ls :symbol)
	    #+(or GCL LUCID CMU) (ls :top-term)
	    (pwd)
	    (! :top-term)
	    ((+ ? |:?| |:h| h |:help| help))
	    ))
	(Selector
	   (:one-of
	    ;; (term) (top) (subterm)
	    (|{| :int :append (:seq-of |,| :int) |}|)
	    (|(| (:seq-of :int) |)|)
	    (\[ :int (:optional |..| :int) \])))
	  )))
	     
;;; REWRITE COUNT LIMIT
;;; ("rwt" <number>)
;;;
(defun cafein-rewrite-count-limit-proc (inp)
  (declare (type list inp)
	   (values t))
  (let ((count (cadr inp)))
    (if (member count '("off" "none" ".") :test #'equal)
	(eval-ast (%rewrite-count* 'off))
	(eval-ast (%rewrite-count* count)))))

;;; STOP AT PATTERN
;;; ("stop" <term> ".")
;;;
(defun cafein-stop-at-proc (inp)
  (eval-ast (%stop-at* (cdadr inp))))

;;; GO STEP
;;;
(defun cafein-go-step-proc (inp)
  (let ((num (cadr inp)))
    (when (stringp num) (setq num (parse-integer num)))
    (setq *steps-to-be-done* num)
    (throw 'cafein-stepper-exit nil)))

;;; GO ONE STEP
;;;
(defun cafein-next-step-proc (inp)
  (declare (ignore inp))
  (setq *steps-to-be-done* 1)
  (throw 'cafein-stepper-exit ':next))

;;; CONTINUE
;;;
(defun cafein-continue-step-proc (inp)
  (declare (ignore inp))
  (setq *steps-to-be-done* nil)
  (throw 'cafein-stepper-exit ':continue))

;;; ABORT
;;;
(defun cafein-abort-step-proc (inp)
  (declare (ignore inp))
  (setq *steps-to-be-done* nil)
  (throw 'rewrite-abort $$term))

;;; SHOW RULE
;;;
(defun cafein-step-show-rule-proc (inp)
  (declare (ignore inp))
  ;; (format t "~&[current rewrite rule]: ")
  (let ((*fancy-print* nil)
	(*print-with-sort* t))
    (print-chaos-object *cafein-current-rule*)))

;;; SHOW SUBST
;;;
(defun cafein-step-show-subst-proc (inp)
  (declare (ignore inp))
  (print-substitution *cafein-current-subst*))

;;; HELP
;;;
(defun cafein-stepper-help-proc (inp)
  (declare (ignore inp))
  (format t "~&-- Stepper command help :")
  (format t "~&  ?~18Tprint out this help")
  (format t "~&  n(ext)~18Tgo one step")
  (format t "~&  g(o) <number>~18Tgo <number> step")
  (format t "~&  c(ontinue)~18Tcontinue rewriting without stepping")
  (format t "~&  q(uit)~18Tleave stepper continuing rewrite")
  (format t "~&  a(bort)~18Tabort rewriting")
  (format t "~&  r(ule)~18Tprint out current rewrite rule")
  (format t "~&  s(subst)~18Tprint out substitution")
  (format t "~&  l(imit)~18Tprint out rewrite limit count")
  (format t "~&  p(attern)~18Tprint out stop pattern")
  (format t "~&  stop [<term>] .~18Tset(unset) stop pattern")
  (format t "~&  rwt [<number>] .~18Tset(unset) max number of rewrite")
  (format t "~&-- the followings are subset of CafeOBJ interpreter commands")
  ;; (format t "~&  rwt limit {<number>| .}~%~18Tset(unset) max number of rewriting")
  ;; (format t "~&  stop at [<term>] .~18Tset(unset) stop pattern")
  (format t "~&  show -or-")
  (format t "~&  describe~18Tprint various info., for further help, type `show ?'")
  (format t "~&  set~18Tset toplevel switches, for further help: type `set ?'")
  (format t "~&  cd <directory> ~18Tchange current directory")
  (format t "~&  ls <directory> ~18Tlist files in directory")
  (format t "~&  pwd ~18Tprint current directory")
  (format t "~&  lisp -or-")
  (format t "~&  lispq <lisp> ~18Tevaluate lisp expression <lisp>")
  (format t "~&  ! <command> ~18Tfork shell <command>. Under Unix only")
  )

;;;
;;;
(defun cafein-show-rewrite-limit (&rest ignore)
  (declare (ignore ignore))
  (print-next)
  (format t "[rewrite limit]: ~a" (if *rewrite-count-limit*
				      *rewrite-count-limit*
				      "not specified.")))

(defun cafein-show-stop-pattern (&rest ignore)
  (declare (ignore ignore))
  (print-next)
  (format t "[stop pattern]: ")
  (if *rewrite-stop-pattern*
      (let ((*fancy-print* nil)
	    (*print-with-sort* t))
	(term-print *rewrite-stop-pattern*))
      (princ "not specified.")))
				    
;;; EOF
