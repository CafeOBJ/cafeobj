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
;;;
(in-package :chaos)
#|=============================================================================
			    System:Chaos
			  Module:BigPink
			   File:infer.lisp
=============================================================================|#
#-:chaos-debug
(declaim (optimize (speed 3) (safety 0) #-GCL (debug 0)))
#+:chaos-debug
(declaim (optimize (speed 1) (safety 3) #-GCL (debug 3)))

;;;                       ******************
;;;			   Inference Engine
;;;                       ******************

;;; ==========
;;; INFER-MAIN
;;; ==========
;;; main loop

(defun infer-main (mod)
  (declare (type module mod))
  (let ((status :keep-searching))
    (declare (type symbol status))
    ;; perform db reset in automatic mode.
    (unless *pn-no-db-reset*
      (if (or (pn-flag auto)
	      (pn-flag auto1)
	      (pn-flag auto2)
	      (pn-flag auto3))
	  (progn
	    (clear-all-index-tables)
	    (reset-module-proof-system mod))
	;;
	(unless (module-proof-system mod)
	  (auto-db-reset mod))
	))
    ;;
    (with-proof-context (mod)
      (let ((ex-code nil))
	(declare (type symbol ex-code))
	(setq ex-code
	  (catch :exit-inference
	    ;; -----------
	    ;; preparation
	    ;; -----------
	    (prepare-inference mod)
	    (setq status (check-pn-stop))
	    (if (eq status :keep-searching)
		(setq *given-clause* (extract-given-clause))
	      (setq *given-clause* nil))
	    ;; ---------------
	    ;; start main loop
	    ;; ---------------
	    (when (pn-flag print-message)
	      (format t "~% ~%** Starting PigNose _____________________~% ~%")
	      )
	    (loop
	      (unless (and *given-clause*
			   (eq status :keep-searching))
		(return))
	      ;;
	      (incf (pn-stat cl-given))
	      (when (pn-flag print-given)
		(with-output-simple-msg ()
		  (format t "#~d(weight=~d):"
			  (pn-stat cl-given)
			  (clause-pick-weight *given-clause*))
		  (print-next)
		  (print-clause *given-clause* *standard-output*))
		)
	      ;;
	      (index-clash-literals *given-clause*)
	      (append-clause :usable *given-clause*)
	  
	      ;; ************
	      ;; DO INFERENCE
	      ;; ************
	      (setq *new-demodulator* nil)
	      (infer *given-clause*)
	      ;;
	      #||
	      (when (and (< 0 (pn-parameter interrupt-given))
			 (= 0 (mod (pn-stat cl-given)
				   (pn-parameter interrupt-given))))
		(when (pn-flag print-message)
		  (with-output-msg ()
		    (format t "~d clauses have been given."
			    (pn-stat cl-given))))
		;; todo
		(pn-interact))
	      ||#
	      ;;
	      (setq status (check-pn-stop))
	      ;;
	      (when (eq status :keep-searching)
		(when (= (pn-parameter change-limit-after)
			 (pn-stat cl-given))
		  (let ((new-limit (pn-parameter new-max-weight)))
		    (setf (pn-parameter max-weight) new-limit)
		    (when (pn-flag print-message)
		      (with-output-msg ()
			(format t "reducing weight limit to ~d" new-limit)))))
		;; get next clause
		(setq *given-clause* (extract-given-clause))
		)
	      ;;
	      #|| report : not yet
	      (when (and (eq status :keep-searching)
			 *given-clause*
			 (< 0 (pn-parameter report)))
		;; TODO
		;; (pn-report)
		)
	      (when (pn-flag print-message)
		(print-in-progress "."))
	      ||#
	      )

	    ;; ------------------
	    ;; loop ends
	    ;; report the result
	    ;; ------------------
	    (cond ((eq status :keep-searching)
		   (setq status :sos-empty-exit)
		   (when (pn-flag print-stats)
		     (format t "~%** Search stopped because SOS is empty.~% ~%")))
		  (t (let ((reason nil))
		       (case status
			 (:max-given-exit (setq reason "max-given"))
			 (:max-gen-exit (setq reason "max-gen"))
			 (:max-kept-exit (setq reason "max-kept"))
			 (:max-seconds-exit (setq reason "max-seconds"))
			 (otherwise (setq reason "???")))
		       (when (pn-flag print-stats)
			 (format t "~%** Search stopped due to ~a option.~% ~%"
				 reason))
		       ))
		  )
	    ;;
	    (infer-clean-up)
	    status))
	;;
	(when .debug-pn-memory.
	  (report-pn-memory))
	;;
	(if ex-code
	    ex-code
	  status)))
    ))

(defun pn-interact ()
  (with-output-simple-msg ()
    (format t "sorry, but interaction during inference is not supported yet.")
    ))

;;; =====
;;; INFER
;;; =====
;;; - applies specified inference rules to given clause.
;;; - inference rules append kept clauses to SOS (set of support).
;;; - after each inference rule is finished, the newly kept clauses
;;;   are `post-process'ed (back subsumption, back demodulation, etc.).
;;;
(declaim (inline given-clause-ok))

(defun given-clause-ok (clause-id)
  (declare (type fixnum clause-id))
  (let ((clause (get-clause clause-id (psystem-clause-hash *current-psys*))))
    (and clause
	 (clause-container clause))))

(defun infer (clause)
  (declare (type clause clause))
  (let ((gen-cls nil)			; clauses generated
	(cl-id (clause-id clause))	; identifier of given clause
	)
    (declare (type list gen-cls)
	     (type fixnum cl-id))
    ;;
    ;; adjust max-weight
    ;;
    (when (pn-flag control-memory)
      (pn-control-memory))

    ;;
    ;; binary resolution
    ;;
    (when (and (pn-flag binary-res)
	       (given-clause-ok cl-id))
      (setq gen-cls
	(binary-resolution clause))	; inference rule appends newly 
					; kept clauses to *SOS* also.
      ;; post-process new clases in *SOS*
      ;; - may append even more clauses to *SOS*. 
      (when gen-cls
	(post-proc-all gen-cls nil :sos))
      )

    ;; special treatment for propoitional literals
    (when (and (not (pn-flag binary-res))
	       (pn-flag prop-res))
      (let ((do-prop-resolve nil))
	(setq do-prop-resolve
	  (or (pn-flag hyper-res)
	      (pn-flag neg-hyper-res)))
	#||
	(setq do-prop-resolve
	  (or (and (pn-flag hyper-res)
		   (not (positive-clause? clause)))
	      (and (pn-flag neg-hyper-res)
		   (not (negative-clause? clause)))))
	||#
	(when do-prop-resolve
	  (setq gen-cls (binary-resolution clause :propositional-only)))
	(when gen-cls
	  (post-proc-all gen-cls nil :sos)))
      )
	
    ;; for subsequent inference rules, check the given clause has
    ;; not back demodulated or back subsumed.....................
    
    ;;
    ;; hyper resolution
    ;;
    (when (and (pn-flag hyper-res)
	       (given-clause-ok cl-id))
      (setq gen-cls (hyper-resolution clause))
      (when gen-cls
	(post-proc-all gen-cls nil :sos)))
    
    ;;
    ;; negative hyper resolution
    ;;
    (when (and (pn-flag neg-hyper-res)
	       (given-clause-ok cl-id))
      (setq gen-cls
	(neg-hyper-resolution clause))
      (when gen-cls
	(post-proc-all gen-cls nil :sos)))
    
    ;;
    ;; ur(unit resulting) resolution
    ;;
    (when (and (pn-flag ur-res)
	       (given-clause-ok cl-id))
      (setq gen-cls
	(ur-resolution clause))
      (when gen-cls
	(post-proc-all gen-cls nil :sos)))

    ;; paramudulations:
    ;; paramodulation-into

    (when (and (pn-flag para-into)
	       (given-clause-ok cl-id))
      (setq gen-cls
	(paramodulation-into clause))
      (when gen-cls
	(post-proc-all gen-cls nil :sos)))

    ;; paramodulation-from

    (when (and (pn-flag para-from)
	       (given-clause-ok cl-id))
      (setq gen-cls
	(paramodulation-from clause))
      (when gen-cls
	(post-proc-all gen-cls nil :sos)))
    
    ;; finally, the demodulation process

    (when (and (pn-flag demod-inf)
	       (given-clause-ok cl-id))
      (let ((c nil))
	(declare (type (or null clause) c))
	(setq c (copy-clause clause))
	;; (register-clause c *current-psys*)
	(incf (pn-stat cl-generated))
	(incf (pn-stat demod-inf-gen))
	(setf (clause-parents (the clause c))
	  (list (list (clause-id clause))))
	(when (pre-process c nil :sos)
	  (post-proc-all (list c) nil :sos))))
    ))

;;; POST-PROCESS sos-pointer input lst
;;; - finished processing a clause
;;; - the clause has already been integrated, indexed and appended to
;;;   *sos* 
;;; - does back subsumption
;;; - possibly generates more clauses (factoring, back demodulation,
;;;   host lists, etc.)
;;; - any newly generated and kept clause will be appended to lst and
;;;   will wait their turn to be post-processed.
;;;
(defun post-process (clause input list)
  (declare (type clause clause)
	   (type symbol list))
  (when (and (pn-flag eq-units-both-ways)
	     (unit-clause? clause))
    ;; generate a flipped copy if
    ;; 1. it's a (pos or neg) eq unit, and
    ;; 2. either
    ;;    a. order-equation is clear, or
    ;;    b. order-equation is set, and it couldn't be oriented.
    ;;
    (let ((lit (ith-literal clause 1)))
      (declare (type literal lit))
      (when (and (eq-literal? lit)
		 (or (not (pn-flag order-eq))
		     (not (test-bit (literal-stat-bits lit)
				    oriented-eq-bit))))
	(let ((c2 (copy-clause clause)))
	  (declare (type clause c2))
	  ;; (register-clause c2 *current-psys*)
	  ;; (break "a!")
	  (setf (clause-parents c2)
	    (list (list :copy-rule (clause-id clause)
			:flip-eq-rule
			)))
	  (setq lit (ith-literal c2 1))
	  (let* ((atom (literal-atom lit))
		 (new-atom (make-term-with-sort-check *fopl-eq*
						      (list (term-arg-2 atom)
							    (term-arg-1 atom)))))
	    (setf (literal-atom lit) new-atom))
	  ;;
	  (pre-process c2 input list)
	  ))
      ))
  
  ;; Back DEMODULATION
  (when (or (not (pn-flag no-new-demod))
	    input)
    (when (and (pn-flag back-demod)
	       (unit-clause? clause))
      (when (assq clause *new-demodulator*)
	(unless (pn-flag quiet)
	  (when (or input (pn-flag print-back-demod))
	    (with-output-simple-msg ()
	      (format t "* starting back demodulation with ~d."
		      (clause-id clause))))))
      (back-demodulate *new-demodulator* clause input list)
      )
    )

  ;; BACK SUBSUMPTION

  (when (pn-flag back-sub)
    (let ((cp (back-subsume clause)))
      (dolist (e cp)
	(declare (type clause e))
	(incf (pn-stat cl-back-sub))
	(unless (pn-flag quiet)
	  (when (or input (pn-flag print-back-sub))
	    (with-output-msg ()
	      (format t "~d backsubsumes ~d."
		      (clause-id clause)
		      (clause-id e))
	      ;;
	      ;; (print-next)
	      ;; (print-clause e)
	      ;;
	      )
	    ))
	;;
	(clause-full-un-index e)
	)))

  ;; FACTORING

  (when (pn-flag factor)
    (all-factors clause list)
    )

  ;; BACK UNIT DELETION

  (when (and (pn-flag back-unit-deletion)
	     (unit-clause? clause))
    (unless (pn-flag quiet)
      (when (or (pn-flag print-back-demod)
		input)
	(with-output-simple-msg ()
	  (format t "* starting back unit deletion with ~d."
		  (clause-id clause)))))
    (back-unit-deletion clause input)
    )
  ;;
)

;;;
;;; POST-PROC-ALL : List[Clause] Bool ClauseListMarker -> Void
;;;
(defun post-proc-all (clauses input clause-list-marker)
  (declare (type list clauses)
	   (type symbol clause-list-marker))
  (when (pn-flag debug-infer)
    (with-output-msg ()
      (princ "start[post-proc-all]:")
      (pr-clause-list clauses t)))
  (unless clauses
    (if (eq clause-list-marker :sos)
	(setq clauses *sos*)
      (if (eq clause-list-marker :usable)
	  (setq clauses *usable*))))
  (dolist (c clauses)
    (post-process c input clause-list-marker))
  ;;
  (setq *new-demodulator* nil)
  )


;;; HEAT-IS-ON : NOT YET
(defun heat-is-on () nil)

(defun end-pre-process ()
  (with-output-msg ()
    (princ "end[pre-process]")))

;;; PRE-PROCESS clause input list
;;;
(defun pre-process (clause input list &optional dont-delete)
  (declare (type clause clause)
	   (type symbol list))
  (when (pn-flag debug-infer)
    (with-output-msg ()
      (format t "start[pre-process]")
      (print-next)))
  #|| not yet
  (when (heat-is-on)
    (incf (pn-stat hot-generated)))
  ||#
  ;;
  (let ((original-input (if (clause-parents clause)
			    nil
			  (copy-clause clause)))
	(gen-result nil))
    (setq gen-result (proc-gen clause input))
    (unless gen-result
      (unless dont-delete
	(cl-delete clause))
      (when original-input
	(cl-delete original-input))
      (return-from pre-process nil))

    (when (pn-flag debug-infer)
      (with-output-msg ()
	(format t "after proc-gen:")
	(print-clause clause)))
    
    (when original-input
      ;; when input clauses are changed (unit-del, factor-simp,
      ;; demod) during pre-process, we keep the original so that
      ;; proofs make sense.
      (setf (clause-parents original-input)
	(list (list :copy-rule (clause-id clause))))
      ;; (register-clause original-input *current-psys*)
      )

    ;; registering & indexing
    (index-all-literals clause)
    (when (and (eq list :usable)
	       (not (eq clause *given-clause*)))
      (index-clash-literals clause))

    ;; append to list
    (append-clause list clause)
    
    ;; weight
    (setf (clause-pick-weight clause)
      (weight-clause clause))

    ;; modify pick-weight by age factor
    #||
    (unless (= 0 (pn-parameter age-factor))
      (incf (clause-pick-weight clause)
	    (/ (pn-stat cl-given) (pn-parameter age-factor))))
    ||#

    #|| no yet
    (unless (= 0 (pn-parameter distinct-vars-factor))
      (incf (clause-pick-weight clause)
	    (* (clause-distinct-variables clause)
	       (pn-parameter distinct-vars-factor))))
    ||#
    ;;
    (incf (pn-stat cl-kept))
    #||
    (when (< 0 (clause-heat-level clause))
      (incf (pn-stat hot-kept)))
    ||#
    ;;
    (when (or (and input (not (pn-flag quiet)))
	      (pn-flag print-kept))
	(with-output-simple-msg ()
	  (format t "* kept in ~a : weight=~d" list (clause-pick-weight clause))
	  (print-next)
	  (print-clause clause))
	)

    ;; dynamic demodulation

    (when (or (not (pn-flag no-new-demod))
	      input)
      (when (and (or (pn-flag dynamic-demod)
		     (pn-flag demod-inf))
		 (unit-clause? clause)
		 (= 1 (the fixnum (num-literals-all clause)))
		 (or (positive-eq-literal? (the literal (ith-literal clause 1)))
		     (and input
			  (not (eq-literal?
				(the literal (ith-literal clause 1)))))))
	;;
	(let ((demod-flag (dynamic-demodulator clause)))
	  (declare (type symbol demod-flag))
	  (when demod-flag
	    (let ((new-demod (new-demodulator clause demod-flag)))
	      (declare (type demod new-demod))
	      (unless (pn-flag quiet)
		(when (pn-flag print-new-demod)
		  (with-output-simple-msg ()
		    (princ "* new demodulator: ")
		    (print-next)
		    (print-demodulator new-demod))
		  ))
	      (push (cons clause new-demod) *new-demodulator*)
	      )))
	))
    
    ;; check for proof
    (let ((e nil))
      (setq e (check-for-proof clause list))
      (when (and (not (= -1 (pn-parameter max-proofs)))
		 (>= (pn-stat empty-clauses)
		     (pn-parameter max-proofs)))
	;; the end
	(when (pn-flag print-stats)
	  (format t "~%** Search stopped due to max-proofs option.~% ~%")
	  )
	(infer-clean-up)
	;;
	(exit-pn-proof :max-proofs-exit))
      (when e
	(when (pn-flag debug-infer)
	  (with-output-msg ()
	    (princ "End[pre-process]: empty clause.")))
	(return-from pre-process nil))
      )
    ;;
    #|| NOT YET
    (when (and (not input)
	       (<= (clause-pick-weight clause)
		   (pn-parameter dynamic-heat-weight)))
      (hot-dynamic clause))
    ||#
    ;;
    (when (pn-flag debug-infer)
      (end-pre-process))
    clause
    ))

;;; EXIT-PN-PROOF
;;;
(defun exit-pn-proof (exit-status)
  (throw :exit-inference exit-status))

;;; PROC-GEN : Clause Input -> Bool
;;; main processing applied to generated clauses.
;;;
;;; if input is non-nil, clause is an input clause, and some
;;; tests should not be performed.
;;;
;;; taks a generated clause and do the following (* mesans optional):
;;;   1 rename variables
;;;  *2 print the clause
;;;   3 demodulate
;;;   5 handle evaluable literals (not yet)
;;;  *6 order equalities
;;;  *7 unit-deletion
;;;   8 merge identical literals
;;;  *9 max literals test (if not input)
;;; *10 max listict vars check (if not input)
;;;  11 tautology check
;;; *12 max weight test (if not input)
;;; *13 delete identical nested skolems (if not input)
;;; *14 sort literals
;;; *15 forward subsumption
;;;  16 rename variables (again)
;;;
(defun proc-gen (clause &optional (input nil))
  (declare (type clause clause)
	   (values (or null clause)))
  ;; RENAME VARIABLES

  (cl-unique-variables clause)

  (when (pn-flag very-verbose)
    (with-output-msg ()
      (princ "new clause:  ")
      (print-clause clause))
    )

  ;; DEMODULATION

  (let ((rwc (pn-stat rewrites)))
    (declare (type fixnum rwc))
    (demodulate-clause clause)
    (when (and (pn-flag very-verbose)
	       (not (= rwc (pn-stat rewrites))))
      (with-output-simple-msg ()
	(princ "  * after dmodulation: ")
	(print-next)
	(print-clause clause)))
    )
  
  ;; 
  ;; check c1 = c2
  ;;
  (when (pn-flag dist-const)
    (pn-distinct-constants clause)
    )

  ;;
  ;; reduce t/f valued literals
  ;;
  #||
  (when (pn-flag debug-infer)
    (with-output-msg ()
      (princ "*before t/f elim: ")
      (print-clause clause)))
  ||#
  (when (literal-true-false-reduce clause)
    (incf (pn-stat cl-tautology))
    (return-from proc-gen nil))
  
  #||
  (when (pn-flag debug-infer)
    (with-output-msg ()
      (princ "*after t/f elim: ")
      (print-clause clause)))
  ||#
  
  ;; ORDER EQUALITIES

  (when (pn-flag order-eq)
    (if (pn-flag lrpo)
 	(order-equalities-lrpo clause input)
      (order-equalities clause input))
    (when (and (not input)
	       (pn-flag discard-non-orientable-eq)
	       (unit-clause? clause) 
	       (= (the fixnum (num-literals-all clause)) 1)
	       (positive-eq-literal? (the literal (ith-literal clause 1)))
	       (not (test-bit (literal-stat-bits
			       (the literal (ith-literal clause 1)))
			      oriented-eq-bit))
	       )
      (return-from proc-gen nil)))

  ;; UNIT DELETION

  (when (and (pn-flag unit-deletion)
	     (> (the fixnum (num-literals clause)) 1))
    (unit-deletion clause)
    )

  ;; FACTOR SIMPLIFY

  (when (pn-flag factor)
    (let ((num (factor-simplify clause)))
      (declare (type fixnum num))
      (incf (pn-stat factor-simplifications) num)))
    
  ;; MERGE IDENTIAL LITERALS

  (merge-clause clause)
    
  ;; check stop conditions specified by parameters.
  ;; 
  ;; max-literals
  (when (and (not input)
	     (not (= -1 (pn-parameter max-literals))))
    (when (< (pn-parameter max-literals) (num-literals clause))
      (incf (pn-stat cl-wt-delete))
      (return-from proc-gen nil)))
  #||
  ;; max-answers
  (when (and (not input)
	     (not (= -1 (pn-parameter max-answers))))
    (when (< (pn-parameter max-answers) (num-answers clause))
      (incf (pn-stat cl-wt-delete))
      (return-from proc-gen nil)))
  ;; 
  ||#

  (when (and (not input)
	     (pn-flag discard-xx-resolvable)
	     (xx-resolvable clause))
    (incf (pn-stat cl-wt-delete))
    (return-from proc-gen nil))

  ;; TAUTOLOGY CHECK

  (when (cl-tautology? clause)
    (incf (pn-stat cl-tautology))
    (return-from proc-gen nil))
    
  ;; MAX WEIGHT TEST

  (when (and (not input)
	     (not (= (pn-parameter max-weight)
		     most-positive-fixnum)))
    (let ((wt 0))
      (declare (type fixnum wt))
      (setq wt (weight-clause clause))
      (when (> wt (pn-parameter max-weight))
	(when (pn-flag very-verbose)
	  (with-output-simple-msg ()
	    (format t "   deleted because weight=~d." wt)))
	(incf (pn-stat cl-wt-delete))
	(return-from proc-gen nil))))

  ;; DELETE IDENTICAL NESTED SKOLEM FUNCTIONS.
  
  (when (and (not input)
	     (pn-flag delete-identical-nested-skolem))
    (when (ident-nested-skolems clause)
      (incf (pn-stat cl-wt-delete))
      (return-from proc-gen nil))
    )
    
  ;; SORT LITERALS

  (when (pn-flag sort-literals)
    (sort-literals clause)
    )

  ;;
  (when (pn-flag order-eq)
    ;; for each equality literal that has been flipped, add and
    ;; entry to the history. to make sense, this has to be done
    ;; after sort-literals.
    (let ((n 0))
      (declare (type fixnum n))
      (dolist (lit (clause-literals clause))
	(declare (type literal lit))
	(incf n)
 	(when (test-bit (literal-stat-bits lit) scratch-bit)
	  ;; scratch-bit meaning flipped.
	  (clear-bit (literal-stat-bits lit) scratch-bit)
 	  (setf (clause-parents clause)
	    (nconc (clause-parents clause)
 		   (list (list :flip-eq-rule)))))))

    )

  ;; FORWARD SUBSUMPTION

  (when (pn-flag for-sub)
    (when (pn-flag debug-infer)
      (with-output-msg ()
	(princ "*proc-gen: start forward subsumption:")
	))
    (let ((e nil))
      (declare (type (or null clause) e))
      (setq e (forward-subsume clause))
      (when e
	(if (pn-flag very-verbose)
	    (with-output-simple-msg ()
	      (format t "  * subsumed by ~d." (clause-id e)))
	  (when (and input (not (pn-flag quiet)))
	    (with-output-simple-msg ()
	      (format t "-- following clause subsumed by ~d during input processing:"
		      (clause-id e))
	      (print-next)
	      (print-clause clause))
	    ))
	(incf (pn-stat cl-for-sub))
	(when (eq (clause-container e) :sos)
	  (incf (pn-stat for-sub-sos)))
	;;
	(return-from proc-gen nil)
	))
    (when (pn-flag debug-infer)
      (with-output-msg ()
	(princ "*proc-gen: end forward subsumption.")
	))
    )
  ;; all over
  clause)

;;; ----------------------------------
;;; PREPARE-INFERENCE : Module -> Void
;;;
(defun prepare-inference (mod)
  (declare (type module mod))
  ;;
  (clear-all-index-tables)
  ;;
  ;; add x = x if required
  ;;
  (if (pn-flag universal-symmetry)
      (let ((eqvar (make-variable-term *cosmos* (gensym "Univ"))))
	(declare (type term eqvar))
	(let ((symm (car (cnf-to-list
			  (make-term-with-sort-check *fopl-eq*
						     (list eqvar eqvar))
			  *current-psys*))))
	  (declare (type clause symm)
		   (type psystem *current-psys*))
	  (if (or (pn-flag auto)
		  (pn-flag auto1)
		  (pn-flag auto2)
		  (pn-flag auto3))
	      (push symm (psystem-axioms *current-psys*))
	    (progn (push symm (psystem-usable *current-psys*))
		   (push symm *usable*))
	    )
	  ;;
	  #||
	  (if (pn-flag simple-index)
	      (setq *universal-symmetry* nil)
	    (setq *universal-symmetry* (car symm)))
	  ||#
	  ))
    ;; (setq *universal-symmetry* nil)
    ()
    )
  ;; a dirty kludge
  (unless (or (pn-flag auto)
	      (pn-flag auto1)
	      (pn-flag auto2)
	      (pn-flag auto3))
    (setf (psystem-sos *current-psys*)
      (remove :system-goal (psystem-sos *current-psys*) :test #'eq))
    (setf *sos*
      (remove :system-goal *sos* :test #'eq)))

  ;; reset statistics

  (reset-pn-clocks)
  (reset-infer-statistics)
  ;; (clock-start pn-global-run-time)
  (pn-start-internal-clock)
  
  ;; setting flags/options for automode.
  
  (if (or (pn-flag auto) (pn-flag auto1))
      (pn-automatic-settings-1)
    (if (pn-flag auto2)
	(pn-automatic-settings-2)
      (if (pn-flag auto3)
	  (pn-automatic-settings-3)
	;; else, full manual mode:
	;; support setting sos implicitly by axiom label.
	;; (pn-automatic-sos-setting)
	;; NOT for now.
	()
	)))
  ;; 
  (check-pn-options)

  ;; process demodulators
  (setup-demodulators)

  ;; 
  (cond ((pn-flag process-input)
	 ;; PROCESS INPUT if RQUIRED
	 (when (pn-flag print-message)
	   (format t "~% ~%** start input processing.~%")
	   )
	 (when (and (pn-flag print-message)
		    (not (pn-flag print-lists-at-end)))
	   (print-usable-list))
	 (when (pn-flag print-message)
	   (with-output-simple-msg ()
	     (format t " process usable:")))
	 (setf (pn-stats usable-size) 0)
	 (let ((list *usable*))
	   (setq *usable* nil)
	   (dolist (c list)
	     (pre-process c t :usable))
	   (post-proc-all nil t :usable))
	 (when *current-psys*
	   (setf (psystem-usable *current-psys*) *usable*))
	 ;;
	 (when (and (pn-flag print-message)
		    (not (pn-flag print-lists-at-end)))
	   (print-sos-list)
	   )
	 (when (pn-flag print-message)
	   (with-output-simple-msg ()
	     (format t " process sos:")))
	 (setf (pn-stats sos-size) 0)
	 (let ((list *sos*))
	   (setq *sos* nil)
	   (dolist (c list)
	     (pre-process c t :sos)))
	 (post-proc-all nil t :sos)
	 ;;
	 (let ((list *passive*))
	   (dolist (c list)
	     ;; index passive
	     (index-all-literals c)))
	 ;;
	 (when (and (pn-flag print-message)
		    (not (pn-flag print-lists-at-end)))
	   (print-passive-list)
	   (print-demodulators-list))
	 ;;
	 (when (pn-flag print-message)
	   (format t "~%** end process input.~%"))
	 )
	;;
	(t
	 (setf (pn-stats usable-size) (length *usable*))
	 (setf (pn-stats sos-size) (length *sos*))
	 (pignose-index-all mod)
	 ))
  ;; weight clauses
  (let ((input-sos-first? (pn-flag input-sos-first)))
    (dolist (cl *sos*)
      (setf (clause-pick-weight cl)
	(if input-sos-first?
	    most-negative-fixnum
	  (weight-clause cl)))))

  ;; 
  (reset-memory-control)
  ;;
  (when *current-psys*
    ;; clean up sos & usable of module psys
    ;; they are now bound to globals
    ;; note: we must remain passive as is.
    (setf (psystem-sos *current-psys*) nil)
    (setf (psystem-usable *current-psys*) nil))

  ;; NOT USED....
  (setq *max-input-id* (1- (next-clause-num)))
  ;;
  )

;;; CHECK-PN-OPTIONS
;;; - check for inconsistent or odd settings
;;; - if a bad combination of sttings is found, either a warning
;;;   message is printed.
;;;
(defun check-pn-options ()
  (unless (or (pn-flag binary-res)
	      (pn-flag hyper-res)
	      (pn-flag neg-hyper-res)
	      (pn-flag ur-res)
	      (pn-flag para-from)
	      (pn-flag para-into)
	      (pn-flag demod-inf)
	      )
    (with-output-chaos-warning ()
      (princ "no inference rules are specified.")))
  ;;
  (when (and (pn-flag para-from)
	     (not (pn-flag para-from-right))
	     (not (pn-flag para-from-left)))
      (with-output-chaos-warning ()
	(princ "`para-from' is set, but `para-from-left' and `para-from-right' are both off.")))
    ;;
    (when (and (pn-flag para-into)
	       (not (pn-flag para-into-right))
	       (not (pn-flag para-into-left)))
      (with-output-chaos-warning ()
	(princ "`para-into' is set, but `para-into-left' and `para-from-right' are both off.")))
    ;;
    (when (and (not (pn-flag para-from))
	       (not (pn-flag para-into))
	       (pn-flag para-ones-rule))
      (with-output-chaos-warning ()
	(princ "`para-from', `para-into' rules are off, but `para-ones-rule' is set.")))
    ;;
    (when (and (or (pn-flag kb)
		   (pn-flag kb2)
		   (pn-flag kb3))
	       (not (pn-flag lrpo)))
      (with-output-chaos-warning ()
	(princ "`knuth-bendix' is set and `lrpo' is off.")))
    ;;
    (when (= (pn-parameter demod-limit) 0)
      (with-output-chaos-warning ()
	(princ "demod-limit=0; set it to -1 for no limit.")))

    (when (= (pn-parameter max-literals) 0)
      (with-output-chaos-warning ()
	(princ "max-literals=0; set it to -1 for no limit.")))

    (when (= (pn-parameter max-proofs) 0)
      (with-output-chaos-warning ()
	(princ "max-proofs=0; set it to -1 for no limit.")))

    (when (not (= -1 (pn-parameter pick-given-ratio)))
      (if (pn-flag sos-stack)
	  (with-output-chaos-warning ()
	    (princ "`sos-stack' has priority over `pick-given-ratio'."))
	(if (pn-flag sos-queue)
	    (with-output-chaos-warning ()
	      (princ "`sos-queue' has priority over `pick-given-ratio'.")))))
    (when (and (pn-flag sos-stack)
	       (pn-flag sos-queue))
      (with-output-chaos-warning ()
	(princ "`sos-queue' has priority over `sos-stack'.")))
    ;;
    #||
    (when (and (pn-flag para-all)
	       (pn-flag detailed-history))
      (with-output-chaos-warning ()
	(princ "detailed paramod history is ignored when `para-all' is set.")))
    ||#
    )

;;; EOF

