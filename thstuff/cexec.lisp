;;;-*-Mode:LISP; Package: CHAOS; Base:10; Syntax:Common-lisp -*-
;;; $Id: cexec.lisp,v 1.27 2010-07-02 07:03:49 sawada Exp $
(in-package :chaos)
#|=============================================================================
                               System:CHAOS
                              Module:thstuff
                             File:cexec.lisp
=============================================================================|#
#-(or :chaos-debug SBCL)
(declaim (optimize (speed 3) (safety 0) #-GCL (debug 0)))
#+:chaos-debug
(declaim (optimize (speed 1) (safety 3) #-GCL (debug 3)))

;;; set t if you want a debug mode --> set debug exec on.
;;; (defvar *cexec-debug* nil)

;;;
(declaim (special $$cexec-term))        ; the target term

;;; *****
;;; RULEs
;;; *****

;;; RULE-PAT
;;; - a rule applicable to the current target
;;; - POS: position matching 
;;; - RULE: the rule
;;; - SUBST: the substitution
;;;
(defstruct (rule-pat (:print-function print-rule-pattern))
  (pos nil :type list)			; matched position
  (rule nil)				; matched rule
  (subst nil)				; variable substitution
  (cond-ok t)				; t iff condition part of the rule is satisfied
  (condition nil)			; resulting condition part ('if') when cond-ok = nil
  (num 0 :type fixnum)			; sequential #, used for debugging
  )

(defvar .rules-so-far. 0)

(defun print-rule-pattern (rpat &optional (stream *standard-output*) &rest ignore)
  (format stream "~%-- rule pattern: ~d" (rule-pat-num rpat))
  (format stream "~%  posisition: ~a" (rule-pat-pos rpat))
  (format stream "~&  rule      :")(print-chaos-object (rule-pat-rule rpat))
  (format stream "~&  subst     :")(print-substitution (rule-pat-subst rpat))
  (format stream "~&  cond-ok   :~a" (rule-pat-cond-ok rpat))
  (format stream "~&  condition :")(term-print (rule-pat-condition rpat)))

(defun make-rule-pat-with-check (pos rule subst sch-context)
  (let ((condition (rule-condition rule)))
    (unless condition
      (return-from make-rule-pat-with-check (make-rule-pat :pos pos :rule rule :subst subst)))
    ;; pre check the condition part is satisfied or not
    (when (and (is-true? condition)
               (null (rule-id-condition rule)))
      (return-from make-rule-pat-with-check
        (make-rule-pat :pos pos :rule rule :subst subst :num (incf .rules-so-far.))))
    (let (($$term nil)
	  ($$cond (set-term-color
		   #||
		   (substitution-image-simplifying subst
						   condition
						   t
						   :slow)
		   ||#
		   (substitution-image-cp subst condition)
		   )))
      (when *cexec-debug*
	(format t "~%rule: cond ") (term-print-with-sort $$cond)
	(format t "~%      subst") (print-substitution subst)
	(let ((vars (term-variables $$cond)))
	  (dolist (v vars)
	    (format t "~% var ") (term-print-with-sort v))))

      (catch 'rule-failure
	(if (and (or (null (rule-id-condition rule))
                     (rule-eval-id-condition subst
                                             (rule-id-condition rule)
                                             :slow))
                 (is-true? (progn (normalize-term $$cond) $$cond)))
	    ;; the condition is satisfied
	    (return-from make-rule-pat-with-check 
	      (make-rule-pat :pos pos :rule rule :subst subst :cond-ok t :condition $$cond :num (incf .rules-so-far.)))
	  (if (rwl-sch-context-if sch-context)
	      ;; rule condition fail & there exists 'if'
	      (return-from make-rule-pat-with-check
		(make-rule-pat :pos pos :rule rule :subst subst :cond-ok nil :condition $$cond :num (incf .rules-so-far.)))
	    (return-from make-rule-pat-with-check nil))))
      nil)))

#||
(defmacro rule-pat-pos (pat) `(car ,pat))
(defmacro rule-pat-rule (pat) `(cadr ,pat))
(defmacro rule-pat-subst (pat) `(caddr ,pat))
||#

(defun rule-pat-equal (pat1 pat2)
  (and (equal (rule-pat-pos pat1) (rule-pat-pos pat2))
       (eq (rule-pat-rule pat1) (rule-pat-rule pat2))
       (substitution-equal (rule-pat-subst pat1) (rule-pat-subst pat2))))

;;; *****
;;; STATE
;;; *****

;;; RWL-STATE
;;; represents a state
;;;
(defstruct (rwl-state
            (:print-function pr-rwl-state))
  (state 0 :type fixnum)                ; fixnum value identifying this state
  (term nil)                            ; a term
  (trans-rules nil)                     ; applicable rules to this state
  (rule-pat nil)			; the rule-pat which derived this state
  (subst nil)                           ; list of substitution !!
  (is-final nil)                        ; t iff the state is a final state
  (loop nil)                            ; t iff the same state occurs more than once
  (condition nil)			;
  )

(defun state-is-valid-transition (state)
  (let ((cond (rwl-state-condition state)))
    (and (not (rwl-state-loop state))
	 (or (null cond)
	     (is-true? cond)))))

(defun pr-rwl-state (state &optional (stream *standard-output*) &rest ignore)
  (declare (ignore ignore))
  (let ((*standard-output* stream))
    (format t "#<rwl-state(~D):" (rwl-state-state state))
    (term-print (rwl-state-term state))
    (princ ", ")
    (dolist (sub (rwl-state-subst state))
      (print-substitution sub))
    (when (rwl-state-is-final state)
      (princ " ,final"))
    (princ ">")))

(defun print-rwl-state (state &optional (stream *standard-output*) &rest ignore)
  (declare (ignore ignore)
           (type rwl-state state)
           (type stream stream))
  (let ((*standard-output* stream))
    (format t "~&[state ~D] " (rwl-state-state state))
    (let ((*print-indent* (+ 4 *print-indent*)))
      (term-print-with-sort (rwl-state-term state))
      (when *cexec-trace*
        (format t "~& matched with the substitution "))
      (let ((*print-indent* (+ 4 *print-indent*)))
	(dolist (subst (rwl-state-subst state))
	  (print-next)
	  (print-substitution subst)))
      (flush-all))))

(defun print-state-transition (state sub-states &optional (stream *standard-output*))
  (declare (type rwl-state state)
           (type list sub-states)
           (type stream stream))
  (let ((*standard-output* stream)
        (arc-num 0))
    (declare (type fixnum arc-num))
    (format t "~&[state ~D] " (rwl-state-state state))
    (term-print-with-sort (rwl-state-term state))
    (dolist (sub sub-states)
      (format t "~&  arc ~D --> [state ~D] " arc-num (rwl-state-state sub))
      (let ((*print-indent* (+ 4 *print-indent*)))
        (print-next)
        (print-axiom-brief (rule-pat-rule (rwl-state-rule-pat sub))))
      (incf arc-num))
    ))

;;; ***********
;;; SEARCH TREE
;;; ***********

;;; Search tree
;;; - bi-directional dag (see comlib/dag.lisp)
;;; - datum contains an instance of rwl-state.
;;; 
(defstruct (rwl-sch-node (:include bdag)
            (:conc-name "SCH-NODE-")
            (:print-function pr-rwl-sch-node))
  (done nil)                            ; t iff this node is checked already
  (is-solution nil))                    ; t iff this node found as a solution

(defmacro create-sch-node (rwl-state)
  `(make-rwl-sch-node :datum ,rwl-state :subnodes nil :parent nil :is-solution nil))

(defun pr-rwl-sch-node (node &optional (stream *standard-output*) &rest ignore)
  (declare (ignore ignore))
  (let ((*standard-output* stream))
    (format t "SCH-NODE:~A" (dag-node-datum node))))

;;; RWL-SCH-NODE utils
;;;

;;; print the rule & state
;;;
(defun show-rwl-sch-state (dag &optional (path? t) (bind-pattern nil))
  (declare (type rwl-sch-node dag))
  (let* ((st (dag-node-datum dag))
         (term (rwl-state-term st))
         (rl (rule-pat-rule (rwl-state-rule-pat st)))
         (state (rwl-state-state st)))
    (when (and rl path?)
      (print-next)
      (princ "  ")
      (let ((*print-indent* (+ 8 *print-indent*)))
        (print-axiom-brief rl)))
    (format t "~&[state ~D] " state)
    (term-print-with-sort term)
    (dolist (sub (rwl-state-subst st))
      (format t "~&    ")
      (print-substitution sub)
      (when bind-pattern
	(let ((bimage (substitution-image-simplifying sub bind-pattern)))
	  (normalize-term bimage)
	  (format t "~%    => ")
	  (term-print-with-sort bimage))))))

;;; print the label of a rule which derived a state
;;; that denode contains.
;;;
(defun show-rwl-sch-label (dnode)
  (declare (type rwl-sch-node dnode))
  (let* ((dt (dag-node-datum dnode))
         (rl (rule-pat-rule (rwl-state-rule-pat dt)))
         (label (car (rule-labels rl))))
    (if label
        (format t "~&[~a]" label)
      (format t "~&NONE"))))

;;; **************
;;; SEARCH CONTEXT
;;; **************

;;; RWL-SCH-CONTEXT
;;; 
(defstruct (rwl-sch-context
            (:print-function print-sch-context))
  (module nil)                          ; context module
  (term nil)                            ; initial term
  (pattern nil)                         ; pattern to be matched
  (condition nil)                       ; =(*)=> with COND
  (zero-trans-allowed nil)              ; ... =>*
  (final-check nil)                     ; ... =>!
  (max-sol most-positive-fixnum :type fixnum) ; =(max-sol, )=>
  (sol-found 0 :type fixnum)            ; found solutions so far
  (max-depth most-positive-fixnum :type fixnum)
                                        ; =(, max-depth)=>
  (cur-depth 0 :type fixnum)            ; current depth
  (root nil)                            ; root node of the search tree
                                        ;   (an instance of rwl-sch-node) 
  ;; (states-so-far 0 :type integer)       ; # of states so far
  (trans-so-far 0 :type integer)        ; # of transitions so far
  (last-siblings nil)                   ; nodes to be checked
                                        ; initially, this contains the root.
  (state-predicate nil)                 ; STATE equality predicate
  (answers nil)                         ; list of STATEs satisfying specified
                                        ; conditions.
  (bind nil)				; ....
  (if nil)				;
  (pr-out? nil)				;
  )

(defun print-sch-context (ctxt &optional (stream *standard-output*) &rest ignore)
  (declare (ignore ignore))
  (let ((*standard-output* stream)
        (mod (rwl-sch-context-module ctxt)))
    (with-in-module (mod)
      (format t "~&<< sch context >>")
      (format t "~%   module: ")
      (print-chaos-object (rwl-sch-context-module ctxt))
      (format t "~%   term: ")
      (term-print-with-sort (rwl-sch-context-term ctxt))
      (format t "~%   pattern: ")
      (term-print-with-sort (rwl-sch-context-pattern ctxt))
      (format t "~%   condition: ")
      (if (rwl-sch-context-condition ctxt)
          (term-print-with-sort (rwl-sch-context-condition ctxt))
        (princ "None."))
      (format t "~%   zero?: ~A" (rwl-sch-context-zero-trans-allowed ctxt))
      (format t "~%   final?: ~A" (rwl-sch-context-final-check ctxt))
      (format t "~%   max sol. : ~D" (rwl-sch-context-max-sol ctxt))
      (format t "~%   solutions: ~D" (rwl-sch-context-sol-found ctxt))
      (format t "~%   max depth: ~D" (rwl-sch-context-max-depth ctxt))
      (format t "~%   current depth: ~D" (rwl-sch-context-cur-depth ctxt))
      (format t "~%   root node: ~A" (rwl-sch-context-root ctxt))
      ;; (format t "~%   states: ~D" (rwl-sch-context-states-so-far ctxt))
      (format t "~%   transitions: ~D" (rwl-sch-context-trans-so-far ctxt))
      (format t "~%   last siblings: ")
      (dolist (s (rwl-sch-context-last-siblings ctxt))
        (format t "~%     ~A" s))
      (format t "~%   answers: ")
      (dolist (x (reverse (rwl-sch-context-answers ctxt)))
        (term-print-with-sort (rwl-state-term x)))
      (when (rwl-sch-context-bind ctxt)
	(format t "~%   bind pattern: ")
	(term-print-with-sort (rwl-sch-context-bind ctxt)))
      (when (rwl-sch-context-if ctxt)
	(format t "~%   if: ")
	(term-print-with-sort (rwl-sch-context-if ctxt))))))

;;; .RWL-SCH-CONTEXT.
;;;  moved to comlib/globals.lisp
;;; (defvar .rwl-sch-context. nil)

;;; SEARCH CONTEXT UTILS
;;;

;;; show-rwl-sch-graph
;;;
(defun show-rwl-sch-graph (&optional num)
  (let ((c-num (if num
		   (read-from-string num)
		 0))
	(sch-context nil))
    (unless (integerp c-num)
      (with-output-chaos-error ('invalid-context-number)
	(format t "invalid search graph number ~s" num)))
    (setq sch-context (nth c-num (reverse .rwl-context-stack.)))
    (unless sch-context
      (with-output-chaos-error ('no-such-context)
	(format t "no such search graph ~d" num)))
    (let ((mod (rwl-sch-context-module sch-context))
	  (root (rwl-sch-context-root sch-context)))
      (unless mod
	(with-output-chaos-error ('no-context)
	  (format t "no context module...")))
      (unless root
	(with-output-chaos-error ('no-root)
	  (format t "no search result exists...")))
      (when (and *current-module*
		 (not (eq *current-module* mod)))
	(with-output-chaos-warning ()
	  (format t "the context(module) of search graph is different from the current module.")))
      ;;
      (with-in-module (mod)
	(let ((state-hash (make-hash-table)))
	  (dag-wfs root
		   #'(lambda (d)
		       (let* ((state-node (dag-node-datum d))
			      (state (rwl-state-state state-node)))
			 (unless (gethash state state-hash)
			   (setf (gethash state state-hash) t)
			   (print-state-transition
			    state-node
			    (mapcar #'(lambda (sd)
					(dag-node-datum sd))
				    (dag-node-subnodes d))))))))))))

(defun find-rwl-sch-state (num &optional (sch-context .rwl-sch-context.))
  (declare (type fixnum num))
  (unless sch-context
    (with-output-chaos-error ('no-root-node)
      (format t "no search result exists")))
  (let ((dag nil))
    (setq dag
      (catch 'dag-found
        (dag-wfs (rwl-sch-context-root sch-context)
                 #'(lambda (d)
                     (let ((st (dag-node-datum d)))
                       (when (= (rwl-state-state st) num)
                         (throw 'dag-found d)))))
        nil))
    dag))

(defun find-rwl-sch-state-globally (num)
  (declare (type fixnum num))
  (dolist (context .rwl-context-stack.)
    (let ((st (find-rwl-sch-state num context)))
      (when st (return-from find-rwl-sch-state-globally (values context st))))))

(defun show-rwl-sch-path (num-tok &optional (label? nil)
                                            (sch-context .rwl-sch-context.)
					    (state-only? nil))
  (unless num-tok
    (return-from show-rwl-sch-path
      (format t "~%nothing to be reported...")))
  (unless sch-context
    (with-output-chaos-error ('no-context)
      (format t "~%there is no search context.")))
  (let ((num (read-from-string num-tok)))
    (unless (and (integerp num) (>= num 0))
      (with-output-chaos-error ()
        (format t "state must be a positive integer value.")))
    (multiple-value-bind (sch-context dag)
	(find-rwl-sch-state-globally num)
      (unless dag
        (with-output-chaos-error ('no-state)
          (format t "no such state ~D" num)))
      (let ((mod (rwl-sch-context-module sch-context)))
        (when (and *current-module*
                   (not (eq *current-module* mod)))
          (with-output-chaos-warning ()
            (format t "the context(module) of search result is different from the current module.")))
        (with-in-module (mod)
	  (cond (state-only? (show-rwl-sch-state dag nil (rwl-sch-context-bind sch-context)))
		(t (let ((parents (get-bdag-parents dag)))
		     (cond (label?
			    (dolist (p (cdr parents)) ;root has no transition
			      (show-rwl-sch-label p))
			    (show-rwl-sch-label dag))
			   (t (dolist (p parents)
				(show-rwl-sch-state p t (rwl-sch-context-bind sch-context)))
			      (show-rwl-sch-state dag t (rwl-sch-context-bind sch-context))))))))))))


;;; *************
;;; PATTERN MATCH
;;; *************

;;; matcher
;;; 
#|| not used
(defun cexec-pat-match (pat target)
  (multiple-value-bind (gs sub no eeq)
      (@matcher pat target :match)
    (declare (ignore eeq))
    (null no)))
||# 

;;; finds all transition rules possibly applicable to the given target term
;;;
(defun find-matching-rules-for-exec (target sch-context &optional start-pos)
  (let ((module (rwl-sch-context-module sch-context)))
    (when start-pos
      (setq target (get-target-subterm target start-pos)))
    ;;
    (with-in-module (module)
      (let* ((*module-all-rules-every* t)
	     (rules (get-module-axioms *current-module* t))
	     (rls nil)
	     (res nil))
	(dolist (rule rules)
	  (when (rule-is-rule rule)
	    (push rule rls)
	    ;; add extensions also if any
	    ;; needless because 'apply-rule' applies extensions
	    #||
	    (let ((a-extensions (give-A-extensions rule))
		  (ac-extension (give-ac-extension rule)))
	      (dolist (rl a-extensions)
		(when rl
		  (push rl rls)))
	      (dolist (rl ac-extension)
		(when rl
		  (push rl rls))))
	    ||#
	    ))
	;; gather rules
	;; (clean-rule-table)
	(setq res (find-matching-rules-for-exec* target rls start-pos sch-context))
	(setq res (delete-duplicates res
				     :test #'rule-pat-equal))
	;;
	(when *cexec-debug*
	  (format t "~%** ~D rules were found for term: "
		  (length res))
	  (term-print target)
	  (terpri)
	  (dolist (r res)
	    (print-rule-pattern r)))
	;;
	res ))))

(defun find-matching-rules-for-exec* (target rules pos sch-context)
  (when *cexec-debug*
    (format t "~&find matching rules. ")
    (term-print target)
    (terpri))
  (if (term-is-application-form? target)
      (let ((res nil)
            (rule-pat nil))
        (do* ((rls rules (cdr rls))
              (rule (car rls) (car rls)))
            ((endp rls))
          (let* ((patterns nil)
                 (lhs (rule-lhs rule))
                 (head (if (term-is-variable? lhs)
                           nil
                         (term-head lhs))))
            ;;::
            ;;(unless rule (break "HANA !!!"))
            (push rule patterns)
	    ;; #|| ------- apply-rule always applies extensions
            (when head
              (when (method-is-associative head)
                (if (method-is-commutative head)
                    (let ((ac-ext (give-AC-extension rule)))
                      (when ac-ext
                        (unless (car ac-ext)
                          (print ac-ext)
                          (break "Here it is!"))
                        (push (car ac-ext) patterns)))
                  ;;
                  (let ((a-exts (give-A-extensions rule)))
                    (dolist (r a-exts)
                      ;; (unless r (break "HANA 2"))
                      (when r
                        (push r patterns)))))))
	    ;; ------------ ||#
            ;;
            (dolist (pat patterns)
              (block next
                ;; (break)
                (unless pat (break "HANA my"))
                #||
                (when (cexec-pat-match (axiom-lhs pat) target)
                  (push (make-rule-pat-with-check pos pat) res))
                ||#
                ;; find all possible subst
                (multiple-value-bind (gs sub no-match eeq)
                    (@matcher (axiom-lhs pat) target :match)
                  (declare (ignore eeq))
                  (when no-match (return-from next))
                  (setq rule-pat (make-rule-pat-with-check pos pat sub sch-context))
                  (when rule-pat
                    (push rule-pat res))
                  (loop
                    (multiple-value-setq (gs sub no-match)
                      (next-match gs))
                    (when no-match (return-from next))
                    (setq rule-pat (make-rule-pat-with-check pos pat sub sch-context))
                    (when rule-pat
                      (push rule-pat res))))
                ))
            ))                          ; done for all rules
        ;; recursively find rules for subterms
        (dotimes (x (length (term-subterms target)))
          (let ((r (find-matching-rules-for-exec* (term-arg-n target x)
						  rules
						  (append pos (list x))
						  sch-context)))
            (when r (setq res (nconc res r)))))
        ;;
        res)
    nil))

;;; ****************
;;; SOLUTION CHECKER
;;; ****************

(defun if-binding-should-be-printed (sch-context)
  #||
  (when *cexec-debug*
    (format t "~%++ checking print or not:~%  if = ~s, current depth = ~d, max = ~d"
	    (rwl-sch-context-if sch-context)
	    (rwl-sch-context-cur-depth sch-context)
	    (rwl-sch-context-max-depth sch-context)))
  ||#
  (and (rwl-sch-context-if sch-context)
       (<= (rwl-sch-context-cur-depth sch-context) (rwl-sch-context-max-depth sch-context))))

;;; rwl-sch-check-conditions (node rwl-sch-context)
;;; check if the given state matches to the target pattern.
;;; return t iff matches, otherwise nil.
;;;
(defun rwl-sch-check-conditions (node sch-context)
  (declare (type rwl-sch-node node)
           (type rwl-sch-context sch-context))
  (flet ((condition-check-ok (subst)
	   (let ((cond (rwl-sch-context-condition sch-context))
		 ($$term nil)
		 ($$cond nil)
		 (*rewrite-exec-mode* (if *rewrite-exec-condition*
					  *rewrite-exec-mode*
					nil)))
	     (if (null cond)
		 (setq $$cond *bool-true*)
	       (setq $$cond (set-term-color
			     (substitution-image-cp subst cond))))
	     (when *cexec-debug*
	       (format t "~&   subst:    ") (print-substitution subst)
	       (format t "~&   suchThat: ") (term-print $$cond))
	     (or (is-true? $$cond)
		 (is-true? (progn
			     (normalize-term $$cond)
			     (when *cexec-debug*
			       (format t " ---> ") (term-print $$cond)
			       (format t "~& = ~s" (is-true? $$cond)))
			     $$cond))))))
    ;; if checked already, we return immediately as non.
    (when (and (sch-node-done node) (null (rwl-sch-context-if sch-context)))
      (return-from rwl-sch-check-conditions nil))
    ;;
    (let* ((state (dag-node-datum node))
	   (if-var (rwl-sch-context-if sch-context))
	   (rule-pat (rwl-state-rule-pat state)))
      (declare (type rwl-state state))
      ;;
      (when *chaos-verbose*
        (format t " ~D" (rwl-state-state state)))
      ;;
      (setf (sch-node-done node) t)     ; mark checked already
      ;;
      ;; *** 
      ;; (return-from rwl-sch-check-conditions nil)
      (when *cexec-debug* 
	(when (rwl-sch-context-condition sch-context)
	  (format t "~%** check condition ")
	  (term-print-with-sort (rwl-sch-context-condition sch-context))
	  (if rule-pat
	      (print-rule-pattern rule-pat)
	    (format t "~% no rule-pat."))))
      ;; 0 transition?
      (when (and (not (rwl-sch-context-zero-trans-allowed sch-context))
                 ;; (= 0 (rwl-sch-context-cur-depth sch-context))
		 (= 0 (rwl-sch-context-trans-so-far sch-context)))
	;; (format t "~%Wow!")
	(when *cexec-debug*
	  (format t "~%.check condition return with 0 transition."))
        (return-from rwl-sch-check-conditions nil))
      ;; check with target pattern.
      (multiple-value-bind (gs sub no-match eeq)
          (@matcher (rwl-sch-context-pattern sch-context)
                    (rwl-state-term state)
                    :match)
        (declare (ignore eeq))
        (when no-match
	  (when *cexec-debug*
	    (format t "~%.check condition return with no-match."))
          (return-from rwl-sch-check-conditions nil))
	;; expand subst with 
	(when rule-pat
	  (setq sub (append sub (rule-pat-subst rule-pat))))
	;; additionaly expand subst 'if' part bindings
	(when if-var
	  (setq sub (substitution-add sub if-var (or (rwl-state-condition state)
						     *bool-true*))))
	(when (condition-check-ok sub)
	  (when	(if-binding-should-be-printed sch-context) ; if-var
	    (pr-used-rule state)
	    (print-subst-if-binding-result state sub sch-context))
	  (when (state-is-valid-transition state)
	    (push sub (rwl-state-subst state))))
        ;; try other patterns untill there's no hope
        (loop
          (multiple-value-setq (gs sub no-match)
            (next-match gs))
          (when no-match (return))
	  ;; expand subst with 
	  (setq sub (append sub (rule-pat-subst rule-pat)))
	  (when if-var
	    (setq sub (substitution-add sub if-var (or (rwl-state-condition state)
						       *bool-true*))))
	  (when (condition-check-ok sub)
	    (when (if-binding-should-be-printed sch-context) ; if-var
	      (when (pr-used-rule state)
		(print-subst-if-binding-result state sub sch-context)))
	    (when (state-is-valid-transition state)
	      (push sub (rwl-state-subst state))))))
      (not (null (rwl-state-subst state))))))

(defun pr-used-rule (state)
  (let ((rule-pat (rwl-state-rule-pat state))
	(rule nil))
    (unless rule-pat (return-from pr-used-rule nil))
    (setq rule (rule-pat-rule rule-pat))
    (unless *print-exec-rule*
      (when (member (axiom-kind rule) .ext-rule-kinds.)
	(return-from pr-used-rule nil)))
    (format t "~%=> ")
    (print-axiom-brief rule)
    t))

(defun print-subst-if-binding-result (state sub sch-context)
  (declare (ignore state))
  (setf (rwl-sch-context-pr-out? sch-context) t)
  (format t "~%    ") (print-substitution sub)
  (when (rwl-sch-context-bind sch-context)
    (let ((bimg (substitution-image-simplifying sub (rwl-sch-context-bind sch-context))))
      (normalize-term bimg)
      (format t "~%    --> ")
      (term-print-with-sort bimg))))

;;; ******************
;;; SOME UTILs on TERM
;;; ******************
;;; returns a subterm at position 'pos'
;;;
(defun get-target-subterm (term pos)
  (let ((cur term))
    (when pos
      (dolist (p pos)
        (setq cur (term-arg-n cur p))
        (unless cur
          (with-output-panic-message ()
            (format t "could not find subterm at pos ~d" pos)
            (format t "~% target was ")
            (term-print term)
            (break "wow!")
            (chaos-error 'panic)))))
    cur))

;;; *********
;;; TERM HASH
;;; *********
(defvar .cexec-term-hash. nil)

(defun initialize-cexec-term-hash ()
  (unless .cexec-term-hash.
    (setq .cexec-term-hash. (alloc-svec term-hash-size)))
  (clear-term-memo-table .cexec-term-hash.))

#-GCL
(declaim (inline get-sch-hashed-term))

(#-GCL defun #+GCL si:define-inline-function
 get-sch-hashed-term (term term-hash)
 (let ((val (hash-term term)))
   ;; (declare (type term-hash-key val))
   (let* ((ent (svref term-hash
                      (mod val term-hash-size)))
          (val (cdr (assoc term ent :test #'term-equational-equal))))
     (when val (incf (the (unsigned-byte 29) *term-memo-hash-hit*)))
     val)))

#-GCL
(declaim (inline set-sch-hashed-term))

(#-GCL defun #+GCL si:define-inline-function
 set-sch-hashed-term (term term-hash value)
 (let ((val (hash-term term)))
   ;; (declare (type term-hash-key val))
   (let ((ind (mod val term-hash-size)))
     (let ((ent (svref term-hash ind)))
       (let ((pr (assoc term ent :test #'term-equational-equal)))
         (if pr (rplacd pr value)
           (setf (svref term-hash ind) (cons (cons term value) ent))))))))

(defmacro cexec-get-hashed-term (term)
  `(get-sch-hashed-term ,term .cexec-term-hash.))

(defmacro cexec-set-hashed-term (term state-num)
  `(set-sch-hashed-term ,term .cexec-term-hash. ,state-num))

(defun cexec-sch-check-predicate (term t1 pred-pat)
  (let ((pred (car pred-pat))
        (vars (cdr pred-pat))
        (subst nil)
        (res nil))
    ;; make substittion
    (if (sort<= (term-sort term) (term-sort (car vars)) *current-sort-order*)
	(push (cons (car vars) term) subst)
      (with-output-chaos-error ('invalid-state)
	(format t "withStateEq: sort of term does not match with variable:")
	(format t "~%  variable: ")
	(term-print-with-sort (car vars))
	(format t "~%  term:  ")
	(term-print-with-sort term)))
    (if (sort<= (term-sort term) (term-sort (cadr vars)) *current-sort-order*)
	(push (cons (cadr vars) t1) subst)
      (with-output-chaos-error ('invalid-state)
	(format t "withStateEq: sort of term does not match with variable:")
	(format t "~%  variable: ")
	(term-print-with-sort (cadr vars))
	(format t "~%  term: ")
	(term-print-with-sort t1)))
      
    ;; apply subst with coping pred
    ;; then reduce
    (setq res
      (is-true?
       (let (($$cond (set-term-color
                      (substitution-image-cp subst pred)))
             (*rewrite-exec-mode*
              (if *rewrite-exec-condition*
                  *rewrite-exec-mode*
                nil)))
         (normalize-term $$cond)
         $$cond)))
    (when (and res *cexec-trace*)
      (format t "~&state predicate returned `true'."))
    res))

(defun cexec-loop-check (term sch-context)
  (or (cexec-get-hashed-term term)
      (let ((pred-pat (rwl-sch-context-state-predicate sch-context)))
        (if pred-pat
            (dotimes (x term-hash-size nil)
              (let ((ent (svref .cexec-term-hash. x)))
                (dolist (e ent)
                  (let ((t1 (car e)))
                    (when (cexec-sch-check-predicate term t1 pred-pat)
                      (return-from cexec-loop-check (cdr e)))))))
          nil))))

;;; 
;;; MAKE-RWL-STATE-WITH-HASH
;;;
(defun make-rwl-state-with-hash (target rule-pat sch-context)
  (let* ((ostate-num (cexec-loop-check target sch-context))
	 ;; (rule (rule-pat-rule rule-pat))
	 (condition (rule-pat-condition rule-pat))
	 (new-state nil))
    (cond (ostate-num
	   ;; this means the same state has alredy been generated
	   ;; from a node other than this node.
	   ;; we create brand new state with the same state number
	   (setq new-state (make-rwl-state :state ostate-num
					   :term  target
					   :rule-pat  rule-pat
					   :subst  nil
					   :condition condition))
	   (when (or *cexec-trace* *chaos-verbose*)
	     (format t "~&* loop"))
	   (setf (rwl-state-loop new-state) t))
          (t  (let (;; (state-num (incf (rwl-sch-context-states-so-far sch-context)))
		    (state-num (incf .rwl-states-so-far.)))
                (setq new-state (make-rwl-state :state state-num
                                                :term  target
                                                :rule-pat  rule-pat
                                                :subst  nil
						:condition  condition))
                ;; register the term
		(when *cexec-debug*
		  (format t "~%** hasing state ~D" state-num))
                (cexec-set-hashed-term target state-num))))
    ;;
    new-state))

;;; *******************
;;; ONE STEP TRANSITION
;;; *******************

;;; RWL-STATE-SET-TRANSITION-RULES
;;;
(defun rwl-state-set-transition-rules (state sch-context)
  (let ((rule-pats (find-matching-rules-for-exec (rwl-state-term state) sch-context)))
    (setf (rwl-state-trans-rules state) rule-pats)
    (unless rule-pats
      (setf (rwl-state-is-final state) t))))

;;;
;;; APPLY-RULE-CEXEC: rule target -> Bool
;;;
(defun apply-rule-cexec (rule term subst)
  (let ((condition (rule-condition rule))
        (builtin-failure nil))
    (when (and (is-true? condition)
               (null (rule-id-condition rule)))
      (setq builtin-failure
        (catch 'rule-failure
          (progn
            (term-replace-dd-simple
             term
             (set-term-color
              (substitution-image-simplifying subst
                                              (rule-rhs rule)
                                              (rule-need-copy rule)
                                              :slow)))
            (return-from apply-rule-cexec t)))))
    (when builtin-failure
      (return-from apply-rule-cexec nil))
    ;; check condition
    (catch 'rule-failure
      (when t
        #|| because we already check the condition is satisfied or not
        
        (and (or (null (rule-id-condition rule))
                 (rule-eval-id-condition subst
                                         (rule-id-condition rule)
                                         :slow))
             (is-true?
              (let (($$cond (set-term-color
                             (substitution-image-simplifying subst condition t :slow))))
                (normalize-term $$cond)
                $$cond)))
        ||#
        ;; the condition is satisfied
        (progn
          (term-replace-dd-simple
           term
           (set-term-color
            (substitution-image-simplifying subst
                                            (rule-rhs rule)
                                            (rule-need-copy rule)
                                            :slow)))
          (return-from apply-rule-cexec t))
        ))
    ;; failure
    nil))

;;; CEXEC-TERM-1 (state-as-dag)
;;;
;;; - compute all possible transitions from the given state(an instance of
;;;   rwl-sch-node).
;;; - returns the list of substates which derived from the given state.
;;; - NOTE: term of the given state is NOT modified.
;;;
(defun cexec-term-1 (dag sch-context)   ; node-num ...
  (declare (type rwl-sch-node dag)
           (type rwl-sch-context sch-context)
                                        ; (type fixnum node-num)
           )
  ;;
  (let* ((state (dag-node-datum dag))
         (term (rwl-state-term state)))
    (flet ((no-more-transition ()
             (when (or *cexec-trace* *chaos-verbose*)
               (when (and (term-is-applform? term)
                          (method-has-trans-rule (term-head term)))
                 (with-output-simple-msg ()
                   (format t "-- no more transitions from state ~D."
                           (rwl-state-state state)))))
             (setf (rwl-state-is-final state) t)
             nil)
           (exec-trace-form ()
             (format t "=(~a,~a)=>~a"
                     (if (= (rwl-sch-context-max-sol sch-context)
                            most-positive-fixnum)
                         "*"
                       (rwl-sch-context-max-sol sch-context))
                     (rwl-sch-context-cur-depth sch-context)
                     (if (rwl-sch-context-final-check sch-context)
                         "!"
                       (if (rwl-sch-context-zero-trans-allowed sch-context)
                           "*"
                         "+"))))
	   (state-is-valid? (state)
	     (let ((cond (rwl-state-condition state)))
	       (or (null cond) (is-true? cond)))))
      ;;
      (unless (state-is-valid? state)
	(return-from cexec-term-1 nil))
      ;;
      (let ((xterm term)
            (ptrans? (dag-node-subnodes dag)))
        (when *cexec-debug*
          (format t "~%[cexec-term-1] target = ")
          (let ((*fancy-print* nil))
            (term-print-with-sort xterm))
          (flush-all))
        ;; already computed ..
        (when ptrans? (return-from cexec-term-1 ptrans?))
        ;;
        ;; apply all rules found
        ;;
        (let ((rule-pats (rwl-state-trans-rules state))
              (*rewrite-exec-mode* t)
              (sub-states nil)
	      (real-pats nil))
	  (setq real-pats (remove-if #'(lambda (x) (not (rule-pat-cond-ok x))) rule-pats))
	  (when *cexec-debug*
	    (format t "~%++ ~D rule patterns for state" (length rule-pats))
	    (pr-rwl-state state))
	  (when *chaos-verbose*
	    (format t "~&-- from [state ~D] "
		    (rwl-state-state state))
	    (format t "~D possible transitions....."
                    (length real-pats)))
	  ;;
          (unless rule-pats
            ;; no rules
            (no-more-transition)
            (return-from cexec-term-1 nil))
          ;; 
          (when *cexec-trace*
            (flush-all)
            (format t "~%~%**> Step ~D from [state ~D] "
                    (rwl-sch-context-cur-depth sch-context)
                    (rwl-state-state state))
            (term-print-with-sort (rwl-state-term state))
            (flush-all))
          ;; apply all possible rules
          (do* ((rls rule-pats (cdr rls))
                (rule-pat (car rls) (car rls)))
              ;; ((endp rls))
	      ((null rule-pat))
            (let* ((target-whole (simple-copy-term xterm))
                   (target (get-target-subterm target-whole
                                               (rule-pat-pos rule-pat))))
              #||
              (when (eq target-whole target)
                (setq target (simple-copy-term target-whole)))
              ||#
              ;; the following should be done iff the target is NOT
              ;; in hash table + register target in hash.
              (when (apply-rule-cexec (rule-pat-rule rule-pat)
                                      target
                                      (rule-pat-subst rule-pat))
		#||
		(when (rule-pat-cond-ok rule-pat)
		  (incf (rwl-sch-context-trans-so-far sch-context)))
		||#
		(incf (rwl-sch-context-trans-so-far sch-context))
                ;;
                (when *cexec-normalize*
                  (when *cexec-debug*
                    (format t "~&.. start doing normalization because cexec normalize is on.~%  -- ")
                    (term-print target-whole))
                  (let ((*rewrite-exec-mode* nil)
                        (xterm (if (and *cexec-trace* *chaos-verbose*)
                                   (simple-copy-term target-whole)
                                 nil)))
		    (mark-term-as-not-lowest-parsed target-whole)
                    (reset-reduced-flag target-whole)
                    (rewrite* target-whole)
                    (when *cexec-debug*
                      (format t "~&==> ")
                      (term-print target-whole))
                    (when xterm
                      (print-next)
                      (unless (term-equational-equal xterm target-whole)
                        (flush-all)
                        (let ((*fancy-print* nil)
                              (*print-indent* (+ 4 *print-indent*)))
                          (princ "> pre normalization : ")
                          (term-print xterm)
                          (print-next)
                          (princ "== ")
                          (term-print target-whole))
                        (flush-all)))))
                ;;
                (let ((sub-state (make-rwl-state-with-hash target-whole
                                                           rule-pat
                                                           sch-context)))
                  (when (and sub-state
			     ;; (rule-pat-cond-ok rule-pat)
			     t
			     )
		    (when *cexec-debug*
		      (format t "~%** used rule pat = ~d" (rule-pat-num rule-pat)))
                    (when *cexec-trace*
                      (print-next)
                      (flush-all)
                      (let ((*fancy-print* nil)
                            (*print-indent* (+ 4 *print-indent*)))
                        (format t "@[~{~d~^ ~}]" (mapcar #'1+ (rule-pat-pos rule-pat)))
                        (exec-trace-form)
                        (format t " [state ~D] " (rwl-state-state sub-state))
                        (term-print-with-sort target-whole)
			(print-next)
			(print-axiom-brief (rule-pat-rule rule-pat))
			(print-next)
			(print-substitution (rule-pat-subst rule-pat))) ; ***
                      (flush-all))
                    ;;
                    (push sub-state sub-states)))))
            )                           ; done apply all rules
          ;;
          (if sub-states
              (progn
                (when *chaos-verbose*
                  (format t " => ~D (new) states."
                          (length sub-states) ))
                sub-states)
            (progn
              ;; for some unknown reason, no real transitions happened...
              (no-more-transition)
              nil)))))))

;;; RWL-STEP-FORWARD-1
;;; given a rwl-sch-context, execute one step transition for
;;; each `last-siblings' & check if derived terms match to `pattern'.
;;;
(defun rwl-step-forward-1 (sch-context)
  (declare (type rwl-sch-context sch-context))
  ;; check # of transitions
  (when (>= (rwl-sch-context-trans-so-far sch-context)
            *cexec-limit*)
    (return-from rwl-step-forward-1 (values :max-transitions nil)))
  ;;
  (let ((to-do (rwl-sch-context-last-siblings sch-context))
        (found? nil))
    (when *chaos-verbose*
      (format t "~&-- ~D state(s) to be examined --" (length to-do)))
    ;;
    ;; 1. check for each state if it satisfies the target conditions
    ;;
    (when *chaos-verbose*
      (format t "~&.....condition check for each state.....~%"))
    (loop
      (unless to-do (return nil))       ; done for every state
      (block :continue
        (let ((node (pop to-do)))
          (declare (type rwl-sch-node node))
          ;;
          (when (sch-node-done node)
            ;; already checked 
            (return-from :continue nil))
          ;;
          (let ((state (dag-node-datum node)))
            ;; first prepare applicable rules for the next transition,
            ;; this also marks the state `is-final' iff there are no rules.
            (rwl-state-set-transition-rules state sch-context)
            ;; check state
            (when (and (rwl-sch-context-final-check sch-context)
                       (not (rwl-state-is-final state)))
              (return-from :continue nil)) ; skip this node
            ;;
            (when (rwl-sch-check-conditions node sch-context)
              ;; register answer state
              (push (dag-node-datum node)
                    (rwl-sch-context-answers sch-context))
              ;;
              (unless *rwl-search-no-state-report*
                (format t "~&~%** Found [state ~D] " (rwl-state-state state))
                (term-print-with-sort (rwl-state-term state))
		(dolist (sub (rwl-state-subst state))
		  (print-subst-if-binding-result state sub sch-context)
		  )
                (format t "~&"))
              (setf (sch-node-is-solution node) t) ; mark the node as solution
              (incf (rwl-sch-context-sol-found sch-context))
              (setq found? :found)      ; we found at least one solution
              ;; check the # of solutions
              (when (>= (rwl-sch-context-sol-found sch-context)
                        (rwl-sch-context-max-sol sch-context))
                ;; reaches to the # solutions required.
                ;; mesg
                (unless *rwl-search-no-state-report*
                  (format t "~&-- found required number of solutions ~D."
                          (rwl-sch-context-max-sol sch-context)))
                (return-from rwl-step-forward-1 (values :max-solutions nil))))))
        )                               ; continue
      )                                 ; end loop
    ;;
    ;; 2. perform the next transitions for each node
    ;;
    (when *chaos-verbose*
      (format t "~&** precompute the next all states......"))
    ;; increment depth
    (incf (rwl-sch-context-cur-depth sch-context))
    ;;
    (let ((next-subs nil))
      (dolist (n (rwl-sch-context-last-siblings sch-context))
        ;; (unless n (break "wow! wow! "))
        (let ((subs (cexec-term-1 n sch-context))
              (nexts nil))
          (dolist (state subs)
            (let ((dag (create-sch-node state)))
              (setf (bdag-parent dag) n)
              (push dag (dag-node-subnodes n))
              (if (rwl-state-loop state)
                  ;; mark `done' if the state is already
                  ;; visited before..
		  (progn
		    (setf (sch-node-done dag) t)
		    (when (rwl-sch-context-if sch-context)
		      (when *cexec-debug*
			(format t "~%** calling check condition for reporting only."))
		      (rwl-sch-check-conditions dag sch-context))) ; for reporting only
                (push dag nexts))))
          ;; (format t "~&nexts=~a" nexts)
          (setq next-subs (nconc next-subs nexts))))
      ;; 
      ;; 3. lastly, set the next states as `last-siblings'
      ;;
      (setf (rwl-sch-context-last-siblings sch-context) next-subs)
      ;;
      ;; (or found? next-subs :no-more)
      (values found? (if next-subs
                         nil
                       :no-more)))))

;;; *********
;;; TOP LEVEL
;;; *********
(defun make-anything-is-ok-term ()
  (make-variable-term *cosmos* (gensym "Univ")))

(defun rwl-search* (t1 t2 max-result max-depth zero? final?
                    &optional cond
                              pred-pat
                              module
			      bind
			      if)
  (with-in-module (module)
    (unless t2
      (setq t2 (make-anything-is-ok-term)))
    (let ((svars (term-variables t1))	; variables in source
	  (pvars (term-variables t2))	; variables in pattern
	  (cvars (if cond		; variables in suchThat
		     (term-variables cond)
		   nil))
	  (predvars (if pred-pat	; variables in stateEq
			(term-variables pred-pat)
		      nil))
	  (ifvars (if if
		      (term-variables if)
		    nil))
	  (allvars nil)
	  (.rules-so-far. 0))
      (setq allvars (union svars (union pvars ifvars)))
      ;; check suchThat
      (when cvars
	(unless (subsetp cvars allvars)
	  (with-output-chaos-error ('invalid-such-that)
	    (format t "`suchThat' introduces new variable(s)."))))
      ;; check variables
      (dolist (v svars)
	(when (memq v pvars)
	  (with-output-chaos-error ('subject-var-occus)
	    (format t "Variable ")
	    (term-print-with-sort v)
	    ;; (format t " in subject term occurs in target pattern or coditions..")
	    (format t " in subject term occurs in target pattern.")
	    (format t "~& subject: ")
	    (term-print-with-sort t1)
	    (format t "~& pattern: ")
	    (term-print-with-sort t2))))
      (dolist (v predvars)
	(when (or (memq v svars)
		  (memq v pvars)
		  (memq v cvars))
	  (with-output-chaos-error ('invalid-stateEq)
	    (format t "Variable ")
	    (term-print-with-sort v)
	    (format t " in 'stateEq' occurs in subject term or target pattern or 'suchThat'.."))))
      ;;
      (let ((sch-context (make-rwl-sch-context
			  :module module
			  :term t1
			  :pattern t2
			  :condition cond
			  :zero-trans-allowed zero?
			  :final-check final?
			  :max-sol max-result
			  :max-depth max-depth
			  :state-predicate nil
			  :bind bind
			  :if if))
	    (root nil)
	    (res nil)
	    (no-more nil)
	    (found? nil))
	(flet ((make-state-pred-pat ()
		 (cond (pred-pat
			(let ((vars (term-variables pred-pat)))
			  (unless (sort= (term-sort pred-pat)
					 *Bool-sort*)
			    (with-output-chaos-error ('invalid-sort)
			      (format t "state equality must be of a term of sort Bool.")))
			  (unless (= 2 (length vars))
			    (with-output-chaos-error ('number-of-variables)
			      (format t "state equality pattern must have exactly 2 different variables in it, but ~D given." (length vars))))
			  #||
			  (when (variable= (car vars) (cadr vars))
			    (with-output-chaos-error ('invalid-variables)
			      (format t "variables in state equality pattern must be diffrent from each other.")))
			  ||#
			  (unless (sort= (variable-sort (car vars))
					 (variable-sort (cadr vars)))
			    (with-output-chaos-error ('different-variable-sort)
			      (format t "variables in state equality pattern must be of the same sort.")))
			  (unless (sort<= (term-sort t2) (term-sort (car vars))
					  *current-sort-order*)
			    (with-output-chaos-error ('invalid-variable-sort)
			      (format t "invalid sort of variable in state equality pattern.")))
			  (cons pred-pat vars)))
		       (t nil))))
	  ;;
	  ;; initialize search context
	  ;;
	  (setf (rwl-sch-context-cur-depth sch-context) 0)
	  (setf (rwl-sch-context-sol-found sch-context) 0)
	  ;; (setf (rwl-sch-context-states-so-far sch-context) 0)
	  (setf (rwl-sch-context-trans-so-far sch-context) 0)
	  (setq root (create-sch-node (make-rwl-state :state 0 :term t1)))
	  (setf (rwl-sch-context-root sch-context) root)
	  (setf (rwl-sch-context-last-siblings sch-context) (list root))
	  (setf (rwl-sch-context-answers sch-context) nil)
	  ;; state equality predicate
	  (setf (rwl-sch-context-state-predicate sch-context)
	    (make-state-pred-pat))
	  ;; bind context to global for later use...
	  (setq .rwl-sch-context. sch-context)
	  (push sch-context .rwl-context-stack.)
	  ;; term hash
	  (initialize-cexec-term-hash)
	  (cexec-set-hashed-term t1 0)
	  ;;
	  ;; do the search
	  ;;
	  (when *cexec-debug*
	    (print sch-context))
	  (loop
	    (when *chaos-verbose*
	      (format t "~&** << level ~D >>" (rwl-sch-context-cur-depth sch-context)))
	    ;;
	    (multiple-value-setq (res no-more)
	      (rwl-step-forward-1 sch-context))
	    ;; (setq res (rwl-step-forward-1 sch-context))
	    (case res
	      (:max-transitions (return nil)) ; exit loop
	      (:max-solutions
	       (setq found? t)
	       (return nil))		; exit loop
	      (:found
	       (setq found? t))		; continue..
	      (otherwise nil))
	    (when no-more
	      (unless *rwl-search-no-state-report*
		(format t "~&~%** No more possible transitions."))
	      (return nil))		; exit if no more ...
	    ;; one step deeper
	    (when (> (rwl-sch-context-cur-depth sch-context)
		     (rwl-sch-context-max-depth sch-context))
	      (format t "~&-- reached to the specified search depth ~D."
		      (rwl-sch-context-max-depth sch-context))
	      (return-from rwl-search*
		(if (rwl-sch-context-if sch-context)
		    (if (rwl-sch-context-pr-out? sch-context)
			:found
		      nil)
		  (if found? :found :max-depth))))
	    )				; end loop
	  ;; any solution?
	  (cond ((rwl-sch-context-if sch-context)
		 (if (rwl-sch-context-pr-out? sch-context)
		     :found
		   nil))
		(t (if found? 
		       ;; yes
		       :found
		     ;; no
		     res))))))))

;;; report-rwl-result
;;;
(defun report-rwl-result (res)
  (case res
    (:max-depth
     ;; (format t "~&-- reached to the max depth.")
     )
    (:no-more
     ;; (format t "~&-- no more solutions.")
     )
    (otherwise
     nil))
  res)

;;; RWL-CONTINUE
;;;
(defun rwl-continue (num-tok)
  (multiple-value-bind (num sym)
      (nat*-to-max-option num-tok)
    (declare (ignore sym))
    (report-rwl-result
     (rwl-continue* num))))

(defun rwl-continue+ (num)
  (report-rwl-result (rwl-continue* num)))

(defun rwl-continue* (num)
  (declare (type fixnum num))
  (unless (and .rwl-sch-context.
               (or (null *current-module*)
                   (eq *current-module*
                       (rwl-sch-context-module .rwl-sch-context.))))
    (with-output-chaos-error ('invalid-context)
      (format t "invalid context...")))
  ;;
  (with-in-module ((rwl-sch-context-module .rwl-sch-context.))
    (setf (rwl-sch-context-max-sol .rwl-sch-context.) num)
    (setf (rwl-sch-context-sol-found .rwl-sch-context.) 0)
    (setf (rwl-sch-context-max-depth .rwl-sch-context.) most-positive-fixnum)
    ;;
    ;; do continue search
    ;;
    (let ((sch-context .rwl-sch-context.)
          (res nil)
          (found? nil))
      (loop
        (setq res (rwl-step-forward-1 sch-context))
        (case res
          ((:max-transitions
            :max-solutions
            :no-more)
           (return nil))                ; exit loop
          (:found
           (setq found? t))
          (otherwise nil))
        ;; one step deeper
        (incf (rwl-sch-context-cur-depth sch-context))
        )                               ; end loop
      (if found?
          :found
        res))))

;;; RWL-SEARCH
;;;
(defun rwl-search (&key term
                        pattern
                        (max-result most-positive-fixnum)
                        (max-depth most-positive-fixnum)
                        (zero? nil)
                        (final? nil)
                        (cond nil)
                        (pred nil)
			(bind nil)
			;; the followings are experimental
			(if nil))
  (let ((module (or *current-module* *last-module*))
        max-r
        max-d)
    (unless module
      (with-output-chaos-error ('no-context)
        (format t "no context module..")))
    (if (integerp max-result)
        (setq max-r max-result)
      (if (term-is-builtin-constant? max-result)
          (setq max-r (term-builtin-value max-result))
        (setq max-r most-positive-fixnum)))
    (if (integerp max-depth)
        (setq max-d max-depth)
      (if (term-is-builtin-constant? max-depth)
          (setq max-d (term-builtin-value max-depth))
        (setq max-d most-positive-fixnum)))
    (when (and if (not (term-is-variable? if)))
      (with-output-chaos-warning ()
	(format t "The `if' part is not a varible of sort BOOL, `if' binding is ignored : ")
	(print-next)
	(term-print if)
	(setq if nil)))
    ;; ***
    ;; (clear-term-memo-table *term-memo-table*)
    ;; ***
    (when *cexec-normalize*
      (let ((*rewrite-exec-mode* nil)
            (*clean-memo-in-normalize* nil))
        (rewrite* term)))
    ;;
    (when *cexec-debug*
      (format t "~&* CEXEC: ")
      (term-print-with-sort term))
    ;;
    (let ((*clean-memo-in-normalize* nil))
      (report-rwl-result 
       (rwl-search* term pattern max-r max-d zero? final? cond pred module bind if)))))

;;; rwl-sch-set-result
;;;
(defun rwl-sch-set-result (raw-res)
  (let ((res nil))
    (if (eq raw-res :found)
        (setq res t)
      (setq res nil))
    (setq $$cexec-term (coerce-to-bool res))))

;;; rwl-cont
;;;
(defun rwl-cont (ast)
  (rwl-continue+ (%continue-num ast)))

;;;
;;; for downward compatibility
;;;
(defun nat*-to-max-option (term &optional (infinite most-positive-fixnum))
  (if (term-is-builtin-constant? term)
      (values (term-builtin-value term) "")
    (values infinite (car (method-symbol (term-head term))))))

(defun term-pattern-included-in-cexec (t1 t2 max-depth &optional cond)
  (multiple-value-bind (max sym)
      (nat*-to-max-option max-depth)
    (let ((final? nil)
          (zero? nil)
          )
      (case-equal sym
                  ("!" (setq final? t))
                  ("*" (setq zero? t))
                  (otherwise nil))
      (clear-term-memo-table *term-memo-table*)
      (rwl-search* t1 t2 1 max zero? final? cond nil *current-module*))))

;;; EOF
