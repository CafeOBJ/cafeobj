;;;-*- Mode:LISP; Package: CHAOS; Base:10; Syntax:Common-lisp -*-
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
#|=============================================================================
                                    System:CHAOS
                                   Module:cafein
                                 File:rengine.lisp
=============================================================================|#
#-:chaos-debug
(declaim (optimize (speed 3) (safety 1) #-GCL (debug 0)))
#+:chaos-debug
(declaim (optimize (speed 1) (safety 3) #-GCL (debug 3)))

;;; -------------------
;;; TRACING or STEPPING
;;; -------------------
(defvar .trace-or-step. nil)

 ;;; -------
 ;;; MEMOIZE
 ;;; -------

(deftype term-hash-key () '(unsigned-byte 29))

(defconstant term-hash-mask #x1FFFFFFF)

(defconstant term-hash-size 9001)

(defmacro method-has-memo-safe (m)
  `(and (method-p ,m) (method-has-memo ,m)))

#-GCL (declaim (inline term-hash-equal))
#-(or GCL CMU)
(defun term-hash-equal (x)
  (logand term-hash-mask (sxhash x)))
#+CMU
(defun term-hash-equal (x)
  (sxhash x))
#+GCL
(si:define-inline-function term-hash-equal (x) (sxhash x))

#+GCL
(Clines "static object term_hash_eq(x) 
   object x;
   { return(make_fixnum(((((int)x) & 0x1fffffff)+3)>>3)); }
 ")

#+GCL
(defentry term-hash-eq (object) (object term_hash_eq))

#-GCL
(declaim (inline term-hash-eq))
#-GCL
(defun term-hash-eq (object)
  (ash (+ (the term-hash-key
	    (logand term-hash-mask
		    (the (unsigned-byte 32) (addr-of object))))
	  3)
       -3))

#-GCL
(declaim (inline term-hash-comb))

#||
(defun term-hash-comb (x y)
  ;; (declare (type term-hash-key x y))
  (the term-hash-key
    (logxor (the term-hash-key (ash x -5))
	    y
	    (the term-hash-key
	      (logand term-hash-mask
		      (the term-hash-key (ash (logand x 31) 26)))))))
||#

#-GCL
(defun term-hash-comb (x y)
  ;; (declare (type term-hash-key x y))
  (the term-hash-key (logand term-hash-mask (logand term-hash-mask (+ x y)))))

                                        ;#+GCL
                                        ;(si:define-inline-function term-hash-comb (x y)
                                        ;  (make-and term-hash-mask (+ x y)))

;;; #+GCL
;;; (si:define-inline-function term-hash-comb (x y)
;;;   (make-xor (ash x -5) y (ash (make-and x 31) 26))
;;;  )

;;;
;;; term-hash
;;;
;;; (defvar *on-term-hash-debug* nil)

(defstruct term-hash
  (size term-hash-size :type (unsigned-byte 14) :read-only t)
  (table nil :type (or null simple-array)) )

(defun hash-term (term)
  (cond ((term-is-applform? term)
         (let ((res (sxhash (the symbol (method-id-symbol (term-head term))))))
           (dolist (subterm (term-subterms term))
             (setq res (term-hash-comb res (hash-term subterm))))
           res))
        ((term-is-builtin-constant? term)
         (term-hash-comb (sxhash (the symbol (sort-id (term-sort term))))
                         (term-hash-equal (term-builtin-value term))))
        ((term-is-variable? term) (term-hash-eq term))))

(defun dump-term-hash (term-hash &optional (size term-hash-size))
  (dotimes (x size)
    (let ((ent (svref term-hash x)))
      (when ent
        (format t "~%[~3d]: ~d entrie(s)" x (length ent))
        (dotimes (y (length ent))
          (let ((e (nth y ent)))
            (format t "~%(~d)" y)
            (let ((*print-indent* (+ 2 *print-indent*)))
              (term-print (car e))
              (print-next)
              (princ "==>")
              (print-next)
              (term-print (cdr e)))))))))

#-GCL
(declaim (inline get-hashed-term))

(#-GCL defun #+GCL si:define-inline-function
 get-hashed-term (term term-hash)
 (let ((val (hash-term term)))
   (let* ((ent (svref term-hash
		      (mod val term-hash-size)))
	  (val (cdr (assoc term ent :test #'term-is-similar?))))
     (when val (incf *term-memo-hash-hit*))
     val)))

#-GCL
(declaim (inline set-hashed-term))

(#-GCL defun #+GCL si:define-inline-function
 set-hashed-term (term term-hash value)
 (let ((val (hash-term term)))
   (let ((ind (mod val term-hash-size)))
     (let ((ent (svref term-hash ind)))
       (let ((pr (assoc term ent :test #'term-is-similar?)))
         (if pr (rplacd pr value)
           (setf (svref term-hash ind) (cons (cons term value) ent))) )))))

;;; *TERM-MEMO-TABLE*

(defvar *term-memo-table* nil)
(defvar *memoized-module* nil)

(defun create-term-memo-table ()
  (unless *term-memo-table*
    (setq *term-memo-table*
      (alloc-svec term-hash-size))))

(defun clear-term-memo-table (table)
  (dotimes (x term-hash-size)
    (setf (svref table x) nil))
  table)

;;;		      BASIC COMMON ROUTINES FOR REWRITING

(defvar *cafein-current-rule* nil)
(defvar *cafein-current-subst* nil)
(defvar *matched-to-stop-pattern* nil)

;;; ----------
;;; TERM COLOR
;;; ----------

(defun set-term-color-top (term)
   (if (not *beh-rewrite*)
       (if (sort-is-hidden (term-sort term))
           (set-term-color term :red)
         (set-term-color term))
     (set-term-color term)))

(defun set-term-color (term &optional red?)
   (labels ((set-color (term set-red)
              (if set-red
                  (progn
                    (term-set-red term)
                    (when (term-is-applform? term)
                      (dolist (sub (term-subterms term))
                        (when (sort-is-hidden (term-sort sub))
                          (set-color sub :red)))))
                (when (term-is-applform? term)
                  (let* ((head (term-head term))
                         (is-beh-coh-context
                          (or (method-is-behavioural head)
                              (method-is-coherent head)
                              (eq head *beh-eq-pred*) ; =b=
                              (eq head *beh-equal*) ; =*=
                              (and *beh-rewrite*
                                   (or (eq head *bool-equal*) ; ==
                                       (eq head *bool-nonequal*) ; =/=
                                       ))))
                         (i-am-red nil))
                    (dolist (sub (term-subterms term))
                      (if (sort-is-hidden (term-sort sub))
                          (if is-beh-coh-context
                              (progn
                                (set-color sub nil))
                            (progn
                              (setq i-am-red t)
                              (set-color sub :red)))
                        ;;
                        (set-color sub nil)))
                    (if i-am-red
                        (term-set-red term)
                      (term-set-green term)))))
              ))                        ; end labels
     ;;
     (unless (or *beh-rewrite* *rewrite-semantic-reduce*)
       (return-from set-term-color term))
     ;;
     (set-color term red?)
     term))

;;; **************************
;;; LOW LEVEL REWRITE ROUTINES
;;; **************************

;;; CHECK BEHAVIOURAL CONTEXT

(defmacro beh-context-ok? (rule term)
   `(if (axiom-is-behavioural ,rule)
        (or (not (term-is-red ,term))
            (and *beh-rewrite*
                 (eq $$term ,term)))
      t))

(declaim (inline apply-rules-with-same-top apply-rules-with-different-top))

;;; ----------------------------------------
;;; BASIC PROCS for REWRITE RULE APPLICATION
(defvar *memo-debug* nil)

(declaim (inline term-replace-dd-simple))
#-gcl
(defun term-replace-dd-simple (old new)
   (declare (type term old new)
            (values term-body))
   (incf *rule-count*)
   (term-replace old new))

#+gcl
(si::define-inline-function term-replace-dd-simple (old new)
   (incf *rule-count*)
   (term-replace old new))

(declaim (special *m-pattern-subst* $$cond))
(defvar *m-pat-debug* nil)

(defun !apply-one-rule (rule term &aux (applied nil))
  (declare (type axiom rule)
           (type term term)
           (values (or null t)))
  (when (or (is-true? term) (is-false? term))
    (return-from !apply-one-rule nil))
  ;; check stop pattern
  (when .trace-or-step.
    (check-stop-pattern term))
  
  ;; apply rule
  (setq *cafein-current-rule* rule)
  ;; before rewriting, check if := matching has been done in this context
  (when (and *m-pattern-subst* $$cond)
    (let ((nt (set-term-color
               (substitution-image-simplifying *m-pattern-subst*
                                               term
                                               (rule-need-copy rule)))))
      ;; substitute variables in the current target with subst obtained by := match.
      (term-replace term nt)
      (when *m-pat-debug*
        (format t "~&[applied *m-pattern-subst*]")
        (print-substitution *m-pattern-subst*)
        (format t "--> ")
        (term-print-with-sort term))))
  ;; start rewriting
  (setq applied                         ; will be t iff a rewrite rule is applied
    (block the-end
      (let* ((condition nil)
             (cur-trial nil)
             (next-match-method nil)
             (*trace-level* (1+ *trace-level*))
             (*print-indent* *print-indent*)
             (*self* term)
             (builtin-failure nil)
             (rhs-instance nil))
        (multiple-value-bind (global-state subst no-match E-equal)
            ;; first we find matching rewrite rule 
            (funcall (or (rule-first-match-method rule)
                         (progn
                           (when *chaos-verbose*
                             (with-output-chaos-warning ()
                               (format t "Internal, no 'matching-mehod' is assigned for:")
                               (print-next)
                               (print-axiom-brief rule)))
                           (compute-rule-method rule)
                           (rule-first-match-method rule)))
                     (rule-lhs rule)
                     term)
          ;; stat, count up number of matching trials
          (incf $$matches)
          (setq *cafein-current-subst* subst) ; I don't remember for what this is used
          ;; if matching fail no hope to rewriting. 
          (when no-match (return-from the-end nil))
          ;; 
          (unless (beh-context-ok? rule term)
            (return-from the-end nil))
          
          ;; technical assignation related to substitution-image.
          (when E-equal (setq subst nil))
          ;; match success with LHS of the rewrite rule.
          ;; next we check condition part of the rewrite rule.
          (setq condition (rule-condition rule))
          (when (and (is-true? condition)
                     (null (rule-id-condition rule)))
            ;; the case of non-conditional rule.
            ;; we generate an instance of RHS of the rule.
            (setq builtin-failure       ; will be t iff there occured an error 
                                        ; in making instance of RHS with builtin lisp form.
              (catch 'rule-failure
                ;; there is no condition --
                ;; rewrite term.
                
                ;; handle trace
                (when (or $$trace-rewrite
                          (rule-trace-flag rule))
                  (let ((*print-with-sort* t))
                    (print-trace-in)
                    (princ "rule: ")
                    (let ((*print-indent* (+ 2 *print-indent*)))
                      (print-axiom-brief rule))
                    (let ((*print-indent* (+ 4 *print-indent*)))
                      (print-next)
                      (print-substitution subst))))
                ;; note that the computation of the substitution
                ;; made a copy of the rhs.
                (setq rhs-instance (set-term-color
                                    (substitution-image-simplifying subst
                                                                    (rule-rhs rule)
                                                                    (rule-need-copy rule))))
                ;; rewrite the term with the instance of RHS.
                (if .trace-or-step.
                    (term-replace-dd-dbg term rhs-instance)
                  (term-replace-dd-simple term rhs-instance))
                ;; successfull rewriting.
                (return-from the-end t))))

          ;; We come here either catching an error with builtin rule
          ;; or, the target rewrite rule is conditional.
          ;; both case need trying different mathing if exists
          (setq next-match-method (rule-next-match-method rule))
          (when builtin-failure
            ;; this means that the term contains some variables:
            ;; if we are lucky, we may find a successful match.
            (loop
              (when (or $$trace-rewrite
                        (rule-trace-flag rule))
                (with-output-msg ()
                  (format t "!! built in rule failed !!")))
              ;;
              (multiple-value-setq (global-state subst no-match)
                (progn
                  (incf $$matches)
                  (funcall next-match-method global-state)))
              (when no-match
                ;; no more match, we failed
                (return-from the-end nil))
              ;; found another match, try rewrite with this
              (setq *cafein-current-subst* subst) ; what is this...
              (setq cur-trial $$trials)
              (when (or $$trace-rewrite
                        (rule-trace-flag rule))
                (let ((*print-with-sort* t))
                  (print-trace-in)
                  (princ "-- rule: ")
                  (let ((*print-indent* (+ 2 *print-indent*)))
                    (print-axiom-brief rule))
                  (let ((*print-indent* (+ 4 *print-indent*)))
                    (print-next)
                    (print-substitution subst))
                  (force-output)))
              ;; 
              (catch 'rule-failure
                (setq rhs-instance (set-term-color
                                    (substitution-image-simplifying subst
                                                                    (rule-rhs rule)
                                                                    (rule-need-copy rule))))
                (if .trace-or-step.
                    (term-replace-dd-dbg term rhs-instance)
                  (term-replace-dd-simple term rhs-instance))
                (return-from the-end t))))

          ;; here is the case of conditional rule. 
          ;; if the condition is not trivial, we enter in a loop
          ;; where one try to find a match such that the condition 
          ;; is satisfied.
          (loop 
            ;;
            (when (and *condition-trial-limit*
                       (>= $$trials *condition-trial-limit*))
              (with-output-chaos-warning ()
                (format t "~%Infinite loop? Evaluating rule condition, exceeds trial limit ~d" $$trials)
                (format t "~&terminates rewriting: ")
                (term-print $$term))
              (chaos-error 'too-deep))
            ;;
            (setq *cafein-current-subst* subst)
            (setq cur-trial $$trials)
            (when (= 1 cur-trial) (setq *m-pattern-subst* nil)) ; !!
            (when (or $$trace-rewrite
                      (rule-trace-flag rule))
              (let ((*print-with-sort* t))
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
            (catch 'rule-failure
              (when (and (or (null (rule-id-condition rule))
                             (rule-eval-id-condition subst
                                                     (rule-id-condition rule)))
                         (is-true?
                          (let (($$cond (set-term-color
                                         (substitution-image-cp subst condition)))
                                (*rewrite-exec-mode*
                                 (if *rewrite-exec-condition*
                                     *rewrite-exec-mode*
                                   nil))
                                ($$trials (1+ $$trials)))
                            ;; no simplyfing since probably wouldn't pay
                            (normalize-term $$cond)
                            ;; :=
                            (when *m-pattern-subst*
                              (dolist (sub *m-pattern-subst*)
                                (push sub subst))
                              (when *m-pat-debug*
                                (format t "~%[subst-+] ")
                                (print-substitution *m-pattern-subst*)
                                (format t "~&[subst-updated] ")
                                (print-substitution subst)))
                            $$cond)))
                ;; the condition is satisfied
                (when (or $$trace-rewrite
                          (rule-trace-flag rule))
                  (print-trace-in)
                  (format t "match success #~D" cur-trial))
                (setq rhs-instance (set-term-color
                                    (substitution-image-simplifying subst
                                                                    (rule-rhs rule)
                                                                    (rule-need-copy rule))))
                  (if .trace-or-step.
                      (term-replace-dd-dbg term rhs-instance)
                    (term-replace-dd-simple term rhs-instance))
                  (return-from the-end t)))
            
            ;; else, try another ...
            (multiple-value-setq (global-state subst no-match)
              (progn
                (incf $$matches)
                (funcall next-match-method global-state)))
            (when no-match
              (when (or $$trace-rewrite
                        (rule-trace-flag rule))
                (print-trace-in)
                (format t "rewrite rule exhausted (#~D)" cur-trial)
                (force-output))
              (return))
            ;;
            (unless (beh-context-ok? rule term)
              (return-from the-end nil))
            )                           ; end loop
          ))))                          ; end of main process
  ;;
  (unless $$cond
    ;; we reset := substitution 
    (setq *m-pattern-subst* nil))
  ;;
  (if applied
      ;; applied a rule.
      t
    ;; else no rule was applied
    (if *matched-to-stop-pattern*
        (if *rewrite-stepping*
            nil
          (progn
            (setq *matched-to-stop-pattern* nil)
            (throw 'rewrite-abort $$term)))
      nil)))

(defun term-replace-dd-dbg (old new)
  (declare (type term old new))
  ;; stat number of rewriting
  (incf *rule-count*)
  ;; check if given stop pattern was matched to the resultant term.
  (when *matched-to-stop-pattern*
    ;; yes
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
        (term-print-with-sort old)
        (print-check 0 5)
        (princ " --> ")
        (term-print-with-sort new))
      (unless $$trace-rewrite-whole (terpri))))
  ;; trace whole
  (if $$trace-rewrite-whole
      (let ((*print-with-sort* t)
            (*fancy-print* t))
        (if $$cond
            (progn
              (format t "~&[~a(cond)]: " *rule-count*)
              (let ((*print-indent* (+ 2 *print-indent*)))
                (term-print-with-sort $$cond)
                (print-next)
                (let ((res (term-replace old new)))
                  (print-check 0 5)
                  (princ " --> ")
                  (let ((*print-indent* (+ 2 *print-indent*)))
                    ;; (print-check)
                    (term-print-with-sort $$cond))
                  res)))
          (progn
            (format t "~&[~a]: " *rule-count*)
            (let ((*print-indent* (+ 2 *print-indent*)))
              (term-print-with-sort $$term))
            (print-next)
            (let ((res (term-replace old new)))
              (print-check 0 5)
              (princ "---> ")
              (let ((*print-indent* (+ 2 *print-indent*)))
                ;; (print-check)
                (term-print-with-sort $$term))
              res))))
    ;; after tracing, we finally rewrite the target
    (term-replace old new))
  ;; check rewrite count limit
  (when (and *rewrite-count-limit*
             (<= *rewrite-count-limit* *rule-count*))
    (format *error-output* "~%>> aborting rewrite due to rewrite count limit (= ~d) <<"
            *rewrite-count-limit*)
    (flush-all)
    (throw 'rewrite-abort $$term))
  ;;
  $$term)

(defun apply-rules-with-same-top (term rule-ring)
  (declare (type term term)
           (type rule-ring rule-ring))
  (let ((rr-ring (rule-ring-ring rule-ring)))
    (when rr-ring
      (let ((rr-current rr-ring)
            (rr-mark rr-ring)
            rule)
        (loop
          (setq rule (car rr-current))
          (unless (eq (axiom-kind rule) :bad-rule)
            (when (apply-rule rule term)
              (setq rr-mark rr-current)
              (loop (unless (apply-rule rule term) (return nil))))
            (setq rr-current (cdr rr-current))
            (when (eq rr-current rr-mark) (return nil))))))))

(defun apply-rules-with-different-top (term rules)
 (declare (type term term)
          (type list rules)
          (values (or null t)))
 (block the-end
   (dolist (rule rules nil)
     (unless (eq (axiom-kind rule) :bad-rule)
       (when (apply-rule rule term) (return-from the-end t))))))

(defun apply-rules (term strategy)
  (declare (type term term)
           (type list strategy)
           (values (or null t)))
  (labels ((apply-rules-internal ()
             (let ((top nil))
               ;; (unless (term-is-lowest-parsed? term) (update-lowest-parse term))
               (setq top (term-head term))
               ;; apply same top rules
               (apply-rules-with-same-top term (method-rules-with-same-top top))
               (if (not (eq top (term-head term)))
                   (progn
                     (mark-term-as-not-lowest-parsed term)
                     (normalize-term term))
                 (if (apply-rules-with-different-top term
                                                     (method-rules-with-different-top top))
                     (progn
                       (mark-term-as-not-lowest-parsed term)
                       (normalize-term term))
                   (reduce-term term (cdr strategy)))))))
    ;;
    (if *memo-rewrite*
        ;; check memo
        (if (or *always-memo*
                (method-has-memo (term-head term)))
            (let ((normal-form (get-hashed-term term *term-memo-table*)))
              (if normal-form
                  (term-replace term normal-form)
                (apply-rules-internal)))
          (apply-rules-internal))
      ;; non memoise
      (apply-rules-internal))))

;;; APPLY-A-EXTENSIONS : rule term method -> Bool
;;;-----------------------------------------------------------------------------
;;; Apply the associative-extensions. returns true iff the some rule is applied.
;;;
(defun apply-A-extensions (rule term top)
  (declare (type axiom rule)
           (type term term)
           (type method top)
           (values (or null t)))
  (declare (optimize (speed 3) (safety 0)))
  (let ((listext (!axiom-a-extensions rule))
        (a-ext nil)
        (is-applied nil))
    (when (null listext)
      ;; then need to pre-compute the extensions and store then
      (setq listext (compute-A-extensions rule top)))
    (when (setq a-ext (car listext))
      ;; the first extension exists
      (setq is-applied (apply-one-rule a-ext term)))
    (setq listext (cdr listext))
    (when (setq a-ext (car listext))
      ;; the second extension exists
      (setq is-applied (or (apply-one-rule a-ext term)
                           is-applied)))
    (setq listext (cdr listext))
    (when (setq a-ext (car listext))
      ;; the third extension exists
      (setq is-applied (or (apply-one-rule a-ext term)
                           is-applied)))
    ;;
    is-applied))

;;; APPLY-AC-EXTENSION : rule term method -> Bool
;;;-----------------------------------------------------------------------------
;;; Apply the associative-commutative-extension. returns t iff the rule is applied.
;;;
(defun apply-AC-extension (rule term top)
  (declare (type axiom rule)
           (type term term)
           ;;(type method top)
           (values (or null t)))
  (declare (ignore top))
  (let ((listext (give-AC-extension rule))
        (is-applied nil))
    (when (car listext)
      ;; the extension exists
      (setq is-applied (apply-one-rule (car listext) term)))
    is-applied))

;;; RULE-EVAL-TERM : teta term -> term'
;;;
(defun rule-eval-term (teta term &optional (slow? nil))
  (declare (type list teta)
           (type term term)
           (values list))
  (macrolet ((assoc% (_x _y)
               `(let ((*_lst ,_y))
                  (loop
                    (when (null *_lst) (return nil))
                    (when (eq ,_x (caar *_lst)) (return (car *_lst)))
                    (setq *_lst (cdr *_lst))))))
    (cond ((term-is-variable? term)
           (let ((im (if slow?
                         (variable-image-slow teta term)
                       (cdr (assoc% term teta)))))
             (if im;; i.e. im = teta(term)
                 im
               ;; if variable doesn't have a binding, it evaluates to itself
               term)))
          (t term))))

;;; RULE-EVAL-ID-CONDITION : substitution condition ->
;;;-----------------------------------------------------------------------------
;;; really not not want to use normalize -- perhaps could use normal expressions.
(defun rule-eval-id-condition (subst cond &optional (slow? nil))
  (declare (type list subst cond)
           (values (or null t)))
  (cond ((eq 'and (car cond))
         (dolist (sc (cdr cond) t)
           (unless (rule-eval-id-condition subst sc slow?) (return nil))))
        ((eq 'not-equal (car cond))
         (not (term-is-similar?
               (rule-eval-term subst (cadr cond) slow?)
               (rule-eval-term subst (caddr cond) slow?))))
        ((eq 'equal (car cond))
         (term-is-similar?
          (rule-eval-term subst (cadr cond) slow?)
          (rule-eval-term subst (caddr cond) slow?)))
        ((eq 'or (car cond))
         (dolist (sc (cdr cond) nil)
           (when (rule-eval-id-condition subst sc slow?) (return t))))
        ((eq 'not (car cond))
         (not (rule-eval-id-condition subst (cadr cond) slow?)))
        ((eq 'xor (car cond))           ;@@ remove?
         (let ((res nil))
           (dolist (sc (cdr cond))
             (setq res (if (rule-eval-id-condition subst sc slow?) (not res) res)))
           res))
        (t
         (with-output-panic-message ()
           (format t "illegual id condition : ~a" cond))
         t)))

;;; APPLY-RULE : rule term -> Bool
;;;-----------------------------------------------------------------------------
;;; Returns true iff the rule has been sucessfully apply. Note that in this case
;;; "term" is also modified. 
;;; The associative extensions are automatiquely generated and applied if needed.
;;;
(defun apply-rule (rule term)
  (declare (type axiom rule)
           (type term term)
           (values (or null t)))
  (let ((is-applied nil))
    (tagbody
      (when (rule-is-rule rule)
        (if *rewrite-exec-mode*
            (go do-apply)
          (return-from apply-rule nil)))
      ;; rule is equation
      (when (and (not *cexec-normalize*)
                 (term-is-applform? term)
                 (method-has-trans-rule (term-head term)))
        (return-from apply-rule nil))
      ;;---- 
     do-apply
      ;;----
      ;;
      (when *rewrite-debug*
        (with-output-msg ()
          (format t "-- apply rule:  ")
          (print-chaos-object rule)))
      ;; first apply the given rule.
      (setq is-applied (apply-one-rule rule term))

      ;; then there may be some extensions.
      (when (and (not is-applied) (term-is-applform? term))
        (let ((top (term-method term)))
          (declare (type method top))
          (unless (let ((val (axiom-kind rule)))
                    (and val
                         (not (eq :id-theorem val))
                         (not (eq :idem-theory val))))
            (when (method-is-associative top)
              (if (method-is-commutative top)
                  (setq is-applied
                    (or (apply-AC-extension rule term top)
                        is-applied))
                ;; the operator is only associative,
                (setq is-applied
                  (or (apply-A-extensions rule term top)
                      is-applied))
                ))))))                  ; end tagbody
    ;; return t iff the rule is applied.
    is-applied))

;;;
;;;                              REWRITE ENGINE
;;;

;;; the following procs assumes that the runtime environment is properly set:
;;; *current-module*, *current-sort-order*, *current-opinfo-table*.
;;;

;;;-----------------------------------------------------------------------------
;;; REWRITE : TERM -> TERM' ----------------------------------------------------
;;;-----------------------------------------------------------------------------

(defun reduce-term (term strategy)
  (declare (type term term)
           (type list strategy)
           (values (or null t)))
  (when *rewrite-debug*
    (with-output-simple-msg ()
      (format t "[reduce-term](NF=~a,LP=~a): " (term-is-reduced? term) (term-is-lowest-parsed? term))
      (term-print-with-sort term)
      (format t "~%  strat = ~a" strategy)))
  ;;
  (let ((occ nil)
        (top (term-head term)))
    (cond ((null strategy)
           ;; no strat, or exhausted.
           (unless (term-is-lowest-parsed? term)
             (multiple-value-bind (xterm assoc?)
                 (update-lowest-parse term)
               (declare (ignore xterm))
               (when (or assoc?
                         (not (method= (term-method term) top)))
                 (when *rewrite-debug*
                   (with-output-msg ()
                     (format t "- resetting reduced flag ...")))
               (reset-reduced-flag term)
               (return-from reduce-term (normalize-term term)))))
           (unless (or *rewrite-semantic-reduce*
                       *beh-rewrite*)
             (mark-term-as-reduced term)))
          
          ;; whole
          ((= 0 (the fixnum (setf occ (car strategy))))
           ;; (unless (term-is-reduced? term)
             (apply-rules term strategy))
           ;; )

          ;; explicit lazy
          ((< (the fixnum occ) 0)
           (let ((d-arg (term-arg-n term (1- (abs occ)))))
             (unless (term-is-reduced? d-arg) (mark-term-as-on-demand d-arg))
             (reduce-term term (cdr strategy))))

          ;; normal case, reduce specified subterm
          (t (unless (normalize-term (term-arg-n term (1- occ)))
               (mark-term-as-not-lowest-parsed term))
             (reduce-term term (cdr strategy))))))

;;; THE TOP LEVEL -------------------------------------------------------------
;;; term may be modified.
;;;

(defun rewrite (term &optional (module *current-module*) mode)
  (declare (type term term)
           (type module module)
           (values term))
  (case mode
    (:exec+
     (let ((*rwl-search-no-state-report* t))
       (rwl-search* term
                    nil                 ; pattern
                    1                   ; max result
                    most-positive-fixnum ; max depth
                    nil                 ; zero?
                    t                   ; final?
                    nil                 ; cond
                    nil                 ; pred
                    *current-module*    ; module
                    )
       (if (rwl-sch-context-answers .rwl-sch-context.)
           (term-replace term
                         (rwl-state-term
                          (car (rwl-sch-context-answers .rwl-sch-context.))))
         (with-output-chaos-error ()
           (format t "PANIC!")))))
    (otherwise
     (setq $$trials 1)
     (when *memo-rewrite*
       (when (or *clean-memo-in-normalize*
                 (not (eq module *memoized-module*)))
         (clear-term-memo-table *term-memo-table*))
       (setq *memoized-module* module))
     (let ((*trace-level* 0))
       (with-in-module (module)
         (let ((*beh-rewrite* (and (not *rewrite-semantic-reduce*)
                                   (module-has-behavioural-axioms module))))
           (declare (special *beh-rewrite*))
           (set-term-color-top term)
           (normalize-term term))))))
  term)

(defun rewrite* (term)
  (declare (type term term)
           (values term))
  (setq $$trials 1)
  (when *memo-rewrite*
    (when (or *clean-memo-in-normalize*
              (not (eq *current-module* *memoized-module*)))
      (clear-term-memo-table *term-memo-table*))
    (setq *memoized-module* *current-module*))
  (let ((*beh-rewrite* (and (not *rewrite-semantic-reduce*)
                            (module-has-behavioural-axioms *current-module*))))
    (declare (special *beh-rewrite*))
    (set-term-color-top term)
    (normalize-term term))
  term)

;;; rewrite-exec
;;; 
(defun rewrite-exec (term &optional (module *current-module*) mode)
  (declare (type term term)
           (type module module)
           (values term))
  (case mode
    (:exec+
     (let ((*rwl-search-no-state-report* t))
       (rwl-search* term
                    nil                 ; pattern
                    1                   ; max result
                    most-positive-fixnum ; max depth
                    nil                 ; zero?
                    t                   ; final?
                    nil                 ; cond
                    nil                 ; pred
                    *current-module*    ; module
                    )
       (if (rwl-sch-context-answers .rwl-sch-context.)
           (term-replace term
                         (rwl-state-term
                          (car (rwl-sch-context-answers .rwl-sch-context.))))
         (with-output-chaos-error ()
           (format t "PANIC!")))))
    (otherwise
     (setq $$trials 1)
     (when *memo-rewrite*
       (when (or *clean-memo-in-normalize*
                 (not (eq module *memoized-module*)))
         (clear-term-memo-table *term-memo-table*))
       (setq *memoized-module* module))
     (let ((*trace-level* 0))
       (setq $$matches 0)
       (setq *term-memo-hash-hit* 0)
       (with-in-module (module)
         (let ((*beh-rewrite* (and (not *rewrite-semantic-reduce*)
                                   (module-has-behavioural-axioms module))))
           (declare (special *beh-rewrite*))
           ;;
           (set-term-color-top term)
           (normalize-term term))))))
  term)

;;;
(defun term-memo-get-normal-form (term strategy)
  (let ((term-nu nil)
        (normal-form (get-hashed-term term *term-memo-table*)))
    (unless normal-form
      (setq term-nu (simple-copy-term  term))
      ;; compute the normal form of "term"
      (reduce-term term strategy)
      (setq normal-form term)
      (set-hashed-term term-nu *term-memo-table* normal-form))
    normal-form))

(defmacro check-closed-world-assumption (?term)
  ` (when *closed-world*
      (when (and (sort= (term-sort ,?term) *bool-sort*)
                 (not (is-true? ,?term))
                 (term-is-applform? ,?term))
        (term-replace-dd-simple ,?term *bool-false*))))

;;; NORMALIZE-TERM : TERM -> BOOL
;;;----------------------------------------------------------------------------
;;; normalize term, returns NIL iff the term is rewriten.
;;;
(defun normalize-term (term)
  (declare (type term term)
           (values (or null t)))
  ;; (unless (term-is-lowest-parsed? term)
  ;;  (update-lowest-parse term))
  (when *rewrite-debug*
    (with-output-simple-msg ()
      (format t "[normalize-term]:(NF=~A,LP=~A,OD=~A) "
              (term-is-reduced? term)
              (term-is-lowest-parsed? term)
              (term-is-on-demand? term))
      (term-print-with-sort term)))
  (let ((strategy nil))
    (cond ((term-is-reduced? term)
           (when (term-is-builtin-constant? term)
             (update-lowest-parse term))
           t)
          ((null (setq strategy
                   (method-rewrite-strategy (term-head term))))
           ;; (check-closed-world-assumption term)
           (mark-term-as-reduced term)
           t)
          ((and *memo-rewrite*
                (or *always-memo* (method-has-memo (term-head term))))
           (term-replace term
                         (term-memo-get-normal-form term strategy))
           nil)
          ;;
          (t (reduce-term term strategy)
             nil))))

(defun !normalize-term (term)
  (declare (type term term)
           (values term))
  (normalize-term term)
  term)


;;;*****************************************************************************
;;; TERM REWRITING DEBUGGING FACILITIES
;;;

;;;*****************************************************************************
;;;                   REWRITING WITH TRACE, STEP
;;;*****************************************************************************

;;; APPLY-ONE-RULE-DBG
;;;-----------------------------------------------------------------------------
;;; returns true iff the rule has been sucessfully apply. Note that
;;; in this case "term" is also modified.
;;;
;;;
(defun print-trace-in ()
  (format *trace-output* "~%~d>[~a] " *trace-level* (1+ *rule-count*)))

(defun print-trace-out ()
  (format *trace-output* "~%~d<[~a] " *trace-level* *rule-count*))

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
                  (format t "~%>> term matches to stop pattern: ")
                  (let ((*print-indent* (+ *print-indent* 8)))
                    (term-print *rewrite-stop-pattern*))
                  (format t "~%<< will stop rewriting")
                  )
              (progn
                (format t "~%>> subterm : ")
                (let ((*print-indent* (+ *print-indent* 8)))
                  (term-print matched))
                (format t "~&   of term : ")
                (let ((*print-indent* (+ *print-indent* 8)))
                  (term-print $$term))
                (format t "~&   matches to stop pattern: ")
                (let ((*print-indent* (+ *print-indent* 8)))
                  (term-print *rewrite-stop-pattern*))
                (format t "~%<< will stop rewriting")
                ))
            (force-output))
        ;;
        (unless *rewrite-stepping*
          (setq *matched-to-stop-pattern* nil))))))

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
      (("x" ":x") . cafein-show-context-term)
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
  ;; print current term
  (format t "~%>> target: ")
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
          (format t "~%STEP[~D]? " *rule-count*)
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
            ((:+ x |:x| ))
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
(defun parse-stop-at (inp)
  (%stop-at* (cdadr inp)))

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
  (format t "~%-- Stepper command help :")
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

(defun cafein-show-context-term (&rest ignore)
  (declare (ignore ignore))
  (print-next)
  (format t "[context]: ")
  (let ((*fancy-print* nil)
        (*print-with-sort* t))
    (term-print $$term)))

#||
(defun apply-one-rule (rule term)
  (declare (ignore rule term))
  (format t "~%APPLY-ONE-RULE : INTERNAL ERROR, SPECIFIC REWRITEING ENGINE ISN'T SPECIFIED.")
  (break))
||#

(defun rew-matcher (pat term)
  (if (term-is-variable? pat)
      (if (sort<= (term-sort term) (variable-sort pat)
                  (module-sort-order *current-module*))
          (values nil (list (cons pat term)) nil nil)
        (values nil nil t nil))
    (if (term-is-lisp-form? pat)
        (values nil nil t nil)
      (first-match pat term))))

(declaim (inline under-debug-rewrite))
(defun under-debug-rewrite ()
  (or $$trace-rewrite $$trace-rewrite-whole *rewrite-stepping*
      *rewrite-count-limit* *rewrite-stop-pattern*))

(defun apply-one-rule (rule term)
  (when (rule-non-exec rule)
    (return-from apply-one-rule nil))
  (let ((mandor (axiom-meta-and-or rule))
        (.trace-or-step. (under-debug-rewrite)))
    (declare (special .trace-or-step.))
    (cond (mandor
           (let ((all-subst nil)
                 (rhs-list nil)
                 (new-rhs nil))
             (multiple-value-bind (gs sub no-match eeq)
                 (rew-matcher (rule-lhs rule) term)
               (declare (ignore eeq))
               (when no-match
                 (return-from apply-one-rule nil))
               (push sub all-subst)
               ;;
               ;; try other patterns untill there's no hope
               (loop
                 (multiple-value-setq (gs sub no-match)
                   (next-match gs))
                 (when no-match (return))
                 (push sub all-subst)))
             ;; 
             (if (cdr all-subst)
                 (progn
                   (when *debug-meta*
                     (format t "~%~s[subst]" mandor))
                   (dolist (sub all-subst)
                     (push (set-term-color (substitution-image-simplifying sub (rule-rhs rule))) rhs-list)
                     (when *debug-meta*
                       (let ((*print-indent* (+ 4 *print-indent*)))
                         (print-next)
                         (print-substitution sub))))
                   ;; 
                   (setq new-rhs (make-right-assoc-normal-form-with-sort-check
                                  (case mandor
                                    ('|:m-and| *bool-and*)
                                    ('|:m-and-also| *bool-and-also*)
                                    ('|:m-or| *bool-or*)
                                    ('|:m-or-else| *bool-or-else*)
                                    (otherwise (with-output-panic-message ()
                                                 (format t "internal error, invalid meta rule label ~s" mandor))))
                                  rhs-list))
                   ;; DEBUG
                   (when *debug-meta* 
                     (format t "~%~s[=>] " mandor)
                     (term-print-with-sort new-rhs))
                   ;;
                   ;; do rewrite
                   ;;
                   (if .trace-or-step.
                       (progn (term-replace-dd-dbg term new-rhs) t)
                     (progn (term-replace-dd-simple term new-rhs) t)))
               (!apply-one-rule rule term))))
          ;; normal case
          (t (!apply-one-rule rule term)))))
;;;
;;; SOME MEL SUPPORT
;;;
;;; (defvar *mel-debug* nil)
(defvar .memb-term-hash. nil)
(defvar .memb-last-module. nil)
(defun clear-memb-hash () (setq .memb-term-hash. nil))
(defun get-memb-hash (term)
  (cdr (assoc term .memb-term-hash.
              :test #'term-equational-equal)))
(defun set-memb-hash (term value)
  (let ((old-ent (assoc term .memb-term-hash. :test #'term-equational-equal)))
    #||
    (when *mel-debug*
      (with-output-simple-msg ()
        (princ "[MEL]: entering term hash ")
        (print-chaos-object term)
        (print-next)
        (format t "with value: ~a" value)
        (when old-ent
          (format t "~% old-ent = ~a" old-ent))))
    ||#
    (if old-ent
        (setf (cdr old-ent) value)
      (if (symbolp value)
          (push (cons term value) .memb-term-hash.)
            (push (cons (simple-copy-term term) value)
              .memb-term-hash.)))))

(defun apply-sort-memb (term module)
  (unless (eq module .memb-last-module.)
    (clear-memb-hash)
    (setq .memb-last-module. module))
  ;;
  (if *mel-always*
      (apply-sort-memb-internal term module)
    (when (err-sort-p (term-sort term))
      (apply-sort-memb-internal term module)))
  term)

(defun sort-to-sort-id-term (sort &optional (module (get-context-module)))
  (let* ((name (string (sort-id sort)))
         (op (find-method-in module (list name) nil *sort-id-sort*)))
    (unless op
      (with-output-panic-message ()
        (format t "Internal error, could not find SortId constant ~A" name)
        (break)))
    ;;
    (make-applform *sort-id-sort* op nil)))

(declaim (special .sort-memb-nesting.))
(defvar .sort-memb-nesting. 0)
(defparameter .sort-memb-nesting-limit. 100)

(defun apply-sort-memb-internal (term module)
  (let ((.sort-memb-nesting. (1+ .sort-memb-nesting.)))
    (when (> .sort-memb-nesting. .sort-memb-nesting-limit.)
      (with-output-chaos-error ('too-deep)
        (format t "sort membership test nesting too deep ~d"
                .sort-memb-nesting.)))
    (with-in-module (module)
      (when *mel-debug*
        (with-output-simple-msg ()
          (princ "[MEL]: given ")
          (print-chaos-object term)))
      ;;
      ;;
      (when (term-is-applform? term)
        (dolist (sub (term-subterms term))
          (apply-sort-memb-internal sub module)))
      (update-lowest-parse term)
      ;;
      (let ((val (get-memb-hash term)))
        (when val
          (unless (symbolp val)
            (when *mel-debug*
              (with-output-simple-msg ()
                (format t "[MEL]: setting hashed sort ~a" val)))
            (setf (term-sort term) val))
          (return-from apply-sort-memb-internal term)))
      ;;
      (let* ((sort (term-sort term))
             (sorts (maximal-sorts
                     (if (err-sort-p sort)
                         (get-family sort *current-sort-order*)
                       (sub-or-equal-sorts sort *current-sort-order*))
                     *current-sort-order*))
             (res nil)
             (final-res nil)
             (next nil)
             (saved-$$term $$term))
        (when (or (sort= sort *universal-sort*)
                  (sort= sort *huniversal-sort*)
                  (sort= sort *cosmos*)
                  (sort= sort *string-sort*)
                  (sort= sort *bottom-sort*)
                  (sort= sort *hbottom-sort*))
          (return-from apply-sort-memb-internal term))
        (loop
          (setq next nil)
          (dolist (m sorts)
            (unless (memq m res)
              (let ((target-term
                     (make-applform *bool-sort*
                                    *sort-membership*
                                    (list term
                                          (sort-to-sort-id-term m)))))
                ;; (setq $$term target-term)
                (apply-rules target-term '(0))
                (if (is-true? target-term)
                    (progn
                      (push m res)
                      (setq next
                        (delete-duplicates
                         (nconc next
                                (direct-subsorts m *current-sort-order*))
                         :test #'eq)))
                  (set-memb-hash term :false))
                )))                     ; end-do for each sorts.
          ;; check next term
          (unless next (return))
          (setq sorts next))
        ;;
        (when *mel-debug*
          (with-output-simple-msg ()
            (format t "[MEL]: candidates 1 = ~a" res)))
        ;;
        (setq final-res res)
        (when (cdr res)
          (setq final-res (minimal-sorts res *current-sort-order*)))
        (when *mel-debug*
          (with-output-simple-msg ()
            (format t "[MEL]: minimals = ~a" final-res)))
        (if (and final-res (null (cdr final-res)))
            (progn
              (set-memb-hash term (car final-res))
              (setf (term-sort term) (car final-res))
              )
          (let ((cand final-res)
                (next nil))
            (loop
              (unless cand (return nil))
              (setq next nil)
              (dolist (s cand)
                (setq next (nconc next
                                  (remove-if-not
                                   #'(lambda (x)
                                       (memq x res))
                                   (direct-supersorts s
                                                      *current-sort-order*))
                                  )))
              (setq next (delete-duplicates next :test #'eq))
              (when (null (cdr next))
                (setq final-res next)
                (return nil))
              (setq cand next))         ; end looop
            ;;
            (when *mel-debug*
              (with-output-simple-msg ()
                (format t "[MEL]: max-minorants = ~a" final-res)))
            (if (and final-res
                     (null (cdr final-res))
                     (not (err-sort-p (car final-res))))
                (progn
                  (set-memb-hash term (car final-res))
                  (setf (term-sort term) (car final-res))
                  )
              (set-memb-hash term :false)
              )))
        ;;
        (setq $$term saved-$$term)
        term))))

;;; EOF

