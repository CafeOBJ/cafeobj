;;;-*- Mode:LISP; Package:CHAOS; Base:10; Syntax:Common-lisp -*-
;;; $Id: eval-ast2.lisp,v 1.29 2010-08-04 04:37:34 sawada Exp $
(in-package :chaos)
#|==============================================================================
				   System: CHAOS
				    Module: eval
				File: eval-ast2.lisp
==============================================================================|#
#-:chaos-debug
(declaim (optimize (speed 3) (safety 0) #-GCL (debug 0)))
#+:chaos-debug
(declaim (optimize (speed 1) (safety 3) #-GCL (debug 3)))

;;; ** DESCRIPTION =============================================================
;;; Evaluators of ASTs of Chaos's script sub-language.
;;;

(defparameter *chaos-version* "2.0")

(declaim (special *interactive*))

;;; ** TO DO for other platforms
(defvar *top-level-tag*
    #+KCL si::*quit-tag*
    #+CMU 'common-lisp::top-level-catcher
    #+EXCL 'top-level::top-level-break-loop
    #+(or LUCID :CCL) '(*quit-tag*)
    #+CLISP 'system::debug
    )

(defun top-noshow ()
  (or (and (null *chaos-input-source*)
           (<= *chaos-input-level* 0))
      *chaos-quiet*))

;;; ****
;;; EVAL
;;; ****
(defun eval-form (ast)
  (let ((form (%eval-form ast)))
    (cond ((eq form '$$term)
           (eval-$$term))
          (t (eval-ast form))
          )))

(defun eval-$$term ()
  ;; some module must be opened.
  (unless *open-module*
    (with-output-chaos-error ('no-context)
      (format t "no module is open.")))
  ;; $$term must be bound.
  (unless $$term
    (with-output-chaos-error ('no-term)
      (format t "$$term is not bound.")))
  ;;
  (let ((in-form (with-output-to-string (stream)
                   (with-in-module (*current-module*)
                     (term-print $$term stream)))))
    (with-input-from-string (*standard-input* in-form)
      (process-cafeobj-input))
    ))

;;; *********
;;; LISP-EVAL
;;; *********
(defun eval-lisp-form (ast)
  (let ((form (%lisp-eval-form ast)))
    (setq form
	  (cond ((consp form)
             (if (symbolp (car form))
                 (if (fboundp (car form))
                     form
                   (with-output-chaos-error ('invalid-lisp-form)
                     (format t "no such Lisp function or macro \"~a\"."
                             (car form))
                     ))
               form))
            (t (if (symbolp form)
                   (if (boundp form)
                       form
                     (with-output-chaos-error ('invalid-lisp-form)
                       (format t "unbound Lisp symbol \"~a\"." form)
                       ))
                 form))))
    (eval form)))

;;; ************
;;; DYNA-COMMENT
;;; ************
(defun print-dyna-comment (ast)
  (fresh-all)
  (flush-all)
  (let ((flg nil))
    (dolist (form (%dyna-comment-form ast))
      (when flg (princ " "))
      (if (consp form)
          (print-simple-princ-open form)
        (princ form))
      (setf flg t))
    (flush-all)
    t))

;;; ******
;;; REDUCE
;;; ******
(defun perform-reduction (ast)
  (let ((preterm (%reduce-term ast))
        (modexp (%reduce-module ast))
        (mode (%reduce-mode ast))
        (result-as-text (%reduce-return-text ast)))
    (unless mode
      (setq mode :red))
    (perform-reduction* preterm modexp mode result-as-text)))

(defun perform-reduction* (preterm &optional modexp mode (result-as-text nil))
  ;; (setq $$trials 1)
  (setq *m-pattern-subst* nil)
  ;;
  (let ((*consider-object* t)
        (*rewrite-exec-mode* (or (eq mode :exec)
                                 (eq mode :exec+)))
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
                (return-from perform-reduction* nil))
              (when *rewrite-stepping* (setq *steps-to-be-done* 1))
              (when *show-stats*
                (setq time2 (get-internal-run-time))
                (setf time-for-parse
                  (format nil "~,3f sec"
                          ;; (/ (float (- time2 time1)) internal-time-units-per-second)
                          (elapsed-time-in-seconds time1 time2)
                          )))
              (unless *chaos-quiet*
                ;; (fresh-all)
                (flush-all)
                (if (eq mode :exec)     ; *rewrite-exec-mode*
                    (format t "~&-- execute in ")
                  (if (eq mode :exec+)
                      (format t "~&-- execute! in ")
                    (if (eq mode :red)
                        (format t "~&-- reduce in ")
                      (format t"~&-- behavioural reduce in "))
                    ))
                (print-simple-mod-name *current-module*)
                (princ " : ")
                (let ((*print-indent* (+ 4 *print-indent*)))
                  (print-check 0 20)
                  (term-print-with-sort term))
                (flush-all))
              ;; ******** 
              (reset-target-term term *last-module* mod)
              ;; ********
              (setq $$matches 0)
              (setq time1 (get-internal-run-time))
              (let ((*perform-on-demand-reduction* t)
                    (*rule-count* 0))
                (let ((res nil))
                  (catch 'rewrite-abort
                    (let ((*do-empty-match* nil)) ; t
                      (if (and *rewrite-exec-mode*
                               *cexec-normalize*)
                          (rewrite-exec term *current-module* mode)
                        (rewrite term *current-module* mode))))
                  ;;
                  #|| ============= TODO
                  (when (term-op-contains-theory $$term)
                    (reset-reduced-flag $$term)
                    (setq term $$term)
                    (catch 'rewrite-abort
                      (let ((*do-empty-match* nil))
                        (if (and *rewrite-exec-mode*
                                 *cexec-normalize*)
                            (rewrite-exec term *current-module* mode)
                          (rewrite term *current-module* mode)))))
                  ||#
                  ;;
                  (setq res $$term)
                  (when *mel-sort*
                    (setq res (setq $$term (apply-sort-memb res mod)))
                    )
                  ;;
                  (setq time2 (get-internal-run-time))
                  (setf time-for-reduction
                    (format nil "~,3f sec"
                            (elapsed-time-in-seconds time1 time2)))
                  (setf number-matches $$matches)
                  (setq $$matches 0)
                  (setq $$norm res)
                  ;; print out the result.
                  (if result-as-text
                      (let ((red-term (term-print-with-sort-string res))
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
                        (return-from perform-reduction* (values red-term stat)))
                    (progn
                      (terpri)(term-print-with-sort res)
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
                      (flush-all)
                      ;; (terpri)
                      ))
                  ))
              ))
          (context-pop-and-recover))))))

;;; **************
;;; TEST REDUCTION
;;; **************
(defun perform-test-reduction (ast)
  (let ((preterm (%test-reduce-term ast))
        (modexp (%test-reduce-module ast))
        (mode (%test-reduce-mode ast))
        (expect (%test-reduce-expect ast)))
    (perform-reduction* preterm modexp (if (eq mode :red) nil t))
    (with-in-module ($$mod)
      (let ((ans (simple-parse-ground "a test reduction" *current-module* expect)))
        (if (and (not (symbolp $$norm))
                 (term-equational-equal $$norm ans))
            (progn
              (unless *chaos-quiet*
                (with-output-simple-msg ()
                  (princ "** success test reduction.")))
              *bool-true*)
          (progn
            (unless *chaos-quiet*
              (with-output-simple-msg ()
                (format t "** test reduction failed~%-- expected:~a~%" expect)))
            *bool-false*))))))

;;; *****
;;; PARSE
;;; *****
(defun do-parse-term (ast)
  (let* ((preterm (%parse-term ast))
         (modexp (%parse-module ast))
         (result-as-text (%parse-return-text ast)))
    (when result-as-text
      (with-output-simple-msg ()
        (princ "`return result as string' option is not implemented yet.")))
    (do-parse-term* preterm modexp)))

(defun do-parse-term* (preterm &optional modexp)
  (let ((mod (if modexp
                 (eval-modexp modexp)
               *last-module*)))
    (unless mod
      (with-output-chaos-error ('no-context)
	(princ "no module expression provided and no selected(current) module.")))
    (when (modexp-is-error mod)
      (with-output-chaos-error ('no-such-module)
	(princ "incorrect module expression, not such module: ")
	(print-chaos-object modexp)))
    ;;
    (context-push-and-move *last-module* mod)
    (with-in-module (mod)
      (prepare-for-parsing *current-module*)
      (let ((*parse-variables* nil))
	(let ((res (simple-parse *current-module* preterm *cosmos*)))
	  ;; ******** MEL 
	  (when *mel-sort*
	    (!setup-reduction mod)
	    (setq res (apply-sort-memb res
				       mod)))
	  (reset-target-term res *last-module* mod)
	  ;; ********
	  (format t "~&")
	  (term-print-with-sort res *standard-output*)
	  (flush-all)
	  ;; (break "...")
	  #||
	  (when *chaos-verbose*
	    (print-term-tree res t))
	  ||#
	  )))
    (context-pop-and-recover)))

;;; *TODO*
(defun red-loop (mod &optional prompt)
  (declare (ignore mod prompt))
  (with-output-simple-msg ()
    (princ "sorry, red-loop is not implemented yet.."))
  (return-from red-loop nil)
  #||
  (setq $$trials 1)
  (setq mod (eval-modexp-top mod))
  (if (modexp-is-error mod)
      (with-output-chaos-error ('no-such-module)
        (princ "undefined module")
        )
    (let (in
          (flag nil)
          (top-level (at-top-level)))
      (!setup-reduction mod)
      (loop
        (chaos-init)
        (when (and prompt top-level)
          (terpri)
          (print-mod-name mod) (princ "> "))
        (let ((cur (!set-single-reader '("[" "]" "_"))))
          (progn
            (setq in (read-seq-of-term '(|.|)))
            (!set-reader cur)))
        (when (null in) (return))
        (unless top-level
          (if flag
              (progn (princ "---------------------------------------")
                     (terpri))
            (setq flag t)))
        (perform-reduction in)          ; should ...
        )))
  :done
  ||#
  )

(defun check-bad-rules (mod)
  (declare (ignore mod))
  nil)

;;; *****************
;;; TRACE/TRACE-WHOLE
;;; *****************
(defun eval-trace (ast)
  (let ((flag (%trace-flag ast)))
    (if (eq flag :on)
        (trace-on)
      (trace-off))))

(defun eval-trace-whole (ast)
  (let ((flag (%trace-whole-flag ast)))
    (if (eq flag :on)
        (trace-whole-on)
      (trace-whole-off))))

(defun under-debug-rewrite ()
  (or $$trace-rewrite $$trace-rewrite-whole *rewrite-stepping*
      *rewrite-count-limit* *rewrite-stop-pattern*))

(defun rewrite-debug-on ()
  (setf (symbol-function 'apply-one-rule)
	(symbol-function 'apply-one-rule-dbg)))

(defun rewrite-debug-off ()
  (unless (under-debug-rewrite)
    (setf (symbol-function 'apply-one-rule)
	  (symbol-function 'apply-one-rule-simple))))

(defun trace-on ()
  (setq $$trace-rewrite t)
  (rewrite-debug-on))

(defun trace-off ()
  (setq $$trace-rewrite nil)
  (rewrite-debug-off))

(defun trace-whole-on ()
  (setq $$trace-rewrite-whole t)
  (rewrite-debug-on))

(defun trace-whole-off ()
  (setq $$trace-rewrite-whole nil)
  (rewrite-debug-off))

;;; *************
;;; REWRITE LIMIT
;;; *************
(defun eval-rewrite-count-limit (ast)
  (let ((count (%rewrite-count-limit ast)))
    (if (eq count 'off)
        (set-rewrite-count-limit 'off)
      (multiple-value-bind (num len)
          (parse-integer count :junk-allowed t)
        (if (= len (length count))
            (set-rewrite-count-limit num)
	      (with-output-chaos-error ('invalid-value)
            (format t "invalid rewrite count limit ~a" count)
            ))))))

(defun set-rewrite-count-limit (num)
  (if (integerp num)
      (if (zerop num)
          (progn (setq *rewrite-count-limit* nil)
                 (rewrite-debug-off))
        (if (> num 0)
            (progn (setq *rewrite-count-limit* num)
                   (rewrite-debug-on))
	      (with-output-chaos-error ('invalid-value)
            (format t "invalid rewrite count limit value ~d" num)
            (print-next) (princ "must be a positive integer.")
            )))
    (progn (setq *rewrite-count-limit* nil)
           (rewrite-debug-off))))

(defun set-rewrite-count-limit2 (value)
  (if (or (null value)
          (equal value '(".")))
      (set-rewrite-count-limit 'off)
    (multiple-value-bind (num len)
        (parse-integer (car value) :junk-allowed t)
      (if (= len (length (car value)))
          (set-rewrite-count-limit num)
	    (with-output-chaos-error ('invalid-value)
	      (format t "invalid rewrite count limit ~a" (car value))
	      (print-next)
	      (princ "must be a positive integer.")
	      )))))

(defun set-cond-trial-limit (value)
  (if (or (null value)
          (equal value '(".")))
      (setq *condition-trial-limit* nil)
    (multiple-value-bind (num len)
        (parse-integer (car value) :junk-allowed t)
      (if (and (= len (length (car value)))
               (> num 0))
          (setq *condition-trial-limit* num)
	    (with-output-chaos-error ('invalid-value)
	      (format t "invalid condition trial limit ~a" (car value))
	      (print-next)
	      (princ "must be a positive integer.")
	      )))))

;;; ********************
;;; REWRITE STOP PATTERN
;;; ********************
(defun eval-stop-at (ast)
  (let ((pat (%stop-at-pattern ast)))
    (set-rewrite-stop-pattern2 pat)))

(defun set-rewrite-stop-pattern (pat)
  (if (memq pat '(null nil none))
      (progn (setq *rewrite-stop-pattern* nil)
             (rewrite-debug-off))
    (progn (setq *rewrite-stop-pattern* pat)
           (rewrite-debug-on))))

(defun set-rewrite-stop-pattern2 (pat)
  (if (or (null pat)
          (member pat '(("none") ("off") ("nil") ("null"))))
      (set-rewrite-stop-pattern 'none)
    (let ((mod (or *current-module*
                   *last-module*
                   (with-output-chaos-error ('no-context)
                     (princ "no context (current) module is specified.")))
               ))
      (let* ((*parse-variables* (module-variables mod))
             (term (simple-parse mod
                                 pat *cosmos*)))
        (when (or (null (term-sort term))
                  (sort<= (term-sort term) *syntax-err-sort*
                          *chaos-sort-order*))
          (return-from set-rewrite-stop-pattern2 nil))
        (set-rewrite-stop-pattern term)))))

;;; *******
;;; STEPPER
;;; *******
(defun eval-step (ast)
  (let ((flag (%step-flag ast)))
    (if (eq flag :on)
        (step-on)
      (step-off))))

(defun step-on ()
  (setq *rewrite-stepping* t)
  (setq *steps-to-be-done* 1)
  (rewrite-debug-on))

(defun step-off ()
  (setq *rewrite-stepping* nil)
  (rewrite-debug-off))

;;; *****
;;; INPUT
;;; *****
(defun eval-input-file (ast)
  (chaos-input-file :file (%input-file-name ast)
                    :proc (%input-proc ast)
                    :load-path (%input-load-path ast)
                    :suffix (%input-suffixes ast)
                    :args (%input-args ast)))

;;; ***************
;;; DESCRIBE-MODULE
;;; ***************

(defun eval-describe-module (ast)
  (let ((modexp (%describe-module-modexp ast))
        mod)
    (setf mod (eval-modexp modexp))
    (when (modexp-is-error mod)
      (with-output-chaos-error ('no-such-module)
        (format t "incorrect module expression, unknown module?")
        (print-modexp modexp)
        ))
    (describe-module mod)))


;;; ***********
;;; OPEN-MODULE
;;; ***********
(defun eval-open-module (ast)
  (let ((modexp (%open-module-modexp ast))
        ;; (*current-module* nil)
        mod)
    (setf mod (if (null modexp)
                  *last-module*
                (eval-modexp modexp)))
    (when (modexp-is-error mod)
      (with-output-chaos-error ('no-such-module)
        (princ "incorrect module expression or uknown module")
        (print-modexp modexp)
        ))
    ;;
    (unless mod
      (with-output-chaos-error ('no-context)
        (princ "no module to be opened!")
        ))
    ;;
    (unless *chaos-quiet*
      (fresh-all)
      (flush-all)
      (print-in-progress "-- opening module ")
      (print-mod-name mod)
      (flush-all)
      (print-in-progress "."))
    (!open-module mod)
    (unless *chaos-quiet*
      (print-in-progress ". done.")
      (terpri)
      )
    ))

(defparameter *module-open-form*
    (%module-decl* "%"
                   :object
                   :user
                   nil))

(defun !open-module (mod)
  (let ((*auto-context-change* nil))
    (when *open-module*
      (with-output-chaos-warning ()
        (princ "another module is already opened: ")
        (print-mod-name *open-module*) (print-next)
        (princ "closing this module...") (print-next)
        (eval-close-module nil)))
    (setq *open-module* mod)
    (setq *last-before-open* *last-module*)
    (setq *last-module* mod)
    (clear-term-memo-table *term-memo-table*)
    (let ((*chaos-quiet* t)
          (*copy-variables* t))
      (setf (%module-decl-kind *module-open-form*) (module-kind mod))
      (setq *last-module* (eval-ast *module-open-form*))
      (import-module *last-module* :using mod)
      ;; (import-module *last-module* :including mod)
      ;; (import-variables mod *last-module*)
      (compile-module *last-module*))
    (change-context *last-before-open* *last-module*)
    *last-module*))

;;; ************
;;; CLOSE-MODULE
;;; ************
(defun eval-close-module (&rest ast)
  (declare (ignore ast))
  (if *open-module*
      (let ((saved-open *open-module*))
        (when (and saved-open (equal "%" (module-name saved-open)))
          ;; (delete-module-all saved-open)
          ;; discard all resources
          (initialize-module *open-module*)
          (setq *open-module* nil))
        (change-context *last-module* *last-before-open*)
        (setq *open-module* nil)
        (when *current-module*
          (change-current-module *last-module*))
        (setq *last-before-open* nil))
    (with-output-chaos-warning ()
      (princ "no module is open.")
      )))


;;; ***********
;;; SAVE SYSTEM
;;; ***********

(defun eval-save (ast)
  (let ((file (%save-file ast)))
    (save-system :file file)))

(defvar *seen-saved* nil)
(defconstant .fill-space. " ")

(defun save-system (&key (file "/tmp/chaos-system")
                         (compile nil))
  (setq *seen-saved* nil)
  (with-open-file (stream file :direction :output
                   :if-exists :new-version
                   :if-does-not-exist :create)
    (flet ((exporting-modules (mod)
             (let ((e-mods (module-exporting-modules mod))
                   (res nil))
               (dolist (ee e-mods)
                 (when (module-type (car ee))
                   (push ee res)))
               res)))
      (let ((top-modules nil))
        (dolist (entry *modules-so-far-table*)
          (let ((mod (cdr entry)))
            (unless (or (exporting-modules mod)
                        (module-is-hard-wired mod)
                        (module-is-system-module mod)
                        (eq (module-type mod) nil))
              (push mod top-modules))))
        (princ *chaos-binary-magic* stream)
        (terpri stream)
        (princ "#|" stream)
        (let ((*print-line-limit* 80))
          (terpri stream)
          (print-centering "-- Chaos snap shot file --" .fill-space. stream)
          (terpri stream)
          (print-centering (format nil "chaos version: ~a" *chaos-version*)
                           .fill-space. stream)
          (terpri stream)
          (print-centering (format nil "file: ~a" file) .fill-space. stream)
          (terpri stream)
          (print-centering (format nil "date: ~a" (get-time-string))
                           .fill-space. stream)
          (terpri stream)
          (print-centering
           "* NOTE : DO NOT MODIFY THIS FILE ULESS YOU REALLY KNOW WHAT YOU ARE DOING!."
           .fill-space.
           stream)
          )
        (terpri stream)
        (princ "|#" stream)
        (format stream "~&(in-package \"CHAOS\")")
        (format stream "~&(eval-when (eval load)")
        (format stream "~&;;; system standard prelude.")
        (dolist (elt *system-standard-prelude*)
          (format stream "~&(eval-ast-if-need-no-error '~s)" elt))
        (format stream "~&;;; user defined modules.")
        (dolist (module top-modules)
          (dump-user-module stream module))
        (format stream "~&;;; views.")
        (dolist (entry *modexp-view-table*)
          (let ((v (cdr entry)))
            (unless (or (memq v *seen-saved*)
                        ;; *TO DO*
                        ;; (view-is-system-view y)
                        )
              (format stream "~&(eval-ast-if-need-no-error '~s)"
                      (%view-decl* (view-name v)
                                   (view-decl-form v))))))
        ;; the end
        (format stream "~&)")
        (when compile
          (compile-file file))))))

(defun dump-user-module (stream module)
  (let ((subs nil))
    (dag-dfs (module-dag module)
             #'(lambda (node)
                 (let ((mod (car (dag-node-datum node))))
                   (push mod subs))))
    (dolist (sub (nreverse subs))
      (when (and (module-p sub) (module-is-user-module sub))
        (let ((name (module-name sub)))
          (unless (or (modexp-is-parameter-theory name)
                      (equal name "%")
                      (memq sub *seen-saved*))
            (push sub *seen-saved*)
            (let ((decl (object-decl-form sub))
                  (*print-pretty* t))
              (when decl
                (format stream "~&(eval-ast-if-need-no-error '~s)"
                        decl))
              nil )))))                 ; do nothing now.
    ))

;;;
(defun eval-ast-if-need (ast)
  (when (chaos-ast? ast)                ; for safety
    (case (ast-type ast)
      (%module-decl
       (let* ((name (%module-decl-name ast))
              (canon (normalize-modexp name)))
         (let ((mod (find-module-in-env canon)))
           (cond (mod
                  (when (or (module-is-inconsistent mod)
                            (not (equal ast (module-decl-form mod))))
                    (eval-ast ast)))
                 (t (eval-ast ast))))))
      (t (eval-ast ast)))))

(defun eval-ast-if-need-no-error (ast)
  (ignoring-chaos-error (eval-ast-if-need ast)))

;;; **************
;;; RESTORE SYSTEM
;;; **************
(defun eval-restore (ast)
  (let ((file (%restore-file ast)))
    (restore-system file)))

(defun restore-system (file)
  (catch *top-level-tag*
    (with-chaos-top-error ()
      (with-chaos-error ()
        (let ((*chaos-quiet* (not *chaos-verbose*)))
          (load file))))))

;;; ************
;;; RESET SYSTEM
;;; ************

;;; recover definitions of soft-wired modules and standard prelude.
;;;
(defun eval-reset-system (&rest ignore)
  (declare (ignore ignore))
  (let ((msg? (and (at-top-level) (not *chaos-quiet*))))
    (when msg?
      (with-output-simple-msg ()
        (format t "~%** start resetting system")
        (format t "~&   re-installing system built-in modules...")))
    (install-chaos-soft-wired-modules)
    (init-tram-bi-modules)
    (init-builtin-universal)
    (when msg?
      (with-output-simple-msg ()
        (format t "~&   re-installing prelude...")))
    (dolist (elt *system-standard-prelude*)
      (eval-ast-if-need elt))
    (when msg?
      (with-output-simple-msg ()
        (format t "~&** done restting system.")
        (force-output)))
    ))

;;; **********
;;; FULL-RESET
;;; **********
(defun eval-full-reset (&rest ignore)
  (declare (ignore ignore))
  (let ((msg? (and (at-top-level) (not *chaos-quiet*))))
    (when msg?
      (with-output-simple-msg ()
        (format t "~%** start full resetting system")
        (format t "~%   clearing system data bases:")))
    (when msg?
      (format t "~%   start clean up modules ."))
    (dolist (m *modules-so-far-table*)
      (clean-up-module (cdr m))
      (when msg?
        (print-in-progress ".")))
    (when msg?
      (format t "~&   start clean up views ."))
    (dolist (v *modexp-view-table*)
      (clean-up-view (cdr v))
      (when msg?
        (print-in-progress ".")))
    ;;
    (clear-global-db)
    (clear-trs-db)
    (clear-term-memo-table *term-memo-table*)
    ;;
    (when msg?
      (print-in-progress " done")
      (terpri)
      )
    (setq *chaos-features* nil)
    (setq *open-module* nil)
    (setq *last-before-open* nil)
    (setq *current-sort-order* nil)
    (setq *current-opinfo-table* nil)
    (setq *old-context* nil)
    (setq *bootstrapping-bool* nil)
    ;;
    (when msg?
      (with-output-simple-msg ()
        (format t "~&   re-boot kernel...")))
    (boot-chaos)
    (when msg?
      (with-output-simple-msg ()
        (format t "~&   re-installing hard-wired modules...")))
    (install-chaos-hard-wired-modules)
    (when msg?
      (with-output-simple-msg ()
        (format t "~&   re-installing built-in modules...")))
    (install-chaos-soft-wired-modules)
    (init-tram-bi-modules)
    (init-builtin-universal)
    (when msg?
      (with-output-simple-msg ()
        (format t "~&   re-installing prelude ...")))
    (dolist (elt *system-standard-prelude*)
      (eval-ast-if-need elt))
    (when msg?
      (with-output-simple-msg ()
        (format t "~&** done system full reset.")
        (force-output)))))

;;; ************
;;; LOAD PRELUDE
;;; ************

(defun eval-load-prelude (ast)
  (load-prelude (%load-prelude-file ast)
                (or (%load-prelude-processor ast)
                    'process-cafeobj-input)))

(defun load-prelude (file processor &optional (no-error nil))
  (load-prelude* file processor t (not no-error)))
(defun load-prelude+ (file processor &optional (no-error nil))
  (load-prelude* file processor nil (not no-error)))

(defun load-prelude* (file processor &optional override (errorp t))
  (catch *top-level-tag*
    (with-chaos-top-error ()
      (with-chaos-error ()
        (let ((*dribble-ast* t)
              (*ast-log* nil)
              (f nil))
          (setq f (chaos-input-file :file file :proc processor
                                    :load-path *system-prelude-dir*
                                    :errorp errorp))
          (if (and *system-standard-prelude* (not override))
              (setq *system-standard-prelude*
                (nconc *system-standard-prelude*
                       (nreverse *ast-log*)))
            (setq *system-standard-prelude* (nreverse *ast-log*)))
          f)))))

;;; *******
;;; PROVIDE
;;; *******
(defun eval-provide-command (ast)
  (pushnew (%provide-feature ast) *chaos-features*
           :test #'equal))

;;; *******
;;; REQUIRE
;;; *******
(defun eval-require-command (ast)
  (let ((feature (%require-feature ast))
        (file (%require-file ast))
        (proc (%require-proc ast)))
    (unless (member feature *chaos-features* :test #'equal)
      (unless proc
        (with-output-panic-message ()
          (format t "require: reading proc is not specified!")
          (chaos-to-top)))
      (if file
          (funcall proc file)
        (funcall proc feature)))))

;;; *******
;;; PROTECT
;;; *******
(defun eval-protect (ast)
  (let* ((mod (%protect-module ast))
         (mode (%protect-mode ast))
         (modval (eval-mod-ext (if (atom mod)
                                   (list mod)
                                 mod))))
    (if (and modval (not (modexp-is-error modval)))
        (if (eq mode :unset)
            (setf (module-protected-mode modval) nil)
          (setf (module-protected-mode modval) t)))))

;;; *******
;;; DRIBBLE
;;; *******
(defun eval-dribble (ast)
  (let ((file (%dribble-file ast)))
    (if file
        (let ((stream (open file :direction :output
                            :if-exists :supersede
                            :if-does-not-exist :create)))
          (unless stream
            (with-output-chaos-error ('no-such-file)
              (format t "could not open file ~a." file)
              ))
          (with-output-msg ()
            (format t "starts dribbling to ~a (~a)." (namestring file)
                    (get-time-string)))
          (setq *dribble-ast* t)
          (setq *dribble-stream* stream))
      (when *dribble-stream*
        (with-output-msg ()
          (princ "finishing dribble."))
        (close *dribble-stream*)
        (setq *dribble-stream* nil)
        (setq *dribble-ast* nil)))))

;;; **********
;;; SAVE-CHAOS
;;; **********
(defun eval-save-chaos (ast)
  (if (%save-chaos-top ast)
      (save-chaos (%save-chaos-top ast)
                  (%save-chaos-file ast))
    (save-chaos 'cafeobj-top-level
                (%save-chaos-file ast))))

;;; **
;;; LS
;;; **
(defun eval-ls (ast)
  (let ((dir (%ls-dir ast)))
    #+(or GCL EXCL CMU LUCID CLISP OPENMCL)
    (if (equal dir '("."))
        (chaos-ls "../")
      (if dir
          (chaos-ls dir)
	    (chaos-ls ".")))
    #-(or GCl EXCL CMU LUCID CLISP OPENMCL)
    (princ-simple-princ-open (chaos-ls (concatenate 'string dir "/")))
    (force-output)))

;;; ***
;;; PWD
;;; ***
(defun eval-pwd (ast)
  (declare (ignore ast))
  (princ (chaos-pwd))
  (force-output))

;;; *****
;;; SHELL
;;; *****
(defun eval-shell (ast)
  (let ((command (%shell-command ast)))
    #+(OR GCL LUCID EXCL CLISP)
    (when command
      (setq command (reduce #'(lambda (x y) (concatenate 'string x " " y))
                            command))
      #+GCL (system command)
      #+EXCL (excl:shell command)
      #+CLISP (ext::shell command)
      )
    #+CMU
    (when command
      (let ((com (car command))
            (args (cdr command)))
        (ext:run-program com args :output t)))
    #+:openmcl
    (when command
      (let ((com (car command))
            (args (cdr command)))
        (ccl:run-program com args :output t)))
    ))

;;; **
;;; CD
;;; **
(defun eval-cd (ast)
  (chaos-cd (%cd-directory ast))
  (princ (chaos-pwd))
  (force-output))

;;; *****
;;; PUSHD
;;; *****
(defun eval-pushd (ast)
  (chaos-pushd (%pushd-directory ast) t)
  (chaos-print-directory-stack))

;;; ****
;;; POPD
;;; ****
(defun eval-popd (ast)
  (if (%popd-num ast)
      (chaos-popd (%popd-num ast))
    (chaos-popd))
  (format t "~&~a" (chaos-pwd)))

;;; ****
;;; DIRS
;;; ****
(defun eval-dirs (ast)
  (declare (ignore ast))
  (chaos-print-directory-stack))

;;; ****
;;; SHOW
;;; ****
(defun show-describe (tag dat)
  (let ((it (car dat))
        (describe (eq tag 'describe)))
    (case-equal it
                (("mod" "module") (print-mod (cdr dat) describe))
                (("view") (show-view (cdr dat) describe))
                ("sorts" (show-sorts (cdr dat) describe))
                ("sort" (show-sort (cdr dat) describe))
                (("psort" "principal-sort")
                 (print-principal-sort (cdr dat)))
                (("ops" "operators") (show-ops (cdr dat) describe))
                (("op" "operator") (show-op (cdr dat) describe))
                ("context" (show-context (cdr dat)))
                ("select" (eval-mod-ext (if (equal tag 'select)
                                            dat
                                          (cdr dat))
                            t))
                (("sign" "sig" "signature")(show-sign (cdr dat) describe))
                ("memo" (show-term-memo-table))
                ("vars" (print-vars (cdr dat)))
                (("axioms" "eqs" "eqns" "rls") (print-axs (cdr dat) describe))
                ("subs" (print-subs (cdr dat)))
                ;; ("name" (print-name (cdr dat)))
                ;; ("abbrev" (print-abbrev-name (cdr dat)))
                ("tree"
                 (if (and $$term (not (eq 'void $$term)))
                     (print-term-tree $$term *chaos-verbose*)
                   (with-output-chaos-warning ()
                     (princ "no current term to display."))))
                ("term"
                 (let* ((target (if (not (equal (second dat) "tree"))
                                    (second dat)
                                  nil))
                        (tree? (if target
                                   (third dat)
                                 (second dat))))
                   (show-term target tree?)))
                ("subterm"
                 (if $$subterm
                     (show-term $$subterm (cadr dat))
                   (with-output-chaos-warning ()
                     (format t "no subterm is selected."))))
                ("selection" (show-apply-selection))
                (("let" "binding") (show-bindings))
                ("sub" (multiple-value-bind (no len)
                           (if (cadr dat)
                               (parse-integer (cadr dat) :junk-allowed t)
                             (values 1 0))
                         (unless (and (integerp no)
                                      (= (length (cadr dat)) len))
                           (with-output-chaos-error ()
                             (format t "Invalid submodule number ~a" (cadr dat))
                             (chaos-to-top)))
                         (show-sub (cddr dat) (1- no) describe)))
                ("params" (print-params (cdr dat)))
                ("param" (multiple-value-bind (no len)
                             (if (cadr dat)
                                 (parse-integer (cadr dat) :junk-allowed t)
                               (values 1 0))
                           (if (and (integerp no) (= len (length (cadr dat))))
                               (show-param (cddr dat) (1- no) describe)
                             (show-param (cddr dat) (cadr dat) describe))))
                ("time" (let ((val (timer)))
                          (format t "~8,3f cpu    ~8,3f real~%" (car val) (cadr val))))
                ("rules" (print-rules (cdr dat)))
                ("all" (case-equal (cadr dat)
                                   ("rules"
                                    (let ((*module-all-rules-every* t))
                                      (print-rules (cddr dat))))
                                   (("axioms" "eqns" "eqs" "rls")
                                    (let ((*module-all-rules-every* t))
                                      (print-axs (cddr dat) describe)))
                                   ("ops" (show-ops (cddr dat) describe t))
                                   ("sorts" (show-sorts (cddr dat) describe t))
                                   (("sign" "sig" "signature") (show-sign (cddr dat) describe t))
                                   ;; obsolate.
                                   ;; (("switch" "switches" "modes") (show-modes t))
                                   (otherwise (with-output-chaos-error ()
                                                (format t "no such `show' option ~a"
                                                        (cadr dat))))
                                   ))
                ("modules" (print-modules (cdr dat)))
                ("views" (print-views (cdr dat)))
                ("rule" (apply-print-rule (cadr dat)))
                ("pending" (print-pending))
                (("modes" "switches") (show-modes t))
                (("switch" "sw" "mode") (show-modes (cdr dat)))
                ("limit" (cafein-show-rewrite-limit))
                ("stop" (cafein-show-stop-pattern))
                (("features" "feature") (print-simple-princ-open *chaos-features*))
                ;; PigNose Commands
                #+:BigPink
                ("clause" (pignose-show-clause (cadr dat) describe))
                #+:BigPink
                ;; ("option" (pignose-show-option (cadr dat) describe))
                ("option" (pignose-show-option (cadr dat)))
                ;; =(*)=> support
                (("exec" "search" "sch") (case-equal (cadr dat)
                                                     ("graph" (show-rwl-sch-graph))
                                                     (otherwise
                                                      (with-output-chaos-error ()
                                                        (format t "no such `show exec' option"
                                                                (cadr dat))))))
                ("path" (let ((opt (cadr dat)))
                          (if (member opt '("labels" "label") :test #'equal)
                              (show-rwl-sch-path (caddr dat) :label)
                            (show-rwl-sch-path opt))))
                ;;
                ("?"    
                 (princ "** general module inspection commands.")
                 (terpri)
                 (princ "  show|describe [sorts|ops|vars|axioms|params|subs|sign]")
                 (terpri)
                 (princ "  show|describe [<Modexp>]") (terpri)
                 (princ "  show|describe sort <Sort>") (terpri)
                 (princ "  show|describe op <Operator>") (terpri)
                 (princ "  show|describe [all] {sorts|ops|sign|axioms}")
                 ;; (princ "  show select <Modexp>") (terpri)
                 (terpri)
                 (princ "** print view.")
                 (princ "  show view <view-name>") (terpri)
                 (terpri)
                 (princ "** print submodules/prameters")
                 (terpri)
                 (princ "  show sub <number> [<Modexp>]")
                 (terpri)
                 (princ "  show param <argname> [<Modexp>]")
                 ;;
                 (terpri)
                 (princ "** supporting commands for proof.")
                 (terpri)
                 (princ "  show [all] rules [<Modexp>] .") (terpri)
                 ;; (princ "  show abbrev [<Modexp>] .") (terpri)
                 (princ "  show tree") (terpri)
                 (princ "  show term [let-variable] [tree]") (terpri)
                 (princ "  show subterm [tree]") (terpri)
                 (princ "  show let") (terpri)
                 (princ "  show selection") (terpri)
                 (princ "  show [all] rule <RuleSpec> .") (terpri)
                 (princ "  show pending") (terpri)
                 (princ "  show context") (terpri)
                 ;; (princ "  show apply context") (terpri)
                 (princ "** misc.")
                 (terpri)
                 (princ "  show modules") (terpri)
                 (princ "  show views") (terpri)
                 ;; (princ "  show [all] modes") (terpri)
                 (princ "  show switch [<Switch>]") (terpri)
                 (princ "  show time") (terpri)
                 (princ "  show limit") (terpri)
                 (princ "  show stop") (terpri)
                 (princ "  show features") (terpri)
                 (princ "  show memo")(terpri)
                 ;;
                 (princ "** PigNose resolve base proof system commands.")
                 (terpri)
                 (princ "  show clause <ClauseId>")
                 (terpri)
                 )
                (otherwise (print-mod dat describe)))
    ))

(defun eval-show (ast)
  (show-describe 'show (%show-args ast)))

;;; ********
;;; DESCRIBE
;;; ********
(defun eval-describe (ast)
  (show-describe 'describe (%describe-args ast)))

;;; ******
;;; SELECT
;;; ******
(defun eval-select (ast)
  (let ((modexp (%select-modexp ast)))
    (eval-mod-ext modexp t)))

;;; ***
;;; SET
;;; ***
(defun eval-set (ast)
  (let ((which (%set-switch ast))
        (value (%set-value ast)))
    (set-chaos-switch which value)))

;;; **********
;;; REGULARIZE
;;; **********

(defun eval-regularize (ast)
  (let ((mod (eval-mod-ext (%regularize-modexp ast))))
    (unless *chaos-quiet*
      (with-output-simple-msg ()
        (format t ">> started process of regularizing signature ..."))
      (terpri)
      (force-output))
    (regularize-signature mod)))

;;; *****
;;; CHECK
;;; *****
(defun eval-check (ast)
  (let ((args (%check-args ast)))
    (case (%check-what ast)

      ;; regularity
      (:regularity
       (let ((module (eval-mod-ext args)))
         (unless *chaos-quiet*
           (with-output-simple-msg ()
             (format t ">> start regularity check ...")
             (terpri)
             (force-output)))
         (check-regularity module)))

      ;; operator strictness
      (:strictness
       (let ((mod (if *last-module* *last-module*
                    (if *current-module*
                        *current-module*
                      (with-output-chaos-error ('no-context)
                        (princ "no context (current) module.")
                        )))))
         ;;
         (!setup-reduction mod)
         (with-in-module (mod)
           (if args
               (let ((parsedop (parse-op-name args)))
                 (let ((ops (find-qual-operators parsedop mod)))
                   (if ops
                       (dolist (op ops)
                         (check-operator-strictness op mod t))
                     (with-output-chaos-error ('no-such-operator)
                       (princ "no such operator")
                       (print-chaos-object parsedop)
                       ))
                   ))
             (check-operator-strictness-whole mod t)))))

      ;; TRS compatibility
      (:compatibility
       (let ((module (eval-mod-ext args)))
         (unless *chaos-quiet*
           (with-output-simple-msg ()
             (format t ">> started compatibility check:"))
           (terpri)
           (force-output))
         (let ((res (check-compatibility module))
               (*print-indent* (+ 2 *print-indent*)))
           (if res
               (with-in-module (module)
                 (with-output-simple-msg ()
                   (format t ">> module (corresponding TRS) is NOT compatible:")
                   (dolist (r-ms res)
                     (format t "~&- rewrite rule")
                     (let ((*print-indent* (+ 2 *print-indent*)))
                       (print-next)
                       (print-chaos-object (car r-ms))
                       )
                     (format t "~&  violates the compatibility,")
                     (format t "~&  and following operator(s) can possibly be affected:")
                     (let ((*print-indent* (+ 2 *print-indent*)))
                       (dolist (m (cdr r-ms))
                         (print-next)
                         (print-chaos-object m))))))
             (with-output-simple-msg ()
               (format t ">> module is compatible."))))))
      ;;;
      ;;;
      ;;;
      (:coherency
       (let ((mod (if *last-module* *last-module*
                    (if *current-module*
                        *current-module*
                      (with-output-chaos-error ('no-context)
                        (princ "no context (current) module.")
                        )))))
         ;;
         (!setup-reduction mod)
         (with-in-module (mod)
           (if args
               (let ((parsedop (parse-op-name args)))
                 (let ((ops (find-qual-operators parsedop mod)))
                   (if ops
                       (dolist (op ops)
                         (check-operator-coherency op mod t))
                     (with-output-chaos-error ('no-such-operator)
                       (princ "no such operator")
                       (print-chaos-object parsedop)
                       ))
                   ))
             (check-operator-coherency-whole mod)))))
      ;;
      ;; SENSIBILITY of the signature
      ;;
      (:sensible
       (let ((module (eval-mod-ext args)))
	 (unless *chaos-quiet*
	   (with-output-simple-msg ()
	     (format t ">> Start sensible check ...")
	     (terpri)
	     (force-output)))
	 (check-sensible module t)))
      (:rew-coherence
       (let ((module (eval-mod-ext (cdr args))))
	 (let ((r-arg (car args)))
	   (unless (or (equal "coherency" r-arg)
		       (equal "coh" r-arg))
	     (with-output-chaos-error ('invalid-arg)
	       (format t "check rewriting: Invalid argument ~s" r-arg)))
	   (check-rwl-coherency module))))

      ;; PigNose extention
      #+:BigPink
      (:invariance
       (pn-check-invariance args))
      #+:BigPink
      (:safety
       (pn-check-safety args))
      #+:BigPink
      (:refinement
       (pn-check-refinement args))
      ;; unknown
      (t (with-output-chaos-error ('invalid-arg)
           (format t "unknown option to check: ~a" (%check-what ast))
           )))))

;;; *************
;;; TRAM COMPILER
;;; *************
(defun eval-tram (ast)
  (let ((command (%tram-command ast))
        (modexp (%tram-modexp ast))
        (pre-term (%tram-term ast))
        (debug (%tram-debug ast)))
    ;; reset interface
    (when (eq command :reset)
      (kill-tram-process)
      (return-from eval-tram t))
    ;; first we check the context
    (let ((mod (if modexp
                   (eval-modexp modexp)
                 *last-module*)))
      ;;
      (when (or (null mod) (modexp-is-error mod))
        (if (null mod)
            (with-output-chaos-error ('no-context)
              (princ "no module expression provided and no selected(current) module.")
              )
          (with-output-chaos-error ('no-such-module)
            (princ "incorrect module expression, no such module ")
            (print-chaos-object modexp)
            )))
      ;; process specified command
      (case command
        ((:compile :compile-all)
         (multiple-value-bind (res err)
             (tram-compile-chaos-module (if (eq command :compile)
                                            nil
                                          t)
                                        mod debug)
           (when err
             (with-output-simple-msg ()
               (princ "[Error] error occured while module compilation ...")))
           (fresh-line)
           (princ (car res))
           (when (cadr res)
             (print-next)
             (princ (cadr res)))
           (force-output)))
        ((:reduce :execute)
         (multiple-value-bind (result err-flg)
             (tram-reduce mod pre-term (if (eq command :reduce)
                                           nil
                                         t))
           (if err-flg
               (with-output-simple-msg ()
                 (princ "[Error] error occured while reduction in compiled code...")
                 (terpri)
                 (princ (car result))
                 (when (cadr result)
                   (terpri)
                   (princ (cadr result)))
                 (force-output))
             (progn
               (context-push-and-move *last-module* mod)
               (let ((*print-indent* (+ 4 *print-indent*)))
                 (with-in-module (mod)
                   (setq $$term (car result))
                   (update-lowest-parse $$term)
                   (when *mel-sort*
                     (setf $$term
                       (apply-sort-memb $$term mod)))
                   (fresh-line)
                   (term-print $$term)
                   (print-check 0 3)
                   (princ ":")
                   (print-sort-name (term-sort $$term) mod)
                   (when (cadr result)
                     (terpri)
                     (princ (cadr result)))
                   (force-output)
                   (reset-target-term $$term *last-module* mod)))
               (context-pop-and-recover)))))
        ;;
        (otherwise (with-output-panic-message ()
                     (format t "internal error, unknown tram command ~a"
                             command)
                     (chaos-error 'panic))))
      )))

;;; ********
;;; AUTOLOAD
;;; ********
(defun eval-autoload (ast)
  (let ((modname (%autoload-mod-name ast))
        (file (%autoload-file ast)))
    (let ((entry (assoc modname *autoload-alist* :test #'equal)))
      (if entry
          (setf (cdr entry) file)
        (push (cons modname file) *autoload-alist*)))
    ))

;;; *********************
;;; MISC SUPOORT ROUTINES
;;; *********************

;;; NOT USED.
(defvar *real-time* 0)
(defvar *run-time* 0)

(defun timer ()
  (let ((real *real-time*) (sys *run-time*))
    (setq *real-time* (get-internal-real-time))
    (setq *run-time* (get-internal-run-time))
    (list (float (/ (- *run-time* sys) internal-time-units-per-second))
          (float (/ (- *real-time* real) internal-time-units-per-second)))))

#||
(defmacro call-that (x)
  `(progn (setq ,x (term-copy-and-returns-list-variables $$norm)) 'done))

(defun termcopy (x) (term-copy-and-returns-list-variables x))

(defun show ()
  (when (and $$term (not (eq 'void $$term)))
    (term-print $$term))
  (values)
  )
||#

;;; =====
;;; CBRED
;;; =====
(defun eval-cbred (ast)
  (let ((modexp (%cbred-module ast))
        (pre-lhs (%cbred-lhs ast))
        (pre-rhs (%cbred-rhs ast))
        (*consider-object* t)
        (*rewrite-semantic-reduce* nil)
        sort
        time1
        time2
        (time-for-parse nil)
        (time-for-reduction nil)
        (number-matches 0))
    (let ((mod (if modexp
                   (eval-modexp modexp)
                 *last-module*)))
      (unless (eq mod *last-module*)
        (clear-term-memo-table *term-memo-table*))
      (when (or (null mod) (modexp-is-error mod))
        (if (null mod)
            (with-output-chaos-error ('no-context)
              (princ "no context mdoule."))
          (with-output-chaos-error ('no-such-module)
            (princ "no such module: ")
            (print-chaos-object modexp))))
      ;;
      (context-push-and-move *last-module* mod)
      (with-in-module (mod)
        (when *auto-context-change*
          (change-context *last-module* mod))
        (!setup-reduction mod)
        (setq $$mod *current-module*)
        (setq sort *cosmos*)
        (when *show-stats* (setq time1 (get-internal-run-time)))
        (let* ((*parse-variables* nil)
               (lhs (simple-parse *current-module* pre-lhs sort))
               (rhs (simple-parse *current-module* pre-rhs sort)))
          (when (or (null (term-sort lhs))
                    (null (term-sort rhs))
                    (sort<= (term-sort lhs) *syntax-err-sort* *chaos-sort-order*)
                    (sort<= (term-sort rhs) *syntax-err-sort* *chaos-sort-order*))
            (context-pop-and-recover)
            (return-from  eval-cbred nil))
          (when *show-stats*
            (setq time2 (get-internal-run-time))
            (setq time-for-parse
              (format nil "~,3f sec"
                      (elapsed-time-in-seconds time1 time2))))
          ;;
          (unless *chaos-quiet*
            (fresh-all)
            (flush-all)
            (princ "-- cbred in ")
            (print-simple-mod-name *current-module*)
            (print-check 0 3)
            (princ " : ")
            ;; (print-check)
            (let ((*print-indent* (+ 4 *print-indent*)))
              (term-print lhs)
              (print-check 0 4)
              (princ " == ")
              ;; (print-check)
              (term-print rhs))
            (flush-all))
          ;;
          (setq $$matches 0)
          (setq time1 (get-internal-run-time))
          
          (let ((*perform-on-demand-reduction* t)
                (*rule-count* 0))
            (multiple-value-bind (ok? goals)
                (do-cbred *current-module* lhs rhs)
              ;;
              (setq time2 (get-internal-run-time))
              (setq time-for-reduction
                (format nil "~,3f sec"
                        (elapsed-time-in-seconds time1 time2)))
              (setq number-matches $$matches)
              (setq $$matches 0)
              (with-output-simple-msg ()
                (princ "** Result: ")
                (if ok?
                    (princ "true")
                  (progn
                    (princ "falied.")
                    (let ((*print-indent* *print-indent*))
                      (print-next)
                      (princ "remaining goals:")
                      (dolist (goal goals)
                        (print-next)
                        (term-print (car goal))
                        (print-check 0 4)
                        (princ " == ")
                        ;; (print-check)
                        (term-print (cdr goal)))))))
              ;;
              (when *show-stats*
                (format t "~%(~a for parse, ~s rewrites(~a), ~d matches"
                        time-for-parse
                        *rule-count*
                        time-for-reduction
                        number-matches))
              (if (zerop *term-memo-hash-hit*)
                  (format t ")~%")
                (format t ", ~d memo hits)~%"
                        *term-memo-hash-hit*))
              (flush-all))
            )))
      (context-pop-and-recover)
      )))

;;; INSEPCT
(defun eval-inspect (ast)
  (let ((modexp (%inspect-modexp ast))
        mod)
    (setf mod (if (null modexp)
                  *last-module*
                (eval-modexp modexp)))
    (when (modexp-is-error mod)
      (with-output-chaos-error ('no-such-module)
        (princ "incorrect module expression or uknown module: ")
        (print-modexp modexp)
        ))
    ;;
    (unless mod
      (with-output-chaos-error ('no-context)
        (princ "no module to be inspeted!")
        ))
    ;;
    (!inspect-module mod) ))

;;;
;;; WHAT-IS
;;;
(defun eval-what-is (ast)
  (let ((name (%what-is-name ast))
        (modexp (%what-is-module ast))
	(mod nil))
    (setf mod (if (null modexp)
		  *last-module*
		(eval-modexp modexp)))
    (when (modexp-is-error mod)
      (with-output-chaos-error ('no-such-module))
      (princ "incorrect module expression or unknown module: ")
      (print-modexp modexp))
    ;;
    ;; (!what-is name mod)
    ))

;;; EVAL-LOOK-UP
;;;
(defun eval-look-up (ast)
  (let ((name (%look-up-name ast))
        (modexp (%look-up-module ast))
	(mod nil))
    (setf mod (if (null modexp)
		  *last-module*
		(eval-modexp modexp)))
    (when (modexp-is-error mod)
      (with-output-chaos-error ('no-such-module))
      (princ "incorrect module expression or unknown module: ")
      (print-modexp modexp))
    ;;
    (!look-up name mod)))

;;; 
;;; DELIMITER
;;;
(defun eval-delimiter (ast)
  (let ((op (%delimiter-operation ast))
	(chars (%delimiter-char-list ast)))
    (case op
      ((:set :add) (!force-single-reader chars))
      ((:delete) (!unset-single-reader chars))
      (otherwise (with-output-chaos-error ('internal)
		   (format t "Internal error, invalid delimiter operation ~s" op)
		   )))))

;;; *******************
;;; Chaos Top
;;; *******************
(defun eval-chaos-top (ast)
  (let ((parameters (%chaos-parameters ast)))
    (declare (ignore parameters))       ; for now
    (chaos-top)))

;;; EOF
