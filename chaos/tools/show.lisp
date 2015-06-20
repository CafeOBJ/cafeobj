;;;-*- Mode:LISP; Package:CHAOS; Base:10; Syntax:Common-lisp -*-
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
#|==============================================================================
                                 System: CHAOS
                                 Module: tools
                                File: show.lisp
==============================================================================|#
#-:chaos-debug
(declaim (optimize (speed 3) (safety 0) #-GCL (debug 0)))
#+:chaos-debug
(declaim (optimize (speed 1) (safety 3) #-GCL (debug 3)))

;;;-----------------------------------------------------------------------------
;;; SHOW commands handlers
;;;-----------------------------------------------------------------------------

;;; ************
;;; SHOW CONTEXT
;;; ************
(defun show-context (toks)
  (let ((mod (eval-mod-ext toks)))
    (unless mod
      (with-output-msg ()
        (princ "no current context, `select' some module first."))
      (return-from show-context nil))
    (if (eq (get-context-module) mod)
        (format t "~%-- current context :")
        (progn (format t "~%-- context of : ")
               (print-chaos-object mod)))
    (context-push-and-move (get-context-module) mod)
    (with-in-module (mod)
      (format t "~%[module] ")
      (print-chaos-object *current-module*)
      (format t "~&[special bindings]")
      (when (and $$term (not (eq $$term 'void)))
        (unless (check-$$term-context *current-module*)
          (format t "~&*Notice* : term and selected subterm are not valid in the current context.")))
      (let ((*print-indent* (+ *print-indent* 2)))
        (print-next)
        (princ "$$term    = ")
        (if (and $$term (not (eq $$term 'void)))
            (show-term $$term nil)
            (princ "none."))
        (print-next)
        (show-apply-selection *current-module*)
        (show-bindings *current-module*)
        (show-selection-stack *current-module*)
        (print-pending *current-module*)
        (show-stop-pattern *current-module*)
        ;; (when *proof-tree* (pr-ptree *proof-tree*))
        ))
    (context-pop-and-recover)))

;;; SHOW BINDINGS

(defun show-bindings (&optional (module (get-context-module)))
  (unless module
    (with-output-msg ()
      (princ "no context (current module) is specified.")
      (return-from show-bindings nil)))
  (with-in-module (module)
    (let ((bindings (module-bindings *current-module*)))
      (format t "~&[bindings] ")
      (if bindings
          (dolist (bind bindings)
            (print-next)
            (format t "~a = " (car bind))
            (term-print (cdr bind)))
          (princ "empty.")))))

;;: show stop pattern
(defun show-stop-pattern (&rest ignore)
  (declare (ignore ignore))
  (format t "~&[stop pattern] ")
  (if *rewrite-stop-pattern*
      (let ((*fancy-print* nil)
            (*print-with-sort* t))
        (term-print *rewrite-stop-pattern*))
      (princ "not specified.")))
              
;;; show apply selection

(defun show-apply-selection (&optional (module (get-context-module)))
  (unless module
    (with-output-msg ()
      (princ "no context (current module) is specified.")
      (return-from show-apply-selection nil)))
  (when $$term-context
    (with-in-module ($$term-context)
      (format t "$$subterm = ")
      (unless $$subterm
        (format t "no subterm selection is made by `choose'.")
        (return-from show-apply-selection nil))
      (if (term-eq $$term $$subterm)
          (format t " $$term")
          (show-term $$subterm nil)))))

;;; show selection stack

(defun show-selection-stack (&optional ignore)
  (declare (ignore ignore))
  (format t "~&[selections] ")
  (if (null $$selection-stack)
      (format t " empty.")
      (let ((depth 1))
        (terpri)
        (dolist (selection $$selection-stack)
          (dotimes (i (1- depth)) (princ "    "))
          (format t "~3d| " depth)
          (print-simple-princ-flat selection)
          (terpri)
          (incf depth)))))

;;;
;;; print-pending
;;;
(defun print-pending (&optional (module (get-context-module)))
  (unless module
    (with-output-msg ()
      (princ "no context (current module) is specified.")
      (return-from print-pending nil)))
  (with-in-module (module)
    (format t"~&[pending actions] ")
    (if (null $$action-stack)
        (format t " none.")
        (let ((depth 1))
          (terpri)
          (dolist (dact (reverse $$action-stack))
            (dotimes (i (- depth 1)) (princ "   "))
            (format t "~3d| in " depth)
            (term-print (nth 0 dact))
            (princ "  at ")
            (if (term-eq (nth 0 dact) (nth 1 dact))
                (princ "top")
                (term-print (nth 1 dact)))
            (terpri)
            (dotimes (i depth) (princ "   "))
            (princ "| rule ") (print-axiom-brief (nth 2 dact))
            (terpri)
            (dotimes (i depth) (princ "   "))
            (princ "| condition ") (term-print (nth 3 dact))
            (princ "  replacement ") (term-print (nth 4 dact))
            (terpri)
            (incf depth)
            )))))

;;; **************
;;; SHOW TERM ....
;;; **************

(defun show-term (target tree?)
  (when (and tree?
             (not (equal tree? "."))
             (not (equal tree? "tree"))
             (not (equal tree? "graph")))
    (with-output-chaos-warning ()
      (format t "unknown option for `show term' : ~a" tree?))
    (return-from show-term nil))
  (unless (get-context-module)
    (with-output-msg ()
      (princ "no current context, `select' some module first.")
      (return-from show-term nil)))
  (unless target
    (setq target "$$term"))
  (with-in-module ((get-context-module))
    (when (stringp target)
      ;; let variable
      (catch 'term-context-error
        (let ((val (get-bound-value target)))
          (unless val
            (with-output-msg ()
              (format t "current module has no let binding for \"~a\""
                      target)
              (return-from show-term nil)))
          (setq target val))))
    (when (stringp target)
      ;; cought context error
      (return-from show-term nil))
    (let ((*fancy-print* nil)
          (*print-indent* (+ *print-indent* 4)))
      (if (and $$term-context
               (not (check-$$term-context *current-module*)))
          (with-in-module ($$term-context)
            (format t "~%** temporarily changing current context to ")
            (print-simple-mod-name $$term-context)
            (print-next)
            (term-print-with-sort target))
        (progn (print-next)
               (term-print-with-sort target)))
      ;; (terpri)
      (when (equal tree? "tree")
        (print-term-tree target *chaos-verbose*))
      (when (equal tree? "graph")
        (print-term-graph target *chaos-verbose*)))))

;;; ************
;;; SHOW MOD ...
;;; ************
(defun print-mod (toks &optional (desc nil))
  (let ((mod (if (not (equal "tree" (car toks)))
                 toks
                 (cdr toks)))
        (tree (equal (car toks) "tree")))
    (let ((modval (eval-mod-ext mod)))
      (when modval
        (if tree
            (if desc
                (describe-module-graph (module-dag modval))
              (print-module-graph modval))
          (if desc
              (describe-module modval)
            (show-module modval)))))))

;;; *************
;;; SHOW VIEW ...
;;; *************
(defun show-view (toks &optional (desc nil))
  (declare (ignore desc))
  (let ((view (find-view-in-env (normalize-modexp (car toks)))))
    (if view
        (print-view view *standard-output* nil nil)
        (with-output-chaos-error ('no-such-view)
          (format t "no such view : ~a" (car toks))
          ))))

;;; **********
;;; SHOW SORTS
;;; **********
(defun show-sorts (toks &optional (desc nil) (all nil))
  (let ((mod (if (not (equal "tree" (car toks)))
                 toks
                 (cdr toks)))
        (tree (equal (car toks) "tree")))
    (let ((modval (eval-mod-ext mod)))
      (when modval
        (if tree
            (print-module-sort-graph modval)
            (print-module-sorts modval desc all))))))

;;; ********
;;; SHOW OPS
;;; ********
(defun show-ops (toks &optional (desc nil)(all nil))
  (print-module-ops (eval-mod-ext toks) desc all))

;;; *********
;;; SHOW SIGN
;;; *********
(defun show-sign (toks &optional (desc nil) (all nil))
  (let ((mod (eval-mod-ext toks)))
    (print-module-sorts mod desc all)
    (print-module-ops mod desc all)))

;;; *********
;;; SHOW VARS
;;; *********
(defun print-vars (toks &optional (desc nil))
  (print-module-variables (eval-mod-ext toks) desc))

;;; *********
;;; SHOW EQNS
;;; *********
(defun print-eqs (toks &optional (desc nil))
  (let ((mod (eval-mod-ext toks)))
    (!setup-reduction mod)
    (print-module-eqs mod desc)))

;;; ***********
;;; SHOW AXIOMS
;;; ***********
(defun print-axs (toks &optional (desc nil))
  (let ((mod (eval-mod-ext toks)))
    (!setup-reduction mod)
    (print-module-axs mod desc)))

;;; ********
;;; SHOW RLS
;;; ********
(defun print-rls (toks &optional (desc nil))
  (let ((mod (eval-mod-ext toks)))
    (!setup-reduction mod)
    (print-module-rls mod desc)))

;;; **********
;;; SHOW RULES
;;; **********
(defun print-rules (toks &optional (desc nil))
  (declare (ignore desc))
  (let ((mod (eval-mod-ext toks)) (i 1))
    (with-in-module (mod)
      (!setup-reduction mod)
      (format t "~% -- rewrite rules in module : ")
      (print-simple-mod-name mod)
      (dolist (r (get-module-axioms mod t))
        (format t "~&~3D : " i)
        (print-axiom-brief r)
        (incf i))
      )))

;;; *********
;;; SHOW SUBS
;;; *********
(defun print-subs (toks &optional (desc nil))
  (print-module-submodules (eval-mod-ext toks) desc))

;;; **********
;;; SHOW PRAMS
;;; **********
(defun print-params (toks &optional (desc nil))
  (print-module-parameters (eval-mod-ext toks) *standard-output* desc))

(defun top-print-name (toks)
  (let ((mod (eval-mod-ext toks)))
    (print-chaos-object mod)
    (when (print-merged mod) (princ " ** opening"))
    (terpri)))

#|
(defun print-abbrev-name (toks)
  (let ((mod (eval-mod-ext toks)))
    (let ((num (print$mod-num mod)))
      (if (= 0 num)
          (princ  "(...)")
          (progn (princ "MOD") (prin1 num))
          )
      (princ " is ")
      (let ((*print-abbrev-mod* nil))
        (print-mod-name mod))
      (terpri))))
|#

;;; **  TODO ***
(defun print-principal-sort (toks)
  (let ((mod (eval-mod-ext toks)))
    (let ((*current-module* mod))
      (print-sort-name (module-principal-sort mod) mod)
      (terpri)
      )))

;;; *********
;;; SHOW SORT
;;; *********
(defun show-sort (toks &optional (desc nil))
  (declare (ignore desc))
  (let* ((tree? (equal (car toks) "tree"))
         (sort (if tree?
                   (cdr toks)
                   toks))
         (mod nil))
    (multiple-value-bind (sort-n modexp)
        (check-qualified-sort-name sort)
      (cond (modexp
             (setq mod (eval-modexp modexp))
             (unless (module-p mod)
               (with-output-msg ()
                 (format t "no such module ~a" modexp)
                 (return-from show-sort nil))))
            (t (setq mod (get-context-module))
               (unless (module-p mod)
                 (with-output-msg ()
                   (princ "no context(current) module, select some first.")
                   (return-from show-sort nil)))))
      (with-in-module (mod)
        (let ((srt (find-sort-in mod sort-n)))
          (if srt
              (if tree?
                  (print-sort-graph srt)
                  (describe-sort srt))
              (with-output-msg ()
                (format t "no such sort ~a" sort-n))))))))

;;; *******
;;; SHOW OP
;;; *******
(defun parse-op-name (tokens)
  (let ((res nil))
    (if tokens
        (progn
          (when (and (null (cdr tokens))
                     (stringp (car tokens)))
            (setq tokens (read-opname-from-string (car tokens))))
          (let ((*modexp-parse-input* tokens))
            (let ((val (parse-operator-reference nil)))
              (when *on-modexp-debug*
                (format t "[parse-op-name] *modexp... = ~s" *modexp-parse-input*))
              (when (or (null *modexp-parse-input*)
                        (and (null (cdr *modexp-parse-input*))
                             (equal "." (car *modexp-parse-input*))))
                (setq res val))
            res)))
      nil)))

(defun get-module-from-opref (parsedop)
  (let ((mod nil))
    (cond ((%opref-module parsedop)
           (setq mod (%opref-module parsedop))
           (unless (module-p mod)
             (setq mod (eval-modexp (%opref-module parsedop)))
             (unless (module-p mod)
               (with-output-chaos-error ('no-such-module)
                 (princ "resolving operator reference ")
                 (print-ast parsedop)
                 (print-next)
                 (princ "no such module ")
                 (princ (%opref-module parsedop))))))
          (t (setq mod (get-context-module))
             (unless mod
               (with-output-chaos-error ('no-context)
                 (princ "no context module is given.")))))
    mod))

(defun resolve-operator-reference (opref &optional (no-error nil))
  (let ((mod (get-module-from-opref opref)))
    (!setup-reduction mod)
    (with-in-module (mod)
      (let* ((name (%opref-name opref))
             (ops (find-all-qual-operators-in mod name)))
        (unless ops
          (when (equal "." (car (last name)))
            (setq name (butlast name))
            (setq ops (find-all-qual-operators-in mod name))))
        (unless ops
          (if no-error
              (with-output-simple-msg ()
                (format t "no such operator: ~a " name)
                (return-from resolve-operator-reference
                  (values nil mod)))
            (with-output-chaos-error ('no-such-op)
              (format t "no such operator: ~a" name))))
        (values ops mod)))))

(defun show-op (toks &optional (desc nil))
  (let ((parsedop (parse-op-name toks)))
    (multiple-value-bind (ops mod)
        (resolve-operator-reference parsedop t)
      (with-in-module (mod)
        (dolist (op ops)
          (if desc
              (describe-operator op)
            (describe-operator-brief op)))))))

;;; ********
;;; SHOW SUB
;;; ********
(defun show-sub (toks no &optional describe)
  (let* ((mod (eval-mod-ext toks))
         (sub (nth-sub no mod)))
    (if sub
        (progn
          (with-in-module (sub)
            (if describe
                (describe-module sub)
                (show-module sub))
            (terpri)))
        (with-output-msg ()
          (princ "no such sub-module")))
    ))

;;; ***********
;;; SHOW PARAM
;;; ***********
(defun show-param (toks no &optional describe)
  (let ((mod (if toks
                 (eval-mod-ext toks)
               (get-context-module))))
    (unless mod
      (with-output-msg ()
        (format t "no context (current module) is specified.")
        (return-from show-param nil)))
    (let ((param (find-parameterized-submodule no mod)))
      (if (and param (not (modexp-is-error param)))
          (progn
            (with-in-module (param)
              (if describe
                  (describe-module param)
                  (show-module param)))
            (terpri))
          (with-output-msg ()
            (if (null (module-parameters mod))
                (princ "module has no parameters.")
                (format t "no such parameter ~a" (if (integerp no)
                                                        (1+ no)
                                                        no))))))
    ))

;;; ************
;;; SHOW MODULES
;;; ************
(defun print-modules (x)
  (declare (ignore x))
  (let ((*print-indent-contin* nil)
        (*print-line-limit* 80)
        (mods nil))
    (dolist (entry *modules-so-far-table*)
      (let ((m (cdr entry)))
        (cond ((or (module-hidden m) (module-is-parameter-theory m))
               (when (or *on-debug* *chaos-verbose*)
                 (push m mods)))
              (t (unless (equal (module-name m) "%") (push m mods))))))
    ;;
    (dolist (m (sort mods #'ob< :key #'(lambda (x)
                                         (let ((name (module-name x)))
                                           (if (atom name)
                                               name
                                               (car name))))))
      (print-check)
      (when (< 0 (filecol *standard-output*))
        (princ "  "))
      ;; (print-modexp-simple m)
      (print-mod-name m *standard-output* t t)
      (print-check))
    (fresh-line)))

;;; **********
;;; SHOW VIEWS
;;; **********
(defun print-views (x)
  (declare (ignore x))
  (let ((*print-indent-contin* nil))
    #||
    (maphash #'(lambda (key m)
                 (declare (ignore m))
                 (print-check)
                 (when (< 0 (filecol *standard-output*))
                   (princ "  "))
                 (princ key)
                 (print-check))
             *modexp-view-table*)
    ||#
    (dolist (entry *modexp-view-table*)
      (let ((key (car entry)))
        (print-check)
        (when (< 0 (filecol *standard-output*))
          (princ "  "))
        (princ key)
        (print-check)))
    ))

;;;
;;; MEMO TABLE
;;;
(defun show-term-memo-table ()
  (unless *memoized-module*
    (return-from show-term-memo-table nil))
  (with-in-module (*memoized-module*)
    (format t "** terms in memo table of module ")
    (print-mod-name *memoized-module*)
    (dump-term-hash *term-memo-table*)))

;;; EOF
