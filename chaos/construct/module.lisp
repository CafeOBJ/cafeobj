;;;-*- Mode:LISP; Package:CHAOS; Base:10; Syntax:Common-lisp -*-
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
#|==============================================================================
                                 System: Chaos
                               Module: construct
                               File: module.lisp
==============================================================================|#
#-:chaos-debug
(declaim (optimize (speed 3) (safety 0) #-GCL (debug 0)))
#+:chaos-debug
(declaim (optimize (speed 1) (safety 3) #-GCL (debug 3)))

;;; == DESCRIPTION =============================================================
;;; All procs for stand alone module.
;;;

;;;-----------------------------------------------------------------------------
;;; PRIMITIVE CONSTRUCTOR
;;;-----------------------------------------------------------------------------

;;; CREATE-MODULE : NAME -> MODULE
;;; creates an intance of module . if a module with `name' already exists,
;;; it will be re-initilized.
;;; 
(defun create-module (name)
  (declare (type t name))
  (let ((mod (find-module-in-env name nil)))
    (declare (type (or null module) mod))
    (unless mod
      (when *on-debug*
        (format t "~%[create-module]: creating brand new"))
      (setf mod (module* name)))
    (initialize-module mod)
    (when *on-debug*
      (let ((*print-array* nil) (*print-circle* nil))
        (format t "~%[create-module]: object=~a, name= " mod)
        (print-chaos-object name)))
    (setf (module-creation-date mod) (get-universal-time))
    mod))

(defun !create-module (name)
  (declare (type t name))
  (let ((mod nil))
    (when *on-debug*
      (format t "~%[!create-module]: creating brand new"))
    (setf mod (module* name))
    (initialize-module mod)
    (when *on-debug*
      (let ((*print-array* nil) (*print-circle* nil))
        (format t "~%[!create-module]: object=~a, name= " mod)
        (print-chaos-object name)))
    (setf (module-creation-date mod) (get-universal-time))
    mod))

;;; other useful accessors
(defun module-all-methods (mod &optional (no-error-methods t))
  (let ((ops (module-all-operators mod))
        (res nil))
    (dolist (opinfo ops)
      (dolist (m (opinfo-methods opinfo))
        (when (or (not no-error-methods)
                  (not (method-is-error-method m)))
          (push m res))))
    (nreverse res)))

;;; methods via signature
(defun signature-methods (sig &optional (no-error-methods t))
  (unless *current-module*
    (with-output-chaos-error ('no-context-module)
      (format t "No context module is specified.")))
  (with-in-module (*current-module*)
    (let ((ops (signature$operators sig))
          (res nil))
      (dolist (opinfo ops)
        (dolist (m (opinfo-methods opinfo))
          (when (or (not no-error-methods)
                    (not (method-is-error-method m)))
            (push m res))))
      (nreverse res))))

;;; ***********************************
;;; PREPARETION for PARSING & REWRITING_________________________________________
;;; ***********************************

(defun compute-protected-modules (module)
  (declare (type module module)
           (values list))
  (setf (module-protected-modules module)
        (do-compute-protected-modules module)))

;;; TODO
(defun do-compute-protected-modules (module)
  (declare (type module module)
           (values list))
  module
  nil)

;;;
;;; AUTOMATIC DEPENDENCY CHECK --> RECONSTRUCTION
;;;
(defun reconstruct-module-if-need (module)
  (declare (type module module)
           (values module))
  (cond ((module-is-inconsistent module)
         (reconstruct-module module)
         module)
        (t module)))

(defun reconstruct-module (module)
  (declare (type module module)
           (values t))
  ;; reconstruct module in a bottom up manner
  (when *on-change-debug*
    (format t "~%** reconstructing module")
    (prin1 module))
  (dag-dfs (module-dag module)
           #'(lambda (node)
               (let* ((datum (dag-node-datum node))
                      (mode (cdr datum))
                      (mod (car datum)))
                 (when (and (module-is-inconsistent mod)
                            (not (eq mode :modmorph)))
                   (let ((decl (module-decl-form mod)))
                     (if decl
                         (eval-ast decl)
                         (with-output-chaos-warning ()
                           (princ "Specified module is inconsistent due to some changes in its submodule(s).")
                           (print-next)
                           (princ "The system could not reconstruct it in automatic: ")
                           (if (module-name mod)
                               (prin1 mod))
                           (print-next)
                           (princ "This can happens when you redefine modules.")
                           (print-next)
                           (princ "Please redfine it from the scratch,")
                           (print-next)
                           (princ "if you are loading some file, RE-LOAD it again please.")
                           (print-next)
                           (princ "(If the switch `auto reconstrut' is on, please reset it to `off'.)")
                           (chaos-error 'reconstruct-failure)))))))))

;;;
;;; PREPARE-FOR-PARSING
;;;

;;; list of hook functions, called each time
;;; a module is prepared for parsing.
(defvar *prepare-for-parse-hook* nil)

(defun module-indirect-submodules (module)
  (let ((dmods (module-direct-submodules module))
        (res (cons nil nil)))
    (dolist (dmod dmods)
      (unless (or (eq (cdr dmod) :modmorph)
                  (member dmod (car res) :test #'equal)
                  (module-is-parameter-theory (car dmod)))
        (gather-submodules (car dmod) res)))
    (car res)))

(defun prepare-for-parsing (module &optional force no-error-sort)
  (declare (type module module)
           (type (or null t) force no-error-sort)
           (values t))
  (let ((*on-preparing-for-parsing* t))
    (declare (special *on-preparing-for-parsing*))
    (when *auto-reconstruct*
      (reconstruct-module-if-need module))
    (with-in-module (module)
      (when (or (need-parsing-preparation module) force)
        (print-in-progress "_")
        (check-submodules module)
        ;;
        (let ((als (module-alias module)))
          (dolist (sub (module-all-submodules module))
            (unless (or (assoc sub als)
                        (not (modexp-is-simple-name (module-name (car sub)))))
              (symbol-table-add (module-symbol-table module)
                                (module-name (car sub))
                                (car sub)))))
        ;; regularity check
        (regularize-signature-internal module)
        ;; implicit check regularity
        (setf (module-is-regular module)
          (check-regularity module t))
        ;; 
        (when (and *check-regularity*
                   (not (module-is-theory module)))
          (if (not (module-is-regular module))
              (with-output-chaos-warning ()
                (princ "signature of module ")
                (print-mod-name module *standard-output* t)
                (princ " is not regular. ")
                (print-next)
                (princ "try `check regularity' command for details.")
                (print-next))))
        ;;
        (unless no-error-sort
          (let ((oerrs (generate-err-sorts (module-sort-order module))))
            (declare (ignore oerrs))
            (delete-error-operators-in module)))
        ;; setup operators for various semantic relations.
        (setup-sem-relations-in module)
        ;; (setup-if-then-else-in module)
        (declare-sort-id-constants module)
        (make-operator-clusters-in module)
        ;; (declare-sort-memb-predicates module)
        (setup-error-operators-in module)
        (setup-operators-in module)
        ;; do postponed variable declarations of error sorts
        (declare-error-variables-in module)
        ;; sensible check
        (when (and *check-sensibleness*
                   (not (module-is-theory module)))
          (check-sensible module t))    ; report on
        ;; coherency check
        (when (and *check-rwl-coherency*
                   (not (module-is-theory module)))
          (check-rwl-coherency module t))

        ;; for simple-parser.
        ;; (check-polimorphic-overloading-in module)
        ;; (propagate-attributes module)
        (set-operator-syntactic-properties module)
        (update-parse-information module)
        ;;
        (dolist (hook-fun *prepare-for-parse-hook*)
          (funcall hook-fun module))
        ;;
        )
      (mark-module-ready-for-parsing module)
      ;; that's end.
      module)))

;;;
;;; COMPILE-MODULE
;;;
(defvar *do-=*=-proof* t)

(defun compile-module (module &optional (force nil))
  (declare (type module module)
           (type (or null t) force)
           (values t))
  (prepare-for-parsing module force)
  ;; evaluate postponed psort decl.
  (when (module-psort-declaration module)
    (eval-psort-declaration (module-psort-declaration module) module))
  ;;
  (when (or force (need-rewriting-preparation module))
    (compile-module-internal module)
    (when *do-=*=-proof*
      (try-beh-proof-in module))
    (when (and *check-compatibility*
               (not (module-is-theory module)))
      (when (check-compatibility module)
        (with-output-chaos-warning ()
          (princ "TRS of module ")
          (print-mod-name module *standard-output* t)
          (princ " is not compatible.")
          (print-next)
          (princ "please try `check compatible' command for details.")))))
  module)

(defun !setup-reduction (mod)
  (declare (type module mod))
  (compile-module mod))

(defun final-setup (module)
  (declare (type module module)
           (values t))
  (compile-module module))

(defun compile-module-internal (module)
  (declare (type module module)
           (values t))
  (with-in-module (module)
    (print-in-progress "*")
    ;; do evaluation of delayed declarations such as imported axioms
    ;; with error operator in them.
    (do-delayed-declarations module)
    ;; add operator theory axioms
    (unless (and *open-module*
                 (equal "%" (get-module-print-name module)))
      (dolist (oinfo (module-all-operators module))
        (add-operator-theory-axioms module oinfo)))
    ;;
    (add-identity-completions module)
    ;; add equations for behavioural congruence relation
    (construct-beh-stuff module)
    ;; we need fix axioms before rwl axioms are generated
    ;; (fix-error-method-terms module)
    ;; add rwl axioms if need
    (add-rwl-axioms module)
    ;; genrate rewrite rules
    (generate-rewrite-rules module)
    (mapc #'(lambda (opinfo)
              (compute-rew-strategy module opinfo)
              (fix-strategy-and-rules module opinfo))
          (module-all-operators module))
    ;; TODO.
    ;; (fix-rewrite-rules module)
    (check-behavioural-rules module)
    (normalize-rules-in module)
    (module-error-check module)
    (check-operator-congruency module)
    ;; add labels into symbol table for inspection commands
    (let* ((*module-all-rules-every* t)
           (axs (get-module-axioms module)))
      (dolist (ax axs)
        (let ((labels (axiom-labels ax)))
           (dolist (lab labels)
             (symbol-table-add (module-symbol-table module)
                               lab
                               ax)))))
    ;; set status.
    (mark-module-ready-for-rewriting module)))

(defun do-delayed-declarations (module)
  (with-in-module (module)
    (dolist (decl (reverse (module-delayed-declarations module)))
      (eval-ast decl))
    ;; if this is the opening module, we don't want to
    (when (eq module (eval-modexp "%"))
      (setf (module-delayed-declarations module) nil))))

(defun check-behavioural-rules (module)
  (declare (type module module)
           (values (or null t)))
  (setf (module-has-behavioural-axioms module) nil)
  (dolist (rule (module-all-rules module))
    (when (axiom-is-behavioural rule)
      (setf (module-has-behavioural-axioms module) t)
      (return-from check-behavioural-rules t))))

#|
(defun fix-error-method-terms (module &optional clean)
  (declare (type module module)
           (type (or null t) clean)
           (values t))
  (check-module-rules module)
  (when (module-terms-to-be-fixed module)
    (with-in-module (module)
      (let ((name (module-name module))
            (op-map nil)
            (sort-map nil))
        (cond ((int-instantiation-p name)
               (let ((modmorph (views-to-modmorph
                                (int-instantiation-module name)
                                (int-instantiation-args name))))
                 (setq op-map (modmorph-op modmorph))
                 (setq sort-map (modmorph-sort modmorph))))
              ((int-rename-p name)
               (setq op-map (int-rename-op-maps name))
               (setq sort-map (int-rename-sort-maps name))))
        ;;
        (dolist (term-pair (module-terms-to-be-fixed module))
          (replace-error-method module (cdr term-pair) op-map sort-map))
        (dolist (rule-pair (module-axioms-to-be-fixed module))
          (compute-rule-method (cdr rule-pair)))
        (when clean
          (setf (module-terms-to-be-fixed module) nil
                (module-axioms-to-be-fixed module) nil))))))
|#

#|
(defun fix-rewrite-rules (module)
  (declare (type module module)
           (values t))
  (let ((res nil)
        (tobe-fixed (module-axioms-to-be-fixed module)))
    (dolist (rl (module-rewrite-rules module))
      (push (or (cdr (assq rl tobe-fixed))
                rl)
            res))
    (setf (module-rewrite-rules module)
      (nreverse res))))
|#

#|
(defun check-module-rules (module)
  (declare (type module module)
           (values t))
  (setf (module-terms-to-be-fixed module) nil)
  (setf (module-axioms-to-be-fixed module) nil)
  (dolist (rule (module-all-rules module))
    (check-axiom-error-method module rule)))
|#

(defun module-error-check (module)
  (declare (type module module)
           (values t))
  (with-in-module (module)
    ;; check sort cycles
    (maphash #'(lambda (s sl)
                 (when (memq s (_subsorts sl))
                   (with-output-chaos-warning ()
                     (princ "!! cycle in sort structure !!")
                     (print-next)
                     (format t "the sort ")
                     (print-chaos-object s)
                     (princ " is in a cycle."))))
             *current-sort-order*)))

;; *todo* must re-import iff necessary.
;;
(defun check-submodules (module)
  (declare (type module module)
           (values t))
  (dolist (mod (module-direct-submodules module))
    (compile-module (car mod))))

;;; ADD-PARAMETER-THEOREM
;;;
(defun add-parameter-theorem (mod)
  (declare (type module mod)
           (values t))
  (let ((params (get-module-imported-parameters mod)))
    (declare (type list params))
    (dolist (param params)
      (let ((pmod (parameter-theory-module param)))
        (dolist (ax (module-equations pmod))
          (pushnew (check-axiom-error-method mod ax)
                   (module-theorems mod) :test #'eq))
        (dolist (rl (module-rules pmod))
          (pushnew (check-axiom-error-method mod rl)
                   (module-theorems mod) :test #'eq))))))

;;;-----------------------------------------------------------------------------
;;; DELETING MODULES/VIEWS
;;;-----------------------------------------------------------------------------
;;; MODEXP-IS-SUBMODULE-OF : x y -> bool
;;; return non-nil iff the module denoted by a modexp `x' is a submodule
;;; of the module y.
;;; *NOTE* y must be a module expression or module object.
;;;
(defun modexp-is-submodule-of (x y)
  (declare (type t x y)
           (values (or null t)))
  (if (not (module-p y))
      (and (view-p y)
           (or ;; we also lookup in local submodules..
               ;; 
            (modexp-is-submodule-of x (eval-modexp (view-src y) t))
            (modexp-is-submodule-of x (eval-modexp (view-target y) t))))
      (or (assq x (module-submodules y))
          (let ((nm (module-name y)))
            (when (chaos-ast? nm)
              (cond ((%is-instantiation nm) (eq x (%instantiation-module nm)))
                    ((%is-rename nm) (eq x (%rename-module nm)))
                    (t nil))))
          (some #'(lambda (sm)
                    (or (eq x (car sm))
                        (modexp-is-submodule-of x (car sm))))
                (module-submodules y)))))

(defun propagate-module-change (x)
  (declare (type module x)
           (values t))
  (mark-module-as-inconsistent x)
  (when (null (module-name x))
    (return-from propagate-module-change nil))
  (let ((exobj (object-all-exporting-objects x)))
    (clean-up-sub-objects exobj))
  (delete-parameters x)
  (delete-object-from-assoc-table *modexp-eval-table* x))

(defun delete-parameters (x)
  (declare (type module x)
           (values t))
  (when *on-change-debug*
    (format t "~%** start deleting parameters ~a of module ~a"
            (module-parameters x)
            x))
  (when (null (module-name x))
    (return-from delete-parameters nil))
  ;;
  (dolist (param (module-parameters x))
    (when *on-change-debug*
      (format t "~%!! deleting parameter ~a of module ~a" param x))
    (let ((pth (parameter-theory-module param)))
      (declare (type module pth))
      (delete-object-from-assoc-table *modules-so-far-table* pth)
      (delete-object-from-assoc-table *modexp-local-table* pth)
      (delete-object-from-assoc-table *modexp-normalized-table*
                                      (module-name pth))
      (let ((subs (object-all-exporting-objects pth)))
        (clean-up-module pth)
        (clean-up-sub-objects subs)))))

(defun propagate-view-change (x)
  (declare (type view-struct x)
           (values t))
  (mark-object-as-inconsistent x)
  (when (null (view-name x))
    (return-from propagate-view-change nil))
  (let ((subs (object-all-exporting-objects x)))
    (clean-up-sub-objects subs)))

(defun clean-up-sub-objects (subs)
  (declare (type list subs)
           (values t))
  (dolist (sub subs)
    (let ((object (car sub)))
      (unless (eq (cdr sub) :using)
        (unless (object-is-inconsistent object)
          (cond ((module-p object)
                 (if (and (module-decl-form object)
                          (modexp-is-simple-name (module-name object)))
                     (progn (mark-object-as-inconsistent object)
                            (delete-parameters object))
                     (delete-module object)))
                ((view-p object)
                 (if (view-decl-form object)
                     (mark-object-as-inconsistent object)
                     (delete-view object)))
                (t (with-output-panic-message ()
                     (format t "unknown type of exporting object : ")
                     (prin1 object)
                     (chaos-error 'panic)))))))))

(defun delete-module (x)
  (declare (type module x)
           (values t))
  (when *on-change-debug*
    (format t "~%!! deleting module ")
    (print x))
  (when (null (module-name x))
    (return-from delete-module nil))
  (delete-object-from-assoc-table *modules-so-far-table* x)
  (delete-object-from-assoc-table *modexp-eval-table* x)
  (delete-parameters x)
  (clean-up-module x))

(defun delete-view (x)
  (declare (type view-struct x)
           (values t))
  (when (null (view-name x))
    (return-from delete-view nil))
  (delete-object-from-assoc-table *modexp-view-table* x)
  (clean-up-view x))

;;; EOF
