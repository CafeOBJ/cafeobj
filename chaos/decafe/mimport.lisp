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
                                 System: CHAOS
                                 Module: deCafe
                               File: mimport.lisp
==============================================================================|#
#-:chaos-debug
(declaim (optimize (speed 3) (safety 0) #-GCL (debug 0)))
#+:chaos-debug
(declaim (optimize (speed 1) (safety 3) #-GCL (debug 3)))

;;;*****************************************************************************
;;;********************* MODULE IMPORTATION WORK HORSES ************************
;;;*****************************************************************************

;;;=== DESCRIPTION =============================================================
;;; All of the internal processes of module importation.
;;;

;;; ***********
;;; IMPORTATION__________________________________________________________________
;;; ************

;;; IMPORT-MODULE : MODULE MODE SUBMODULE &optional PARAMETER -> MODULE'
;;; The top proc for module importation:
;;; imports `submodule' to `module' with mode `mode'.
;;; 
;;; - MODULE, SUBMODULE : module expression or module object.
;;; - MODE : one of :protecting, :extending, :using, or :including.
;;; - PARAMETER : if specified, submodule should be imported as a parameter theory
;;; of the module. in this case, it must be a name (string) of the formal argument.
;;;
;;; mainly used by `eval-import-modexp' the evaluator of module importation ast.
;;;
;;; (defvar *on-import-debug* nil)

(defvar *import-sort-map* nil)

(defun import-module (im mode sub &optional parameter alias)
  (let ((*auto-context-change* nil))
    (setq *import-sort-map* nil)
    (prog1
        (import-module-internal im mode sub parameter nil alias)
      (setq *import-sort-map* nil))))

(defun import-module-internal (im mode sub &optional parameter theory-mod alias)
  (when *on-import-debug*
    (format t "~%[import-module]: ")
    (print-next)
    (princ " ") (print-modexp im)
    (format t " <==(~a)== " mode)
    (print-modexp sub)
    (if parameter (format t " : ~a" parameter)))
  ;;
  (flet ((eval-modexp-or-error (modexp)
           (let (val)
             (if (module-p modexp)
                 (setf val modexp)
                 (progn
                   (setf val (eval-modexp modexp)) ; must be global
                   (when (modexp-is-error val)
                     (with-output-chaos-error ('modexp-eval)
                       (princ "importing module, cannot evaluate module expression ")
                       (print-modexp modexp)
                       ))))
             val))
         (is-directly-using (mod1 mod2)
           ;; IS-DIRECTLY-USING : Module-1 Module-2 -> Bool
           ;; returns t iff the module-1 imports module-2 directly.
           ;; `directly' means that some own constructs of Module-2 (sors and
           ;; operators declared in Module-2) are included in Module-1's
           ;; constructs, i.e., Module-2 is a node of a module hierarchy with
           ;; Module-1 at top. 
           (or  (some #'(lambda (x) (eq mod2 (sort-module x)))
                      (module-all-sorts mod1))
                (some #'(lambda (x)
                          (eq mod2 (operator-module (opinfo-operator x))))
                      (module-all-operators mod1))))
         (create-variant-name (parent mod)
           ;; CREATE-VARIANT-NAME
           ;; variant name ::= (:name <module name> <natural>)
           ;; We carete a brand new module when imported module refers some
           ;; soncstructs of importing module. this can happen when we import an
           ;; instantiated module with an actual parameter includes some sorts
           ;; or operators of importing module in its module morphism. In such
           ;; case, we create a module with the same name of importing module,
           ;; then importing module is changed its name to `variant-name'. The
           ;; newly created module, then imports this module. 
           (let ((modname (module-name parent))
                 (num -1))
             (declare (type fixnum num))
             (dolist (sm (module-submodules mod))
               (when (eq :protecting (cdr sm))
                 (let ((smnm (module-name (car sm))))
                   (when (and (consp smnm)
                              (eq :name (car smnm))
                              (eq (cadr smnm) modname) ; by construction works
                              (< num (the fixnum (caddr smnm))))
                     (setq num (caddr smnm))))))
             `(:name ,modname ,(1+ (the fixnum num)))
             )))
    ;;
    (let ((module (eval-modexp-or-error im))
          (submodule (eval-modexp-or-error sub)))
      (unless (and (module-p module) (module-p submodule))
        ;; (break)
        (return-from import-module-internal nil))
      (when (eq module submodule)
        (with-output-chaos-error ('invalid-import)
          (princ "module cannot import itself!")))

      ;; compile submodule if need
      (compile-module submodule)
      ;; alias
      (when alias
        (symbol-table-add (module-symbol-table module)
                          alias
                          submodule))
      ;; 
      (dolist (al (module-alias submodule))
        (let ((mod (car al))
              (nm (cdr al)))
          (add-module-alias module mod nm)))
      ;;
      (with-in-module (module)
        (if parameter
            ;; PARAMETERIZED MODULE IMPORTATION.
            ;; We carete a new module with name `(formal-name "::" module-object)'
            ;; where, formal-name is the name of formal parameter name (we get
            ;; this as the argument param), module-object is the object of
            ;; submodule to be imported as parameter theory.
            ;; The `parameters' module will be updated to including this
            ;; importation, each entry is is the form of
            ;;    `((formal-name . parameter-module) . mode)
            (let ((true-name (list parameter "::" submodule module))
                  (*include-bool* (if (memq *bool-sort* (module-all-sorts submodule))
                                      t
                                      nil)))
              (let ((param-mod (create-renamed-module-2 submodule true-name module)))
                ;; register it to local environment.
                (add-modexp-local-defn (list parameter (module-name module))
                                       param-mod)
                (push (cons (cons parameter param-mod) mode)
                      (module-parameters module))
                (import-module-internal module mode param-mod)
                ))
            ;;
            ;; NON PARAMETERIZED MODULE IMPORTATION.
            ;;
            (if (or (eq :using mode)
                    (not (is-directly-using submodule *current-module*)))
                (let* ((subs (module-all-submodules module))
                       (val (assq submodule subs)))
                  (when val
                    (let ((real-mode (get-real-importing-mode submodule module)))
                      (if (and  *check-import-mode*
                                (not (or (eq real-mode :using)
                                         (eq (cdr val) :using)))
                                (not (eq mode real-mode)))
                          (with-output-chaos-error ('import-error)
                            (format t "module ~a is already imported into ~a"
                                    (make-module-print-name submodule)
                                    (make-module-print-name module))
                            (print-next)
                            (format t "with the effective mode : ~a," real-mode)
                            (print-next)
                            (format t "this conflicts to the new mode : ~a." mode)
                            )
                          ;; we omit this importation
                          (progn
                            (when *on-import-debug*
                              (format t "~%module is already imported, skipping.."))
                            (return-from import-module-internal t)))))
                  (when *check-import-mode*
                    ;; other more complex importation check.
                    ;; checks confliction among shared submodules.
                    (let ((s-subs (mapcar #'car
                                          (module-all-submodules submodule))))
                      (dolist (ms subs)
                        (when (memq (car ms) s-subs)
                          (let ((m1 (get-real-importing-mode (car ms) module))
                                (m2 (get-real-importing-mode (car ms) submodule)))
                            (unless (eq m1 m2)
                              (if (or (memq m1 '(:?extending :extending))
                                      (memq m2 '(:?extending :extending)))
                                  ;;
                                  nil   ; do nothing now
                                  (when (not (or (eq m1 :using)
                                                 (eq m2 :using)))
                                    (with-output-chaos-error ('import-error)
                                      (format t "confliction in importation mode of common submodule ~a"
                                              (get-module-print-name (car ms)))
                                      (print-next)
                                      (format t "module ~a already imports with effective mode ~a,"
                                              (get-module-print-name module)
                                              m1)
                                      (print-next)
                                      (format t "module ~a imports with effective mode ~a."
                                              (get-module-print-name submodule)
                                              m2)
                                      )))))))))
                
                  ;; `incorporate-module' do the real importation.
                  (incorporate-module module mode submodule theory-mod)

                  ;; imported modules are stored at `module-submodules' in a form
                  ;; (<module> <mode>), <mode> is one of :protecting, :extending,
                  ;; :using, and :including.
                  (add-imported-module module mode submodule alias)
                  ;;
                  module)
              
                ;; MUTUALLY RECURSIVE CASE.
                ;; imported module refers some constructs of importing module.
                ;; current-module --> variant
                ;; 
                (let ((newmod (make-module :name (module-name module)))
                      (modname (module-name module))
                      (submod module))
                  (initialize-module newmod)
                  (setf (module-parameters newmod)
                        (module-parameters module))
                  (setf *current-module* newmod)
                  (setf *current-sort-order* (module-sort-order newmod))
                  (setf *current-opinfo-table* (module-opinfo-table newmod))
                  (let ((subname (create-variant-name newmod submod)))
                    (setf (module-name submod) subname)
                    ;; (add-canon-modexp subname subname)
                    ;; (modexp-update-name subname submod)
                    )
                  (final-setup submod)
                  (add-modexp-defn modname newmod)
                  (add-imported-module newmod :protecting submod)
                  (incorporate-module newmod :protecting submod)
                  (add-imported-module newmod mode submodule)
                  (incorporate-module newmod mode submodule)
                  (dolist (par (module-parameters newmod))
                    (add-imported-module newmod (cdr par)(cdar par))
                    (incorporate-module newmod (cdr par) (cdar par)))
                  (unless *chaos-quiet* (princ ")" *error-output*))
                  newmod)))))))

;;; INCORPORATE-MODULE : Module Mode SubModule -> Module'
;;; Do the importation.
;;; Module & SubModule must be a module object (i.e.,evaluated modexp).
;;;
(declaim (special *import-local-vars*))
(defvar *import-local-vars* nil)
(declaim (special *import-use-decl-form*))
(defvar *import-use-decl-form* nil)

(defun incorporate-module (module mode submodule &optional theory-mod)
  (if (memq mode '(:protecting :extending :including))
      (prog1 (incorporate-module-sharing module submodule theory-mod)
        (when (eq mode :including)
          (when (and (module-psort-declaration submodule)
                     (null (module-psort-declaration module)))
            (setf (module-psort-declaration module)
                  (copy-tree (module-psort-declaration submodule))))))
      (incorporate-module-copying module submodule nil theory-mod)))

(defun incorporate-module-sharing (module submodule &optional theory-mod)
  (let ((*import-local-vars* nil))
    (with-in-module (module)
      ;;
      ;; *NOTE* : the follwing code is executed in the context of given `module' 
      ;;          = *current-module*.
      ;;-----------------------------------------------
      ;; import sorts
      (dolist (s (reverse (module-all-sorts submodule)))
        ;; we imports only sorts user declared.
        (unless (sort-is-for-regularity? s submodule)
          (add-sort-to-module s module)))
      ;; import error-sorts
      (dolist (s (module-error-sorts submodule))
        (pushnew s (module-error-sorts module) :test #'eq))
      ;; import sort relations
      (let ((so (module-sort-order module)))
        (dolist (sl (module-sort-relations submodule))
          (let ((new-sl (elim-sys-sorts-from-relation sl)))
            (when new-sl
              (adjoin-sort-relation new-sl module)
              (add-relation-to-order new-sl so)))))
      ;; at this point, we want 
      ;; import operators + axioms.
      (setf (module-methods-with-rwl-axiom module)
            (delete-duplicates (append (module-methods-with-rwl-axiom module)
                                       (module-methods-with-rwl-axiom
                                        submodule))
                               :test #'eq))
      (setf (module-rules-with-rwl-axiom module)
            (delete-duplicates (append (module-rules-with-rwl-axiom module)
                                       (module-rules-with-rwl-axiom submodule))
                               :test #'eq))
      (let ((opinfos (module-all-operators submodule)))
        (dolist (opinfo opinfos)
          (transfer-operator module submodule opinfo nil theory-mod)))
      ;; import error operators which might be reused.
      ;; (dolist (em (module-error-methods submodule))
      ;; (when (method-is-user-defined-error-method em)
      ;;   (pushnew em (module-error-methods module) :test #'eq)))
      (dolist (em (module-error-methods submodule))
          (pushnew em (module-error-methods module) :test #'eq))
      ;; import macros
      (dolist (macro (module-macros submodule))
        (add-macro-to-module module macro))
      ;;
      ;; all done, anyway ...
      )))

;;; import module copying
(defun incorporate-module-copying (module submodule
                                   &optional
                                   copy-parameters
                                   theory-module
                                   (context-module *current-module*))
  (let ((*import-local-vars* nil)
        (imported-params nil))
    (labels ((import-recreate-sort (s)
               (%copy-sort s module nil t))
             (using-recreate-sort-if-need (sort_)
               (if (and (eq (sort-module sort_) submodule)
                        (not (member sort_
                                     (module-sorts-for-regularity submodule))))
                   (or (cdr (assq sort_ *import-sort-map*))
                       (let ((news (import-recreate-sort sort_)))
                         (when *on-import-debug*
                           (format t "~%[copy] putting ~a to *import-sort-map*"
                                   (cons sort_ news)))
                         (push (cons sort_ news) *import-sort-map*)
                         news))
                 sort_))

             (using-find-sort (_sort)
               (or (cdr (assq _sort *import-sort-map*)) _sort))

             (using-import-var (var)
               (let ((nm (variable-name var))
                     (sort (using-find-sort (variable-sort var))))
                 (let ((val (find-variable-in module nm)))
                   (if (and val (not (sort= sort (variable-sort val))))
                       (with-output-chaos-warning ()
                         (princ "imported variable discarded due to name conflict")
                         (print-next)
                         (format t "with the existing variable: ~a" nm))
                     (unless val
                       (setq val (make-variable-term sort nm))
                       (when *copy-variables*
                         (push (cons nm val) (module-variables module)))
                       (push (cons nm val) *import-local-vars*))))))
             ;;
             (using-find-sort-err (s)
               (let ((sort (cdr (assq s *import-sort-map*))))
                 (cond (sort sort)
                       ((err-sort-p s)
                        (setq sort
                          (find-compatible-err-sort s module
                                                    *import-sort-map*))
                        (if sort
                            (progn
                              (when *on-import-debug*
                                (format t "~%-- adding import sort map: ~a"
                                        (cons s sort)))
                              (push (cons s sort) *import-sort-map*)
                              sort)
                          (with-output-panic-message ()
                            (format t "could not find compatible error sort of ~a"
                                    s))))
                       (t s))))
             ;;
             (using-recreate-term (term)
               (cond ((term-is-builtin-constant? term) 
                      (make-bconst-term (using-find-sort-err (term-sort term))
                                        (term-builtin-value term)))
                     ((term-is-variable? term)
                      (let ((var-name (variable-name term))
                            (new-sort (using-find-sort-err (variable-sort term))))
                        (let ((val2 (assq var-name *import-local-vars*)))
                          (if (and val2 (sort= new-sort
                                               (variable-sort (cdr val2))))
                              (cdr val2)
                            (let ((new-var (make-variable-term
                                            new-sort var-name)))
                              (push (cons var-name new-var)
                                    *import-local-vars*)
                              new-var)))))
                     ((term-is-lisp-form? term) term)
                     (t (let ((head (term-head term)))
                          (let ((new-head
                                 (find-method-in
                                  module
                                  (method-symbol head)
                                  (mapcar #'(lambda (x)
                                              (using-find-sort-err x))
                                           (method-arity head))
                                  (using-find-sort-err 
                                   (method-coarity head)))))
                            (when (null new-head)
                              (when *on-import-debug*
                                (format t "~%!! recreate-term null new-head~%")
                                (with-in-module (module)
                                  (print-chaos-object head)
                                  (format t "~% arity = ~a" (method-arity head))
                                  (format t "~% coarity = ~a"
                                          (method-coarity head))))
                              (setq new-head head))
                            (make-applform (method-coarity new-head)
                                           new-head
                                           (mapcar #'(lambda (tm)
                                                       (using-recreate-term tm))
                                                    (term-subterms term))))))))
             #|| not used now
             (using-recreate-axiom (axiom)
             (when *on-import-debug*
             (princ "[using-recreate-axiom]")
             (with-in-module (submodule)
             (print-axiom-brief axiom)))
             (make-rule :lhs (using-recreate-term (axiom-lhs axiom))
             :rhs (using-recreate-term (axiom-rhs axiom))
             :condition (if (is-true? (axiom-condition axiom))
             *bool-true*
             (using-recreate-term (axiom-condition axiom)))
             :labels (axiom-labels axiom)
             :type (axiom-type axiom)
             :behavioural (axiom-is-behavioural axiom)
             :kind (axiom-kind axiom)
             :non-exec (axiom-non-exec axiom)
             :meta-and-or (axiom-meta-and-or axiom)))
             ||#
             (using-import-sub (s mode)
               (let ((subs (module-all-submodules module)))
                 (unless (assq s subs)
                   (if (module-is-parameter-theory s)
                       (let ((param-mod s)
                             (arg-name (car (module-name s))))
                         (push param-mod imported-params)
                         (if (and copy-parameters
                                  (not (eq (fourth (module-name s))
                                           context-module)))
                             (import-module-internal module
                                                     mode
                                                     param-mod
                                                     arg-name
                                                     module)
                           (progn
                             (import-module-internal module
                                                     mode
                                                     param-mod
                                                     nil
                                                     (or theory-module
                                                         submodule))
                             (add-modexp-local-defn (list arg-name
                                                          (module-name module))
                                                    param-mod)
                             (push (cons (cons arg-name param-mod) mode)
                                   (module-parameters module)))))
                     (if (eq mode :using)
                         (using-import-subs s)
                       (import-module-internal module
                                               mode
                                               s
                                               nil
                                               (or theory-module submodule)))))))
             (using-import-subs (smod)
               (dolist (s (reverse (module-direct-submodules smod)))
                 (using-import-sub (car s) (cdr s))))
             )                          ; end labels
      ;;
      (with-in-module (module)
        ;; *NOTE* : the follwing code is executed in the context of given
        ;; `module' = *current-module*.
        ;;
        ;; import submodules of submodule
        ;;
        (using-import-subs submodule)
        ;;
        ;; import sorts of submodule recreating
        ;;
        (dolist (s (reverse (module-sorts submodule)))
                                        ; sorts of sub-sumodules should already be
                                        ; imported at this point.
          (let ((new-sort (using-recreate-sort-if-need s)))
                                        ; thus, `if-need' is redundant though..
            (when new-sort
              (add-sort-to-module new-sort module))))
        ;;
        ;; reconstruct sort relations
        ;;
        (let ((so (module-sort-order module)))
          (dolist (rel (module-sort-relations submodule))
            (let* ((new-rel (elim-sys-sorts-from-relation rel))
                   (xnew-rel (when new-rel
                               (make-sort-relation
                                (using-find-sort (sort-relation-sort new-rel))
                                (mapcar #'(lambda (x) (using-find-sort x))
                                         (_subsorts new-rel))
                                (mapcar #'(lambda (x) (using-find-sort x))
                                         (_supersorts new-rel))))))
              (when xnew-rel
                (adjoin-sort-relation xnew-rel module))
              (add-relation-to-order xnew-rel so)))
          (generate-err-sorts so))
        ;;
        ;; import operators(methods) copying
        ;;
        (let ((m-so-far nil))
          (dolist (opinfo (reverse (module-all-operators submodule)))
                                        ; again, operators(methods) of
                                        ; sub-submodules already be imported at
                                        ; this point.
                                        ; BUT, operator object is not created
                                        ; iff strictly overloaded. thus we must
                                        ; check ALL operators.
            (let ((op-symbol (operator-symbol (opinfo-operator opinfo))))
              (dolist (meth (opinfo-methods opinfo))
                (when (eq submodule (method-module meth))
                  (when (or (method-is-user-defined-error-method meth)
                            (and (not (method-is-error-method meth))
                                 (not (method-is-user-defined-error-method meth))
                                 (not (memq meth
                                            (module-methods-for-regularity
                                             submodule)))))
                    (let* ((new-arity (mapcar #'(lambda (x)
                                                  (using-find-sort-err x))
                                               (method-arity meth)))
                           (new-coarity (using-find-sort-err
                                         (method-coarity meth)))
                           (new-meth nil))
                      (when *on-import-debug*
                        (format t "~%* trying to make new method ~a:" op-symbol)
                        (format t "~%  arity = ~a" new-arity)
                        (format t "~%  coarity = ~a" new-coarity))
                      (setq new-meth (recreate-method submodule
                                                      meth
                                                      module
                                                      op-symbol
                                                      new-arity
                                                      new-coarity
                                                      *import-sort-map*))
                      (push (cons meth new-meth) m-so-far)
                      (when *on-import-debug*
                        (format t "~%* created method ~a: " new-meth)
                        (print-chaos-object new-meth))))))))

          ;; check identity in theory
          (dolist (om-nm m-so-far)
            (let ((meth (car om-nm))
                  (new-meth (cdr om-nm)))
              (let ((theory (method-theory meth (module-opinfo-table submodule))))
                (when (theory-contains-identity theory)
                  (let ((zero (theory-zero theory)))
                    (setq zero (cons (using-recreate-term (car zero))
                                     (cdr zero)))
                    (setf (method-theory new-meth)
                      (theory-make (theory-info theory) zero))
                    (compute-method-theory-info-for-matching new-meth)))))))
        ;;
        ;; vertually import variables copying
        ;;
        (dolist (v (nreverse (mapcar #'cdr (module-variables submodule))))
          (using-import-var v))

        ;;
        ;; inherit principal-sort if defined.
        ;;
        (when (and (module-psort-declaration submodule)
                   (null (module-psort-declaration module)))
          (setf (module-psort-declaration module)
            (copy-tree (module-psort-declaration submodule))))
        ;;
        ;; import error operator declarations
        ;; the evaluation will be delayed
        (dolist (eop (module-error-op-decl submodule))
          (when *on-import-debug*
            (with-output-msg ()
              (format t "* importing err op decl:")
              (print-next) (princ "  ")
              (print-chaos-object eop)))
          (pushnew eop (module-error-op-decl module) :test #'equal))
        
        ;;
        ;; copy macros
        ;;
        (dolist (macro (module-macros submodule))
          (let ((new-macro (make-macro :lhs (using-recreate-term (macro-lhs macro))
                                       :rhs (using-recreate-term (macro-rhs macro)))))
            (add-macro-to-module module new-macro)))
        ;;
        ;; copy let bindings
        ;;
        (setf (module-bindings module) (copy-tree (module-bindings submodule))
              (module-special-bindings module)
              (copy-tree (module-special-bindings submodule)))

        ;;
        ;; import equations & rules copying
        ;;
        (prepare-for-parsing module nil t)

        ;; in this stage, error sorts & methods are all available,
        ;; but we must delay the axiom importation
        ;; because there can happen reorganizing operators in different ways
        (dolist (e (reverse (module-equations submodule)))
          (unless (axiom-kind e)
            (delay-axiom-importation module e submodule)))
        
        (dolist (r (reverse (module-rules submodule)))
          (unless (axiom-kind r)
            (delay-axiom-importation module r submodule)))
        ;;
        ;; all done, hopefully
        ;;
        ))))

;;; TRANSFER-OPERATOR : Module Module OpInfo -> Void
;;;
(defun transfer-operator (module from-module opinfo &optional (given-opinfos nil)
                                 theory-mod)
  (let* ((opinfos given-opinfos)
         (from-op (opinfo-operator opinfo))
         (proto-method (car (opinfo-methods opinfo)))
         (a-len (length (method-arity proto-method)))
         (new-op nil)
         (new-opinfo nil))
    ;;
    (when *on-import-debug*
      (format t "~&[transfer-operator]: ~a from " (operator-symbol from-op))
      (print-modexp from-module)
      (format t " to ")
      (print-modexp module))
    ;;
    (unless opinfos
      (setq opinfos (find-operators-in-module (operator-symbol from-op)
                                              a-len
                                              module)))
    ;;
    (with-in-module (module)
      (let ((so (module-sort-order module)))
        ;; find the method group to be inserted
        (dolist (method (opinfo-methods opinfo))
          (when (and (not (method-is-error-method method))
                     (not (method-is-for-regularity? method from-module)))
            (setq new-opinfo
                  (dolist (x opinfos nil)
                    (when (or (null (method-arity method))
                              (is-in-same-connected-component*
                               (method-coarity method) 
                               (method-coarity (or (cadr (opinfo-methods x))
                                                   (car (opinfo-methods x))))
                               so))
                      (return x))))
            (return nil)))
        ;; create new operaotr info if could not find.
        (cond (new-opinfo
               (setq new-op (opinfo-operator new-opinfo)))
              (t
               (when *on-import-debug*
                 (format t "~%* creating new opinfo for operator ~s : "
                         (opinfo-operator opinfo))
                 (print-chaos-object (opinfo-operator opinfo)))
               ;;
               (setq new-op (opinfo-operator opinfo))
               (setq new-opinfo
                     (make-opinfo :operator new-op))
               (push new-opinfo (module-all-operators module))
               (push new-opinfo opinfos)))
        ;; add to symbol table : 2012/07/15
        (symbol-table-add (module-symbol-table module) (first (operator-name new-op)) new-op)
        ;;
        (dolist (method (reverse (opinfo-methods opinfo)))
          ;;
          (when (or (method-is-user-defined-error-method method)
                    (and (not (method-is-error-method method))
                         (not (method-is-for-regularity? method from-module))))
            (when *on-import-debug*
              (format t "~%-- importing method ~s : " method)
              (print-chaos-object method))
            ;; adding to 
            (modexp-add-method-to-table new-opinfo method module)
            ;; import attributes
            (transfer-operator-attributes method module from-module theory-mod)
            ;; import axioms
            (import-operator-axioms module method from-module)))
        (when *on-import-debug*
          (format t "~%* done transfer-operator"))))))

(defun import-operator-axioms (module method from-module)
  (let ((from-opinfo (module-opinfo-table from-module)))
    (dolist (rule (rule-ring-to-list
                   (method-rules-with-same-top method from-opinfo)))
      (import-an-axiom module rule method from-module))
    (dolist (rule (reverse (method-rules-with-different-top method
                                                            from-opinfo)))
      (import-an-axiom module rule method from-module))))

;;; delay-axiom-importation
;;; if an axiom contains error operator, 
;;; we must delay importation after all error operator is generated
;;; 
(defun delay-axiom-importation (module axiom from-module)
  (let ((ast (parse-module-element-1 (cafeobj-parse-from-string (axiom-declaration-string axiom from-module)))))
    (pushnew (change-axiom-decl-to-now ast)
             (module-delayed-declarations module)
             :test #'equal)))

(defun import-an-axiom (module rule method from-module)
  (when (eq method (term-head (axiom-lhs rule)))
    (if (axiom-contains-error-method rule)
        (progn
          (when *on-import-debug*
            (with-in-module (from-module)
              (format t "~%-- delaying importing axiom ")
              (print-chaos-object rule)))
          (delay-axiom-importation module rule from-module))
      (progn
        (when *on-import-debug*
          (with-in-module (from-module)
            (format t "~%-- importing axiom ")
            (print-chaos-object rule)
            (format t "~%   for method : ")
            (print-chaos-object method)))
        (add-rule-to-method rule
                            method
                            (module-opinfo-table module))
        (pushnew rule (module-all-rules module) :test #'rule-is-similar?)))))

(defun modexp-add-method-to-table (opinfo method module)
  (let ((pmeth (find method (opinfo-methods opinfo)
                     :test #'(lambda (x y)
                               (and (sort-list= (method-arity x)
                                                (method-arity y))
                                    (sort= (method-coarity x)
                                           (method-coarity y))))))
        (method-info-table (module-opinfo-table module)))
    (if (eq pmeth method)
        nil
      (progn
        (setf (get-method-info method method-info-table)
          (make-method-info method
                            module
                            (opinfo-operator opinfo)))
        (pushnew method (opinfo-methods opinfo))
        (setf (opinfo-method-table opinfo) nil)
        (when (method-is-behavioural method)
          (if (sort-is-hidden (method-coarity method))
              (pushnew method (module-beh-methods module))
            (pushnew method (module-beh-attributes module))))
        t))))

(defun transfer-operator-attributes (method to-module from-module
                                            &optional theory-mod)
  ;; transfer operator theory
  (transfer-operator-theory method to-module from-module theory-mod)
  ;; transfer other attributes
  (transfer-operator-attrs method to-module from-module theory-mod))

(defun transfer-operator-theory (method to-module from-module
                                        &optional theory-mod)
  (let ((new-theory (modexp-merge-operator-theory method
                                                  to-module
                                                  from-module
                                                  theory-mod)))
    (when new-theory
      (setf (method-theory method (module-opinfo-table to-module))
            new-theory)
      (compute-method-theory-info-for-matching method
                                               (module-opinfo-table to-module)))))

(defun modexp-merge-operator-theory (method to-module from-module
                                            &optional theory-mod)
  (let* ((to-opinfo (module-opinfo-table to-module))
         (th1 (method-theory method to-opinfo))
         (from-opinfo (if theory-mod
                          (module-opinfo-table theory-mod)
                          (module-opinfo-table from-module)))
         (th2 (method-theory method from-opinfo)))
    (merge-operator-theory-in to-module method th1 th2)))

(defun transfer-operator-attrs (meth to-module from-module &optional theory-mod)
  (declare (ignore theory-mod))
  (let ((coh nil)
        (meta-demod nil))
    (with-in-module (from-module)
      (setq coh (method-is-coherent meth))
      (setq meta-demod (method-is-meta-demod meth)))
    (with-in-module (to-module)
      (setf (method-is-coherent meth) coh)
      (setf (method-is-meta-demod meth) meta-demod))))

;;; *****************************************
;;; AUTOMATIC IMPORATION OF BUILT-IN MODULES.___________________________________
;;; *****************************************
;;; conditionally automatically include BOOL/OBJECT/RECORD-STRUCTURE
;;;

(defparameter *import-bool-ast*
  (%import* :protecting (%modexp* "BOOL")))
(defparameter *import-hard-wired-ast*
  (%import* :protecting (%modexp* "CHAOS:PARSER")))

(defun include-chaos-module (&optional (module *current-module*))
  (unless (memq *syntax-err-sort* (module-all-sorts module))
    (with-in-module (module)
      (eval-import-modexp *import-hard-wired-ast*))))

(defun include-BOOL (&optional (module *current-module*))
  (when *include-BOOL*
    (unless (assq *bool-module*
                  (module-all-submodules module))
      (with-in-module (module)
        (eval-import-modexp *import-bool-ast*))))
  (include-chaos-module))

(defparameter *import-object-ast*
  (%import* :extending (%modexp* "OBJECT")))

(defun include-object ()
  (unless (memq *class-id-sort*
                (module-all-sorts *current-module*))
    (eval-import-modexp *import-object-ast*)))

(defparameter *import-record-ast*
  (%import* :extending (%modexp* "RECORD-STRUCTURE")))

(defun include-record ()
  (unless (memq *record-id-sort*
                (module-all-sorts *current-module*))
    (eval-import-modexp *import-record-ast*)))

(defparameter *import-rwl-ast*
  (%import* :protecting (%modexp* "RWL")))

(defun include-rwl (&optional (module (get-context-module)))
  (when *include-rwl*
    (unless (module-includes-rwl module)
      (with-in-module (module)
        (eval-import-modexp *import-rwl-ast*)))))

;;;
;;; IMPORT-VARIABLES
;;;
(defun import-variables (from to)
  (let ((vs (module-variables from)))
    (dolist (v vs)
      (let ((s (find-sort-in to (sort-id (variable-sort v))))
            (name (variable-name v)))
        (if s
            (push (cons name (make-variable-term s name))
                  (module-variables to))
            (with-output-chaos-warning ()
              (format t "importing variable ~a, could not find sort ~a"
                      name
                      (sort-id (variable-sort v)))))))))

;;; EOF
