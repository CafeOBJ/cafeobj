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
                           File:refine.lisp
=============================================================================|#
#-:chaos-debug
(declaim (optimize (speed 3) (safety 0) #-GCL (debug 0)))
#+:chaos-debug
(declaim (optimize (speed 1) (safety 3) #-GCL (debug 3)))
;;; 

;;;
;;; REFINEMENT CHECKER
;;;
(defun pn-get-image-of-axioms (view)
  (declare (type view-struct view))
  (let* ((source (view-source view))
         (target (view-target view))
         (morph (convert-view-to-modmorph source
                                          view)))
    (declare (type module source target)
             (type modmorph morph))
    (let ((sort-map (modmorph-sort morph))
          (op-map (modmorph-op morph))
          (mod-map (modmorph-module morph))
          (axs nil))
      (dolist (ax (get-module-axioms source))
        (let ((ax-image (modmorph-recreate-axiom target
                                                 sort-map
                                                 op-map
                                                 mod-map
                                                 ax)))
          (push ax-image axs)))
      (nreverse axs)))
  )

(defun pn-axiom-image (ax morph target)
  (declare (type axiom ax)
           (type modmorph morph)
           (type module target))
  (let ((sort-map (modmorph-sort morph))
        (op-map (modmorph-op morph))
        (mod-map (modmorph-module morph)))
    (modmorph-recreate-axiom target
                             sort-map
                             op-map
                             mod-map
                             ax)))

(defun check-refine (view-expr)
  (let ((view (find-view-in-env (normalize-modexp view-expr)))
        (source nil)
        (morph nil)
        (target-mod nil)
        (ng-axs nil)
        (*chaos-quiet* (if (pn-flag debug-refine)
                           nil
                         t)))
    (declare (type (or null view-struct) view)
             (type (or null module) source target-mod)
             (type (or null modmorph) morph)
             (type list ng-axs))
    (unless view
      (with-output-chaos-error ('no-such-view)
        (format t "no such view \"~a\"" view-expr)))
    (setq source (view-source view))
    (setq morph (convert-view-to-modmorph source view))
    (setq target-mod (view-target view))
    ;;
    (when (pn-flag debug-refine)
      (let ((*chaos-quiet* nil))
        (with-output-simple-msg ()
          (format t "** starting refinement check with view ~a" view-expr))))
    ;;
    (dolist (im-ax (get-module-axioms source))
      (block next
        (let ((lhs (axiom-lhs im-ax)))
          (when (and (term-is-application-form? lhs)
                     (equal (method-symbol (term-head lhs))
                            (method-symbol *beh-equal*)))
            (return-from next nil)))
        (when (module-proof-system *pn-refinement-check-module*)
          (initialize-psystem (module-proof-system *pn-refinement-check-module*)
                              *pn-refinement-check-module*))
        (initialize-module *pn-refinement-check-module*)
        (import-module *pn-refinement-check-module* :protecting target-mod)
        (import-module *pn-refinement-check-module* :protecting
                       *fopl-sentence-module*)
        (compile-module *pn-refinement-check-module*)
        (with-in-module (*pn-refinement-check-module*)
          (let ((ax (pn-axiom-image im-ax morph *current-module*))
                (ax-form nil)
                (ax-cls nil)
                (psys nil)
                (flags (save-pn-flags))
                (parameters (save-pn-parameters))
                (ret-code nil)
                (*pn-no-db-reset* t))
            ;;
            (when (pn-flag debug-refine)
              (let ((*chaos-quiet* nil))
                (with-output-msg ()
                  (princ "check axiom : ")
                  (print-next)
                  (print-axiom-brief ax))))
            ;; db reset by hand
            (clear-all-index-tables)
            (reset-module-proof-system *current-module*)
            (setq psys (module-proof-system *current-module*))
            ;; negate then convert to clause form
            (setq ax-form (axiom->formula ax))
            (normalize-quantifiers ax-form)
            (setq ax-form (negate-sentence ax-form))

            (setq ax-cls (formula->clause-1 ax-form
                                            psys))
            (dolist (a ax-cls)
              (push a (psystem-axioms psys)))
            ;; invoke PigNose
            (unless (pn-flag debug-refine)
              (setf (pn-flag print-message) nil)
              (auto-change-flag quiet t)
              (auto-change-flag print-proofs nil))
            (auto-change-flag auto t)
            (auto-change-flag universal-symmetry t)
            (setf (pn-parameter max-proofs) 1)
            (setq ret-code (do-resolve *current-module*))
            ;;
            (restore-pn-flags flags)
            (restore-pn-parameters parameters)
            ;;
            (unless (eq ret-code :max-proofs-exit)
              (push im-ax ng-axs)))
          
          )))                           ; done for all axioms
    ;; 
    (if ng-axs
        (values ng-axs source target-mod)
      (values nil source target-mod))
    ))

;;; PN-CHECK-REFINEMENT : InputArgs -> Void
;;; args ::= '(view-expr)'
;;;
(defun pn-check-refinement (args)
  (declare (type list args))
  (unless *pn-refinement-check-module*
    (with-output-chaos-error ()
      (princ "prelude file fopl.mod has not been loaded yet."))
    )
  (let ((view-expr (car args)))
    (multiple-value-bind (ng? source-mod target-mod)
        (check-refine view-expr)
      (declare (ignore target-mod))
      (if ng?
          (with-in-module (source-mod)
            (with-output-simple-msg ()
              (princ "no")
              (dolist (ax ng?)
                (print-next)
                (print-axiom-brief ax))))
        (with-output-simple-msg ()
          (princ "yes"))))
    ))

;;; EOF
