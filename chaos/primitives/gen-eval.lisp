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
                                 Module: chaos
                              File: gen-eval.lisp
==============================================================================|#
#-:chaos-debug
(declaim (optimize (speed 3) (safety 0) #-GCL (debug 0)))
#+:chaos-debug
(declaim (optimize (speed 1) (safety 3) #-GCL (debug 3)))

;;; ****************************************************************************
;;;                          GENERIC AST EVALUATOR
;;; ****************************************************************************

;;;-- Generic Evaluator --------------------------------------------------------
;;; EVAL-AST : ast -> semantic_object
;;; generic evaluator of ast.
;;;-----------------------------------------------------------------------------
;;; (declaim (special *chaos-eval-context*))
;;; (defvar *chaos-eval-context* nil)
(declaim (special *dribble-ast* *ast-log*))
(defvar *dribble-ast* nil)
(defvar *dribble-stream* nil)
(defvar *ast-log* nil)
(defvar *no-log-parameter* t)
(declaim (special *eval-ast*))
(defvar *eval-ast* t)

(defun ast-to-be-dribbled? (ast)
  (and (chaos-ast? ast)
       (or (eq (ast-category ast) ':chaos-script)
           (eq (ast-type ast) '%view-decl)
           (if (eq (ast-type ast) '%module-decl)
               (or (not *no-log-parameter*)
                   (not (and (consp (%module-decl-name ast))
                             (equal "::" (cadr (%module-decl-name ast))))))
               (or *open-module*
                   nil)))))

(defun eval-ast (ast &optional (print-result nil))
  (when *dribble-ast*
    (when (ast-to-be-dribbled? ast)
      (when *dribble-stream*
        (write (list 'eval-ast-if-need `',ast) :stream *dribble-stream* :escape t)
        (terpri *dribble-stream*)
        (force-output *dribble-stream*))
      (push ast *ast-log*)))
  ;;
  (when *eval-ast*
    (cond ((chaos-ast? ast)
           (let ((evaluator (or (ast-evaluator ast)
                                (and (fboundp (car ast))
                                     (symbol-function (car ast))))))
             (cond (evaluator
                    (let ((module (get-context-module t)))
                      (when (and module (not (module-p module)))
                        (setq module (find-module-in-env
                                      (normalize-modexp (string module)))))
                      (if module
                          (if (null *current-module*)
                              (with-in-module (module)
                                (prog1 (funcall evaluator ast)
                                  ;; (deallocate-ast ast)
                                  ))
                              (prog1 (funcall evaluator ast)
                                ))
                          ;; may cause panic.
                        (return-from eval-ast (funcall evaluator ast)))))
                   (t (let ((val (eval-modexp ast)))
                        (if (modexp-is-error val)
                            (with-output-chaos-warning ()
                              (format t  "AST evaluator accepted an ast ~s with no evaluator specified."
                                      (print-ast ast))
                              (return-from eval-ast ast))) ; returns the ast as is.
                        )))))
          (t ;; evaluate it as lisp form
           (cond ((symbolp ast)
                  (unless (boundp ast)
                    (format t "~%symbol ~s has no bound value." ast)
                    (return-from eval-ast nil)))
                 ((listp ast)
                  (unless (symbolp (car ast))
                    (format t "~%invalid function application form: ~a" ast)
                    (return-from eval-ast nil))
                  (unless (fboundp (car ast))
                    (format t "~%symbol ~s has no function definition." (car ast))
                    (return-from eval-ast nil))))
           ;;
           (let ((res (eval ast)))
             (when print-result
               (format t "~%~s" res))
             (return-from eval-ast res))))))

(defun eval-seq (seq)
  (mapcar #'(lambda (obj) (eval-ast obj))
          (%seq-args seq)))

(defun eval-ast2 (ast)
  (eval-ast ast)
  )

;;; EOF
