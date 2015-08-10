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
                                  Module: eval
                              File: chaos-top.lisp
==============================================================================|#

;;; == DESCRIPTION =============================================================
;;; Chaos toplevel.
;;;
;;;
;;;
(defun define-builtin-module (mod-name)
  (let ((name (normalize-modexp mod-name)))
    (let ((mod (create-module name)))
      (setf (module-type mod) :hard)
      (setf (module-kind mod) :object)
      (setf (module-hidden mod) t)
      (add-modexp-defn name mod)
      mod)))

;;; GLOBAL DB INITIALIZATION
(defun clear-global-db ()
  (setq *modules-so-far-table* nil)
  (setq *modexp-local-table* nil)
  (setq *modexp-view-table* nil)
  (setq *modexp-eval-table* nil)
  ;; (clear-all-sorts)
  (clear-builtin-sorts))

;;;

(defvar *chaos-new* t)

#+GCL
(defun save-chaos (top &optional (path "./bin/chaos.exe"))
  (setq *chaos-new* t)
  (when top
    (defun system::top-level () (funcall top))
    (si::set-up-top-level)
    ;; (setf (symbol-function 'si::top-level) (symbol-function top))
    )
  (system::save-system path)
  (bye))

#+CMU
(defun save-chaos (top &optional (path "bin/chaos.core"))
  (setq *chaos-new* t)
  (ext:gc)
  (ext:purify)
  (ext:gc)
  (if top
      (ext:save-lisp path
                     :purify nil
                     :init-function top
                     :print-herald nil
                     )
      (ext:save-lisp path
                     :purify nil
                     :print-herald nil)))

#+LUCID
(defun save-chaos (top &optional (path "bin/chaos.exe"))
  (setq *chaos-new* t)
  (if top
      (disksave path
                :full-gc t
                :restart-function top)
      (disksave path
                :full-gc t)))

#+:ccl
(defun save-chaos (top &optional (path "chaos"))
  (setq *chaos-new* t)
  (if top
      (save-application path :toplevel-function top
                        :size '(6144000 4196000))
      (save-application path 
                        :size '(6144000 4196000))))
#+:ALLEGRO
(defun save-chaos (top &optional (path "aobj"))
  (setq *chaos-new* t)
  (setq excl:*restart-app-function* top)
  (setq excl:*print-startup-message* nil)
  (setq excl::.dump-lisp-suppress-allegro-cl-banner. t)
  (dumplisp :name path :suppress-allegro-cl-banner t))

#+:CLISP
(defun save-chaos (top &optional (path "chaos"))
  (setq *chaos-new* t)
  (in-package :chaos)
  (if top
      (ext:saveinitmem path :quiet t :init-function top)
    (ext:saveinitmem path :quiet t)))

#+SBCL
(defun save-chaos (top &optional (path "chaos.sbcl"))
  (declare (ignore top))
  (setq *chaos-new* t)
  (sb-ext:save-lisp-and-die path
                            :toplevel 'chaos::cafeobj-top-level
                            :purify t
                            :executable t
                            :save-runtime-options t))

;;; PROCESS-CHAOS-INPUT
;;;
(defun chaos-prompt (&optional (stream *error-output*))
  (let ((*standard-output* stream))
    (fresh-all)
    (flush-all)
    (format t "~%[")
    (if (get-context-module t)
        (print-simple-mod-name (get-context-module))
      (princ "*"))
    (princ "]> ")))

(defun handle-chaos-error (val)
  (if *chaos-input-source*
      (chaos-error val)
      val))

(defun handle-chaos-top-error (val)
  (if *chaos-input-source*
      (chaos-to-top val)
      val))

(defun chaos-read (&optional (stream *standard-input*))
  (let ((inp (read stream nil :eof nil)))
    (when (memq inp '(:eof eof quit :quit :q q))
      (return-from chaos-read :quit))
    inp))

(defun chaos-eval-reader (stream char)
  (declare (ignore char))
  (let ((obj (read stream nil :eof t)))
    (if (eq obj :eof)
        (values)
      (eval-ast obj))))
  
(defun process-chaos-input ()
  (let ((*print-array* nil)
        (*print-circle* nil)
        (*old-context* nil)
        (*show-mode* :chaos)
        (top-level (at-top-level)))
    (unless (or top-level *chaos-quiet*)
      (if *chaos-input-source*
          (with-output-simple-msg ()
            (format t "rocessing input : ~a~%" (namestring *chaos-input-source*)))
          (with-output-simple-msg ()
            (format t "processing input .......................~%")))
      )
    (let ((ast nil)
          (*readtable* (copy-readtable)))
      ;; (declare (special *readtable*))
      (set-macro-character #\! #'chaos-eval-reader)
      (block top-loop
        (loop
          (with-chaos-top-error ('handle-chaos-top-error)
            (with-chaos-error ('handle-chaos-error)
             (when top-level
               (chaos-prompt))
             (setq ast (chaos-read))

             ;; QUIT -----------------------------------------------------------
             (when (eq ast :quit)
               (return-from top-loop nil))
             ;; PROCESS INPUT COMMANDS =========================================
             (block process-input
               #||
               (when (eq ast '!)
                 (setq ast (eval (chaos-read)))
                 (when (eq ast :quit) (return-from top-loop nil)))
               ||#
               (eval-ast ast :print-generic-result)
               )
             (setq *chaos-print-errors* t)))
          )))))

 ;;; CHAOS TOP LEVEL LOOP
;;; [ast/script/lisp-form] ---> (read) ---> (eval) ---> (print)
;;;
(defun chaos-top ()
  (catch *top-level-tag*
    (process-chaos-input)))

;;; EOF
