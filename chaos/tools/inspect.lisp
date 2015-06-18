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
(in-package :chaos)
#|=============================================================================
                                  System:CHAOS
                                  Module:tools
                                File:inspect.lisp
=============================================================================|#
#-:chaos-debug
(declaim (optimize (speed 3) (safety 0) #-GCL (debug 0)))
#+:chaos-debug
(declaim (optimize (speed 1) (safety 3) #-GCL (debug 3)))

;;;
;;; INSPECT
;;;
(defun show-module-symbol-table (mod &optional (stream *standard-output*))
  (let* ((st (module-symbol-table mod))
         (names (sort (copy-list (symbol-table-names st)) #'ob< )))
    (dolist (name names)
      (describe-name mod name (symbol-table-get name mod) stream))))

(defvar .current-char-index. nil)

(defun describe-name (mod name tbl &optional (stream *standard-output*))
  (unless tbl
    (format stream "~%No object with name ~A found." name)
    (return-from describe-name nil))
  (let ((*print-indent* 2)
        (print-name (if (symbolp name)
                        (string name)
                      name)))
    (when (and (stringp print-name)
               (not (eql .current-char-index.
                         (char print-name 0))))
      (setq .current-char-index. (char print-name 0))
      (format stream "~%** [~a] -----------------------------------------" 
              (string-upcase .current-char-index.)))
    (format stream "~%~A~10T" (if (symbolp name)
                                  (string name)
                                name))
    
    (let ((parameters (stable-parameters tbl))
          (submodules (stable-submodules tbl))
          (sorts (stable-sorts tbl))
          (operators (stable-operators tbl))
          (variables (stable-variables tbl))
          (axioms (stable-axioms tbl))
          (unknowns (stable-unknowns tbl)))
      (when parameters
        (inspect-show-parameters mod name parameters stream))
      (when submodules
        (inspect-show-submodules mod name submodules stream))
      (when sorts
        (inspect-show-sorts mod name sorts stream))
      (when operators
        (inspect-show-operators mod name operators stream))
      (when variables
        (inspect-show-variables mod name variables stream))
      (when axioms
        (inspect-show-axioms mod name axioms stream))
      (when unknowns
        (inspect-show-unknowns mod name unknowns stream)))))

;;;
;;;
;;;

(defun inspect-show-parameters (mod name objs stream)
  (declare (ignore mod))
  (dolist (obj objs)
    (let ((context-name (get-context-name-extended obj)))
      (print-next)
      (format stream "- parameter theory ~A(type ~S)" name (type-of name))
      (when context-name
        (format stream ", declared in ~A" context-name)))))

(defun inspect-show-submodules (mod name objs stream)
  (dolist (obj objs)
    (let ((context-name (get-context-name-extended obj))
          (alias (if (symbolp name)
                     (rassoc (string name) (module-alias mod) :test #'equal)
                   nil)))
      (print-next)
      (cond ((assoc obj (module-submodules mod))
             (format stream "- direct sub-module")
             (when alias
               (format stream ", alias of module ")
               (print-modexp (module-name (car alias)) stream t)))
            ((module-is-parameter-theory obj)
             (format stream "- parameter theory"))
            (t (format stream "- indirect sub-module")
               (when alias
                 (format stream ", alias of module ")
                 (print-modexp (module-name (car alias)) stream t)))) 
      (when context-name
        (format stream ", declared in ~A" context-name))
      (let ((alias (assoc name (module-alias mod))))
        (when alias
          (format stream ", renamed (original name = ~a)."
                  (with-output-to-string (str)
                    (print-mod-name obj str t))))))))

(defun get-context-name-for-qualify (obj)
  (let ((cmod (object-context-mod obj)))
    (unless cmod
      (with-output-chaos-error ('no-context)
        (format t "Internal error : no context found for object ~s" obj)))
    (let ((qname (get-module-print-name cmod)))
      (unless (module-is-parameter-theory cmod)
        (return-from get-context-name-for-qualify qname))
      (car qname))))

(defun inspect-show-sorts (mod name objs stream)
  (dolist (obj objs)
    (print-next)
    (let ((context-name (get-context-name-extended obj))
          (ambig (cdr objs)))
      (if (sort-is-hidden obj)
          (format stream "- hidden sort declared in ~a" context-name)
        (format stream "- sort declared in ~a" context-name))
      (when ambig
        (let ((qname (get-context-name-for-qualify obj)))
          ;; must be qualified
          (cond ((modexp-is-simple-name qname)
                 (print-next)
                 (format stream "  the name must be qualified for disambiguation: ~A.~A"
                       (string name) qname))
                (t (let ((a-name (rassoc (object-context-mod obj)
                                         (module-alias mod))))
                     (cond (a-name
                            (print-next)
                            (format stream "  the name must be qualified for disambiguation: ~A.~A"
                                  (string name) (car a-name)))
                           (t
                            (print-next)
                            (format stream "  the name must be qualified for disambiguation,")
                            (print-next)
                            (format stream "  but the module name is not simple one:")
                            (print-mod-name (object-context-mod obj)
                                            stream)))))))))))

(defun inspect-show-operators (mod name objs stream)
  (declare (ignore name))
  (dolist (obj objs)
    (print-next)
    (format stream "- operator:")
    (let ((*print-indent* (+ *print-indent* 2)))
      (print-op-brief obj mod t t t))))
         
(defun inspect-show-axioms (mod name objs stream)
  (declare (ignore name mod))
  (dolist (obj objs)
    (print-next)
    (let ((context-name (get-context-name-extended obj)))
      (format stream "- axiom declared in ~a" context-name)
      (let ((*print-indent* (+ *print-indent* 2)))
        (print-next)
        (print-axiom-brief obj stream)))))

(defun inspect-show-variables (mod name objs stream)
  (declare (ignore name))
  (dolist (obj objs)
    (print-next)
    (format stream "- variable of sort ~a"
            (with-output-to-string (str)
              (print-sort-name (variable-sort obj) mod str)))))

(defun inspect-show-unknowns (mod name objs stream)
  (declare (ignore mod name))
  (dolist (obj objs)
    (print-next)
    (format stream "- unknown object ~s" obj)))

(defun inspect-internal-error (mod name obj stream)
  (declare (ignore mod name stream))
  (with-output-chaos-error ('internal-error)
    (format t "inspect: internal error, ~s" obj)))

(defun !inspect-module (mod)
  (let ((.current-char-index. nil))
    (declare (special .current-char-index.))
    (with-in-module (mod)
      (show-module-symbol-table mod))))

;;; *******
;;; LOOK-UP
;;; *******
(defun inspect-canon-name (name)
  (if (stringp name)
      (let ((sname (parse-with-delimiter2 name #\_)))
        (if (stringp sname)
            sname
          (remove "" sname :test #'equal)))
    (mapcan #'inspect-canon-name 
            (remove ")" (remove "(" name :test #'equal) :test #'equal))))

(defun !look-up (name module)
  (declare (ignore ignore))
  (unless (module-p module)
    (with-output-chaos-error ('ivalid-module)
      (format t "~%internal error, look up processor is given illegal module object.")))
  (with-in-module (module)
    (let ((nm (inspect-canon-name name)))
      (describe-name module
                     (canonicalize-object-name nm)
                     (symbol-table-get nm module)
                     *standard-output*))))

;;; EOF
