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
                               Module: primitives
                              File: normodexp.lisp
==============================================================================|#
#-:chaos-debug
(declaim (optimize (speed 3) (safety 0) #-GCL (debug 0)))
#+:chaos-debug
(declaim (optimize (speed 1) (safety 3) #-GCL (debug 3)))

;;; *************
;;; MODEXPR
;;; NORMALIZATION______________________________________________________________
;;; *************

#||
(defvar *modexp-normalized-table* (make-hash-table :test #'equal))

(defun find-normalized-modexp (modexp)
  (gethash modexp *modexp-normalized-table*))

(defun add-modexp-normalized (modexp)
  (setf (gethash modexp *modexp-normalized-table*) modexp))

||#

(declaim (type list *modexp-normalized-table*))

(defvar *modexp-normalized-table* nil)

(defun find-normalized-modexp (modexp)
  (declare (type modexp modexp)
           (values (or null modexp)))
  (find-in-assoc-table *modexp-normalized-table* modexp))

(defun add-modexp-normalized (modexp)
  (declare (type modexp)
           (values t))
  (add-to-assoc-table *modexp-normalized-table* modexp modexp))


;;; NORMALIZE-MODEXP : module-expression -> module-expression'
;;; canonicalize a module expression:
;;;
(defun normalize-modexp (modexp)
  (when (%is-modexp modexp) (setq modexp (%modexp-value modexp)))
  ;;
  (when (and (consp modexp) (null (cdr modexp)))
    (setq modexp (car modexp)))
  ;;
  (when (and (equal modexp "*the-current-module*")
             (get-context-module t))
    (setq modexp (get-context-module)))
  (cond ((module-p modexp) (normalize-modexp (module-name modexp)))
        ((stringp modexp) (canonicalize-simple-module-name modexp))
        ((atom modexp) modexp)
        ((modexp-is-?name? modexp)
         (make-?-name (normalize-modexp (?name-name modexp))))
        ((modexp-is-parameter-theory modexp)
         (let ((norm (find-normalized-modexp modexp)))
           (if norm norm
               (progn (add-modexp-normalized modexp)
                      modexp))))
        (t (let ((norm (find-normalized-modexp modexp)))
             (if norm norm
                 (progn
                   (setq norm (do-normalize-modexp modexp))
                   (add-modexp-normalized norm)
                   norm))))))

(defun canonicalize-simple-module-name (me)
  #||
  (when (and (not (find-module-in-env me nil))
             *current-module*
             (get-modexp-local (list me (module-name *current-module*))))
    (setq me (concatenate 'string me "." (module-name *current-module*))))
  ||#
  (let ((real-me (find-normalized-modexp me)))
    (if real-me
        real-me
        (progn
          (add-modexp-normalized me)
          me))))
            
;;; DO-NORMALIZE-MODEXP modexp
;;; perform canonicalization on modexp. known not to be in canonical form
;;; ops %+, %*, %view, %view-under
;;;
(defun do-normalize-modexp (modexp)
  (declare (type (or module view-struct modexp) modexp))
  (cond ((module-p modexp) modexp)
        ((view-p modexp) modexp)
        ((%is-plus modexp)      ; right associate and re-order
         (normalize-plus modexp))
        ((%is-rename modexp)
         (normalize-rename modexp))
        ((%is-instantiation modexp)
         (normalize-instantiation modexp))
        ;; need to have corresponding theory to be able to interpret view
        ((%is-view modexp) (normalize-view modexp))
        ;; internal error
        (t (break "Internal error : do-normalize-modexp: bad modexp form "))
        ))

;;; NORMALIZE-RENAME
;;;
(defun normalize-rename (modexp)
  (declare (type modexp)
           (values modexp))
  (setf (%rename-module modexp) (normalize-modexp (%rename-module modexp)))
  (setf (%rename-map modexp) (normalize-rename-map (%rename-map modexp)))
  modexp)

;;; NORMALIZE-PLUS : modexp -> modxp
;;; collect args to tree of plus's at top; canonicalize; cannot re-order
;;; build a right-associated tree (with deleting duplications).
;;;
(defun normalize-plus (modexp)
  (declare (type modexp modexp)
           (values modexp))
  (setf (%plus-args modexp)
        (sort (remove-duplicates (mapcar #'normalize-modexp (%plus-args modexp)))
              #'ob<))
  modexp)

;;; NORMALZE-INSTANTIATION
;;;
(defun normalize-instantiation (modexp)
  (declare (type modexp modexp)
           (values modexp))
  (setf (%instantiation-module modexp)
        (normalize-modexp (%instantiation-module modexp)))
  (setf (%instantiation-args modexp)
        (normalize-instantiation-args (%instantiation-args modexp)))
  modexp)

#||
(defun normalize-instantiation-args (args)
  (let ((r-res (sort args #'(lambda (x y)
                              (let ((arg-x (%!arg-name x))
                                    (arg-y (%!arg-name y)))
                                (if (integerp arg-x)
                                    (< arg-x arg-y)
                                  (string< (string (if (consp arg-x)
                                                       (car arg-x)
                                                       arg-y))
                                           (string (if (consp arg-y)
                                                       (car arg-y)
                                                       arg-y)))))))))
    (dolist (arg r-res)
      (setf (%!arg-view arg)
            (normalize-view (%!arg-view arg))))
    r-res))
||#

(defun normalize-instantiation-args (args)
  (declare (type list args)
           (values list))
  (dolist (arg args)
    (setf (%!arg-view arg)
          ;;; (normalize-view (%!arg-view arg))
          (normalize-modexp (%!arg-view arg))
          ))
  args)

;;;
(defun reorder-maps (maps)
  (declare (type list maps)
           (values list))
  (when maps
    (sort maps #'(lambda (x y) (ob< (car x) (car y))))))

(defun normalize-rename-map (rmap)
  (declare (type list rmap)
           (values list))
  (let* ((rmap-body (%rmap-map rmap))
         (sort-map (reorder-maps (cadr (assq '%ren-sort rmap-body))))
         (hsort-map (reorder-maps (cadr (assq '%ren-hsort rmap-body))))
         (op-map (reorder-maps (cadr (assq '%ren-op rmap-body))))
         (bop-map (reorder-maps (cadr (assq '%ren-bop rmap-body))))
         (p-map (reorder-maps (cadr (assq '%vars rmap-body)))))
    (setf (%rmap-map rmap)
          (nconc (when sort-map (list (%ren-sort* sort-map)))
                 (when hsort-map (list (%ren-hsort* hsort-map)))
                 (when op-map (list (%ren-op* op-map)))
                 (when bop-map (list (%ren-bop* bop-map)))
                 (if p-map (list (%vars* p-map)))))
    rmap))

;;; NORMALIZE-VIEW
;;;
(defun normalize-view (view)
  (declare (type modexp view)
           (type modexp))
  (setf (%view-module view) (normalize-modexp (%view-module view)))
  (setf (%view-target view) (normalize-modexp (%view-target view)))
  (when (%view-map view)
    (setf (%view-map view) (normalize-rename-map (%view-map view)))
    )
  view)

;;; EOF
