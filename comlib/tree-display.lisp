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
                                 Module: comlib
                            File: tree-display.lisp
==============================================================================|#
#-:chaos-debug
(declaim (optimize (speed 3) (safety 0) #-GCL (debug 0)))
#+:chaos-debug
(declaim (optimize (speed 1) (safety 3) #-GCL (debug 3)))

;;;-----------------------------------------------------------------------------
;;; customisable parameters
;;;-----------------------------------------------------------------------------

;;; how many space characters between trees
(defparameter tree-spacing 2)

;;; print tree with leaves at bottom?
(defparameter leaves-at-bottom? nil)

;;; USERS MUST BIND THESE FUNCTIONS
;;; which define what a tree is (leaf & internal node) and
;;; how to get its components.
;;;
(declaim (special leaf? leaf-name leaf-info int-node-name int-node-children))

(defvar leaf? nil)
(defvar leaf-name nil)
(defvar leaf-info nil)
(defvar int-node-name nil)
(defvar int-node-children nil)

(defun make-augm-leaf (width root name info)
  (declare (type t width root name info))
  (list 'leaf width root name info))

(defun make-augm-pad (width)
  (declare (type t width))
  (list 'pad width))

(defun make-augm-int-node (width root name lpad rpad children)
  (declare (type t width root name lpad rpad children))
  (list nil width root name lpad rpad children))

(defun augm-tree-int-node? (x)
  (declare (type list x)
           (values (or null t)))
  (null (car x)))

(defun augm-tree-pad? (x)
  (declare (type list x))
  (eq (car x) 'pad))

(defun augm-tree-width (x)
  (declare (type list x)
           (values fixnum))
  (nth 1 x))

(defun augm-tree-root (x)
  (declare (type list x)
           (values t))
  (nth 2 x))

(defun augm-tree-name (x)
  (declare (type list x))
  (nth 3 x))

(defun augm-leaf-info (x)
  (declare (type list x))
  (nth 4 x))

(defun augm-int-node-lpad (x)
  (declare (type list x))
  (nth 4 x))

(defun augm-int-node-rpad (x)
  (declare (type list x))
  (nth 5 x))

(defun augm-int-node-children (x)
  (declare (type list x))
  (nth 6 x))

(defun pad (width l)
  (declare (type fixnum width)
           (type list l)
           (values list))
  (if (> width 0)
      (cons (make-augm-pad width) l)
      l))

(defun field-width (x)
  (declare (type t x)
           (values fixnum))
  " return number of chars in the written repr of x"
  (labels ((l-length (l w)
             (declare (type list l)
                      (type fixnum w)
                      (values fixnum))
             (cond ((null l) w)
                   (t (l-length (cdr l) (+ w (field-width (car l)) 1)))
                   ))
           #|| not used now
           (s-length (i w)
             (if (>= i 0)
                 (let ((c (elt x i)))
                   (s-length (- i 1)
                             (+ w (case c ((#\: #\") 2) (otherwise 1)))))
                 w))
           ||#
           )
    ;;
    (typecase x
      (symbol (length (symbol-name (the symbol x))))
      (character (case x ((#\space) 7) ((#\newline) 9) (otherwise 3)))
      (number (length (format nil "~S" x)))
      (list (+ (l-length (cdr x) (+ (field-width (car x)) 2)) 1))
      (string (length (the simple-string x))
              ;;(s-length (- (length x) 1) 2)
              )
      (t 0))))

(defun augment-tree (tree)
  (declare (type list tree))
  (if (funcall leaf? tree)
      (let* ((name (funcall leaf-name tree))
             (info (funcall leaf-info tree))
             (name-width (field-width name))
             (info-width (field-width info))
             (tree-width (max name-width info-width)))
        (declare (type fixnum name-width info-width tree-width))
        (make-augm-leaf tree-width (truncate tree-width 2) name info))
      (let* ((children (mapcar #'augment-tree (funcall int-node-children tree)))
             (name (funcall int-node-name tree))
             (name-width (field-width name))
             (name-left (truncate name-width 2))
             (name-right (- name-width name-left)))
        (declare (type fixnum name-width name-left name-right)
                 (type list children))
        (if (null children)
            (make-augm-int-node name-width name-left name 0 0 '())
            (let* ((first-child (car children))
                   (last-child (nth (- (length children) 1) children))
                   (width
                    (+ (* (- (the fixnum (length (the list children)))
                             1) tree-spacing)
                       (the fixnum
                         (apply #'+ (mapcar #'augm-tree-width children)))))
                   (left
                    (truncate (+ (- width (the fixnum
                                            (augm-tree-width last-child)))
                                 (+ (the fixnum (augm-tree-root first-child))
                                    (the fixnum (augm-tree-root last-child))))
                              2.0))
                   (right
                    (- width left))
                   (max-left
                    (max name-left left))
                   (max-right
                    (max name-right right)))
              (declare (type fixnum width left right max-left max-right))
              ;;
              (make-augm-int-node (+ max-left max-right) max-left name
                                  (- max-left left) (- max-right right)
                                  children))))))

;;; 
;;;
(declaim (type hash-table _dup-hash_)
         (type fixnum _ref-num-counter_)
         (type list _dup-infos_))
(defvar _dup-hash_ (make-hash-table :test #'equal))
(defvar _ref-num-counter_ -1)
(defvar _dup-infos_ nil)

(defun augment-tree-as-graph (tree)
  (clrhash _dup-hash_)
  (setq _dup-infos_ nil)
  (setq _ref-num-counter_ -1)
  (traverse-tree-checking-dups tree)
  (augment-tree-as-graph-aux tree))

(defstruct grph-info
  (visited 0 :type fixnum)
  name 
  ref-name)

(defstruct (grph-int-node-info (:include grph-info))
  )

(defstruct (grph-leaf-info (:include grph-info))
  info
  )

(defun traverse-tree-checking-dups (tree)
  (let ((info (gethash tree _dup-hash_)))
    (cond (info                         ; duplicates
           (incf (grph-info-visited info))
           (when (= 1 (grph-info-visited info))
             ;; this is the second time
             (setf (grph-info-ref-name info)
                   (format nil "#~d" (incf _ref-num-counter_)))
             ))
          (t                            ; the first time
           (cond ((funcall leaf? tree)
                  ;; leaf tree
                  (let ((name (funcall leaf-name tree))
                        (info (funcall leaf-info tree)))
                    (let ((leaf-info (make-grph-leaf-info :name name
                                                          :info info)))
                      (setf (gethash tree _dup-hash_) leaf-info))))
                 (t
                  ;; internal node
                  (let ((name (funcall int-node-name tree)))
                    (let ((int-info (make-grph-int-node-info :name name)))
                      (setf (gethash tree _dup-hash_) int-info))
                    (mapc #'traverse-tree-checking-dups
                          (funcall int-node-children tree)))))))))
           
(defun augment-tree-as-graph-aux (tree)
  (let* ((info (gethash tree _dup-hash_))
         (ref-num (decf (grph-info-visited info)))
         (ref-name (grph-info-ref-name info))
         (name (cond ((< ref-num 0)
                      (if ref-name
                          (format nil "~a=~a" ref-name (grph-info-name info))
                          (grph-info-name info)))
                     (t ref-name))))
    (declare (type fixnum ref-num))
    (cond ((grph-leaf-info-p info)      ; leaf
           (let* ((leaf-info (grph-leaf-info-info info))
                  (name-width (field-width name))
                  (info-width (field-width leaf-info))
                  (tree-width (max name-width info-width)))
             (declare (type fixnum name-width info-width tree-width))
             (make-augm-leaf tree-width (truncate tree-width 2) name leaf-info)))
          (t                            ; int node
           (let* ((children (if (and (>= ref-num 0) ref-name)
                                nil
                                (mapcar #'augment-tree-as-graph-aux
                                        (funcall int-node-children tree))))
                  (name-width (field-width name))
                  (name-left (truncate name-width 2))
                  (name-right (- name-width name-left)))
             (declare (type list children)
                      (type fixnum name-width name-left name-right))
             (if (null children)
                 ;; (make-augm-int-node name-width name-left name 0 0 '())
                 (make-augm-leaf name-width (truncate name-width 2) name nil)
                 (let* ((first-child (car children))
                        (last-child (nth (- (the fixnum
                                              (length children))
                                            1)
                                         children))
                        (width
                         (+ (* (- (the fixnum (length children))
                                  1)
                               tree-spacing)
                            (the fixnum
                              (apply #'+ (mapcar #'augm-tree-width children)))))
                        (left
                         (truncate (+ (- width
                                         (the fixnum (augm-tree-width last-child)))
                                      (+ (the fixnum (augm-tree-root first-child))
                                         (the fixnum (augm-tree-root last-child))))
                                   2.0))
                        (right (- width left))
                        (max-left (max name-left left))
                        (max-right (max name-right right)))
                   (declare (type fixnum width left right max-left max-right))
                   (make-augm-int-node (+ max-left max-right) max-left name
                                       (- max-left left) (- max-right right)
                                       children))))))))

(defun any-int-nodes? (trees)
  (if (null trees)
      nil
      (or (augm-tree-int-node? (car trees))
          (any-int-nodes? (cdr trees)))))

(defun all-done? (trees)
  (if (null trees)
      t
      (and (augm-tree-pad? (car trees))
           (all-done? (cdr trees)))))

(defun print-seq (c n stream)
  (declare (type fixnum n)
           (type (or null t) c)
           (type stream stream))
  (when n
    (dotimes (x n)
      (princ c stream))))

(defun print-loop1 (l delay-leaves? stream)
  (declare (type list l)
           (type (or null t) delay-leaves?)
           (type stream stream))
  (when (consp l)
    (let* ((tree (car l))
           (tree-width (augm-tree-width tree)))
      (declare (type fixnum tree-width))
      (if (augm-tree-pad? tree)
          (progn
            (print-seq #\space tree-width stream)
            (print-loop1 (cdr l) delay-leaves? stream))
          (let* ((root (augm-tree-root tree))
                 (name (augm-tree-name tree))
                 (name-width (field-width name))
                 (name-left (truncate name-width 2))
                 (name-right (- name-width name-left)))
            (declare (type fixnum root name-width name-left name-right))
            (if (or (not delay-leaves?) (augm-tree-int-node? tree))
                (progn
                  (print-seq #\space (- root name-left) stream)
                  (princ name stream)
                  (print-seq #\space (- tree-width root name-right) stream)
                  (print-loop1 (cdr l) delay-leaves? stream))
                (progn
                  (print-seq #\space root stream)
                  (princ #\| stream)
                  (print-seq #\space (- tree-width root 1) stream)
                  (print-loop1 (cdr l) delay-leaves? stream))))))))

(defun print-loop2 (l new-trees delay-leaves? stream)
  (if (consp l)
      (let* ((tree (car l))
             (tree-width (augm-tree-width tree)))
        (declare (type fixnum tree-width))
        (if (augm-tree-pad? tree)
            (progn
              (print-seq #\space tree-width stream)
              (print-loop2 (cdr l) (append new-trees (list tree))
                           delay-leaves? stream))
            (let* ((root (augm-tree-root tree))
                   (name (augm-tree-name tree))
                   (name-width (field-width name))
                   (name-left (truncate name-width 2))
                   (name-right (- name-width name-left)))
              (declare (type fixnum root name-width name-left name-right))
              (if (augm-tree-int-node? tree)
                  (let ((children (augm-int-node-children tree)))
                    (declare (type list children))
                    (if (null children)
                        (progn
                          (print-seq #\space (- root name-left) stream)
                          (princ name stream)
                          (print-seq #\space (- tree-width root name-right)
                               stream)
                          (print-loop2 (cdr l)
                                 (append new-trees
                                         (pad tree-width '()))
                                 delay-leaves? stream))
                        (let* ((child1 (car children))
                               (root1 (augm-tree-root child1))
                               (width1 (augm-tree-width child1))
                               (lpad (augm-int-node-lpad tree))
                               (rpad (augm-int-node-rpad tree)))
                          (declare (type fixnum root1 width1))
                          (labels ((print-loop3 (l1 l2 right)
                                     (if (consp l1)
                                         (let* ((child (car l1))
                                                (root (augm-tree-root child))
                                                (width (augm-tree-width child)))
                                           (print-seq #\space (+ root tree-spacing right)
                                                      stream)
                                           (if (cdr l1)
                                               (princ #\| stream)
                                               (princ #\\ stream)
                                               ;;(princ "\\ " stream)
                                               )
                                           (print-loop3 (cdr l1)
                                                        (cons child 
                                                              (pad tree-spacing l2))
                                                        (- width (+ root 1))))
                                         (progn
                                           (print-seq #\space (+ right rpad) stream)
                                           (print-loop2 
                                             (cdr l)
                                             (append new-trees
                                                     (reverse (pad rpad l2)))
                                             delay-leaves? stream)))))
                            (print-seq #\space (+ lpad root1) stream)
                            (if (cdr children)
                                (princ #\/ stream)
                                (princ #\|))
                            (print-loop3 (cdr children)
                                         (cons child1 (pad lpad '()))
                                         (- width1 (+ root1 1))
                                         )))))
                  (if delay-leaves?
                      (progn
                        (print-seq #\space root stream)
                        (princ #\| stream)
                        (print-seq #\space (- tree-width root 1)
                                   stream)
                        (print-loop2 (cdr l) (append new-trees
                                               (list tree))
                                     delay-leaves? stream))
                      (let* ((info (augm-leaf-info tree))
                             (info-width (field-width info))
                             (info-left (truncate info-width 2))
                             (info-right (- info-width info-left)))
                        (print-seq #\space (- root info-left) stream)
                        (print-seq #\space info-width stream);(princ info stream)
                        (print-seq #\space (- tree-width root info-right)
                                   stream)
                        (print-loop2 (cdr l)
                                     (append new-trees
                                             (pad tree-width '()))
                                     delay-leaves? stream)))))))
        (when new-trees
          (princ " " stream)
          (print-next nil *print-indent* stream)
          (print-trees new-trees stream))))

(defun print-trees (trees stream)
  (if (not (all-done? trees))
      (let ((delay-leaves? (and leaves-at-bottom? (any-int-nodes? trees))))
        (print-loop1 trees delay-leaves? stream)
        ;; (terpri stream)
        (print-next nil *print-indent* stream)
        (print-loop2 trees '() delay-leaves? stream))))
          
#||
(defun show-tree (inp &optional (show-sort nil) (stream *standard-output*))
  (let ((tree (if (term? inp)
                  inp
                  (setf $$term (simple-parse inp *current-module* *universal-sort*)))))
    (tree-display tree show-sort stream)))

||#
;;; EOF
