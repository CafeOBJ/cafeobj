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
                                 Module: comlib
                             File: print-utils.lisp
=============================================================================|#
#-:chaos-debug
(declaim (optimize (speed 3) (safety 0) #-GCL (debug 0)))
#+:chaos-debug
(declaim (optimize (speed 1) (safety 3) #-GCL (debug 3)))

;;;-----------------------------------------------------------------------------
;;; Utilities for printing
;;;-----------------------------------------------------------------------------

;;; PRINT CONTROL VARIABLES 00--------------------------------------------------
;;; *print-line-limit* : the limit of length of a line
;;; *print-indent*     : current indent level.
;;; *print-indent-increment* : number of spaces per one indentation.
;;;

;;; FILECOL -- output column position
;;;
;; (declaim (function filecol (stream) fixnum))
;;(declaim (function filecol (t) fixnum))

#+GCL
(Clines "static object filecol(x) object x; {return(make_fixnum(file_column(x)));}")

;;(defCfun "object filecol(x) object x;" 0
;;  " Creturn(make_fixnum(file_column(x)));"
;;  )

#+GCL
(defentry filecol (object) (object filecol))

#+LUCID
(defun filecol (x) (declare (values fixnum)) (lucid::calculate-output-column x))

#+CMU
(defun filecol (x)
  (declare (values fixnum))
  (let ((val (lisp::charpos x)))
    (if val val
        0)))

#+EXCL
(defun filecol (x)
  (declare (values fixnum))
  (let ((val (excl::charpos x)))
    (if val val 0)))

#+:openmcl
(defun filecol (x)
  (declare (values fixnum))
  (stream-line-column x))

#+:SBCL
(defun filecol (x)
  (declare (values fixnum))
  (let ((val (sb-kernel::charpos x)))
    (if val val
      0)))

#-(or GCL KCL LUCID CMU EXCL :openmcl SBCL)
(defun filecol (x) (declare (ignore x)) 0) ; use this if you cannot define as

;; (declaim (function file-column (stream) fixnum))
#||
(defun file-column (strm)
  (if (typep strm 'stream)
      (filecol strm)
    0))
||#

(defun file-column (strm)
  (declare (inline filecol)
           (values fixnum))
  (filecol strm))

;;; print-check
;;; checks the current column exceeds the line limit, if so
;;; newline and indent.
;;;
#||
(defun print-check (&optional (indent 0) (fwd 0) (stream *standard-output*))
  (declare (type fixnum indent fwd))
  (if (<= *print-line-limit* (+ (file-column stream) fwd))
      (progn
        (terpri stream)
        (when (>= (1+ indent) *print-line-limit*)
          (setq indent 0)
          (setq .file-col. (* *print-indent* *print-indent-increment*)))
        (if (= 0 indent)
            (dotimes (i (* *print-indent* *print-indent-increment*))
              (princ #\space stream))
          (dotimes (i indent)
            (princ #\space stream)))
        t)
    nil))
||#

(defun print-check (&optional (indent 0) (fwd 0) (stream *standard-output*))
  (declare (type fixnum indent fwd))
  (if (<= *print-line-limit* (+ (file-column stream) fwd))
      (progn
        (print-next)
        (when (>= (1+ indent) *print-line-limit*)
          (setq .file-col. (* *print-indent* *print-indent-increment*)))
        #||
        (dotimes (i indent)
          (princ #\space stream))
        ||#
        t)
    nil))

;;; print-indent
;;; indentation.
;;;
(defun print-indent (indent-char &optional (n *print-indent*) (stream *standard-output*))
  (declare (type fixnum n))
  (dotimes (i (the fixnum (* n *print-indent-increment*)))
    (declare (type fixnum i))
    (princ indent-char stream)))

;;; print-centering
;;; print the given string centering
;;;
#||
(defun print-centering (string &optional (fill-char " ") (stream *standard-output*))
  (declare (type simple-string string))
  (let ((fill-col (truncate (+ (/ (- *print-line-limit* (length string)) 2.0) 0.5))))
    (declare (type fixnum fill-col))
    (dotimes (x fill-col)
      (declare (type fixnum x))
      (princ fill-char stream))
    (princ string stream)
    (unless (equal fill-char " ")
      (dotimes (x fill-col)
        (declare (type fixnum x))
        (princ fill-char stream))
      )))
||#

(defparameter .terminal-width. 70)
(defun print-centering (string &optional (fill-char " ") (stream *standard-output*))
  (declare (type simple-string string))
  (let ((fill-col (truncate (+ (/ (- .terminal-width. (length string)) 2.0) 0.5))))
    (declare (type fixnum fill-col))
    (dotimes (x fill-col)
      (declare (type fixnum x))
      (princ fill-char stream))
    (princ string stream)
    (unless (equal fill-char " ")
      (dotimes (x fill-col)
        (declare (type fixnum x))
        (princ fill-char stream))
      )))
    
;;; print-to-right
;;; print the given string
;;;
(defun print-to-right (string &optional (fill-char " ") (stream *standard-output*))
  (declare (type simple-string string)
           (type (or character simple-string) fill-char)
           (type stream stream))
  (dotimes (x (- .terminal-width. 1 (filecol stream)
                 *print-indent* (length string)))
    (declare (type fixnum x))
    (princ fill-char stream))
  (princ " " stream)
  (princ string stream))

;;; print-to-left
;;; print the given string
;;;
(defun print-to-left (string &optional (fill-char nil) (stream *standard-output*))
  (declare (type simple-string string)
           (type (or null character simple-string) fill-char)
           (type stream stream))
  (let ((*print-line-limit* .terminal-width.))
    (princ string stream)
    (princ " " stream)
    (if fill-char
        (dotimes (x (- *print-line-limit* 1 *print-indent*
                       (filecol stream) (length string)))
          (declare (type fixnum x))
          (princ fill-char stream)))))
    
;;; print-next
;;; print new-line iff the current column is not at the beggining of line
;;; and then indent. given prefix is printed afer the indentation if any.
;;;
(defun print-next (&optional (prefix nil) (n *print-indent*) (stream *standard-output*))
  (declare (type fixnum n)
           (type stream stream))
  #+SBCL
  (progn (terpri stream) (print-indent #\space n stream))
  #-SBCL
  (when (fresh-line stream)
    (print-indent #\space n stream))
  (when prefix (princ prefix stream)))

(defun print-next-prefix (prefix-char &optional (prefix nil) (n *print-indent*) (stream *standard-output*))
  (declare (type fixnum n)
           (type stream stream)
           (type character prefix-char))
  (when (fresh-line stream)
    (print-indent prefix-char n stream))
  (when prefix (princ prefix stream)))

;;; print-simple
;;;
(defun print-simple (x &optional (stream *standard-output*))
  (declare (type stream stream))
  (cond ((atom x) (prin1 x stream))
        (t (let ((flag nil) (tail x))
             (princ "(" stream)
             (loop (when (not (consp tail)) (return))
                   (if flag
                       (princ " " stream)
                       (setq flag t))
                   (print-simple (car tail) stream)
                   (setq tail (cdr tail)))
             (when tail
               (princ " . " stream)
               (prin1 tail stream))
             (princ ")" stream)
             ))))

;;; print-simple-princ
;;;
(defun print-simple-princ (x &optional (stream *standard-output*))
  (declare (type stream stream))
  (let ((.file-col. .file-col.))
    (cond ((atom x) (princ x stream))
          (t (let ((flag nil)
                   (tail x))
               (princ "(" stream)
               (setq .file-col. (1+ (file-column stream)))
               (loop (when (not (consp tail)) (return))
                 (if flag
                     (princ " " stream)
                   (setq flag t))
                 (print-simple-princ (car tail) stream)
                 (setq tail (cdr tail)))
               (when tail
                 (princ " . " stream)
                 (prin1 tail stream))
               (princ ")" stream)))
          )))

;;; print-simple-princ-open
;;;
(defun print-simple-princ-open (x &optional (stream *standard-output*))
  (declare (type stream stream))
  (let ((.file-col. .file-col.))
    (print-check .file-col. 0 stream)
    (cond ((atom x) (princ x stream))
          (t (let ((flag nil)
                   (tail x))
               (loop (when (not (consp tail)) (return))
                 (if flag
                     (princ #\space stream)
                   (setq flag t))
                 (print-simple-princ (car tail) stream)
                 (setq tail (cdr tail))
                 )
               (when tail
                 (princ " ... " stream)
                 (prin1 tail stream)))))
    ))

;;; EOF
