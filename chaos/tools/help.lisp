;;;-*- Mode:LISP; Package:CHAOS; Base:10; Syntax:Common-lisp -*-
(in-package :chaos)
#|==============================================================================
                            System: CHAOS
		          Module: chaos/tools
                            File: help.lisp
==============================================================================|#
#-:chaos-debug
(declaim (optimize (speed 3) (safety 0) #-GCL (debug 0)))
#+:chaos-debug
(declaim (optimize (speed 1) (safety 3) #-GCL (debug 3)))

;;; 
;;; CafeOBJ interpreter On-Line HELP SYSTEM
;;;

(defvar *Help-DB* (make-hash-table :test #'equal))

(defun get-description (com-pat &optional (detail nil))
  (let* ((sdesc (gethash com-pat *Help-DB*))
         (syntax (first sdesc)))
    (if sdesc
        (concatenate 'string "~&[Syntax]: \"" syntax "\"~%  "
                     (if detail
                         (third sdesc)
                       (second sdesc)))
      nil)))

(defun read-help-db (path)
  (clrhash *Help-DB*)
  (with-open-file (strm path :if-does-not-exist :error)
    (loop for entry = (read strm nil :eof)
        while (not (eq entry :eof))
        do (let ((keypat (first entry))
                 (syntax (second entry))
                 (simple (third entry))
                 (detail (fourth entry)))
             (setf (gethash keypat *Help-DB*) (list syntax simple detail))))))

(defun setup-help-db ()
  (let ((fname (chaos-probe-file "help" *chaos-libpath* '(".desc"))))
    (unless fname
      (error "Internal error, can't find help.desc"))
    (read-help-db fname)))

;;; EOF

