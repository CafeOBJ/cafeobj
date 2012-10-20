;;;-*- Mode:LISP; Package: Chaos; Base:10; Syntax:Common-lisp -*-
;;; $Id: debug.lisp,v 1.1.1.1 2003-06-19 08:28:14 sawada Exp $
(in-package :chaos)
#-:chaos-debug
(declaim (optimize (speed 3) (safety 0) #-GCL (debug 0)))
#+:chaos-debug
(declaim (optimize (speed 1) (safety 3) #-GCL (debug 3)))

#|==============================================================================
				 System: Chaos
				  Module: eval
				File: debug.lisp
==============================================================================|#

(defun print-opinfos (module)
  (with-in-module (module)
    (dolist (opinfo (module-all-operators module))
      (let ((op (opinfo-operator opinfo)))
        (print-next)
        (print-as :object opinfo)))))

(defun check-method-info (module)
  (with-in-module (module)
    (dolist (opinfo (module-all-operators module))
      (let ((methods (opinfo-methods opinfo)))
        (dolist (m methods)
          (format t "~&method : ")
          (print-chaos-object m)
          (let ((info (get-method-info m)))
            (if (not info)
              (format t "~&could not get method info ! ")
              (print-method-info info))))))))

(defun print-method-info (info)
  (let ((*print-indent* (+ 2 *print-indent*)))
    (print-next)
    (format t "** method-info ----------------------------")
    (format t "~& operator : ")
    (print-chaos-object (%method-info-operator info))
    (print-next)
    (format t " theory : ")
    (print-theory-brief (%method-info-theory info))
    (print-next)
    (format t "~& overloaded-methods : ")
    (dolist (ovm (%method-info-overloaded-methods info))
      (print-chaos-object ovm)
      (print-next))
    (format t "~& rules-with-same-top : ")
    (print-chaos-object (%method-info-rules-with-same-top info))
    (print-next)
    (format t " rules-with-different-top : ")
    (map nil #'print-chaos-object (%method-info-rules-with-different-top info))
    (print-next)
    (format t " strictly-overloaded : ")
    (print-chaos-object (%method-info-strictly-overloaded info))
    (print-next)
    (format t " rew-strategy : ")
    (print-chaos-object (%method-info-rew-strategy info))
    (print-next)
    ;;(format t " evaluator : ")
    ;;(print-chaos-object (%method-info-evaluator info))
    ))

;;; EOF
