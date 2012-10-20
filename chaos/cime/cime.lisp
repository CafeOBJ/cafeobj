;;;-*-Mode:LISP; Package: CHAOS; Base:10; Syntax:Common-lisp -*-
;;; $Id: cime.lisp,v 1.1.1.1 2003-06-19 08:27:40 sawada Exp $
(in-package :chaos)
#|=============================================================================
			     System:CHAOS
			     Module:cime
			    File:cime.lisp
=============================================================================|#

;;; CiME INERFACE =============================================================

(defun module->cime (&optional modexp)
  (let ((modval (trs-get-mod-or-error modexp)))
    (module->cime* modval)))

(defun module->cime* (module)
  (let ((trs (get-module-trs module)))
    (chaos-trs->cime trs)))

;;;
(defun chaos-trs->cime (trs)
  )

;;; EOF
