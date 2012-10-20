;;;-*- Mode:LISP; Package:CHAOS; Base:10; Syntax:Common-lisp -*-
;;; $Id: patch.lisp,v 1.1.1.1 2003-06-19 08:29:39 sawada Exp $

;;; PATCH
(defvar *patch-level* 0)

(defun apply-patch (patch-file target)
  