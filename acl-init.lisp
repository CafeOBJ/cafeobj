;;; $Id: acl-init.lisp,v 1.1.1.1 2003-06-19 08:25:55 sawada Exp $
(in-package :chaos)
(defvar .cafeobj-sys-dir. nil)
(defun chaos::chaos-init-fun (&rest ignore)
  (declare (ignore ignore))
  (setq .cafeobj-sys-dir.
    (translate-logical-pathname #p"sys:"))
  (setq *cafeobj-install-dir* 
    #+mswindows (namestring .cafeobj-sys-dir.)
    #-mswindows (namestring (merge-pathnames .cafeobj-sys-dir. #p"..")))
  (set-cafeobj-standard-library-path)
  )
  
;;; EOF
