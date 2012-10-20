;;; $Id: mac-site-specific.lisp,v 1.1.1.1 2003-06-19 08:30:19 sawada Exp $
;;; (in-package :user)
;; patched by t-seino@jaist.ac.jp on 2000/02/08
(in-package :common-lisp-user)

;; added by t-seino@jaist.ac.jp on 2000/02/09
;; prepare to install.
(let ((file (concatenate 'string *chaos-root* ":chaosx.system")))
(when (probe-file file)
    (rename-file file "system.lisp")))

;; 
(defclass cafeobj-application (application) ())
(defmethod application-name ((app cafeobj-application)) "CafeOBJ")

(setf *application* (make-instance 'cafeobj-application))

;;; fit the listner into main screen.
(setf *listener-window-position*
    (make-point 8 (+ *menubar-bottom* 8)))
(setf *listener-window-size*
    (make-point 502 (- *screen-height* *menubar-bottom* 16)))

;;; Edit the followings

;;; set to the path where cafeobj distribution is put.
;; patched by t-seino@jaist.ac.jp on 2000/02/09
;; (eval-when (eval load)
;;   (setq *chaos-root* "."))

;;; EOF
