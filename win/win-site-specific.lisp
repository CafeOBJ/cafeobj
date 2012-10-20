;;; $Id: win-site-specific.lisp,v 1.1.1.1 2003-06-19 08:31:12 sawada Exp $
(in-package :user)

;;; *BEGIN SITE SPECIFIC* \\\\\\\\\\\\\\\\\\\\\\\\\\\\\\\\\\\\\\\\\\\\

;;; set to the path where cafeobj distribution is put.
;;;
(eval-when (eval load)
  (setq *chaos-root* ".")
  (setq *chaos-source-path-name* ".")
  (setq *chaos-bin-path-name* "./bin"))

;;; set to the path where cafeobj execution image should be placed.
;;;
(eval-when (eval load)
  (setq chaos::*cafeobj-install-dir* "c:\\cafeobj"))

;;; *END SITE SPECIFIC* \\\\\\\\\\\\\\\\\\\\\\\\\\\\\\\\\\\\\\\\\\\\\\

;;; 
(defun make-appl-image (&optional (path chaos::*cafeobj-install-dir*))
  (setq chaos::-cafeobj-load-time- (chaos::get-time-string))
  ;; (chaos::set-cafeobj-standard-library-path)
  (setq *chaos-vergine* t)
  (setq excl:*restart-app-function* 'chaos::cafeobj-top-level)
  #||
  (setq excl:*restart-init-function*
    #'(lambda () (setq excl:*print-startup-message* nil)))
  ||#
  (setq excl:*print-startup-message* nil)
  (setq excl::.dump-lisp-suppress-allegro-cl-banner. t)
  ;; (dumplisp :name path :suppress-allegro-cl-banner t)
  (excl:generate-application "cafeobj"
			     path
			     '()
			     :allow-existing-directory t
			     :autoload-warning t
			     :application-type :exe
			     :include-compiler nil
			     :include-debugger t
			     :include-devl-env nil
			     :include-tpl t
			     :suppress-allegro-cl-banner t
			     :verbose t)
  )

;;; EOF


