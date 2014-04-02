;;;-*- Mode:LISP; Package: COMMON-LISP-USER; Base:10; Syntax:Common-Lisp -*-
;;; $Id: make-cafeobj.lisp,v 1.1.1.1 2003-06-19 08:26:04 sawada Exp $

;;;*****************************************************************************
;;; Template for making CafeOBJ interpreter.
;;;*****************************************************************************

(eval-when (:execute :load-toplevel)
  (unless (find-package :common-lisp)
    (rename-package :lisp :common-lisp
		    (union '("CL" "LISP")
			   (package-nicknames (find-package :lisp)) :test #'string=)))
  (unless (find-package :common-lisp-user)
    (rename-package :user :common-lisp-user
		    (union '("CL-USER" "USER")
			   (package-nicknames (find-package :user)) :test #'string=)))
  )

#+LUCID (in-package "user")
#+Excl (in-package :user)
#+(or :ccl CMU :SBCL) (in-package :common-lisp-user)
#+GCL (in-package :user)
#+GCL (setf compiler::*compile-ordinaries* t)
(unless (find-package :chaos)
  (make-package :chaos))
#+CLISP (in-package :common-lisp-user)

;;; BEGIN SITE SPECIFIC ------------------------------------------------------
;;; NOTE: users of ACL on windows or MCL should edit the files
;;;       win/win-site-specific.lisp  -- for ACL on windows
;;;       mac/mac-site-specific.lisp  -- for MCL on Machintosh
;;;
(defvar *chaos-root*)

#-(or microsoft (and ccl (not :openmcl)))
(eval-when (:execute :load-toplevel)
  (setq *chaos-root* XCHAOS_ROOT_DIR))

#+clisp
(eval-when (:execute :load-toplevel)
  (setq *chaos-root* (namestring (car (directory (concatenate 'string
						   *chaos-root* "/"))))))

#+microsoft
(load "win/win-site-specific.lisp")

;; patched by t-seino@jaist.ac.jp (2000/02/09)
;; patch by swada@sra.co.jp (2002/12/3)
#+(and ccl (not :openmcl))
(eval-when (:execute :load-toplevel)
 (setq *chaos-root* (string-right-trim ":"
        (mac-directory-namestring *loading-file-source-file*))))
#+(and ccl (not :openmcl))
(load (concatenate 'string *chaos-root* ":mac:mac-site-specific.lisp"))
;;

(defvar chaos::*cafeobj-install-dir*)
#-(or microsoft (and ccl (not :openmcl)))
(eval-when (:execute :load-toplevel)
  (setq chaos::*cafeobj-install-dir* XINSTALL_DIR)
  )
#+(or microsoft (and ccl (not :openmcl)))
(eval-when (:execute :load-toplevel)
  ;; (setq chaos::*cafeobj-install-dir* *chaos-root*)
  (setq *chaos-bin-path-name* (concatenate 'string *chaos-root* "/bin")))

(defvar chaos::*make-bigpink* nil)

;;; END SITE SPECIFIC --------------------------------------------------------

(eval-when (:execute :load-toplevel)
  (setq chaos::*make-bigpink* :BIGPINK)
  ;; (push :chaos-debug *features*)
  (push :bigpink *features*))

#-:ASDF
(eval-when (:execute :load-toplevel)
   #+microsoft
   (load (concatenate 'string *chaos-root* "\\asdf.lisp"))
   #-(or (and CCL (not :openmcl)) microsoft sbcl)
   (load (concatenate 'string *chaos-root* "/asdf.lisp"))
   #+SBCL
   (require 'asdf)
   ;; patch by t-seino@jaist.ac.jp
   ;; patch by sawada@sra.co.jp
   #+(and CCL (not :openmcl))
   (load (concatenate 'string *chaos-root* ":asdf.lisp"))
   ;; patch by t-seino@jaist.ac.jp (2000/02/09)
   ;; patch by sawada@sra.co.jp
   #+(and CCL (not :openmcl)) 
   (load (concatenate 'string *chaos-root* ":system"))
   #+sbcl (require :asdf))

#+GCL
(defun make-exec-image (path)
  (setq chaos::-cafeobj-load-time- (chaos::get-time-string))
  (chaos::set-cafeobj-standard-library-path)
  (setq *chaos-new* t)
  (defun system::top-level () (funcall 'chaos::cafeobj-top-level))
  (si::set-up-top-level)
  (system::save-system path)
  (bye))

#+CMU
(defun make-exec-image (path)
  (setq chaos::-cafeobj-load-time- (chaos::get-time-string))
  (chaos::set-cafeobj-standard-library-path)
  (setq *chaos-new* t)
  (ext:save-lisp path
		 :purify t
		 :init-function 'chaos::cafeobj-top-level
		 :print-herald nil
		 )
  )

#+SBCL
(defun make-exec-image (path)
  (setq chaos::-cafeobj-load-time- (chaos::get-time-string))
  (chaos::set-cafeobj-standard-library-path)
  (setq *chaos-new* t)
  (sb-ext:save-lisp-and-die path
			    :toplevel 'chaos::cafeobj-top-level
			    :purify t
			    :executable t
			    :save-runtime-options t
			    )
  )
  

#+LUCID
(defun make-exec-image (path)
  (setq chaos::-cafeobj-load-time- (chaos::get-time-string))
  (chaos::set-cafeobj-standard-library-path)
  (setq *chaos-new* t)
  (disksave path
	    :full-gc t
	    :restart-function 'chaos::cafeobj-top-level))

#+(and ccl (not :openmcl))
(defun make-exec-image (path)
  (setq chaos::-cafeobj-load-time- (chaos::get-time-string))
  (chaos::set-cafeobj-standard-library-path)
  (setq *chaos-new* t)
  ;; patch by t-seino@jaist.ac.jp
  (save-application path :toplevel-function 'chaos::cafeobj-top-level)
  )

#+:openmcl
(defun make-exec-image (path)
  (setq chaos::-cafeobj-load-time- (chaos::get-time-string))
  (chaos::set-cafeobj-standard-library-path)
  (setq *chaos-new* t)
  (ccl::save-application path :toplevel-function 'chaos::cafeobj-top-level)
  )

#+:ALLEGRO-V5.0
(require :build)

#+:ALLEGRO
(defun make-exec-image (path)
  (setq chaos::-cafeobj-load-time- (chaos::get-time-string))
  (chaos::set-cafeobj-standard-library-path)
  (setq *chaos-new* t)
  (setq excl:*restart-app-function* 'chaos::cafeobj-top-level)
  #||
  (setq excl:*restart-init-function*
    #'(lambda ()
	(excl:use-background-streams)
	(excl:start-emacs-lisp-interface t)))
  ||#
  (setq excl:*print-startup-message* nil)
  (setq excl::.dump-lisp-suppress-allegro-cl-banner. t)
  (dumplisp :name path :suppress-allegro-cl-banner t)
  )

#+:CLISP
(defun make-exec-image (path)
  (setq chaos::-cafeobj-load-time- (chaos::get-time-string))
  (chaos::set-cafeobj-standard-library-path)
  (setq *chaos-new* t)
  (chaos::save-chaos 'chaos::cafeobj-top-level path))

;;;;

(defvar chaos::*compile-builtin-axiom* nil)

(defun make-cafeobj (&optional chaos-root)
  (format t "~%** making CafeOBJ (~a)" (or chaos-root
					   *chaos-root*))
  (when chaos-root
    (setf *chaos-root* chaos-root))
  ;; (mk::operate-on-system :chaosx :compile)
  (setq chaos::*compile-builtin-axiom* nil)
  (load "sysdef.asd")
  (asdf:oos 'asdf:load-op 'chaosx)
  (make-exec-image
   (concatenate 'string *chaos-root*
		#+GCL "/xbin/cafeobj.exe"
		#+microsoft "/xbin/cafeobj.dxl"
		#+(and unix Allegro) "/xbin/cafeobj.acl"
		#+CMU "/xbin/cafeobj.core"
		#+SBCL "/xbin/cafeobj.sbcl"
		#+CLISP "/xbin/cafeobj.mem"
		#+:openmcl "/xbin/cafeobj.img"
		;; patch by t-seino@jaist.ac.jp
		;; patch by sawada@sra.co.jp
		#+(and CCL (not :openmcl)) ":xbin:cafeobj.exe"
		))
  )

(eval-when (:execute :load-toplevel)
  (make-cafeobj *chaos-root*)
  )

;;; EOF
