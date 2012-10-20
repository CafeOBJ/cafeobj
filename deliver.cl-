;;; -*- Mode: LISP; Syntax: Common-Lisp -*-
;;; $Id: deliver.cl,v 1.4 2007-09-14 08:55:28 sawada Exp $
(in-package :common-lisp-user)
(eval-when (eval load)
  (load "chaos-package.fasl")
  )
(defun make-app (path)
  (generate-application "CafeOBJ"
			#-:mswindows
			"dist/cafeobj-1.4/lisp/"
			#+:mswindows
			"dist/cafeobj-1.4/"
			'("pignose.fasl" :emacs :eli
			  :sock :process
			  :acldns :collate :euc :ffcompat :list2
			  :fileutil :foreign :trace
			  :hmac :locale :regexp2 #-:mswindows :sigio 
			  ;; #-:mswindows :ssl
			  :ssl
			  :streama)
			:application-type :exe
			:print-startup-message nil
			:allow-existing-directory t
			:copy-shared-libraries t
			:read-init-files nil
			:restart-app-function 'chaos::cafeobj-top-level
			;; :restart-init-function 'chaos::chaos-init-fun
			:runtime :standard
			:suppress-allegro-cl-banner t
			:runtime-bundle t
			:include-compiler nil
			;; :record-source-file-info nil
			;; :record-xref-info nil
			;; :load-source-file-info nil
			;; :load-xref-info nil
			;; :load-local-names-info nil
			:autoload-warning t
			:discard-local-name-info t
			:discard-source-file-info t
			;; :discard-xref-into t
			:discard-arglists t
			:application-administration
			'(#+:mswindows
			  (:batch-file "cafeobj.bat")
			  )
			))

(eval-when (eval load)
  (make-app nil))

;;; EOF
