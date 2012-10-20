;;; -*- Mode: Lisp; Base: 10; Syntax: Common-Lisp; Package: DSYS -*-

(in-package "DSYS")

(defparameter *clcs-system-date*
  "CLCS 2/1/90") ;   (For akcl-1-530)

(defsystem clcs
    (:pretty-name "Common Lisp Condition System")
  #+kcl (:module clos pcl (:type :system))
  (:parallel
   #+kcl clos
   (:forms :compile (proclaim *fast-declaration*)
	   :load (proclaim *fast-declaration*))
   (:serial
    "package"
    #-(or lucid excl genera cmu)
    (:serial
     (:load "precom")
     "macros"
     "restart"
     "handler"
     "debugger"
     #+kcl "kcl-cond"
     #+kcl "top-patches"
     "conditions"
     "condition-definitions"
     (:compile "precom"))
    "install")))

(defparameter *clcs-files*
  '((("systems") "lisp"
     "clcs")
    (("clcs") "lisp"
     "sysdef"
     "package" "macros" "restart" "handler" "debugger"
     "kcl-cond" "top-patches"
     "conditions" "condition-definitions" "precom" "install")
    (("clcs") nil
     "clcs-readme")
    (("clcs") "text"
     "installing-mailed-clcs")
    (("clcs" "doc") "text"
     ;;"cond18" "status"
     )
    (("clcs" "doc") nil
     ;;"clos-conditions"
     )))

(defvar *clcs-dist-name* "clcs")

(defun clcs-distribution-header ()
  (let* ((*subfile-default-root-pathname* 
	  (make-pathname :directory '(:absolute "mydirectory" "lisp")))
	 (dist-dir (namestring (subfile '())))
	 (dist-file (namestring (subfile '() :name *clcs-dist-name* :type "lisp")))
	 (sys-file (namestring (subfile '() :name *this-file*))))
    (format nil
";;; -*- Mode: LISP; Syntax: Common-lisp; Package: USER; Base: 10 -*-
;;; Common Lisp Condition System Distribution File
;;; Suppose the directory that is to contain the clcs system
;;; is ~S.
;;; To install CLCS:
;;; 
~A
;;;    (1) Put this file in ~S.
;;;    (2) Run lisp, and type:
;;;        (load ~S)
;;; To use CLCS:
;;;    (1) Run lisp, and type:
;;;        (load ~S)

" dist-dir #-akcl ""
#+akcl ";;; The CLCS system redefines the functions LOAD and OPEN (adding
;;; restart handlers), and the function SYSTEM:ERROR-SET.  But AKCL is
;;; set up to compile calls to these functions into direct calls to
;;; C functions.  You can fix this by:
;;;     A. Edit the file cmpnew/lfun_list.lsp, commenting out every line
;;;        that begins with #-clcs.  
;;;     B. Remake AKCL.
;;;     C. Delete the files cmpnew/cmputil.o and lsp/debug.o
;;;        (these files call SYSTEM:ERROR-SET).
;;;     D. Remake AKCL.
;;;
"
dist-file dist-file sys-file)))

(defun write-clcs-distribution (&key output-file)
  (dolist (sys '(clcs pcl))
    (find-system sys nil))
  (unless output-file 
    (setq output-file (subfile '() :name *clcs-dist-name* :type "lisp")))
  (write-distribution :files (append *basic-files* *clcs-files* *pcl-files*)
		      :output-file output-file
		      :header (clcs-distribution-header)
		      #+unix :compress-uu-split-p #+unix t))

(defun read-clcs-distribution (&key input-file)
  (unless input-file
    (setq input-file (subfile '() :name *clcs-dist-name* :type "lisp")))
  (read-distribution :input-file input-file))

(defun clcs-users ()
  (let ((users-file (subfile '("clcs") :name "users" :type "text"))
	(users nil))
    (when (probe-file users-file)
      (with-open-file (in users-file :direction :input)
	(loop (push (or (read in nil) (return nil)) users))))
    (nreverse users)))

#+unix
(defun mail-clcs (&key output-file (new-p :ask) (query-users-p t))
  (unless output-file 
    (setq output-file (subfile '() :name *clcs-dist-name* :type "lisp")))
  (let ((users (clcs-users)) (mail-users nil))
    (if query-users-p
	(dolist (user users)
	  (when (y-or-n-p "Mail CLCS to ~A? " user)
	    (push user mail-users)))
	(setq mail-users users))
    (when (if (eq new-p :ask)
	      (y-or-n-p "~%Make a new distribution first? ")
	      new-p)
      (write-clcs-distribution :output-file output-file))
    (mail-compressed-uu-files 
     :users mail-users
     :file output-file
     :intro-subject "How to install CLCS"
     :intro-file (subfile '("clcs") :name "installing-mailed-clcs" :type "text"))))
