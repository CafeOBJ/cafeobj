;;;-*- Mode:LISP; Package: COMMON-LISP-USER; Base:10; Syntax:Common-Lisp -*-
;;; $Id: chaos-package.lisp,v 1.4 2010-08-04 04:37:34 sawada Exp $
;;;
#+LUCID (in-package "user")
#+Excl (in-package :user)
#+:ccl (in-package :common-lisp-user)
#+gcl (in-package :user)
#+Excl (eval-when (eval compile load) (require 'loop))

#+:GCL (use-package :defpackage :common-lisp-user)

#|
(defpackage "FMCS"
  (:use #+:GCL "LISP" #-:GCL "COMMON-LISP" #+:MCL "CCL" #+:EXCL "EXCL")
  (:shadow "DEFCLASS" "DEFMETHOD" "MAKE-INSTANCE" "SLOT-VALUE"
           "STANDARD-OBJECT" "STANDARD-CLASS" "SELF" "CALL-NEXT-METHOD")
  (:export "*REDEFINE-WARNINGS*" "SELF" "$SLOT" 
           "DEF$FLAVOR" "DEF$METHOD" "UNDEF$METHOD" 
           "DEF$FRAME" "DEF$BEHAVIOR"
           "TRACE$METHOD" "UNTRACE$METHOD" "IS-TRACED$METHOD"
           "COMPILE-$FLAVOR-$METHODS" 
           "DEFWHOPPER" "CONTINUE-WHOPPER" 
           "$SEND" "LEXPR-$SEND"
           "FLAVORP" "FLAVOR-INSTANCEP" "FLAVOR-TYPEP" "FLAVOR-TYPE-OF"
           "GET-FLAVOR-INSTANCE-SLOTS" "SYMBOL-VALUE-IN-$INSTANCE" 
           "MAKE-$INSTANCE" "MAKE-WINDOW-OR-INSTANCE"
           "MCS-TRACE" "MCS-UNTRACE" "MCS-IS-TRACED"))

|#

(push :bigpink *features*)
#+:mswindows
(push :cltl2 *features*)

(defpackage "CHAOS"
    (:shadow "METHOD-NAME"
	     "METHOD"
	     "MAKE-METHOD"
	     #-:GCL "OBJECT"
	     ;; #+(:ALLEGRO-VERSION>= 7.0) "WHILE"
	     #+:EXCL
	     "CLASS"
	     "TIMER"
	     "MODULE"
	     "MODULE-P"
	     "LOAD-FILE"
	     )
  (:use #+:GCL "LISP" #-:GCL "COMMON-LISP"
	;; "FMCS"
	#+:MCL "CCL" #+:EXCL "EXCL"
	#+:GCL "DEFPACKAGE"
	;; #+:common-graphics "COMMON-GRAPHICS"
	)
  )

      
