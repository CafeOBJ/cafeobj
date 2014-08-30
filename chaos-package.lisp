;;;-*- Mode:LISP; Package: COMMON-LISP-USER; Base:10; Syntax:Common-Lisp -*-
;;;
;;; Copyright (c) 2000-2014, Toshimi Sawada. All rights reserved.
;;;
;;; Redistribution and use in source and binary forms, with or without
;;; modification, are permitted provided that the following conditions
;;; are met:
;;;
;;;   * Redistributions of source code must retain the above copyright
;;;     notice, this list of conditions and the following disclaimer.
;;;
;;;   * Redistributions in binary form must reproduce the above
;;;     copyright notice, this list of conditions and the following
;;;     disclaimer in the documentation and/or other materials
;;;     provided with the distribution.
;;;
;;; THIS SOFTWARE IS PROVIDED BY THE AUTHOR 'AS IS' AND ANY EXPRESSED
;;; OR IMPLIED WARRANTIES, INCLUDING, BUT NOT LIMITED TO, THE IMPLIED
;;; WARRANTIES OF MERCHANTABILITY AND FITNESS FOR A PARTICULAR PURPOSE
;;; ARE DISCLAIMED.  IN NO EVENT SHALL THE AUTHOR BE LIABLE FOR ANY
;;; DIRECT, INDIRECT, INCIDENTAL, SPECIAL, EXEMPLARY, OR CONSEQUENTIAL
;;; DAMAGES (INCLUDING, BUT NOT LIMITED TO, PROCUREMENT OF SUBSTITUTE
;;; GOODS OR SERVICES; LOSS OF USE, DATA, OR PROFITS; OR BUSINESS
;;; INTERRUPTION) HOWEVER CAUSED AND ON ANY THEORY OF LIABILITY,
;;; WHETHER IN CONTRACT, STRICT LIABILITY, OR TORT (INCLUDING
;;; NEGLIGENCE OR OTHERWISE) ARISING IN ANY WAY OUT OF THE USE OF THIS
;;; SOFTWARE, EVEN IF ADVISED OF THE POSSIBILITY OF SUCH DAMAGE.
;;;
#+LUCID (in-package "user")
#+Excl (in-package :user)
#+:ccl (in-package :common-lisp-user)
#+gcl (in-package :user)
#+Excl (eval-when (:execute :compile-toplevel :load-toplevel) (require 'loop))

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

(pushnew :bigpink *features*)
#+:mswindows
(pushnew :cltl2 *features*)

(require :asdf)

(defpackage :cl-ppcre-asd
  (:use :cl :asdf))

(defpackage :cl-ppcre
  (:nicknames :ppcre)
  #+:genera
  (:shadowing-import-from :common-lisp :lambda :simple-string :string)
  (:use #-:genera :cl #+:genera :future-common-lisp)
  (:shadow :digit-char-p :defconstant)
  (:export :parse-string
           :create-scanner
           :create-optimized-test-function
           :parse-tree-synonym
           :define-parse-tree-synonym
           :scan
           :scan-to-strings
           :do-scans
           :do-matches
           :do-matches-as-strings
           :all-matches
           :all-matches-as-strings
           :split
           :regex-replace
           :regex-replace-all
           :regex-apropos
           :regex-apropos-list
           :quote-meta-chars
           :*regex-char-code-limit*
           :*use-bmh-matchers*
           :*allow-quoting*
           :*allow-named-registers*
           :*optimize-char-classes*
           :*property-resolver*
           :ppcre-error
           :ppcre-invocation-error
           :ppcre-syntax-error
           :ppcre-syntax-error-string
           :ppcre-syntax-error-pos
           :register-groups-bind
           :do-register-groups))

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

      
