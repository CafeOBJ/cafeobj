;;; -*- Mode: LISP; Syntax: Common-lisp; Base: 10; Lowercase: T;  -*-
;;;
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
;;; ASDF
;;;
(require "asdf")
(in-package :asdf)

(eval-when (eval load)
  (push :bigpink *features*)
  (push :cltl2 *features*))

(defsystem :chaosx
    ;; :source-pathname *chaos-source-path-name*
    ;; :binary-pathname *chaos-bin-path-name*
    ;; :source-extension "lisp"
    :serial t
    :components
    (#+gcl
     (:module "clII"
	      :components (#-:defpackage (:file "loop")
			   #-:defpackage (:file "defpackage")
			   ))
     ;;
     (:file "chaos-package")
     (:file "version")
     ;; (:file "func-spec")
     (:module comlib
	      :serial t
	      :components ((:file "globals")
			   (:file "macros")
			   (:file "print-utils")
			   (:file "message")
			   (:file "error")
			   (:file "misc")
			   (:file "string")
			   (:file "list")
			   (:file "dag")
			   (:file "fsys")
			   (:file "tree-display")
			   (:file "lex")
			   (:file "reader")
			   (:file "let-over-lambda")
			   ))
     (:module "chaos"
	      :components ((:module primitives
				    :serial t
				    :components ((:file "term2")
						 (:file "defterm")
						 (:file "bobject2")
						 (:file "absntax")
						 (:file "script")
						 (:file "op-theory")
						 (:file "bmodexp")
						 (:file "bmodule2")
						 (:file "bview2")
						 (:file "parse-modexp")
						 (:file "normodexp")
						 (:file "bsort")
						 (:file "boperator")
						 (:file "baxioms")
						 (:file "bmacro")
						 (:file "gen-eval")
						 (:file "gen-print")
						 (:file "context")
						 (:file "term-utils")
						 (:file "substitution")
						 (:file "find")
						 (:file "print-object")
						 ))
			      (:module term-parser
				       :serial t
				       :components ((:file "parse-macro")
						    (:file "parse-engine")
						    (:file "parse-top")
						    )
				       )
			      (:module e-match
				       :serial t
				       :components ((:file "match-utils")
						    (:file "match-system")
						    (:file "match-state")
						    (:file "match-e")
						    (:file "match-idem")
						    (:file "match-z")
						    (:file "match-a")
						    (:file "match-c")
						    (:file "match-az")
						    (:file "match-cz")
						    (:file "match-ac")
						    (:file "match-acz")
						    (:file "match")
						    (:file "match2")
						    ))
			      (:module construct
				       :components ((:file "sort")
						    (:file "operator")
						    (:file "variable")
						    (:file "match-method")
						    (:file "axiom")
						    (:file "gen-rule")
						    (:file "cr")
						    (:file "rwl")
						    (:file "beh")
						    (:file "module")
						    (:file "trs")
						    )
				       )
			      (:module decafe
				       :serial t
				       :components ((:file "mutils")
						    (:file "modmorph")
						    (:file "mrmap")
						    (:file "meval")
						    (:file "view")
						    (:file "mimport")
						    ))
			      (:module cafein
				       :components (;; (:file "apply-rule")
						    (:file "rengine")
						    (:file "cbred")
						    ;; (:file "rdebug")
						    ;; (:file "trs")
						    ))
			      (:module tools
				       :components ((:file "regcheck")
						    (:file "regularize")
						    (:file "describe")
						    (:file "sort-tree")
						    (:file "module-tree")
						    (:file "show")
						    (:file "set")
						    (:file "op-check")
						    (:file "compat")
						    (:file "help")
						    (:file "inspect")
						    (:file "sensible")
						    ;; (:file "psupport")
						    ))
			      (:module eval
				       :components ((:file "eval-mod")
						    (:file "eval-ast")
						    (:file "eval-ast2")
						    (:file "chaos-top")
						    )
				       )
			      (:module boot
				       :components ((:file "preproc")
						    (:file "prelude")
						    (:file "builtins")
						    (:file "meta")
						    ))
			      (:module tram
				       :components ((:file "tram")))
			      (:module psup
				       :components ((:file "psup")))
			      ))
     (:module thstuff
	      :serial t
	      :components ((:file "parse-apply")
			   (:file "basics")
			   (:file "eval-match")
			   (:file "eval-apply")
			   (:file "cexec")
			   (:file "case")
			   (:file "proof-struct")
			   (:file "apply-tactic")
			   (:file "citp")))
     (:module "BigPink"
		 :components ((:module codes
				       :serial t
				       :components ((:file "types")
						    (:file "glob")
						    (:file "proof-sys")
						    (:file "syntax")
						    (:file "index")
						    (:file "butils")
						    (:file "unify")
						    (:file "clause")
						    (:file "formula")
						    (:file "modconv")
						    (:file "weight")
						    (:file "lrpo")
						    (:file "resolve")
						    (:file "paramod")
						    (:file "demod")
						    (:file "infer")
						    (:file "sigmatch")
						    (:file "refine")
						    (:file "commands")
						    (:file "inv")
						    ))))
     (:module cafeobj
	      :serial t
	      :components ((:file "cafeobjvar")
			   (:file "creader")
			   (:file "oldoc")
			   (:file "define")
			   (:file "trans-com")
			   (:file "trans-decl")
			   (:file "trans-form")
			   ;; (:file "command-proc")
			   (:file "command-top")
			   (:file "commands")
			   (:file "declarations")
			   (:file "cafeobj-top")
			   ))

     ))


;;; EOF

