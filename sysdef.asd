;;; -*- Mode: LISP; Syntax: Common-lisp; Base: 10; Lowercase: T;  -*-
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
			   (:file "cexec")))
     (:module cafeobj
	      :serial t
	      :components ((:file "cafeobjvar")
			   (:file "creader")
			   (:file "trans-com")
			   (:file "trans-decl")
			   (:file "trans-form")
			   (:file "command-proc")
			   (:file "command-top")
			   (:file "cafeobj-top")
			   ))
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
     ))


;;; EOF

