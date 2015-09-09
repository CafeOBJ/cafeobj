;;; -*- Mode: LISP; Syntax: Common-lisp; Base: 10; Lowercase: T;  -*-
;;;
;;; defsystem for Allegro CL (version 5.0 or higher)
;;;
;;; Copyright (c) 2000-2015, Toshimi Sawada. All rights reserved.
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
;;;
(in-package :common-lisp-user)

(eval-when (eval load)
  (push :bigpink *features*)
  (push :cltl2 *features*)
  (require :asdf))

(excl:defsystem :cl-ppcre
    (:default-pathname
        #+:mswindows
        "c:/Users/sawada/prj/CafeOBJ/cl-ppcre/"
      #-:mswindows
      "cl-ppcre/"
      :default-package :cl-ppcre)
  (:definitions
      "specials"
      (:serial
       "util"
       "errors"
       "charset"
       "charmap"
       "chartest"
       #-:use-acl-regexp2-engine
       "lexer"
       #-:use-acl-regexp2-engine
       "parser"
       #-:use-acl-regexp2-engine
       "regex-class"
       #-:use-acl-regexp2-engine
       "regex-class-util"
       #-:use-acl-regexp2-engine
       "convert"
       #-:use-acl-regexp2-engine
       "optimize"
       #-:use-acl-regexp2-engine
       "closures"
       #-:use-acl-regexp2-engine
       "repetition-closures"
       #-:use-acl-regexp2-engine
       "scanner"
       "api")))

(excl:defsystem :comlib
    (:default-pathname 
        #+:mswindows 
        "c:/Users/sawada/prj/CafeOBJ/comlib/"
      #-:mswindows
      "comlib/"
      :default-package "CHAOS")
  (:definitions
      "globals"
      "macros"
    "message"
    "error"
    (:serial
     "print-utils"
     "misc"
     "string"
     "list"
     "dag"
     "fsys"
     "tree-display"
     "lex"
     "reader"
     "let-over-lambda"
     ))
  )

(excl:defsystem :chaos
    (:default-pathname 
        #+:mswindows 
        "c:/Users/sawada/prj/CafeOBJ/chaos/"
      #-:mswindows
      "chaos/"
      :default-package "CHAOS")
  (:definitions
      :comlib
      (:module-group :primitives
                     (:serial
                      "primitives/term2"
                      "primitives/defterm"
                      "primitives/bobject2"
                      "primitives/bflags"
                      "primitives/absntax"
                      "primitives/script"
                      "primitives/op-theory"
                      "primitives/bmodexp"
                      "primitives/bmodule2"
                      "primitives/bview2"
                      "primitives/parse-modexp"
                      "primitives/normodexp"
                      "primitives/bsort"
                      "primitives/boperator"
                      "primitives/baxioms"
                      "primitives/bmacro"
                      "primitives/gen-eval"
                      "primitives/gen-print"
                      "primitives/context"
                      "primitives/term-utils"
                      "primitives/substitution"
                      "primitives/find"
                      "primitives/print-object"))
    (:serial
     (:module-group :term-parser
                    (:serial
                     "term-parser/parse-macro"
                     "term-parser/parse-engine"
                     "term-parser/parse-top"))
     (:module-group :e-match
                    (:serial
                     "e-match/match-utils"
                     "e-match/match-system"
                     "e-match/match-state"
                     "e-match/match-e"
                     "e-match/match-idem"
                     "e-match/match-z"
                     "e-match/match-a"
                     "e-match/match-c"
                     "e-match/match-az"
                     "e-match/match-cz"
                     "e-match/match-ac"
                     "e-match/match-acz"
                     "e-match/match"
                     "e-match/match2"))
     (:module-group :construct
                    (:parallel
                     "construct/sort"
                     "construct/operator"
                     "construct/variable"
                     "construct/match-method"
                     "construct/axiom"
                     "construct/gen-rule"
                     "construct/rwl"
                     "construct/beh"
                     "construct/module"
                     "construct/trs"))
     (:module-group :decafe
                    (:serial
                     "decafe/mutils"
                     "decafe/modmorph"
                     "decafe/mrmap"
                     "decafe/meval"
                     "decafe/view"
                     "decafe/mimport"))
     (:module-group :cafein
                    (:serial "cafein/rengine"
                             "cafein/cbred"
                             "cafein/reducer"))
     (:module-group :tools
                    (:parallel
                     "tools/regcheck"
                     "tools/regularize"
                     "tools/describe"
                     "tools/sort-tree"
                     "tools/module-tree"
                     "tools/show"
                     "tools/set"
                     "tools/op-check"
                     "tools/compat"
                     "tools/help"
                     "tools/inspect"
                     "tools/sensible"
                     ;; "psupport"
                     ))
     (:module-group :eval
                    (:parallel
                     "eval/eval-mod"
                     "eval/eval-ast"
                     "eval/eval-ast2"
                     "eval/chaos-top"))
     (:module-group :boot
                    (:serial
                     "boot/preproc"
                     "boot/prelude"
                     "boot/builtins"
                     "boot/meta"))
     (:module-group :tram
                    (:serial "tram/tram"))
     (:module-group :psup
                    (:serial "psup/psup"))

     )))

(excl:defsystem :chaosx
    (:default-pathname 
        #+:mswindows "c:/Users/sawada/prj/CafeOBJ/"
      #-:Mswindows "./"
      :default-package "CHAOS")
  (:definitions
      "chaos-package"
      "version"
    (:definitions
        :cl-ppcre
        :chaos
        (:serial
         (:module-group :thstuff
                        (:serial
                         "thstuff/parse-apply"
                         "thstuff/basics"
                         "thstuff/eval-match"
                         "thstuff/eval-apply"
                         "thstuff/cexec"
                         "thstuff/case"
                         "thstuff/proof-struct"
                         "thstuff/apply-tactic"
                         "thstuff/citp"
                         "thstuff/bterm-inspector"))
         (:module-group :bigpink
                        (:definitions
                            "BigPink/codes/types"
                            "BigPink/codes/glob"
                          "BigPink/codes/proof-sys"
                          (:serial
                           "BigPink/codes/syntax"
                           "BigPink/codes/index"
                           "BigPink/codes/butils"
                           "BigPink/codes/unify"
                           "BigPink/codes/clause"
                           "BigPink/codes/formula"
                           "BigPink/codes/modconv"
                           "BigPink/codes/weight"
                           "BigPink/codes/lrpo"
                           "BigPink/codes/resolve"
                           "BigPink/codes/paramod"
                           "BigPink/codes/demod"
                           "BigPink/codes/infer"
                           "BigPink/codes/sigmatch"
                           "BigPink/codes/refine"
                           "BigPink/codes/commands"
                           "BigPink/codes/inv")))
         (:module-group :cafeobj
                        (:definitions
                            "cafeobj/cafeobjvar"
                            (:serial
                             "cafeobj/creader"
                             "cafeobj/oldoc"
                             "cafeobj/define"
                             "cafeobj/trans-com"
                             "cafeobj/trans-decl"
                             ;; "cafeobj/command-proc"
                             "cafeobj/command-top"
                             "cafeobj/commands"
                             "cafeobj/declarations"
                             "cafeobj/cafeobj-top")))
         
         "acl-init"
         ))))


;;; EOF

