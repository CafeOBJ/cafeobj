;;;-*- Mode:LISP; Package:CHAOS; Base:10; Syntax:Common-lisp -*-
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
(in-package :chaos)
#|==============================================================================
                                 System: CHAOS
                               Module: primitives
                               File: script.lisp
==============================================================================|#
#-:chaos-debug
(declaim (optimize (speed 3) (safety 0) #-GCL (debug 0)))
#+:chaos-debug
(declaim (optimize (speed 1) (safety 3) #-GCL (debug 3)))

;;; ** DESCRIPTION =============================================================
;;;
;;; Denfinitions of abstract syntax of Chaos script language.
;;; Each evaluator would be found in eval-ast2.lisp
;;;

;;; =============================================================================
;;; SCRIPT : defines the common structure of script language.
;;; -----------------------------------------------------------------------------

;;; ****
;;; EVAL : evaluate given ast.
;;; ****
(defterm eval (%script)
  :visible (form)
  :eval eval-form)

;;; *****
;;; ERROR : represents error status
;;; *****
(defterm error (%script)
  :visible (type                        ; one of :warn, :error, :fatal?
            message)                    ; string
  :eval process-error)
  
;;; *********
;;; LISP-EVAL : evaluate as lisp form.
;;; *********
(defterm lisp-eval (%script)
  :visible (form)
  :eval eval-lisp-form)

;;; ************
;;; DYNA-COMMENT : dynamic comment.
;;; ************
(defterm dyna-comment (%script)
  :visible (form)
  :eval print-dyna-comment)

;;; ******
;;; REDUCE : reduce term. 
;;; ******
;;; what is the difference with :eval?

(defterm reduce (%script)
  :visible (term &optional (module *current-module*)
                           (mode :red) return-text)
  :eval perform-reduction)

;;; ***********
;;; TEST-REDUCE : test reduction
;;; ***********
(defterm test-reduce (%script)
  :visible (term expect &optional (module *current-module*)
                                  (mode :red) return-text)
  :eval perform-test-reduction)

;;; *****
;;; PARSE : parse term.
;;; *****
(defterm parse (%script)
  :visible (term &optional (module *current-module*)
                           return-text)
  :eval do-parse-term)

;;; *****
;;; INPUT : input Chaos program from file.
;;; *****
(defterm input (%script)
  :visible (file-name
            &optional (load-path *chaos-libpath*)
                      (proc 'process-cafeobj-input)
                      (suffixes '(".bin" ".cafe" ".mod"))
                      args)
  :eval eval-input-file)

;;; *****************
;;; TRACE/TRACE-WHOLE
;;; *****************
(defterm trace (%script)
  :visible (flag)
  :eval eval-trace)

(defterm trace-whole (%script)
  :visible (flag)
  :eval eval-trace-whole)

;;; *******
;;; STEPPER
;;; *******
(defterm step (%script)
  :visible (flag)
  :eval eval-step)

;;; ***************
;;; DESCRIBE-MODULE 
;;; ***************
(defterm describe-module (%script)
  :visible (&optional (modexp *current-module*))
  :eval eval-describe-module)

;;; ***********
;;; OPEN-MODULE
;;; ***********
(defterm open-module (%script)
  :visible (&optional (modexp *current-module*))
  :eval eval-open-module)

;;; ************
;;; CLOSE-MODULE
;;; ************
(defterm close-module (%script)
  :visible (&rest ignore)
  :eval eval-close-module)

;;; ****
;;; SAVE
;;; ****
(defterm save (%script)
  :visible (file)
  :eval eval-save)

;;; *******
;;; RESTORE
;;; *******
(defterm restore (%script)
  :visible (file)
  :eval eval-restore)

;;; *****
;;; RESET
;;; *****
(defterm reset (%script)
  :eval eval-reset-system)

;;; **********
;;; FULL-RESET
;;; **********
(defterm full-reset (%script)
  :eval eval-full-reset)

;;; ************
;;; LOAD-PRELUDE
;;; ************
(defterm load-prelude (%script)
  :visible (file &optional
                 (processor 'process-cafeobj-input))
  :eval eval-load-prelude)

;;; * Follwing two (start, apply) are defined in
;;;   parse-apply.THSTUFF
;;; ---------------------------------------------

#| 
;;; *****
;;; START
;;; *****
(defterm start (%script)
  :visible (target)                     ; terget term
  :eval eval-start-th
  )

;;; *****
;;; APPLY
;;; *****
(defterm apply (%script)
  :visible (action                      ; action to be performed, one-of
                                        ;  :apply, :reduce, :print, :help.
            rule                        ; rule specifier to be applied.
            bindings                    ; list of variable bindings.
            at                          ; one of :at, :within.
            selectors)                  ; list of selectors.
  :eval eval-apply-command)
|#

;;; *******
;;; PROVIDE
;;; *******
(defterm provide (%script)
  :visible (feature)                    ; feature to be provided.
  :eval eval-provide-command)

;;; *******
;;; REQUIRE
;;; *******
(defterm require (%script)
  :visible (feature                     ; required feature
            &optional
            (proc 'process-cafeobj-input) ; process to evaluating fomrs.
            file                        ; filename
            )
  :eval eval-require-command)

;;; *************
;;; REWRITE-COUNT
;;; *************
(defterm rewrite-count (%script)
  :visible (limit)                      ; limitation
  :eval eval-rewrite-count-limit)

;;; *******
;;; STOP-AT
;;; *******
(defterm stop-at (%script)
  :visible (pattern)
  :eval eval-stop-at)

;;; **************
;;; PROTECT-MODULE
;;; **************
(defterm protect (%script)
  :visible (module                      ; module to be set protect mode
            mode                        ; mode = :set | :unset
            )
  :eval eval-protect)

;;; *******
;;; DRIBBLE
;;; *******
(defterm dribble (%script)
  :visible (file)
  :eval eval-dribble)

;;; **********
;;; SAVE-CHAOS
;;; **********
(defterm save-chaos (%script)
  :visible (top
            file)
  :eval eval-save-chaos)

;;; **
;;; LS
;;; **
(defterm ls (%script)
  :visible (&optional (dir "."))
  :eval eval-ls)

;;; ***
;;; PWD
;;; ***
(defterm pwd (%script)
  :eval eval-pwd)

;;; *****
;;; SHELL
;;; *****
(defterm shell (%script)
  :visible (command)
  :eval eval-shell)

;;; **
;;; CD
;;; **
(defterm cd (%script)
  :visible (directory)
  :eval eval-cd)

;;; *****
;;; PUSHD
;;; *****
(defterm pushd (%script)
  :visible (directory)
  :eval eval-pushd)

;;; ****
;;; POPD
;;; ****
(defterm popd (%script)
  :visible (&optional num)
  :eval eval-popd)

;;; ****
;;; DIRS
;;; ****
(defterm dirs (%script)
  :eval eval-dirs)

;;; ****
;;; SHOW
;;; ****
(defterm show (%script)
  :visible (args)
  :eval eval-show)

;;; ********
;;; DESCRIBE
;;; ********
(defterm describe (%script)
  :visible (args)
  :eval eval-describe)

;;; ******
;;; SELECT
;;; ******
(defterm select (%script)
  :visible (modexp)
  :eval eval-select)

;;; ***
;;; SET
;;; ***
(defterm set (%script)
  :visible (switch
            value)
  :eval eval-set)

;;; **********
;;; REGULARIZE
;;; **********
(defterm regularize (%script)
  :visible (modexp)
  :eval eval-regularize)

;;; *****
;;; CHECK
;;; *****
(defterm check (%script)
  :visible (what
            args)
  :eval eval-check)

;;; *************
;;; TRAM COMPILER
;;; *************
(defterm tram (%script)
  :visible (command
            modexp
            term
            debug)
  :eval eval-tram)

;;; *********
;;; AUTO LOAD
;;; *********
(defterm autoload (%script)
  :visible (mod-name
            file)
  :eval eval-autoload)

;;; ***********
;;; NO AUTOLOAD
;;; ***********
(defterm no-autoload (%script)
  :visible (mod-name)
  :eval eval-no-autoload)

;;; ******************************
;;; CIRCULAR COINDUCTIVE REWRITING
;;; ******************************

(defterm cbred (%script)
  :visible (module
            lhs
            rhs)
  :eval eval-cbred)

;;; **********************
;;; invoke Chaos Top Level
;;; **********************
(defterm chaos (%script)
  :visible (&optional parameters)
  :eval eval-chaos-top
  )

;;; *****************
;;; continue
;;; for RWL =(_,_)=> 
;;; *****************
(defterm continue (%script)
  :visible (&optional num)
  :eval rwl-cont
  )

;;; *******
;;; WHAT IS
;;; *******
(defterm what-is (%script)
  :visible (name &optional (module *current-module*))
  :eval eval-what-is)

;;; *******
;;; INSPECT
;;; *******
(defterm inspect (%script)
  :visible (&optional (modexp *current-module*))
  :eval eval-inspect)

;;; *******
;;; LOOK-UP
;;; *******
(defterm look-up (%script)
  :visible (name &optional (module *current-module*))
  :eval eval-look-up)

;;; *********
;;; DELIMITER
;;; *********
(defterm delimiter (%script)
  :visible (operation
            char-list)
  :eval eval-delimiter)
            
;;; ****
;;; CASE
;;; case (<Term>) on (<Modexp>) as (<Name>) : <GoalTerm> .
;;; ****
(defterm scase (%script)
  :visible (bool-term module name body goal-term)
  :eval perform-case-reduction)

;;; ******
;;; GENDOC
;;; gendoc <pathname>
;;; *****

(defterm gendoc (%script)
  :visible (file)
  :eval eval-gendoc)

;;; EOF
