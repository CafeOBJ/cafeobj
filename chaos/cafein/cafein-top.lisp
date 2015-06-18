;;;-*-Mode:LISP; Package: CHAOS; Base:10; Syntax:Common-lisp -*-
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
(in-package :chaos)
#|=============================================================================
                                  System:CHAOS
                                 Module:cafein
                              File:cafein-top.lisp
=============================================================================|#

;;;=============================================================================
;;;                  CafeIn Termrewriting system top-level
;;;=============================================================================

;;; CafeIn COMMANDS
(defvar *cafein-commands* nil)
(eval-when (:execute :load-toplevel)
  (setq *cafein-commands*
        '((top-commands
           (:one-of
            ((:+ match unify) (:seq-of :term) to (:seq-of :term) |.|)
            (parse (:if-present  in :modexp |:|) (:seq-of :term) |.|)
            ((:+ lisp ev eval evq lispq)
             (:call (read)))
            ((:+ show sh set select describe desc) ; do 
             (:seq-of :top-opname))
            (#\^D)
            (eof)
            ((:+ quit q))
            ;; theorem proving stuff.
            (start :term |.|)
            ;; apply
            (apply (:one-of-default
                    (:symbol (:upto
                              (within at)
                              (:optional with :symbol
                                         = (:upto (|,| within at) :term)
                                         :append
                                         (:seq-of |,| :symbol
                                                  = (:upto (|,| within at) :term))))
                             (:+ within at)
                             (:one-of
                              ((:+ top term subterm))
                              ((:+ |(| |{| |[|)
                               :unread
                               ((:! Selector))
                               (:seq-of of ((:! Selector)))
                               |.|)))
                    (?)))
            ;;
            (choose (:one-of
                     ((:+ top term subterm))
                     ((:+ |(| |{| |[|)
                      :unread
                      ((:! Selector))
                      (:seq-of of ((:! Selector)))
                      |.|)))

            (find (:+ rule -rule +rule rules -rules +rules))
            (cd :symbol)
            #-(or GCL LUCID CMU) (ls :symbol)
            #+(or GCL LUCID CMU) (ls :top-term)
            (pwd)
            (! :top-term)
            (?)
            ))
        (Selector
           (:one-of
            ;; (term) (top) (subterm)
            (|{| :int :append (:seq-of |,| :int) |}|)
            (|(| (:seq-of :int) |)|)
            (\[ :int (:optional |..| :int) \])))
          )))

(defun cafein-parse ()
  (reader 'top-commands *cafein-commands*))

;;; EOF
