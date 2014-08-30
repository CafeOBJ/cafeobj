;;;-*-Mode:LISP; Package: Chaos; Base:10; Syntax:Common-lisp -*-
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
#|==============================================================================
				 System: Chaos
			     Module: trs-comp.chaos
			      File: eoperator.lisp
===============================================================================|#

;;;=============================================================================
;;; OPERATOR CODING
;;;=============================================================================

;;; operator is coded in 24bits integers (assume this fixnum).

;;; *******************
;;; operator-coding-map
;;; *******************

;;;  entry                 value
;;;  ----------------------------
;;;  name(id,num-args) ->  code

(defun encode-operators (module)
  (let ((res nil))
    (do ((opinfo-list (module-all-operators module)
		      (cdr opinfo-list))
	 (i 0 (1+ i)))
	((endp opinfo-list))
      (declare (type fixnum i))
      (let ((op-name (operator-name (caar opinfo-list))))
	(push (cons op-name i) res)))
    res))

(defmacro get-opertor-encoding-entry (operator map)
  ` (let ((val (assoc (operator-name ,op) ,map :test #'equal)))
      (unless val
	(error "get-operator-encoding-entry, no entry for op!")
	(print-chaos-object operator))
      val))

(defmacro operator-to-code (op eop-map)
  `(cdr (get-operator-encoding-entry op eop-map)))

(defmacro get-operator-decoding-entry (code map)
  ` (let ((val (find-if #'(lambda(x) (= ,code (cdr x))) ,map)))
      (unless val
	(error "get-operator-decoding-entry, no entry for code ~d!." code))
      val))

(defmacro code-to-operator (code eop-map)
  `(cdr (get-operator-decoding-entry ,code ,eop-map)))


;;; CODED OPERATOR INFORMATIONS
;;; gathers infos while parsing & rewriting.

  