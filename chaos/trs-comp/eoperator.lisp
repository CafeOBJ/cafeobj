;;;-*-Mode:LISP; Package: Chaos; Base:10; Syntax:Common-lisp -*-
;;; $Id: eoperator.lisp,v 1.1.1.1 2003-06-19 08:29:44 sawada Exp $
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

  