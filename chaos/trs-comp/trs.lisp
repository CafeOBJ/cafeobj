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

(defstruct (chaos-trs (:print-function print-chaos-trs))
  module
  sort-name-map
  op-info-map)

(defun cafeobj->trs (mod &optional trs)
  (let ((trs (if trs
		 (setf (chaos-trs-module trs) mod)
		 (make-chaos-trs :module mod))))
    (dolist (s (module-all-sorts mod))
      (push (cons s (chaos-trs-make-sort-name s))
	    (chaos-trs-sort-name-map trs)))
    (dolist (opinfo (module-all-operators mod))
      (dolist (meth (opinfo-methods opinfo))
	(unless (method-is-error-method meth)
	  (push (cons meth (chaos-trs-make-method-info meth trs))
		(chaos-trs-op-info-map trs)))))
    trs))

(defun print-chaos-trs (trs &optional (stream *standard-output*)
			    &rest ignore)
  (declare (ignore ignore))
  (let ((*print-circle* nil)
	(*print-case* :downcase))
    (prin1
     (make-trs-print-form trs)
     stream)))

(defun chaos-trs-get-sort-graph (trs)
  (let* ((mod (chaos-trs-module trs))
	 (so (module-sort-order trs))
	 (snmlist (chaos-trs-sort-name-map trs))
	 (sub-rel nil))
    (dolist (s (module-all-sorts mod))
      (let ((supers (direct-supersorts s so)))
	(if supers
	    (if (and (null (cdr supers))
		     (err-sort-p (car supers)))
		(if (sort-is-hidden s)
		    (push (list (cdr (assq s snmlist))
				sup-huniversal-sort-name)
			  sub-rel)
		    (push (list (cdr (assq s snmlist))
				sup-universal-sort-name)
			  sub-rel))
		;;
		(dolist (sup supers)
		  (push (list (cdr (assq s snmlist))
			      (cdr (assq sup snmlist)))
			sub-rel))))))
    (nreverse sub-rel)))

(defun make-trs-print-form (trs)
  (let ((mod (chaos-trs-module trs)))
    (with-in-module (mod)
      (let ((so (module-sort-order mod)))
	`(:trs
	  ,(make-module-print-name2 mod)
	  :sorts
	  ,(mapcar #'cdr (chaos-trs-sort-name-map))
	  :subsorts
	  ,(chaos-trs-get-sort-graph trs)
	  :operators
	  ,(mapcar #'cdr (chaos-trs-op-info-map trs))
	  :axioms
	  ,(



(defun chaos-trs-make-sort-name (sort)
  (reduce #'(lambda (x y) (concatenate 'string x y))
	  (list (string (sort-id sort))
		"."
		(make-module-print-name2 (sort-module sort)))))

(defun chaos-trs-make-method-info (meth trs)
  (let ((mod (chaos-trs-module trs))
	(smap (chaos-trs-sort-name-map trs)))
    (macrolet ((get-sort-mapped (s)
		 (or (cdr (assq ,s smap))
		     (with-output-panic-message ()
		       (format t "could not find sort ~a in trs."
			       (sort-id ,s))))))
      (let ((nam (reduce #'(lambda (x y) (concatenate 'string x y)))
	      (method-symbol meth))
	    (arity (mapcar #'(lambda (x) (get-sort-maped x))
			   (method-arity meth)))
	    (coarity (get-sort-mapped (method-coarity meth)))
	    (attrs (chaos-trs-make-attr-info meth mod)))
	(list* nam arity coarity attrs)))))

(defun chaos-trs-make-attr-info (meth mod)
  (with-in-module (mod)
    (let ((theory (method-theory meth))
	  (strat (method-rewrite-strategy meth))
	  (constr (method-constructor meth))
	  (prec (method-precedence meth))
	  (assoc (method-associativity meth))
	  (res nil))
      (when (and (eql 0 (car (last strat)))
		 (member 0 (butlast strat)))
	(setq strat (butlast strat)))
      (let ((th-info (theory-info theory))
	    (zero (theory-zero theory)))
	(when (not (eq th-info the-e-property))
	  (when (or (theory-info-is-AC th-info)
		    (theory-info-is-A th-info)
		    (theory-info-is-AI th-info)
		    (theory-info-is-AZ th-info)
		    (theory-info-is-AIZ th-info)
		    (theory-info-is-ACI th-info)
		    (theory-info-is-ACZ th-info)
		    (theory-info-is-ACIZ th-info))
	    (push '(:assoc) res))
	  (when (or (theory-info-is-AC th-info)
		    (theory-info-is-C th-info)
		    (theory-info-is-CI th-info)
		    (theory-info-is-CZ th-info)
		    (theory-info-is-CIZ th-info)
		    (theory-info-is-ACI th-info)
		    (theory-info-is-ACZ th-info)
		    (theory-info-is-ACIZ th-info))
	    (push '(:comm) res))
	  (when (or (theory-info-is-I th-info)
		    (theory-info-is-IZ th-info)
		    (theory-info-is-CI th-info)
		    (theory-info-is-CIZ th-info)
		    (theory-info-is-AI th-info)
		    (theory-info-is-AIZ th-info)
		    (theory-info-is-ACI th-info)
		    (theory-info-is-ACIZ th-info))
	    (push '(:idem) res))
	  (when zero
	    (let ((mth (sup-make-term-method-info (car zero) mod)))
	      (if (null (cdr zero))
		  (push (list ':id mth) res)
		  (push (list ':idr mth) res))))
	  ))
      (when strat
	(push (list ':strat strat) res))
      (when prec
	(push (list ':prec prec) res))
      (when constr
	(push '(:constr) res))
      (when assoc
	(push (if (eq :left assoc)
		  '(:l-assoc)
		  '(:r-assoc))
	      res)))))
			 

(defun chaos-trs-make-term-form (term mod)
  (cond ((term-is-lisp-form? term)
	 (list :lisp (lisp-form-original-form term)))
	((term-is-builtin-constant? term)
	 (list :builtin-value
	       (term-builtin-value term)
	       (sup-make-sort-info (term-sort term))))
	((term-is-variable? term)
	 (list :var (string (variable-name term))
	       (sup-make-sort-info (variable-sort term))))
	((term-is-applform? term)
	 (list* :op
		(sup-make-opname (term-head term))
		(sup-make-sort-info (term-sort term))
		(mapcar #'(lambda (x)
			    (sup-make-term-form x mod))
			(term-subterms term))))
	(t (with-output-panic-message ()
	     (format t "unknown term : ")
	     (term-print term)))))

;;; EOF
