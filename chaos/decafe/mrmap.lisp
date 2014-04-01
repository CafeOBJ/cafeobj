;;;-*- Mode:LISP; Package:CHAOS; Base:10; Syntax:Common-lisp -*-
;;; $Id: mrmap.lisp,v 1.2 2010-06-17 08:23:18 sawada Exp $
(in-package :chaos)
#|==============================================================================
				 System: CHAOS
				 Module: deCafe
				File: mrmap.lisp
==============================================================================|#
#-:chaos-debug
(declaim (optimize (speed 3) (safety 0) #-GCL (debug 0)))
#+:chaos-debug
(declaim (optimize (speed 1) (safety 3) #-GCL (debug 3)))

;;; === DESCRIPTION ============================================================
;;; All of the type definitions and procedures for renaming sorts and operators.
;;; 

;;; ****************
;;; RENAME MAP UTILS____________________________________________________________
;;; ****************
;;; The definition (see "chaos/absntax.lisp"):
;;; (defterm rmap (%ast)
;;;  :visible (&rest map)
;;;  :print 'print-rename-map)

;;; COMPOSE-RENAMES : ren1 ren2 -> ren'
;;; rmap is just a function, so is associative.
;;; comose-renames composes renames, ren2 is applied first, then ren1.
;;;
(defun compose-renames (rmap-1 rmap-2)
  (unless rmap-1 (return-from compose-renames rmap-2))
  (unless rmap-2 (return-from compose-renames rmap-1))
  (let ((ren1 (if (%is-rmap rmap-1)
		  (%rmap-map rmap-1)
		  rmap-2))
	(ren2 (if (%is-rmap rmap-2)
		  (%rmap-map rmap-2)
		  rmap-2)))
    (let ((ops1 (cadr (assq '%ren-op ren1)))
	  (param1 (cadr (assq '%ren-param ren1)))
	  (sorts1 (cadr (assq '%ren-sort ren1))))
      (let ((ren2map (mapcar #'(lambda (map)
				 (cond ((%is-ren-sort map)
					(%ren-sort*
					 (nconc
					  (mapcar #'(lambda (x)
						      (list (car x)
							    (image-rename-sort sorts1
									       (cadr x))))
						  (%ren-sort-maps map))
					  sorts1)))
				       ((%is-ren-op map)
					(%ren-op*
					 (nconc
					  (mapcar #'(lambda (x)
						      (list (car x)
							    (image-rename-op ops1
									     (cadr x))))
						  (%ren-op-maps map))
					  ops1)))
				       ((%is-ren-param map)
					(%ren-param*
					 (nconc
					  (mapcar #'(lambda (x)
						      (list (car x)
							    (image-rename-param param1
										(cadr x))))
						  (%ren-op-maps map))
					  param1)))
				       (t (with-output-chaos-warning ()
					    (princ "renaming ")
					    (print-ast map)
					    (print-next)
					    (princ " is not implemented yet.")))))
			     ren2)))
	(apply #'%rmap* ren2map)))
    ))

(defun rmap-sort-match (srtnm srtpat)
  (or (equal srtnm srtpat)
      (and (consp srtpat) (null (cdr srtpat)) (equal srtnm (car srtpat)))))

;;; returns the mapped image of sort x respect to sort rename `ren'
;;;
(defun image-rename-sort (ren x)
  (let ((imap (find-if #'(lambda (y)
			   (rmap-sort-match x (car y)))
		       ren)))
    (if imap
	(cadr imap)
	x)))
;;;
(defun image-rename-op (ren x)
  (let ((imap (find-if #'(lambda (y)
			   (equal x (car y)))
		       ren)))
    (if imap
	(cadr imap)
	x)))

;;;
(defun image-rename-param (ren x)
  (let ((imap (find-if #'(lambda (y)
			   (equal x (car y)))
		       ren)))
    (if imap
	(cadr imap)
	x)))
		      
;;;
(defun inverse-image-rename-sort (ren x)
  (let ((imap (find-if #'(lambda (y)
			   (rmap-sort-match x (car y)))
		       ren)))
    (if imap
	(cadr imap)
	x)))

;;; Some versions for %*maps
;;;-----------------------------------------------------------------------------

(defun *image-rename-sort (map x)
  (let ((imap (find-if #'(lambda (y)
			   (sort= x (car y)))
		       map)))
    (if imap
	(cdr imap)
	x)))

(defun *image-rename-sorts (map sorts)
  (mapcar #'(lambda (x) (*image-rename-sort map x)) sorts))
	      
(defun *image-rename-method (map x)
  (let ((imap (find-if #'(lambda (y)
			  (eq x (car y)))
		      map)))
    (if imap
	(cdr imap)
	x)))



;;; REDUCE-RENAME : module rename-map -> rename-map
;;; removes rename elements which has no denotation on source components.
;;; result is a rename map re-ordered, sort map first, then operator map
;;; & then parameter map.
;;; each map is sorted (in terms of ob<).
;;;
(defun reduce-rename (mod rmap)
  (let ((ren (if (%is-rmap rmap)
		 (%rmap-map rmap)
		 rmap)))
    (let ((sort-res nil)
	  (op-res nil)
	  (param-res nil))
      (with-in-module (mod)
	(do* ((lst ren (cdr lst))
	      (map (car lst) (car lst)))
	     ((null lst))
	  (cond ((%is-ren-sort map)
		 (dolist (x map)
		   (when (let ((s (find-sort-in mod (car x))))
			   (and s (not (sort-is-hidden s))))
		     (push x sort-res))))
		((%is-ren-hsort map)
		 (dolist (x map)
		   (when (let ((s (find-sort-in mod (car x))))
			   (and s (sort-is-hidden s)))
		     (push x sort-res))))
		((%is-ren-op map)
		 (dolist (x map)
		   (when (find-qual-operators (car x) mod :functional)
		     (push x op-res))))
		((%is-ren-Bop map)
		 (dolist (x map)
		   (when (find-qual-operators (car x) mod :functional)
		     (push x op-res))))
		((%is-ren-param map)
		 (dolist (x map)
		   (when (find-parameterized-submodule (car x) mod)
		     (push x param-res))))
		(t nil))))
      (%rmap* (nconc (when sort-res (list (%ren-sort* (nreverse sort-res))))
		     (when op-res (list (%ren-op* (nreverse op-res))))
		     ;;; (when param-res (list (%ren-param* (nreverse param-res))))
		     )) 
     )))
    
;;; IS-RENAME-INJECTIVE : rmap -> bool
;;; returns non-nil iff the rename map is injective.
;;;
(defun is-rename-injective (rmap)
  (flet ((check-map (ren)
	   (dolist (x ren)
	     (when (find-if #'(lambda (y)
				(and (not (eq x y))
				     (not (equal (car x)
						 (car y)))
				     (equal (cadr x) (cadr y))))
				ren)
	       (return-from check-map :warn)))
	   (dolist (x ren)
	     (when  (find-if #'(lambda (y)
				 (and (not (eq x y))
				      (equal (car x) (car y))
				      (not (equal (cadr x) (cadr y)))))
			     ren)
	       (return-from check-map :invalid)))
	   :ok))
    ;;
    (let* ((ren (if (%is-rmap rmap)
		    (%rmap-map rmap)
		    rmap))
	   (sort-map (cadr (assq '%ren-sort ren)))
	   (op-map (cadr (assq '%ren-op ren))))
      #||
      (unless (and (check-map sort-map)
		   (check-map op-map))
	(return-from is-rename-injective nil))
      ||#
      (let ((sort-check (check-map sort-map))
	    (op-check (check-map op-map)))
	(if (and (eq sort-check :ok)
		 (eq op-check :ok))
	    :ok
	    (if sort-check
		sort-check
		op-check))))))


;;; ******************
;;; RENAME APPLICATION__________________________________________________________
;;; ******************

;;; RENAME-SORT : ModMorph Module Module Sortmap Sort NewName -> Sort
;;; This routine is used for generating 
;;;
;;; (1) If the given sort has an image in sort map of ModMorph, then returns it.
;;; (2) If the sort's module has its image in ModMorph, we find an identical sort
;;;     (with the same name, belongs to the same module) in the image, if found
;;;     returns it.
;;; (3) failure of (1) & (2) means that 
;;;     either (i)  given sort is not in domain of renaming,
;;;     or     (ii) given sort is in the domain, but its image is not generated yet. 
;;;     in both cases, we generate a new sort and returns it.
;;;     This is because renaming sort always requires us to create a new module.
;;;     The module generated sort belongs is;
;;;     (i) if the given sort's module is mapped by ModMorph, its image,
;;;     (ii) otherwise we generate a DUMMY module, and generate a sort in it.
;;;          The dummy module will be replaced later by a REAL renamed module
;;;          the sort should belongs to. By generating dummy, we can delay the
;;;          identification of the renamed module.
;;;
(defun rename-sort (map oldmod newmod old-sort &optional new-name)
  ;; 
  (when (err-sort-p old-sort)
    (return-from rename-sort old-sort))
  ;;
  (let ((val (assq old-sort (modmorph-sort map))))
    (if (and (null val)			; not mapped.
	     (null new-name)		; need not generate a sort.
	     (not (eq oldmod (sort-module old-sort))))
	;; there's no image and is not a sort of oldmod
	;; and we need not to generate a new sort.
	old-sort
      ;; may have image in module morphism or in sortmap.
      ;; or we must generate a sort with new-name.
      (if (sort-struct-p (cdr val))
	  ;; has image in map, and its a sort object.
	  (cdr val)
	;; has no sort object image and the sort is of oldmod,
	;; or no image and must create with new-name.
	(let* ((mod (sort-module old-sort))
	       (mod-image (cdr (assq mod (modmorph-module map))))
	       (old-sort-id (sort-id old-sort)))
	  ;; non nill mod-image means the sort's module is mapped by
	  ;; module morphism `map' to mod-image.
	  (let ((res (if mod-image
			 (find-if #'(lambda (x)
				      (and (equal (sort-id x) old-sort-id)
					   (eq (sort-module x) mod)))
				  (module-all-sorts mod-image)))))
	    ;;
	    (if res
		res
	      (let ((dmod mod-image))
		(unless dmod
		  (setq dmod 
		    (if (eq mod oldmod)	; (assq mod (module-all-submodules oldmod))
			  newmod
		      (create-dummy-module-then-map map
						    (sort-module old-sort)
						    (list old-sort new-name)))))
		(let ((newsort (!recreate-sort dmod old-sort new-name)))
		  (if val
		      (rplacd val newsort)
		    (push (cons old-sort newsort) (modmorph-sort map)))
		  (add-sort-to-module newsort dmod)
		  newsort)))))))))

(defun rename-sorts (map oldmod newmod sorts)
  (mapcar #'(lambda (x) (rename-sort map oldmod newmod x))
	  sorts))

;;; RENAME-RECORD
(defun rename-record (map oldmod newmod old-sort &optional new-name)
  (declare (ignore map oldmod newmod old-sort new-name))
  )


;;; RENAME-OP : ModMorph Module Module OpInfo OperatorName
;;;
;;; *side effect* ModMorph is changed.
;;;
(defun rename-op (map mod newmod opinfo op-name &optional theory-mod)
  (let ((old-method-info-table (module-opinfo-table mod))
	(opnm (if (%is-opref op-name)
		  (%opref-name op-name)
		op-name)))
    (when (check-enclosing-parens op-name)
      (setq opnm (butlast (cdr op-name))))
    ;;
    (dolist (method (opinfo-methods opinfo))
      (when (or (method-is-user-defined-error-method method)
		(not (method-is-error-method method)))
	;;**
	(when *on-modexp-debug*
	  (format t "~%[rename-op] op = ~s" (method-operator method old-method-info-table))
	  (format t "~% meth [~s] " method)
	  (format t "of module ~s" (method-module method)))
	;; **
	(let* ((op (method-operator method old-method-info-table))
	       (oldmod (if (eq mod (method-module method))
			   mod
			 (method-module method))))
	  (let ((amod (cdr (assq (method-module method)
				 (modmorph-module map)))))
	    (if amod
		(setq newmod amod)
	      (setq newmod
		(create-dummy-module-then-map map
					      (method-module method)
					      (list ':op
						    (operator-symbol op)
						    op-name)))))
	  ;;
	  (let ((arity (rename-sorts map oldmod newmod
				     (method-arity method)))
		(coarity (rename-sort map oldmod newmod
				      (method-coarity method)))
		(newop nil)
		(newmeth nil))
	    (declare (type list arity)
		     (type sort* coarity))
	    (with-in-module (newmod)
	      (unless (find-operator opnm (length arity) newmod)
		(setq newop (make-operator-internal opnm (length arity) newmod))
		(setf (operator-theory newop)
		  (rename-recreate-theory (operator-theory op)))
		(setf (operator-precedence newop)
		  (operator-precedence op))
		(setf (operator-associativity newop)
		  (operator-associativity op)))
	      (unless (setq newmeth (find-method-in newmod opnm arity coarity))
		(multiple-value-setq (newop newmeth)
		  (add-operator-declaration-to-module opnm
						      arity
						      coarity
						      newmod
						      (method-constructor method)
						      (method-behavioural method)
						      nil ;; (method-coherent method) -- set later
						      (method-is-user-defined-error-method method)))
		(setf (method-supplied-strategy newmeth)
		  (method-supplied-strategy method))
		(setf (method-precedence newmeth)
		  (method-precedence method))
		(setf (method-has-memo newmeth)
		  (method-has-memo method))
		(setf (method-is-meta-demod newmeth)
		  (method-is-meta-demod method))
		(setf (method-associativity newmeth)
		  (method-associativity method))
		(setf (method-theory newmeth)
		  (rename-recreate-theory
		   (method-theory method
				  (module-opinfo-table
				   (or theory-mod oldmod)))))
		(setf (method-derived-from newmeth) method)
		(setf (method-is-coherent newmeth)
		  (method-is-coherent method
				      (module-opinfo-table
				       (or theory-mod oldmod))))
		(compute-method-theory-info-for-matching newmeth)
		;; (push (cons method newmeth) (modmorph-op map))
		(if (method-is-user-defined-error-method method)
		    (push (cons method (cons :simple-error-map newmeth))
			  (modmorph-op map))
		  (push (cons method (cons :simple-map newmeth))
			(modmorph-op map)))))))))
    map))

;;;
;;; TRANSFER-METHOD
;;;
(defun transfer-method (module from-module method)
  (when (or (method-is-user-defined-error-method method)
	    (and (not (method-is-error-method method))
		 (not (method-is-for-regularity? method from-module))))
    (let ((from-opinfo (module-opinfo-table from-module))
	  (so (module-sort-order module))
	  new-opinfo
	  op)
      (setf op (method-operator method from-opinfo))
      (setf new-opinfo
	(and op
	     (dolist (x (module-all-operators module) nil)
	       (when (and (operator-eql op (opinfo-operator x))
			  (is-in-same-connected-component* (method-coarity method)
							   (method-coarity (car (opinfo-methods x)))
							   so))
		 (return x)))))
      (when *on-modexp-debug*
	(format t "~&[transfer-method]: transfering ~a from " (operator-symbol op))
	(print-modexp from-module)
	(format t " to")
	(print-modexp module))
      (unless new-opinfo
	(when *on-modexp-debug*
	  (format t "~& - creating new operator info for importing ~a.~a"
		  (operator-symbol op)
		  (make-module-print-name (operator-module op))))
	(setf new-opinfo (make-opinfo :operator op))
	(push new-opinfo (module-all-operators module)))
      (with-in-module (module)
	(let ((to-opinfo (module-opinfo-table module)))
	  (let ((method-info (get-method-info method to-opinfo)))
	    (unless method-info
	      (setf (get-method-info method to-opinfo)
		    (make-method-info method module op))
	      ))
	  (when (add-method-to-table new-opinfo method module)
	    (setf (method-theory method to-opinfo)
		  (method-theory method from-opinfo))
	    (setf (method-theory-info-for-matching method to-opinfo)
		  (method-theory-info-for-matching method from-opinfo))
	    )
	  )))))

(defun transfer-method-axioms (module from-module method)
  (with-in-module (module)
    (let ((from-opinfo (module-opinfo-table from-module))
	  (to-opinfo (module-opinfo-table module)))
      (dolist (rule (rule-ring-to-list (method-rules-with-same-top method
								   from-opinfo)))
	(add-rule-to-method (check-axiom-error-method module rule)
			    method
			    to-opinfo)
	(pushnew rule (module-all-rules module) :test #'rule-is-similar?))
      (dolist (r (reverse (method-rules-with-different-top method
							   from-opinfo)))
	(add-rule-to-method (check-axiom-error-method module r)
			    method
			    to-opinfo)
	(pushnew r (module-all-rules module) :test #'rule-is-similar?))
      )))

;;;
;;; RENAME-PARAMETER
;;; TODO

;;;
;;; REDUCE-RENAME-DUMMY
;;;
(defun reduce-rename-dummy (map mod newmod)
  (when *on-modexp-debug*
    (format t "~%[reduce-rename-dummy] : ")
    (print-modexp mod) (princ " ==> ") (print-modexp newmod)
    (format t "~% ... ~a  --> ~a" (module-print-name mod) (module-print-name newmod))
    (format t "~% - map = ") (print-mapping map))
  ;; -------------------------------------------------------
  (let ((modmap (modmorph-module map)))	; module map
    ;; sort mapping
    (dolist (sm (modmorph-sort map))
      (let ((s1 (car sm))		; source
	    (s2 (cdr sm)))		; target
	(let* ((mod1 (sort-module s1))
	       (a1 (cdr (assq mod1 modmap)))
	       (mod2 (sort-module s2)))
	  (when *on-modexp-debug*
	    (format t "~& - source = ~a.~a" (string (sort-id s1)) (module-print-name mod1))
	    ;; (print-modexp mod1)
	    (format t "~& - target = ~a.~a" (string (sort-id s2)) (module-print-name mod2))
	    ;; (print-modexp mod2)
	    (when a1
	      (format t "~& - module of sort ~a is mapped to ~a" (string (sort-id s1)) (module-print-name a1))))
	  ;;
	  (if (and a1 (not (eq a1 mod2)))
	      ;; s1.mod1 -> s2.mod2
	      ;;    mod1 -> a1 =/= mod2
	      ;; module of source sort is mapped and
	      ;; its image is not the same as of target sort.
	      (progn
		;; s2.mod2 ==> s2.a1
		(when *on-modexp-debug*
		  (format t "~& - changes target module to ")
		  (print-modexp a1))
		(setf (sort-module s2) a1)
		(add-sort-to-module s2 newmod))
	    ;; source sort is generated in dummy module.
	    ;; mod1 is not mapped,
	    ;; or s1.mod1 -> s2.mod2
	    ;;       mod1 -> a1 == mod2
	    (if (or ;; (and a1 (eq a1 mod2))
		    ;; s1.mod1 -> s2.mod2
		    ;; mod1 -> a1 = mod2
		    (module-is-rename-dummy-for mod1 mod))
		(progn
		  (when *on-modexp-debug*
		    (format t "~& - changes target module to ~a" (module-print-name newmod))
		    (setf (sort-module s2) newmod)
		    (add-sort-to-module s2 newmod))))))))
    ;;
    ;; operator mapping
    ;; (method1 :simple-map . method2)
    (dolist (om (modmorph-op map))
      (let ((method-1 (car om))		; source
	    (method-2 (cddr om)))	; target
	(let* ((mod1 (method-module method-1))
	       (a1 (cdr (assq mod1 modmap))))
	  (if (and a1 
		   (not (eq a1 (method-module method-2))))
	      (progn
		(setf (method-module method-2) a1)
		(modmorph-check-rank newmod mod map method-2)
		(transfer-method newmod mod method-2))
	    (if (or ;; (and a1 (is-dummy-module a1))
		    (module-is-rename-dummy-for mod1 mod))
		(progn
		  (setf (method-module method-2) newmod)
		  (modmorph-check-rank newmod mod map method-2)
		  (transfer-method newmod mod method-2)))))))))

;;; FIX-SORT-RENAMING
;;; fix the following situation:
;;;   s1.mod1 --> s2.mod2
;;;   mod1 --> a1 (=/= mod2)
;;; 
(defun fix-sort-renaming (map newmod)
  (dolist (sm (modmorph-sort map))
    (let ((s1 (car sm))		; source
	  (s2 (cdr sm)))	; target
      (let* ((mod1 (sort-module s1))
	     (mod2 (sort-module s2))
	     (a1 (cdr (assq mod1 (modmorph-module map)))))
	;; s1.mod1 -> s2.mod2
	;;    mod1 -> a1
	;;
	(when (and a1 (not (eq a1 (sort-module s2))))
	  ;;---
	  (when *on-modexp-debug*
	    (format t "~&fix-sort-renaming : ")
	    (format t "~& - ~a." (string (sort-id s1)))
	    (print-modexp mod1)
	    (format t "~&   (=> ") (print-modexp a1)
	    (format t ") --> ~a." (string (sort-id s2))) (print-modexp mod2))
	  ;;--
	  (setf (module-sorts newmod) (remove s2 (module-sorts newmod)))
	  (setf (module-all-sorts newmod) (remove s2 (module-all-sorts newmod)))
	  (let ((srt (or (modmorph-find-sort-in a1 (sort-id s2))
			 (modmorph-find-sort-in mod2 (sort-id s2))
			 )))
	    ;; (break)
	    (unless srt (error "Sorry, PANIC! no sort image, could not fix."))
	    (add-sort-to-module srt newmod)
	    (rplacd sm srt)
	    (setf (sort-derived-from srt) s1)
	    )
	  )
	))
    ))
      
;;; FIX-METHOD-RENAMING
;;;
(defun fix-method-renaming (map newmod)
  (declare (ignore newmod))
  (let ((modmap (modmorph-module map)))
    (dolist (om (modmorph-op map))
      (let ((method-1 (car om))
            (method-2 (cddr om)))	; (source :simple-map . target)
        (let* ((mod1 (method-module method-1))
               (a1 (cdr (assq mod1 modmap))))
          (when (and a1 (not (eq a1 (method-module method-2))))
	    #||
	    (with-output-panic-message ()
	      (break)
	      (princ "sorry, please e-mail to sawada@sra.co.jp, say \"this happens\"")
	      (chaos-to-top))
	    ||#
	    (setf (method-module method-2) a1) ; is this really right?
	    ))))))

;;; RENAME-RECREATE-THEORY
;;; 
(defun rename-recreate-theory (thy)
  (if thy
      (if (theory-contains-identity thy)
	  (let ((zero (theory-zero thy)))
	    ;; (break)
	    (setq zero (cons '%to-rename zero))
	    (theory-make (theory-info thy) zero))
	  thy)
      nil))

;;; FIND-SOME-METHOD-IN
;;;
(defun find-some-method-in (module arity coarity theory)
  (declare (type module module)
	   (type list arity)
	   (type sort* coarity)
	   (type op-theory theory))
  (macrolet ((is-similar-theory? (th1_? th2_?)
	       (once-only (th1_? th2_?)
		 ` (and (if (theory-contains-associativity ,th1_?)
			    (theory-contains-associativity ,th2_?)
			    t)
			(if (theory-contains-commutativity ,th1_?)
			    (theory-contains-commutativity ,th2_?)
			    t)
			(if (theory-contains-identity ,th1_?)
			    (theory-contains-identity ,th2_?)
			    t)))))
    (let ((opinfos (find-operators-num-args module (length arity))))
      (dolist (opinfo opinfos)
	(let ((val (remove-if-not
		    #'(lambda (method)
			(and (sort= coarity (method-coarity method))
			     (= (the fixnum (length arity))
				(the fixnum (length (method-arity method))))
			     (every #'(lambda (s1 s2)
					(and s1 s2
					     (equal (sort-id s1) (sort-id s2))))
				    arity
				    (method-arity method))
			     (is-similar-theory? theory
						 (method-theory method
								(module-opinfo-table
								 module)))
			     ))
		    (opinfo-methods opinfo))))
	  (when (and val (null (cdr val)))
	    (return-from find-some-method-in (car val)))))
      nil)))

(defun recreate-renamed-sort (mod ren srt)
  (let ((num 0)
	(srtnm (sort-id srt))
	(im nil))
    (declare (type fixnum num))
    (dolist (s (module-all-sorts mod))
      (when (equal srtnm (sort-id s))
	(unless im (setq im s))
	(incf num)))
    (if (= 1 num)
	im
	(let ((renmod (eval-modexp (%rename* (sort-module srt)  ren))))
	  (dolist (s (module-all-sorts renmod))
	    (when (and (eq renmod (sort-module s))
		       (equal srtnm (sort-id s)))
	      (return s)))
	  ))))

#|| the followings are not yet implemented properly.

(defun find-renamed-method-named-in (srtmap mod opn)
  (let ((opnm (if (check-enclosing-parens opn) (butlast (cdr opn)) opn)))
    (if (member "->" (member ":" opnm :test #'equal) :test #'equal)
	(let* ((pos1 (position ":" opnm :from-end t :test #'equal))
	       (pos2 (position "->" opnm :from-end t :test #'equal))
	       (op-symbol (subseq opnm 0 pos1))
	       (ar (subseq opnm (1+ pos1) pos2))
	       (coar (nth (1+ pos2) opnm)))
	  (let ((val (find-method-from-rank ; * TO DO *--------
		      mod
		      (append
		       op-symbol '(":")
		       (mapcar #'(lambda (x)
				   (sort-id (*image-rename-sort srtmap x)))
			       ar)
		       '("->")
		       (sort-id (*image-rename-sort srtmap coar)))
		      )))
	    (when val (list val))))
	(find-method-named-in mod opn))))
  
(defun find-renamed-method-named-in-sort (srtmap mod srt opn)
  (declare (ignore srtmap mod srt opn))
  (break "find-renamed-mehtod-named-in-sort: not yet")
  )

||#

;;; EOF
