;;;-*- Mode: Lisp; Syntax:CommonLisp; Package:CHAOS; Base:10 -*-
;;; $Id: obj3syn.lisp,v 1.1.1.1 2003-06-19 08:30:33 sawada Exp $
(in-package :chaos)
#|=============================================================================
				  System:CHAOS
				  Module: obj3
			       File: obj3syn.lisp
==============================================================================|#

;;;=============================================================================
;;; Schema based generalized reader based on OBJ3 implementation.
;;;=============================================================================
(defvar *obj3-schemas* nil)
(defun obj3-parse ()
  (reader 'Top-form *obj3-schemas*))

;;;=============================================================================
;;; OBJ3 module schemas.
;;;-----------------------------------------------------------------------------

(eval-when (eval load)
  (setf *obj3-schemas*
	'(
	  (Top-form
	   (:one-of
	    ((:+ mod module object obj) :symbol (:optional (:! Params)) is)
	     (:many-of
	      ((:+ dfn define) :symbol is :modexp |.|)
	      ((:+ ex extending) :modexp |.|)
	      ((:+ pr protecting) :modexp |.|)
	      ((:+ us using) :modexp |.|)
	      ((:+ inc including) :modexp |.|) ;@
	      ((:+ sort sorts) :sorts |.|)
	      (bsort :symbol (:call (read)) |.|)
	      ((:+ psort principal-sort) :sort |.|)
	      ((:+ subsort subsorts) (:upto (< |.|) :sorts)
	       :append (:seq-of < (:upto (< |.|) :sorts)) |.|)
	      ((:+ op ops) (:! Op-pattern) |:| :sorts -> :sort
	       (:optional (:! Attr)) |.|)
	      (let :symbol (:optional |:| :sort) = :term |.|)
	      ((:+ var vars) :symbols |:| :sort |.|)
	      (vars-of (:optional :modexp) |.|)
	      (as :sort |:| :term if :term |.|)
	      (op-as (:! Op-pattern) |:| :sorts -> :sort
		     for :term if (:upto ("[" ".") :term)
		     (:optional (:! Attr)) |.|)
	      (eq :term = :term |.|)
	      ((:+ ceq cq) :term = :term if :term |.|)
	      ((:+ beq bq) :term = (:call (read)) |.|)
	      ((:+ cbeq cbq) :term = (:call (read))
	       if :term |.|)
	      ((:+ trans trns ) :term => :term |.|)
	      ((:+ ctrans ctrns) :term => :term if :term |.|)
	      ((:+ btrans btrns) :term => :term |.|)
	      ((:+ bctrans bctrns) :term => :term if :term |.|)
	      ((:+ ---> ***>) :comment)
	      ((:+ --- ***) :commentlong)
	      (parse :term |.|)
	      (ev (:call (read)))
	      ([ (:seq-of :term) ])
	      )
	     (:+ endo jbo endm end |}|)
	     )
	   ((:+ theory th) :symbol (:optional (:! Params)) is
	    (:many-of
	     ((:+ dfn define) :symbol is :modexp |.|)
	     ((:+ ex extending) :modexp |.|)
	     ((:+ pr protecting) :modexp |.|)
	     ((:+ us using) :modexp |.|)
	     ((:+ inc including) :modexp |.|)
	     ((:+ sort sorts) :sorts |.|)
	     ((:+ psort principal-sort) :sort |.|)
	     ((:+ subsort subsorts) (:upto (< |.|) :sorts)
	      :append (:seq-of < (:upto (< |.|) :sorts)) |.|)
	     ((:+ op ops) (:! Op-pattern) |:| :sorts -> :sort
	      (:optional (:! Attr)) |.|)
	     (let :symbol (:optional |:| :sort) = :term |.|)
	     ((:+ var vars) :symbols |:| :sort |.|)
	     (vars-of (:optional :modexp) |.|) ;@
	     (as :sort |:| :term if :term |.|)
	     (op-as (:! Op-pattern) |:| :sorts -> :sort
		    for :term if (:upto ("[" ".") :term)
		    (:optional (:! Attr)) |.|)
	     (eq :term = :term |.|)
	     ((:+ ceq cq) :term = :term if :term |.|)
	     ((:+ ceq cq) :term = :term if :term |.|)
	     ((:+ beq bq) :term = (:call (read)) |.|)
	     ((:+ cbeq cbq) :term = (:call (read))
	      if :term |.|)
	     ((:+ trans trns ) :term => :term |.|)
	     ((:+ ctrans ctrns) :term => :term if :term |.|)
	     ((:+ btrans btrns) :term => :term |.|)
	     ((:+ bctrans bctrns) :term => :term if :term |.|)
	     ((:+ ---> ***>) :comment)
	     ((:+ --- ***) :commentlong)
	     (parse :term |.|)
	     (ev (:call (read)))
	     ([ (:seq-of :term) ])
	     )
	    (:+ endth ht)
	    )
	   (view :symbol
	    :modexp
	    (:+ endv weiv endview)
	    )
	   ((:+ reduce red) (:if-present  in :modexp |:|) (:seq-of :term) |.|)
	   (make :symbol (:optional (:! Params)) is :modexp endm)
	   (test reduction (:if-present in :modexp |:|)
	    (:seq-of :term)
	    |:expect| (:seq-of :term) |.|)
	   (call-that :symbol |.|)
	   ((:+ red-loop rl) :symbol)
	   ((:+ input in) :symbol)
	   ((:+ --> ***>) :comment)
	   ((:+ --- ***) :commentlong)
	   (parse :term |.|)
	   ((:+ ev eval evq eval-quiet)
	    (:call (read)))
	   ((:+ show sh set do select)
	    (:seq-of :term) |.|)
	   (open :modexp |.|)	
	   (openr :modexp |.|)	
	   (close)
	   (eof)
	   ((:+ quit q))
	   ((:+ dfn define) :symbol is :modexp |.|)
	   ((:+ ex extending) :modexp |.|)
	   ((:+ pr protecting) :modexp |.|)
	   ((:+ us using) :modexp |.|)
	   ((:+ inc including) :modexp |.|)
	   ((:+ sort sorts) :sorts |.|)
	   (bsort :symbol (:call (read)) |.|)
	   ((:+ psort principal-sort) :sort |.|)
	   ((:+ subsort subsorts) (:upto (< |.|) :sorts)
	    :append (:seq-of < (:upto (< |.|) :sorts)) |.|)
	   ((:+ op ops) (:! Op-pattern) |:| :sorts -> :sort
	    (:optional (:! Attr)) |.|)
	   ((:+ opth opattr attr)
	    (:! Op-Pattern) |:|
	    (:optional :int) (:! Attr))
	   (let :symbol (:optional |:| :sort) = :term |.|)
	   ((:+ var vars) :symbols |:| :sort |.|)
	   (vars-of (:optional :modexp) |.|) ;@
	   (as :sort |:| :term if :term |.|)
	   (op-as (:! Op-pattern) |:| :sorts -> :sort
	    for :term if (:upto ("[" ".") :term)
	    (:optional (:! Attr)) |.|)
	   (eq :term = :term |.|)
	   ((:+ ceq cq) :term = :term if :term |.|)
	   ((:+ beq bq) :term = (:call (read)) |.|)
	   ((:+ cbeq cbq) :term = (:call (read)) |.|)
	   ((:+ cbeq cbq) :term = (:call (read))
	    if :term |.|)
	   ((:+ trans trns ) :term => :term |.|)
	   ((:+ ctrans ctrns) :term => :term if :term |.|)
	   ((:+ btrans btrns) :term => :term |.|)
	   ((:+ bctrans bctrns) :term => :term if :term 
	    if :term |.|)
	   (start :term |.|)
	   (apply (:one-of-default
		   (:symbol (:upto
			     (within at)
			     (:optional with :symbol
					= (:upto (|,| within at) :term)
					:append
					(:seq-of |,| :symbol
						     = (:upto (|,| within at) :term))))
			    (:+ within at)
			    (:upto (|.|)
				   ((:! Selector))
				   (:seq-of of ((:! Selector)))))
		   (-retr with sort :sort
			  (:+ within at) (:upto (|.|) ((:! Selector))
						(:seq-of of ((:! Selector)))))
		   (?))
	    |.|)
	   (cd :symbol)
	   (ls)
	   (pwd)
	   ([ (:seq-of :term) ])
	   (?))
	
	(Selector
	 (:one-of
	  (term) (top)
	  ({ :int :append (:seq-of |,| :int) })
	  (|(| (:seq-of :int) |)|)
	  (\[ :int (:optional |..| :int) \])))

	(Params (\[ (:! Param) :append (:seq-of |,| (:! Param)) \]))
	(Param 
	 (:one-of-default
	  (:symbols |::| (:upto (|,| \]) :modexp))
	  ((:+ ex extending us using pr protecting inc including) ;@
	   :symbols |::| (:upto (|,| \]) :modexp))))
	  
	(Supers (\[ (:! Super) :append (:seq-of |,| :modexp)))

	(Op-pattern ((:seq-of :term)))
	(Attr
	 (\[ (:many-of
	      ((:+ assoc comm idem associative commutative idempotent))
	      (selectors |(| :symbols |)|) ;not implemented
	      (|id:| :chaos-item)
	      (|identity:| :chaos-item)
	      (|idr:| :chaos-item)
	      (|identity-rules:| :chaos-item)
	      ((:pred general-read-numberp))
	      ((:+ prec precedence) :int) ;7/9/86
	      (|(| (:seq-of :int) |)|)
	      ((:+ strat strategy) |(| (:seq-of :int) |)|)
	      ((:+ gather gathering) |(| :symbols |)|)
	      ((:+ poly polymorphic) (:call (read)))
	      (memo)
	      (intrinsic))
	     \]))
	(SV-Pairs
	 ((:! Sv-pair) :append (:seq-of |,| (:! Sv-pair))))
	(Sv-Pair
	 (:symbol (:one-of (= |(| :term |)|)
			   (|:| :sort))
		  (:upto (|,| |}|))))
	))


