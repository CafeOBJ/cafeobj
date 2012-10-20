;;;-*-Mode:LISP; Package: CHAOS; Base:10; Syntax:Common-lisp -*-
;;; $Id: cafein-top.lisp,v 1.1.1.1 2003-06-19 08:27:37 sawada Exp $
(in-package :chaos)
#|=============================================================================
				  System:CHAOS
				 Module:cafein
			      File:cafein-top.lisp
=============================================================================|#

;;;=============================================================================
;;; 		     CafeIn Termrewriting system top-level
;;;=============================================================================

;;; CafeIn COMMANDS
(defvar *cafein-commands* nil)
(eval-when (eval load)
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
