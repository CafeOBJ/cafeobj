;;;-*-Mode:LISP; Package: CHAOS; Base:10; Syntax:Common-lisp -*-
;;; $Id: cexec.lisp,v 1.17 2007-12-29 07:17:02 sawada Exp $
(in-package :chaos)
#|=============================================================================
				    System:CHAOS
				   Module:thstuff
			        File:proof-struct.lisp
 =============================================================================|#
#-:chaos-debug
(declaim (optimize (speed 3) (safety 0) #-GCL (debug 0)))
#+:chaos-debug
(declaim (optimize (speed 1) (safety 3) #-GCL (debug 3)))

;;; **************************************************************************
;;; Here we define a generic proof structure, i.e. a tree of 'goal's.

;;;---------------------------------------------------------------------------
;;; TACTIC
;;;
(eval-when (:compile-toplevel :execute :load-toplevel)
  (defstruct (tactic (:print-function pr-tactic))
    (name nil    :type symbol)		  ; name
    (executor nil :type (or null symbol)) ; tactic executor
    )

  (defparameter .tactic-si. (make-tactic :name :si
					 :executor 'apply-si)) ; Simultaneous Induction
  (defparameter .tactic-ca. (make-tactic :name :ca
					 :executor 'apply-ca))  ; Case Analysis
  (defparameter .tactic-tc. (make-tactic :name :tc
					 :executor 'apply-tc)) ; Theorem of Constants
  (defparameter .tactic-ip. (make-tactic :name :ip
					 :executor 'apply-ip)) ; Implication
  (defparameter .tactic-cs. (make-tactic :name :cs
					 :executor 'apply-cs)) ; Case Analysis on Sequences
  (defparameter .tactic-rd. (make-tactic :name :rd
					 :executor 'apply-rd)) ; Reduction

  (defparameter .all-builtin-tactics. (list .tactic-si. .tactic-ca. .tactic-tc. .tactic-ip. .tactic-cs. .tactic-rd.))

  ;; default tatics is a seriase of SI CA CS TC IP.
  (defparameter .default-tactics. (list .tactic-si. .tactic-ca. .tactic-cs. .tactic-tc. .tactic-ip.))

  ;; user defiled tactics: assoc list of (name . list-of-tactics)
  ;;
  (defvar .user-defined-tactics. nil)


  )

(defun canonicalize-tactic-name (name)
  (when (stringp name) (setq name (string-upcase name)))
  (when (symbolp name) (setq name (symbol-name name)))
  name)

(defun pr-tactic (tactic &optional (stream *standard-output*) &rest ignore)
  (declare (ignore ignore))
  (format stream "[~a]" (tactic-name tactic)))

;;; get-builtin-tactic : name -> tactic
;;; given a name returns a tactic with this name
;;; name can be symbol or string. the serach is done in case insensitive.
;;;
(defun get-builtin-tactic (name)
  (setq name (canonicalize-tactic-name name))
  (find-if #'(lambda (x) (string-equal name (symbol-name (tactic-name x)))) .all-builtin-tactics.))

;;;
;;; get-user-defined-tactic
;;;
(defun get-user-defined-tactic (name)
  (setq name (canonicalize-tactic-name name))
  (cdr (assoc name .user-defined-tactics.)))

;;;
;;; get-default-tactics
;;; returns the default tactics, i.e. (:si :ca :cs :tc :ip)
;;;
(defun get-default-tactics () .default-tactics.)

;;;
;;; get-tactic : name -> LIST(tactic)
;;;
(defun get-tactic (name)
  (let ((tactic (or (get-user-defined-tactic name)
		    (get-builtin-tactic name))))
    (unless tactic
      (with-output-chaos-error ('no-such-tactic)
	(format t "No such tactic is defined with the name ~s" name)))
    (if (atom tactic)
	(list tactic)
      tactic)))

;;;
;;; make user defined tactic
;;;
(defun declare-tactic (name &rest tactic-names)
  (let ((tactics nil))
    (dolist (n tactic-names)
      (let ((tactic (get-builtin-tactic n)))
	(unless tactic
	  (with-output-chaos-error ('no-such-tactic)
	    (format t "No tactic with the name ~s" n)))
	(push tactic tactics)))
    (setq name (canonicalize-tactic-name name))
    (setq .user-defined-tactics.
      (acons name (nreverse tactics) .user-defined-tactics.))))

;;;---------------------------------------------------------------------------
;;; GOAL
;;; a goal is a set of conditional axioms to be proved.
;;; 
(defstruct (goal (:print-function pr-goal))
  (name "" :type string)		; the name of the goal, we will refer 
					; this goal by this name
  (context nil :type (or null module))	; context module
  (constants nil :type list)		; list of constants introduced
  (indvars nil :type list)		; list of induction variables
  (assumptions nil :type list)		; list of hypothesis
  (tactic nil :type (or null tactic))	; tactic which derived this goal
  (targets nil :type list)		; axioms to be proved
  (proved nil :type list)		; proved targets
  )

(defun goal-is-discharged (goal)
  (declare (type goal goal))
  (null (goal-targets goal)))

#||
(defun get-module-simple-name (module)
  (with-output-to-string (s)
    (let ((*standard-output* s))
      (print-simple-mod-name module))))
||#
(defun get-module-simple-name (module)
  (module-print-name module))

(defun pr-goal (goal &optional (stream *standard-output*) &rest ignore)
  (declare (type goal goal)
	   (type stream stream)
	   (ignore ignore))
  (with-in-module ((goal-context goal))
    (if (goal-tactic goal)
	(format stream "~%~a=>~%:goal { ** ~a -----------------------------------------" (goal-tactic goal) (goal-name goal))
      (format stream "~%:goal { ** ~a -----------------------------------------" (goal-name goal)))
    (let ((*print-indent* (+ 2 *print-indent*))
	  (consts (goal-constants goal))
	  (ass (goal-assumptions goal))
	  (vs (goal-indvars goal))
	  (axs (goal-targets goal))
	  (proved (goal-proved goal))
	  (discharged (goal-is-discharged goal)))
      (print-next)
      (format stream "-- context module: ~a" (get-module-simple-name (goal-context goal)))
      (when proved
	(print-next)
	(format stream "-- proved axiom~p" (length proved))
	(dolist (pv proved)
	  (let ((*print-indent* (+ 2 *print-indent*)))
	    (print-next)
	    (print-axiom-brief pv) (princ " ."))))
      (when vs
	(print-next)
	(format stream "-- induction variable~p" (length vs))
	(dolist (v vs)
	  (let ((*print-indent* (+ 2 *print-indent*)))
	    (print-next)
	    (term-print-with-sort v))))
      (when consts
	(print-next)
	(format stream "-- introduced constant~p" (length consts))
	(dolist (const consts)
	  (let ((*print-indent* (+ 2 *print-indent*)))
	    (print-next)
	    (print-method-brief (term-head const)))))
      (when ass
	(print-next)
	(format stream "-- introduced axiom~p" (length ass))
	(dolist (as ass)
	  (let ((*print-indent* (+ 2 *print-indent*)))
	    (print-next)
	    (print-axiom-brief as) (princ " ."))))
      (when axs
	(print-next)
	(format stream "-- axiom~p to be proved" (length axs))
	(dolist (ax axs)
	  (let ((*print-indent* (+ 2 *print-indent*)))
	    (print-next)
	    (print-axiom-brief ax) (princ " ."))))
      (format stream "~%}")
      (if discharged
	  (format t " << proved >>")))))

;;; -------------------------------------------------------------------------
;;; PTREE-NODE
;;; A node of a proof tree. Contains a goal.
;;; 
(defstruct (ptree-node (:include bdag)
	    (:print-function pr-ptree-node))
  (num-children 0 :type fixnum)		; number of children
  (next-child 0 :type fixnum)		; next child to be proved
  (my-num 0 :type fixnum)		; position in siblings, first = 1
  (my-name "" :type string)		; name
  (done nil :type (or null t)))		; t iff the node is dischaged

(defun pr-ptree-node (ptree-node &optional (stream *standard-output*) &rest ignore)
  (declare (type ptree-node ptree-node)
	   (type stream stream)
	   (ignore ignore))
  (format stream "[Node]: sub nodes = ~d, discharged? = ~a ---------------"
	  (ptree-node-num-children ptree-node)
	  (ptree-node-done ptree-node))
  (pr-goal (ptree-node-datum ptree-node) stream))

(defmacro ptree-node-goal (ptree-node)
  `(ptree-node-datum ,ptree-node))

(defun node-is-discharged? (node)
  (let ((goal (ptree-node-goal node)))
    (or (null (goal-targets goal))
	(and (ptree-node-subnodes node)
	     (every #'(lambda (x) (node-is-discharged? x)) (ptree-node-subnodes node))))))

;;; make-ptree-goal-name : ptree-node fixnum -> string
;;; goal has a name. 
;;;
(defun make-ptree-goal-name (parent-node my-num)
  (declare (type (or null ptree-node) parent-node)
	   (type fixnum my-num))
  (if parent-node
      (let ((p-name (goal-name (ptree-node-goal parent-node))))
	(if (equal p-name "root")
	    (format nil "~d" my-num)
	  (format nil "~a-~d" p-name my-num)))
    "root"))

;;;
;;; context module creator
;;;
(defparameter .next-context-module. (%module-decl* "next-context-dummy" :object :user nil))

(defun make-next-context-module-name (goal-name)
  (declare (type string goal-name))
  (format nil "#Goal-~a" goal-name))

;;;
;;; prepare-next-goal : ptree-node -> goal
;;; prepare next goal structure with associated context module
;;;
(defun prepare-next-goal (ptree-node &optional (tactic nil))
  (let ((goal-name (make-ptree-goal-name ptree-node (incf (ptree-node-num-children ptree-node)))))
    (setf (%module-decl-name .next-context-module.) (make-next-context-module-name goal-name))
    (let ((next-context (eval-ast .next-context-module.))
	  (cur-goal (ptree-node-goal ptree-node))
	  (next-goal (make-goal :name goal-name
				:tactic tactic)))
      ;; import original context module
      (import-module next-context :including (goal-context cur-goal))
      ;; inherit current goal
      (setf (goal-context next-goal) next-context
	    (goal-constants next-goal) (goal-constants cur-goal)
	    (goal-indvars next-goal) (goal-indvars cur-goal)
	    (goal-assumptions next-goal) (goal-assumptions cur-goal))
      (prepare-for-parsing next-context)
      next-goal)))

;;;
;;; make-ptree-root : module goal -> ptree-node
;;;
(defun make-ptree-root (context-module initial-goals)
  (declare (type module context-module)
	   (type list initial-goals))
  (let ((root-node (make-ptree-node :subnodes nil :parent nil)))
    (setf (ptree-node-goal root-node) (make-goal :name (make-ptree-goal-name nil (ptree-node-my-num root-node))
						 :context context-module
						 :targets initial-goals))
    root-node))

;;;
;;; add-ptree-child : ptree-node module List(axiom) -> List(goal)
;;;
(defun add-ptree-child (parent-node child-goal)
  (declare (type ptree-node parent-node)
	   (type goal child-goal))
  ;; (incf (ptree-node-num-children parent-node)) ; this is done in prepare-next-goal
  (setf (ptree-node-subnodes parent-node)
    (nconc (ptree-node-subnodes parent-node)
	   (list (make-ptree-node :datum child-goal
				  :my-num (ptree-node-num-children parent-node)
				  :subnodes nil
				  :parent parent-node)))))

;;;
;;; get-ptree-root : ptree-node -> ptree-node
;;;
(defun get-ptree-root (ptree-node)
  (let ((parent (ptree-node-parent ptree-node)))
    (unless parent (return-from get-ptree-root ptree-node))
    (get-ptree-root parent)))


;;;-----------------------------------------------------------------------------
;;; PTREE : proof tree
;;; whole proof tree structure.
;;;
(defstruct (ptree (:print-function pr-ptree))
  (num-gen-const 0 :type fixnum)	   ; number of generated constants so far
  (root    nil :type (or null ptree-node)) ; root goal
  (current nil :type (or null ptree-node)) ; current target
  )

(defun pr-ptree (ptree &optional (stream *standard-output*) &rest ignore)
  (format stream "~%Proof Tree ===================================")
  (format stream "~%-- root node")
  (pr-goal (ptree-node-goal (ptree-root ptree))))

;;;
;;; initialize-proof-tree : module goal -> ptree
;;;
(defun initialize-proof-tree (context-module initial-goals)
  (let ((root (make-ptree-root context-module initial-goals)))
    (make-ptree :root root
		:current root)))

#||
;;;
;;; discharge : ptree -> Bool
;;; discharget current goal. returns nil iff all targets are discharged.
;;;
(defun discharge (ptree)
  (declare (type ptree ptree))
  (setf (ptree-current ptree) (discharge-node (ptree-current ptree))))
||#

;;;
;;; roll-back : ptree -> Bool
;;; roll back to parent. returns true (non-nil) iff roll back is done.
;;;
(defun roll-back (ptree)
  (declare (type ptree ptree))
  (let* ((current-target (ptree-current ptree))
	 (parent (and current-target (ptree-node-parent current-target))))
    (unless parent (return-from roll-back nil))
    (setf (ptree-node-subnodes parent) nil
	  (ptree-node-num-children parent) 0
	  (ptree-node-next-child parent) 0)
    (setf (ptree-current ptree) parent)))

;;;
;;; find-goal-node
;;;
(defun find-goal-node (ptree name)
  (declare (type ptree ptree)
	   (type string name))
  (dag-wfs (ptree-root ptree)
	   #'(lambda (n) (let ((goal (ptree-node-goal n)))
			   (when (string= (goal-name goal) name)
			     (return-from find-goal-node n))))))

;;;
;;; print-named-goal : name -> void
;;;
(defun print-named-goal (ptree name)
  (declare (type string name))
  (unless ptree
    (with-output-chaos-warning ()
      (format t "There is no proof tree.")
      (return-from print-named-goal nil)))
  (let ((goal-node (find-goal-node ptree name)))
    (unless goal-node
      (with-output-chaos-error ('no-such-goal)
	(format t "No such goal with the name ~s" name)))
    (pr-goal (ptree-node-goal goal-node))))

;;;
;;; get-unproved-nodes : ptree -> List(ptree-node)
;;; uses depth first search
(defun get-unproved-nodes (ptree)
  (let ((nodes nil))
    (dag-dfs (ptree-root ptree)
	     #'(lambda (x) (unless (or (ptree-node-subnodes x) (goal-is-discharged (ptree-node-goal x)))
			     (push x nodes))))
    (nreverse nodes)))

;;;
;;; get-unproved-goals : ptree -> List(goal)
;;;
(defun get-unproved-goals (ptree)
  (mapcar #'(lambda (y) (ptree-node-goal y)) (get-unproved-nodes ptree)))

;;;
;;; print-unproved-goals
;;;
(defun print-unproved-goals (ptree &optional (stream *standard-output*))
  (unless ptree
    (with-output-chaos-warning ()
      (format t "No goal is specified yet.")
      (return-from print-unproved-goals nil)))
  (dolist (goal (get-unproved-goals ptree))
    (pr-goal goal stream)))



;;; ====================
;;; TOP LEVEL FUNCTIONS
;;; ====================

;;;
;;; begin-proof
;;;
(defun begin-proof (context-module goal-axioms)
  (declare (type module context-module)
	   (type list goal-axioms))
  (unless goal-axioms (return-from begin-proof nil))
  (setq *proof-tree* (initialize-proof-tree context-module goal-axioms))
  (pr-goal (ptree-node-goal (ptree-root *proof-tree*)))
  (format t "~%** Initial goal (root) is generated. **")
  *proof-tree*)

;;;
;;; print-proof-tree
;;;
(defun print-proof-tree ()
  (unless *proof-tree*
    (with-output-chaos-warning ()
      (format t "There is no proof tree.")
      (return-from print-proof-tree nil)))
  (!print-proof-tree (ptree-root *proof-tree*)))

(defun !print-proof-tree (root-node &optional (stream *standard-output*))
  (let* ((leaf? #'(lambda (node) (null (dag-node-subnodes node))))
	 (leaf-name #'(lambda (node)
			(with-output-to-string (s)
			  (let ((goal (ptree-node-goal node)))
			    (if (goal-tactic goal)
				(format s "~a ~a" (goal-tactic goal) (goal-name goal))
			      (princ (goal-name goal) s))
			    (when (node-is-discharged? node)
			      (princ "*" s)))
			  s)))
	 (leaf-info #'(lambda (node) (declare (ignore node)) t))
	 (int-node-name #'(lambda (node) (funcall leaf-name node)))
	 (int-node-children #'(lambda (node) (ptree-node-subnodes node))))
    (force-output stream)
    (print-next nil *print-indent* stream)
    (print-trees (list (augment-tree root-node)) stream)))

;;; EOF
