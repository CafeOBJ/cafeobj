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
    (name nil    :type symbol)            ; name
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

  (defparameter .tactic-nf. (make-tactic :name :nf
                                         :executor 'apply-nf)) ; nomalize goals, assumptions

  (defparameter .tactic-ct. (make-tactic :name :ct
                                         :executor 'apply-ct)) ; check contradiction
  
  (defparameter .tactic-nil. (make-tactic :name :nop
                                          :executor 'apply-nil)) ; Do nothing, used internally.

  (defparameter .all-builtin-tactics. (list .tactic-si. .tactic-ca. .tactic-tc. .tactic-ip. .tactic-cs. .tactic-rd. .tactic-nf. .tactic-ct.))

  ;; default tatics is a seriase of SI CA CS TC IP.
  (defparameter .default-tactics. (list .tactic-si. .tactic-ca. .tactic-cs. .tactic-tc. .tactic-ip. .tactic-rd.))
  ;; this is not an ordinary tactic but a command, but it generates goals
  (defparameter .tactic-ctf. (make-tactic :name :ctf
                                          :executor 'apply-ctf))
  ;; this is not an ordinary tactic but a command, but it generates goals
  (defparameter .tactic-csp. (make-tactic :name :csp
                                          :executor 'apply-csp))
  
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

;;; 
;;; for debugging
;;;
(eval-when (:compile-toplevel :execute :load-toplevel)

(defmacro with-citp-debug (&rest body)
  `(when *debug-citp*
     (let ((*print-indent* (+ 2 *print-indent*))
           (*print-line-limit* 90))
       (declare (type fixnum *print-indent* *print-line-limit*))
       ,@body)))

)

;;;---------------------------------------------------------------------------
;;; GOAL
;;; a goal is a set of conditional sentences (in a form of CafeOBJ axiom) to be proved
;;; with context module, introduced constants, introduced axioms (hypothesis), e.t.c.
;;; it holds all the information about a goal.
;;;
(defstruct (goal (:print-function pr-goal))
  (name "" :type string)                ; the name of the goal, we will refer 
                                        ; this goal by this name
  (context nil :type (or null module))  ; context module
  (constants nil :type list)            ; list of (var . constant) introduced for TC/CA/SI
  (ind-constants nil :type list)        ; list of constants introduced for induction
  (indvars nil :type list)              ; list of induction variables
  (skolems nil :type list)              ; list of skolem functions
  (assumptions nil :type list)          ; list of hypothesis
  (tactic nil :type (or null tactic))   ; tactic which derived this goal
  (targets nil :type list)              ; axioms to be proved
  (proved nil :type list)               ; proved targets
  (critical-pairs nil :type list)       ; list of critical pairs not yet axiomatized
  )

(defun goal-is-discharged (goal)
  (declare (type goal goal))
  (null (goal-targets goal)))

(defun get-module-simple-name (module)
  (module-print-name module))

(defun pr-goal (goal &optional (stream *standard-output*) &rest ignore)
  (declare (type goal goal)
           (type stream stream)
           (ignore ignore))
  (let ((*print-line-limit* 80)
        (*print-xmode* :fancy))
    (with-in-module ((goal-context goal))
      (if (goal-tactic goal)
          (format stream "~%~a=>~%:goal { ** ~a -----------------------------------------"
                  (goal-tactic goal) (goal-name goal))
        (format stream "~%:goal { ** ~a -----------------------------------------" 
                (goal-name goal)))
      (let ((*print-indent* (+ 2 *print-indent*))
            (v-consts (goal-constants goal))
            (i-consts (goal-ind-constants goal))
            (skolems (goal-skolems goal))
            (ass (goal-assumptions goal))
            (vs (goal-indvars goal))
            (axs (goal-targets goal))
            (proved (goal-proved goal))
            (discharged (goal-is-discharged goal)))
        (print-next)
        (format stream "-- context module: ~a"
                (get-module-simple-name (ptree-context *proof-tree*)))
        (when proved
          (print-next)
          (format stream "-- discharged axiom~p" (length proved))
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
        (when v-consts
          (print-next)
          (format stream "-- introduced constant~p" (length v-consts))
          (dolist (const (reverse v-consts))
            (let ((*print-indent* (+ 2 *print-indent*)))
              (print-next)
              (print-method-brief (term-head (cdr const))))))
        (when i-consts
          (print-next)
          (format stream "-- constant~p for induction" (length i-consts))
          (dolist (ic (reverse i-consts))
            (let ((*print-indent* (+ 2 *print-indent*)))
              (print-next)
              (print-method-brief (term-head (cdr ic))))))
        (when skolems
          (print-next)
          (format stream "-- introduced skolem function~p" (length skolems))
          (dolist (sk skolems)
            (let ((*print-indent* (+ 2 *print-indent*)))
              (print-next)
              (print-method-brief sk))))
        (when ass
          (print-next)
          (format stream "-- introduced axiom~p" (length ass))
          (dolist (as ass)
            (let ((*print-indent* (+ 2 *print-indent*)))
              (print-next)
              (print-axiom-brief as) (princ " ."))))
        (when axs
          (print-next)
          (format stream "-- sentence~p to be proved" (length axs))
          (dolist (ax axs)
            (let ((*print-indent* (+ 2 *print-indent*)))
              (print-next)
              (print-axiom-brief ax) (princ " ."))))
        (format stream "~%}")
        (if discharged
            (format t " << proved >>"))))))

;;; -------------------------------------------------------------------------
;;; PTREE-NODE
;;; A node of a proof tree. Contains a goal as its datum.
;;; 
(defstruct (ptree-node (:include bdag)
            (:print-function pr-ptree-node))
  (num-children 0 :type fixnum)         ; number of children
  (next-child 0 :type fixnum)           ; next child to be proved
  (my-num 0 :type fixnum)               ; position in siblings, first = 1
  (my-name "" :type string)             ; name
  (done nil :type (or null t)))         ; t iff the node is dischaged

(defun pr-ptree-node (ptree-node &optional (stream *standard-output*) &rest ignore)
  (declare (type ptree-node ptree-node)
           (type stream stream)
           (ignore ignore))
  (format stream "[Node] sub nodes = ~d, discharged? = ~a ---------------"
          (ptree-node-num-children ptree-node)
          (ptree-node-done ptree-node))
  (pr-goal (ptree-node-datum ptree-node) stream))

(defmacro ptree-node-goal (ptree-node)
  `(ptree-node-datum ,ptree-node))

;;;
;;; initialize-ptree-node : ptree-node -> ptree-node
;;; discard existing child nodes. 
;;; 
(defun initialize-ptree-node (node &optional (no-warn nil))
  (unless no-warn
    (when (ptree-node-subnodes node)
      (with-output-chaos-warning ()
        (format t "Discarding exsisting ~d node~p"
                (ptree-node-num-children node)
                (length (ptree-node-subnodes node))))))
  (setf (ptree-node-num-children node) 0
        (ptree-node-subnodes node) nil)
  node)

;;;
;;; node-is-discharged? : ptree-node -> Bool
;;; returns if the node's goal is discharged,
;;; i.e., own goal has no target axioms to be proved,
;;;       or every subnodes are discharged.
;;;
(defun node-is-discharged? (node)
  (let ((goal (ptree-node-goal node)))
    (or (null (goal-targets goal))
        (and (ptree-node-subnodes node)
             (every #'(lambda (x) (node-is-discharged? x)) (ptree-node-subnodes node))))))

;;; make-it-unproved : ptree-node -> ptree-node'
;;;
(defun make-it-unproved (ptree-node)
  (let ((goal (ptree-node-goal ptree-node)))
    (setf (goal-targets goal) (append (goal-targets goal) (goal-proved goal)))))

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
(defvar .goals-so-far. nil)

(defun prepare-next-goal (ptree-node &optional (tactic nil))
  (let ((goal-name (make-ptree-goal-name ptree-node (incf (ptree-node-num-children ptree-node))))
        (decl-form (copy-tree .next-context-module.)))
    (setf (%module-decl-name decl-form) (make-next-context-module-name goal-name))
    (let ((next-context (eval-ast decl-form))
          (cur-goal (ptree-node-goal ptree-node))
          (next-goal (make-goal :name goal-name
                                :tactic tactic)))
      ;; goal module is hidden from user
      (setf (module-hidden next-context) t)
      (push (%module-decl-name decl-form) .goals-so-far.)
      ;; import original context module
      (import-module next-context :including (goal-context cur-goal))
      ;; inherit current goal
      (setf (goal-context next-goal) next-context
            (goal-constants next-goal) (goal-constants cur-goal)
            (goal-ind-constants next-goal) (goal-ind-constants cur-goal)
            (goal-indvars next-goal) (goal-indvars cur-goal)
            (goal-skolems next-goal) (goal-skolems cur-goal)
            (goal-assumptions next-goal) (goal-assumptions cur-goal))
      (prepare-for-parsing next-context)
      (setq *next-default-proof-node* nil) ; we reset the next default target
      next-goal)))

;;;
;;; give-goal-name-each-in-order : ptree-node List(goal) -> void
;;; this is used for renaming goals and their context modules
;;; after applied a tactic.
;;;
(defun give-goal-name-each-in-order (parent-node list-goals)
  (dolist (goal list-goals)
    (let* ((gname (make-ptree-goal-name parent-node (incf (ptree-node-num-children parent-node))))
           (mod-name (make-next-context-module-name gname)))
      (setf (goal-name goal) gname)
      (setf (module-name (goal-context goal)) mod-name))))

;;;
;;; make-ptree-root : module goal -> ptree-node
;;;
(defun make-ptree-root (context-module initial-goals)
  (declare (type module context-module)
           (type list initial-goals))
  (let ((root-node (make-ptree-node :subnodes nil :parent nil)))
    (setf (ptree-node-goal root-node) 
      (make-goal :name (make-ptree-goal-name nil (ptree-node-my-num root-node))
                 :context context-module
                 :skolems (reverse (module-skolem-functions context-module))
                 :targets initial-goals))
    root-node))

;;;
;;; add-ptree-child : ptree-node module List(axiom) -> List(goal)
;;;
(defun add-ptree-child (parent-node child-goal)
  (declare (type ptree-node parent-node)
           (type goal child-goal))
  (setf (ptree-node-subnodes parent-node)
    (nconc (ptree-node-subnodes parent-node)
           (list (make-ptree-node :datum child-goal
                                  :my-num (ptree-node-num-children parent-node)
                                  :subnodes nil
                                  :parent parent-node)))))

;;; add-ptree-children : ptree-node List(goal) -> ptree-node'
;;; add node of given goals as a child of the node.
;;; before adding goal nodes, initialize the node and
;;; give each goal a name.
;;;
(defun add-ptree-children (parent-node list-goals)
  (declare (type ptree-node parent-node)
           (type list list-goals))
  (initialize-ptree-node parent-node t)
  ;; give names to goals
  (give-goal-name-each-in-order parent-node list-goals)
  (dolist (goal list-goals)
    (add-ptree-child parent-node goal))
  parent-node)

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
  (context nil :type (or null module))  ; context module
  (num-gen-const 0 :type fixnum)        ; number of generated constants so far
  (num-gen-const-ind 0 :type fixnum)    ; number of generated constants for induction so far
  (root    nil :type (or null ptree-node)) ; root goal
  (indvar-subst nil :type list)
  (var-subst nil :type list)
  )

(defun pr-ptree (ptree &optional (stream *standard-output*) &rest ignore)
  (declare (type ptree ptree)
           (type stream stream)
           (ignore ignore))
  (let ((*standard-output* stream))
    (format t "~%Proof Tree ===================================")
    (format t "~%-- number of generated constants: ~d" (ptree-num-gen-const ptree))
    (format t "~%-- induction variable bases:")
    (with-in-module ((goal-context (ptree-node-goal (ptree-root ptree))))
      (let ((indvar-subst (ptree-indvar-subst ptree))
            (*print-indent* (+ 2 *print-indent*)))
        (if indvar-subst
            (dolist (is indvar-subst)
              (print-next)
              (term-print-with-sort (car is))
              (princ " => ")
              (princ (cdr is)))
          (progn (print-next) (princ "none" stream))))
      (format stream "~%-- introduced constants:")
      (let ((var-subst (ptree-var-subst ptree))
            (*print-indent* (+ 2 *print-indent*)))
        (if var-subst
            (dolist (is var-subst)
              (print-next)
              (term-print-with-sort (car is))
              (princ " => ")
              (princ (cdr is)))
          (progn (print-next) (princ "none" stream))))
      (format stream "~%-- root node")
      (pr-goal (ptree-node-goal (ptree-root ptree))))))

(defun reset-proof (ptree)
  (setf (ptree-num-gen-const ptree) 0
        (ptree-indvar-subst ptree) nil
        (ptree-var-subst ptree) nil))

;;; intro-const-returns-subst : module name variable -> (variable . constant-term)
;;; introduces a new constant of sort(variable) into a module.
;;; returns a pair (variable . constant-term)
;;;
(defun intro-const-returns-subst (module name variable)
  (multiple-value-bind (op meth)
      (declare-operator-in-module (list name)
                                  nil   ; arity
                                  (variable-sort variable) ; coarity
                                  module ; 
                                  nil   ; constructor?
                                  nil   ; behavioural? always nil.
                                  nil   ; not coherent
                                  )
    (declare (ignore op))
    (prepare-for-parsing module t t)    ; force 
    (cons variable (make-applform-simple (variable-sort variable) meth nil))))

;;;
;;; make-tc-const-name : proof-tree prefix -> string
;;;
#||
(defun make-tc-const-name (variable)
  (format nil "~:@(~a~)~d@~a" 
          (variable-name variable) 
          (incf (ptree-num-gen-const *proof-tree*)))
          (string (sort-name (variable-sort variable))))
||#

(defun make-tc-const-name (variable)
  (format nil "~:@(~a~)@~a" (variable-name variable)
          (string (sort-name (variable-sort variable)))))
;;; 
;;; variable->constant : goal variable -> term
;;;
(defun find-variable-subst-in (alist variable)
  (assoc variable alist :test #'variable-equal))

(defun list-submodules (module)
  (mapcar #'car (module-all-submodules module)))

(defun variable->constant (goal variable)
  (let ((vc-assoc (find-variable-subst-in (goal-constants goal) variable)))
    (or (cdr vc-assoc)
        (let ((name (cdr (find-variable-subst-in (ptree-var-subst *proof-tree*) variable)))
              (v-const nil))
          (unless name
            (setq name (make-tc-const-name variable))
            (push (cons variable name) (ptree-var-subst *proof-tree*)))
          (setq v-const (intro-const-returns-subst (goal-context goal)
                                                   name
                                                   variable))
          (push v-const (goal-constants goal))
          (cdr v-const)))))

;;;
;;; variable->constructor : goal variable op -> term
;;;
(defun make-ind-const-name (name-prefix sort)
  (format nil "~a#~a" (string name-prefix) (string (sort-name sort))))

(defun variable->constructor (goal variable &key (sort nil) (op nil))
  (let ((svar (if sort
                  (make-variable-term sort (intern (format nil "~a_~a" 
                                                           (variable-name variable) 
                                                           (sort-name sort))))
                variable)))
    (flet ((make-iv-const (name)
             (if op
                 (let ((constant (make-applform-simple (method-coarity op) op nil)))
                   (push (cons variable constant) (goal-ind-constants goal))
                   constant)
               (let ((con (intro-const-returns-subst (goal-context goal)
                                                     name
                                                     svar)))
                 (push con (goal-ind-constants goal))
                 (cdr con)))))
      (let ((v-assoc (find-variable-subst-in (goal-ind-constants goal) svar)))
        (or (cdr v-assoc)
            (let ((v-name (cdr (find-variable-subst-in (ptree-indvar-subst *proof-tree*) svar)))
                  (vconst nil))
              (unless v-name 
                (setq v-name (make-ind-const-name (variable-name variable)
                                                  (or sort (variable-sort svar)))))
              (setq vconst (make-iv-const v-name))
              (pushnew (cons svar v-name) (ptree-indvar-subst *proof-tree*) :test #'equal)
              vconst))))))

;;; SKOLEMITIZE
;;; allow citp to represent the goal sentence in FOPLE-SENTENCE
(defun skolemize-if-need (fax)
  (unless (eq (axiom-type fax) :pignose-axiom)
    (return-from skolemize-if-need fax))
  (with-citp-debug ()
    (format t "~%[skolemize]: ")
    (print-axiom-brief fax))
  (let* ((sentence (axiom-lhs fax))
         (type (fopl-sentence-type sentence))
         (*sk-function-num* nil))
    (declare (type symbol type)
             (special *sk-function-num*))
    (when (and (memq type '(:eq :beq))
               (term-is-lisp-form? (term-arg-2 sentence)))
      (return-from skolemize-if-need fax))
    ;; normalize quantified formula
    ;; \Q[v1...vn]S --> \Q[v1]\Q[v2]...\Q[vn]S
    (normalize-quantifiers sentence)
    ;; convert to NNF(negation normal form.)
    (setq sentence (neg-normal-form sentence))
    ;; skolemization -- eliminate \Es
    (skolemize sentence)
    ;; skolemize may introduce new operators.
    (prepare-for-parsing *current-module*)
    ;; eliminate quantifiers -- eliminate \As
    (zap-quantifiers sentence)
    ;; convert to CNF(conjunctive normal form).
    (conj-normal-form sentence)
    ;; make it an equation
    (let ((ax (make-rule :lhs sentence
                         :rhs *bool-true*
                         :condition *bool-true*
                         :labels (axiom-labels fax)
                         :behavioural (axiom-is-behavioural fax)
                         :type :equation)))
      (adjoin-axiom-to-module *current-module* ax)
      ax)))

;;;
;;; initialize-proof-tree : module goal -> ptree
;;;
(defun initialize-proof-tree (context-module goal-module initial-goals)
  (with-in-module (goal-module)
    (let ((*sk-function-num* nil))
      (declare (special *sk-function-num*))
      (let* ((targets (mapcar #'skolemize-if-need initial-goals))
             (root (make-ptree-root goal-module targets)))
          (setq *next-default-proof-node* nil)
          (make-ptree :root root :context context-module)))))

;;;
;;; check-success : ptree -> Bool
;;;
(defun check-success (ptree)
  (let ((unp (get-unproved-nodes ptree)))
    (when unp
      (format t "~%>> Next target goal is ~s." (goal-name (ptree-node-goal (car unp))))
      (setq *next-default-proof-node* (car unp))
      (format t "~%>> Remaining ~d goal~p." (length unp) (length unp))
      (return-from check-success nil))
    (format t "~%** All goals are successfully discharged.~%")
    (setq *next-default-proof-node* nil)
    t))

;;; ------------------------------------------------------------------
;;; roll-back : ptree -> Bool
;;; roll back to parent. returns true (non-nil) iff roll back is done.
;;;
(defun roll-back (ptree)
  (declare (type ptree ptree))
  (let* ((current-target (get-next-proof-context ptree))
         (parent (and current-target (ptree-node-parent current-target))))
    (unless parent
      (format t "~%**> :roll back, already at root.")
      (setq *next-default-proof-node* nil)
      (return-from roll-back nil))
    (setf (ptree-node-subnodes parent) nil
          (ptree-node-num-children parent) 0
          (ptree-node-next-child parent) 0)
    (format t "~%**> :roll back")
    (setq *next-default-proof-node* nil)
    (setq current-target (get-next-proof-context ptree))
    (when current-target
      (format t "~%    next default target is ~s" (goal-name (ptree-node-goal current-target))))
    current-target))

;;;
;;; find-goal-node : ptree string -> { ptree-node | nil }
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
  (unless ptree
    (with-output-chaos-warning ()
      (format t "There is no proof tree.")
      (return-from print-named-goal nil)))
  (let ((goal-node (if name
                       (find-goal-node ptree name)
                     (if (next-proof-target-is-specified?)
                         (get-next-proof-context ptree)
                       (with-output-chaos-error ('no-goal)
                         (format t "No default goal is specified."))))))
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

;;;
;;; get-next-pfoof-context : ptree -> ptree-node
;;;
(defun get-next-proof-context (ptree)
  (or *next-default-proof-node*
      (car (get-unproved-nodes ptree))))

(defun next-proof-target-is-specified? ()
  *next-default-proof-node*)

;;;
;;; select-next-goal : goal-name
;;;
(defun select-next-goal (goal-name)
  (declare (type string goal-name))
  (unless *proof-tree*
    (with-output-chaos-error ('no-proof-tree)
      (format t "No proof is ongoing.")))
  (cond ((string= goal-name ".")
         (setq *next-default-proof-node* nil)
         (let ((next (get-next-proof-context *proof-tree*)))
           (format t "~%:select resetting next default target ...")
           (unless next
             (with-output-chaos-warning ()
               (format t "There is no unproved goal.")
               (return-from select-next-goal nil)))
           (format t "~%>> next default-goal is ~s" (goal-name (ptree-node-goal next)))))
        (t (let ((node (find-goal-node *proof-tree* goal-name)))
             (unless node
               (with-output-chaos-error ('no-goal)
                 (format t "No such goal ~s" goal-name)))
             (when (node-is-discharged? node)
               (with-output-chaos-warning ()
                 (format t "The goal ~s is alreaday discharged." (goal-name (ptree-node-goal node)))
                 (print-next)
                 (format t "This will discard the current status of the goal."))
               (make-it-unproved node))
             (setq *next-default-proof-node* node)
             (when (eq node (ptree-root *proof-tree*))
               (reset-proof *proof-tree*))
             (format t "~%>> setting next default goal to ~s" (goal-name (ptree-node-goal node)))
             node))))

;;; ====================
;;; TOP LEVEL FUNCTIONS
;;; ====================

;;;
;;; begin-proof
;;;
(defparameter .root-context-module. (%module-decl* "#Goal-root" :object :user nil))

;;; for LE check
;; (defvar .int-module. nil)
(defvar .ls-pat. nil)                   ; X < Y
(defvar .le-pat. nil)                   ; X <= Y

(defun prepare-root-context (root-module context-module)
  (unless .int-module.
    (setq .int-module. (eval-modexp "INT"))
    (with-in-module (.int-module.)
      (let ((less (find-operator '("_" "<" "_") 2 .int-module.))
            (le (find-operator '("_" "<=" "_") 2 .int-module.))
            (less-m nil)
            (le-m nil)
            (var-x nil)
            (var-y nil)
            (int-sort (find-sort-in .int-module. '|Int|)))
        (setq less-m (lowest-method* (car (opinfo-methods less))))
        (setq le-m (lowest-method* (car (opinfo-methods le))))
        (setq var-x (make-variable-term int-sort 'X))
        (setq var-y (make-variable-term int-sort 'Y))
        (setq .ls-pat. (make-applform-simple *bool-sort* less-m (list var-x var-y)))
        (setq .le-pat. (make-applform-simple *bool-sort* le-m (list var-x var-y))))))
  (import-module root-module :protecting context-module)
  (import-module root-module :protecting .int-module.)
  (compile-module root-module t))

(defun begin-proof (context-module goal-axioms)
  (declare (type module context-module)
           (type list goal-axioms))
  (unless goal-axioms (return-from begin-proof nil))
  (let* ((*chaos-quiet* t)
         (root-module (eval-ast .root-context-module.)))
    (setf (module-hidden root-module) t)
    (prepare-root-context root-module context-module)
    (when .goals-so-far. 
      (setq *modules-so-far-table* (remove-if #'(lambda (x) 
                                                  (member (car x) .goals-so-far. :test #'equal))
                                              *modules-so-far-table*))
      (setq .goals-so-far. nil))
    (setq *proof-tree* (initialize-proof-tree context-module root-module goal-axioms))
    (pr-goal (ptree-node-goal (ptree-root *proof-tree*)))
    (format t "~%** Initial goal (root) is generated. **")
    (setq *next-default-proof-node* (ptree-root *proof-tree*))
    *proof-tree*))

;;;
;;; print-proof-tree
;;;
(defun print-proof-tree (goal-name &optional (describe nil))
  (unless *proof-tree*
    (with-output-chaos-warning ()
      (format t "There is no proof tree.")
      (return-from print-proof-tree nil)))
  (let ((target-node (if goal-name
                         (or (find-goal-node *proof-tree* goal-name)
                             (with-output-chaos-error ('no-such-goal)
                               (format t "No goal with the name ~s." goal-name)))
                       (ptree-root *proof-tree*))))
    (if describe
        (describe-proof-tree target-node)
      (!print-proof-tree target-node (get-next-proof-context *proof-tree*)))))

(defun !print-proof-tree (root-node next-target &optional (stream *standard-output*))
  (let* ((leaf? #'(lambda (node) (null (dag-node-subnodes node))))
         (leaf-name #'(lambda (node)
                        (with-output-to-string (s)
                          (let ((goal (ptree-node-goal node)))
                            (when (eq node next-target)
                              (princ ">" s))
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

(defun describe-proof-tree (node)
  (declare (type ptree-node node))
  (flet ((proved? ()
           (format nil "~:[unproved~;proved~]" (node-is-discharged? node))))
    (let ((goal (ptree-node-goal node))
          (*print-line-limit* 80)
          (*print-xmode* :fancy))
      (with-in-module ((goal-context goal))
        (if (goal-tactic goal)
            (format t "~a=> GOAL(~a) ~a" (goal-tactic goal) (goal-name goal) (proved?))
          (format t "=> GOAL(~a) ~a" (goal-name goal) (proved?)))
        (princ " ------------------------")
        (let ((*print-indent* (+ 4 *print-indent*)))
          (print-next)
          (format t "** context module: ~a" (get-module-simple-name *current-module*))
          (let ((assumptions (goal-assumptions goal)))
            (when assumptions
              (print-next)
              (format t "** assumption~p" (length assumptions))
              (let ((*print-indent* (+ 2 *print-indent*))
                    (*print-xmode* :fancy))
                (dolist (as assumptions)
                  (print-next)
                  (print-axiom-brief as)))))
          (let ((proved (goal-proved goal)))
            (when proved
              (print-next)
              (format t "** discharged sentence~p:" (length proved))
              (let ((*print-indent* (+ 2 *print-indent*)))
                (dolist (ax proved)
                  (print-next)
                  (print-axiom-brief ax)))))
          (let ((targets (goal-targets goal)))
            (when targets
              (print-next)
              (if (node-is-discharged? node)
                  (format t "** targeted sentence~p:" (length targets))
                (format t "** sentence~p to be proved:" (length targets)))
              (let ((*print-indent* (+ 2 *print-indent*)))
                (dolist (target targets)
                  (print-next)
                  (print-axiom-brief target)))))))
      (let ((subnodes (ptree-node-subnodes node)))
        (when subnodes
          (let ((*print-indent* (+ 2 *print-indent*)))
            (dolist (sub subnodes)
              (print-next-prefix #\.)
              (describe-proof-tree sub))))))))

;;;
;;; print-current-goal : mode -> void
;;;
(defun print-current-goal (describe)
  (let ((current (get-next-proof-context *proof-tree*)))
    (if current
        (if describe                    ; :describe
            (pr-goal (ptree-node-goal current))
          (format t "~%The current goal is ~a" (goal-name (ptree-node-goal current))))
      (with-output-chaos-warning ()
        (format t "All goals have been discharged.")))))

;;; EOF
