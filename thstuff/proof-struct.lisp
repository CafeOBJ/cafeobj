;;;-*-Mode:LISP; Package: CHAOS; Base:10; Syntax:Common-lisp -*-
;;;
;;; Copyright (c) 2000-2016, Toshimi Sawada. All rights reserved.
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

  ;; Simultaneous Induction
  (defparameter .tactic-si. (make-tactic :name :si
                                         :executor 'apply-si))
  ;; Case Analysis
  (defparameter .tactic-ca. (make-tactic :name :ca
                                         :executor 'apply-ca))
  ;; Theorem of Constants
  (defparameter .tactic-tc. (make-tactic :name :tc
                                         :executor 'apply-tc))
  ;; Implication
  (defparameter .tactic-ip. (make-tactic :name :ip
                                         :executor 'apply-ip))
  ;; Implication by modifying the goal by 'imply'
  (defparameter .tactic-ip+. (make-tactic :name :ip+
                                         :executor 'apply-ip+))
  ;; Reduction: goal sentence will be destructively changed
  (defparameter .tactic-rd. (make-tactic :name :rd
                                         :executor 'apply-rd))
  ;; Reduction: keeps original goal sentence if it is not reduced to be 'true'
  (defparameter .tactic-rd-. (make-tactic :name :rd-
                                          :executor 'apply-rd-))
  ;; Normalize goal sentenses
  (defparameter .tactic-nf. (make-tactic :name :nf
                                         :executor 'apply-nf))
  ;; Check contradiction, i.e. true = false
  (defparameter .tactic-ct. (make-tactic :name :ct
                                         :executor 'apply-ct))
  ;; Do nothing, used internally
  (defparameter .tactic-nil. (make-tactic :name :nop
                                          :executor 'apply-nil))

  ;; list of all builtin tactics
  (defparameter .all-builtin-tactics. 
      (list .tactic-si. .tactic-ca. .tactic-tc. .tactic-ip. .tactic-ip+. 
            .tactic-rd. .tactic-rd-. .tactic-nf. .tactic-ct.))

  ;; default tatics is a seriase of SI CA TC IP RD.
  (defparameter .default-tactics. 
      (list .tactic-si. .tactic-ca. .tactic-tc. .tactic-ip. .tactic-rd.))

  ;; this is not an ordinary tactic but a command, but it generates goals
  (defparameter .tactic-ctf. (make-tactic :name :ctf
                                          :executor 'apply-ctf))
  ;; this is not an ordinary tactic but a command, but it generates goals
  (defparameter .tactic-csp. (make-tactic :name :csp
                                          :executor 'apply-csp))
  
  ;; :init as def(ed) tactic
  (defparameter .tactic-init. (make-tactic :name :init
                                           :executor 'apply-init))
  ;; :ind as def(ed) tactic
  (defparameter .tactic-ind. (make-tactic :name :ind
                                          :executor 'apply-ind))

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

;;; tactic-name-is-builtin? : name -> bool
;;;
(defun tactic-name-is-builtin? (name)
  (get-builtin-tactic name))

;;; sequence of tactic :defined
;;; :def <name> = (<tactic-name> ...)
;;;
(defstruct (tactic-seq (:include tactic)
            (:print-function pr-tactic-seq))
  (tactics nil :type list)              ; list of tactics
  )

(defun pr-tactic-seq (obj stream &rest ignore)
  (declare (type tactic-seq obj)
           (ignore ignore))
  (let ((tactics (tactic-seq-tactics obj)))
    (format stream "( ~{~a~^ ~a ~} )" (mapcar #'(lambda (x) (tactic-name x)) tactics))))

;;; :ctf/:csp as tactic
;;;
(defstruct (tactic-ctfp-common (:include tactic))
  (minus nil :type (or null t))         ; t iff :ctf- or :csp-
  (context nil :type (or null module))  ; context module
  )

(defstruct (tactic-ctf (:include tactic-ctfp-common (executor 'apply-ctf-tactic))
            (:print-function pr-tactic-ctf))
  (form nil)                            ; term or equation
  )

(defun pr-tactic-ctf (obj stream &rest ignore)
  (declare (type tactic-ctf obj)
           (ignore ignore))
  (let ((form (tactic-ctf-form obj)))
    (format stream ":ctf")
    (when (tactic-ctf-minus obj)
      (princ "-" stream))
    (with-in-module ((tactic-ctf-context obj))
      (cond ((axiom-p form)
             (princ "{" stream)
             (print-axiom-brief form stream)
             (princ " .}"))
            (t                          ; term
             (princ "[" stream)
             (term-print form stream)
             (princ " .]"))))))

(defstruct (tactic-csp (:include tactic-ctfp-common (executor 'apply-csp-tactic))
            (:print-function pr-tactic-csp))
  (forms nil)                           ; list of equations
  )

(defun pr-tactic-csp (obj stream &rest ignore)
  (declare (type tactic-csp obj)
           (ignore ignore))
  (let ((forms (tactic-csp-forms obj)))
    (format stream ":csp")
    (with-in-module ((tactic-csp-context obj))
      (when (tactic-csp-minus obj)
        (princ "-" stream))
      (princ "{" stream)
      (dolist (ax forms)
        (print-axiom-brief ax stream)
        (princ " . " stream))
      (princ "}" stream))))

;;; :init as tactic
;;;
(defstruct (tactic-init (:include tactic (executor 'apply-init-tactic)))
  (axiom nil)                           ; axiom
  (subst nil)                           ; substitution
  (context nil)                         ; context module
  )

;;; :ind as tactic
;;;
(defstruct (tactic-ind (:include tactic (executor 'apply-ind-tactic)))
  (vars nil)
  (base nil)
  (step nil))

;;; get-defined-tactic
;;;
(defun get-defined-tactic (goal name)
  (setq name (canonicalize-tactic-name name))
  (let ((defs (goal-defs goal)))
    (find-if #'(lambda (x) (string-equal name (canonicalize-tactic-name (tactic-name x)))) defs)))

;;; get-default-tactics
;;; returns the default tactics, i.e. (:si :ca :cs :tc :ip)
;;;
(defun get-default-tactics () .default-tactics.)

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

;;; =====
;;; FLAGS
;;; =====
(defvar *citp-show-rwl* nil)

;;; -------------------------------------------------------------------------------
;;; Various utils which controll 'switch' affected behaviour of the system .
;;;

;;; with-in-context : ptree-node
;;; construct a lexical environment for applying a tactic.
;;;
(eval-when (:compile-toplevel :execute :load-toplevel)

(defmacro with-in-context ((ptree-node) &rest body)
  (once-only (ptree-node)
    `(block :exit
       (let* ((.cur-goal. (ptree-node-goal ,ptree-node))
              (.cur-targets. (goal-targets .cur-goal.))
              (.next-goals. nil))
         (unless .cur-targets. (return-from :exit nil))
         ,@body))))

)

;;; This variable controlls implicit applications of tactics.
;;; 'true' means CITP cares application of implicite applicatins of tactics
;;;  such as 'normalization of the goal', 'contradiction check ('true = false')'.
;;; if this is 'false', CITP does only introduces proof schems defined.
(declaim (special *citp-spoiler*))
(defvar *citp-spoiler* nil)

(eval-when (:compile-toplevel :execute :load-toplevel)
  
(defmacro if-spoiler-on (&key then else)
  `(if *citp-spoiler*
       (progn ,then)
     (progn ,else)))

(defmacro when-spoiler-on (&rest body)
  `(when *citp-spoiler*
     ,@body))

(defmacro with-spoiler-on (&rest body)
  `(let ((*citp-spoiler* t))
     (declare (special *citp-spoiler*))
     ,@body))

)

(declaim (type fixnum *citp-max-flags*))
(defparameter *citp-max-flags* 10)

(defstruct (citp-flag-struct)
  (name "" :type simple-string)
  (value nil)
  (hook #'(lambda(name value) 
            (declare (ignore name value))
            nil) 
        :type (or function symbol)))

(declaim (type (simple-array * (10)) *citp-flags*))
(defvar *citp-flags*)
(eval-when (:execute :load-toplevel)
  (setq *citp-flags* (make-array *citp-max-flags*)))

(defmacro citp-flag-struct (flag-index)
  `(aref *citp-flags* ,flag-index))

(defmacro citp-flag (flag-index)
  `(citp-flag-struct-value (aref *citp-flags* ,flag-index)))

(defmacro citp-flag-name (flag-index)
  `(citp-flag-struct-name (aref *citp-flags* ,flag-index)))

(defmacro citp-flag-hook (flag-index)
  `(citp-flag-struct-hook (aref *citp-flags* ,flag-index)))

;;; flag indexes
(defconstant citp-all 0)
(defconstant citp-verbose 1)
(defconstant citp-show-rwl  2)
(defconstant citp-spoiler 3)
(defconstant citp-print-message 4)
(defconstant citp-normalize-init 5)
(defconstant citp-normalize-lhs 6)

;;; FIND-CITP-FLAG-INDEX : Name -> Index
;;;
(defun find-citp-flag-index (given-name)
  (declare (type simple-string given-name)
           (values (or null fixnum)))
  (let ((i 0)
        (name (concatenate 'string "citp-" given-name)))
    (declare (type fixnum i))
    (dotimes (x *citp-max-flags*)
      (when (string= name (citp-flag-name x))
        (return-from find-citp-flag-index i))
      (incf i))
    nil))

;;; print-citp-flag : index -> void
;;;
(defun print-citp-flag (index)
  (if (= index citp-all)
      (do ((idx 1 (1+ idx)))
          ((<= *citp-max-flags* idx))
        (pr-citp-flag-internal idx))
    (pr-citp-flag-internal index)))

(defun pr-citp-flag-internal (index)
  (unless (equal "" (citp-flag-name index))
    (format t "~&Flag ~a is ~a" (subseq (citp-flag-name index) 5) (if (citp-flag index) "on" "off"))))

;;; help-citp-flag : index
;;;
(defun help-citp-flag (index)
  (let ((flag (citp-flag-struct index)))
    flag))

;;; flag initialization
;;;
(defun initialize-citp-flag ()
  (dotimes (idx *citp-max-flags*)
    (setf (citp-flag-struct idx) (make-citp-flag-struct :value nil)))
  (setf (citp-flag-name citp-all) "citp-all"
        (citp-flag-name citp-verbose) "citp-verbose"
        (citp-flag-name citp-show-rwl) "citp-show-rwl"
        (citp-flag-name citp-spoiler) "citp-spoiler"
        (citp-flag-name citp-print-message) "citp-print-message"
        (citp-flag-name citp-normalize-init) "citp-normalize-init"
        (citp-flag-name citp-normalize-lhs) "citp-normalize-lhs")
  ;; set default
  (setf (citp-flag citp-print-message) t) ; others are 'off'
  (setf (citp-flag citp-normalize-init) t)
  ;; verbose flag hook
  (setf (citp-flag-hook citp-verbose)
    #'(lambda (name value)
        (declare (ignore name))
        (setf *citp-verbose* value)))
  ;; show-rwl hook
  (setf (citp-flag-hook citp-show-rwl)
    #'(lambda (name value)
        (declare (ignore name))
        (setf *citp-show-rwl* value)))
  ;; citp-spoiler hook
  (setf (citp-flag-hook citp-spoiler)
    #'(lambda (name value)
        (declare (ignore name))
        (setf *citp-spoiler* value)))
  )

(eval-when (:execute :load-toplevel)
  (initialize-citp-flag)
  )

;;; messaing when :verbose on
;;;
(eval-when (:compile-toplevel :execute :load-toplevel)

  (defmacro when-citp-verbose (&rest body)
    `(when *citp-verbose*
       (let ((*print-indent* (+ 2 *print-indent*))
             (*print-line-limit* 90))
         (declare (type fixnum *print-indent* *print-line-limit*))
         ,@body)))
  
)

;;; citp standard running env.
;;;
(defvar *citp-silent* t)
(eval-when (:compile-toplevel :execute :load-toplevel)
(defmacro with-citp-env (&rest body)
  `(if *citp-silent*
       (let ((*chaos-quiet* t)
             (*rwl-search-no-state-report* 
              (if *citp-show-rwl*
                  nil
                t)))
         ,@body)
     (progn
       ,@body)))

(defmacro with-next-context ((&optional (node *proof-tree*)) &rest body)
  `(let ((.context. (get-next-proof-context ,node)))
     (unless .context.
       (with-output-chaos-error ('no-context)
         (format t "No proof context is established.")))
     (with-in-module ((goal-context (ptree-node-goal .context.)))
       (with-citp-env ()
         ,@body))))

)

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
  (defs nil :type list)                 ; list of :defined tactics
  (base-ops nil :type list)             ; list of user specified induction base ops
  (step-ops nil :type list)             ; list of user specifief induction step ops
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
            (discharged (goal-is-discharged goal))
            (bases (goal-base-ops goal))
            (steps (goal-step-ops goal)))
        (print-next)
        (format stream "-- context module: ~a"
                (get-module-simple-name (ptree-context *proof-tree*)))
        (when proved
          (print-next)
          (format stream "-- discharged sentence~p" (length proved))
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
        (when bases
          (print-next)
          (format stream "-- user specified induction base~p" (length bases))
          (dolist (b bases)
            (let ((*print-indent* (+ 2 *print-indent*)))
              (print-next)
              (print-method-brief b))))
        (when steps
          (print-next)
          (format stream "-- user specified induction step~p" (length steps))
          (dolist (s steps)
            (let ((*print-indent* (+ 2 *print-indent*)))
              (print-next)
              (print-method-brief s))))
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

;;; use-sentence-in-goal : goal list-axioms
;;;

(defun incorporate-sentences-into-module (module new-axs)
  (unless module
    (with-output-chaos-error ('no-context)
      (format t "No context module is specified.")))
  (with-in-module (module)
    (dolist (ax new-axs)
      (let ((*print-indent* (+ 2 *print-indent*)))
        (print-next)
        (print-axiom-brief ax))
      (adjoin-axiom-to-module module ax)
      (set-operator-rewrite-rule module ax))
    (compile-module module)))

(defun use-sentences-in-goal (goal new-axs)
  (declare (type goal goal))
  (let ((num (length new-axs)))
    (unless (zerop num)
      (format t "~%** In goal ~s, use setence~p as new axiom~p:" (goal-name goal) num num)
      (incorporate-sentences-into-module (goal-context goal) new-axs)
      (setf (goal-assumptions goal) 
        (append (goal-assumptions goal) new-axs)))))

;;; embed-sentences-in-module (module new-axs)
;;;
(defun embed-sentences-in-module (module new-axs)
  (let ((num (length new-axs)))
    (unless (zerop num)
      (format t "~%** Embed the setence~p as new axiom~p into module ~a:" num num
              (get-module-simple-name module))
      (incorporate-sentences-into-module module new-axs))))

;;; the-goal-needs-undo : goal -> bool
;;; returns t iff the goal is generated by :defined :ctf- or :csp-
;;;
(defun the-goal-needs-undo (goal)
  (declare (type goal goal))
  (let ((goal-tactic (goal-tactic goal)))
    (and (tactic-ctfp-common-p goal-tactic)
         (tactic-ctfp-common-minus goal-tactic))))

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

(defun clear-induction-ops (ptree-node)
  (let ((goal (ptree-node-goal ptree-node)))
    (setf (goal-base-ops goal) nil
          (goal-step-ops goal) nil)))

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

;;; context module creator
;;;
(defparameter .next-context-module. (%module-decl* "next-context-dummy" :object :user nil))

(defun make-next-context-module-name (goal-name)
  (declare (type string goal-name))
  (format nil "#Goal-~a" goal-name))

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
            (goal-assumptions next-goal) (goal-assumptions cur-goal)
            (goal-defs next-goal) (goal-defs cur-goal)
            (goal-base-ops next-goal) (goal-base-ops cur-goal)
            (goal-step-ops next-goal) (goal-step-ops cur-goal))
      (prepare-for-parsing next-context)
      (setq *next-default-proof-node* nil) ; we reset the next default target
      next-goal)))

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

;;; ptree utils
;;;

;;; the-node-needs-undo
;;; returns t iff the node is generated by :def(ined)
;;; :ctf- or :csp-
(defun the-node-needs-undo (node)
  (declare (type ptree-node node))
  (the-goal-needs-undo (ptree-node-goal node)))

;;; parent-nedds-undo
;;; returns t iff the parent node is generated by :def(ined)
;;; :ctf- or :csp-
;;;
(defun parent-needs-undo (pnode)
  (declare (type (or null ptree-node) pnode))
  (let ((node (ptree-node-parent pnode)))
    (unless node (return-from parent-needs-undo nil))
    (the-node-needs-undo node)))

;;;-----------------------------------------------------------------------------
;;; PTREE : proof tree
;;; whole proof tree structure.
;;;
(defstruct (ptree (:print-function pr-ptree))
  (context nil :type (or null module))  ; context module
  (num-gen-const 0 :type fixnum)        ; number of generated constants so far
  (num-gen-const-ind 0 :type fixnum)    ; number of generated constants for induction so far
  (root nil :type (or null ptree-node)) ; root goal
  (indvar-subst nil :type list)         ; <variable> -> <constantForInduction>
  (var-subst nil :type list)            ; <variable> -> <constantForTheremOfConstants>
  (defs-so-far nil :type list)          ; :defined name so far
  (constructor-ops nil :type list)      ; list of constructor operators
  )

(defun pr-ptree (ptree &optional (stream *standard-output*) &rest ignore)
  (declare (type ptree ptree)
           (type stream stream)
           (ignore ignore))
  (let ((*standard-output* stream))
    (format t "~%Proof Tree ===================================")
    (with-in-module ((goal-context (ptree-node-goal (ptree-root ptree))))
      (let ((indvar-subst (ptree-indvar-subst ptree))
            (*print-indent* (+ 2 *print-indent*)))
        (format t "~%-- induction variable bases:")
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
      (format stream "~%-- constructors:")
      (let ((num 0))
        (dolist (op (ptree-constructor-ops ptree))
          (print-next)
          (format t "(~d) " (incf num))
          (print-method-brief op)))
      (format stream "~%-- root node")
      (pr-goal (ptree-node-goal (ptree-root ptree))))))

(defun reset-proof (ptree)
  (setf (ptree-num-gen-const ptree) 0
        (ptree-indvar-subst ptree) nil
        (ptree-var-subst ptree) nil))

(defun existing-def-name? (ptree name)
  (setq name (canonicalize-tactic-name name))
  (member name (ptree-defs-so-far ptree) :test #'equal))

;;; PROOF
;;;
(defstruct citp-proof
  (context nil)                         ; context module in which proof is performed
  (discharged nil)                      ; list of proved sentences
  )

(defvar *the-citp-proof* (make-citp-proof :context :none :discharged nil))

(defun get-discharged-sentence-with-label (label)
  (declare (type string label))
  (let ((name (intern label))
        (res nil))
    (dolist (ax (citp-proof-discharged *the-citp-proof*))
      (when (member name (axiom-labels ax))
        (push ax res)))
    (when (> (length res) 1)
      (with-output-chaos-warning ()
        (format t "Found more than 1 sentences with name ~s." label)))
    (unless res
      (with-output-chaos-error ()
        (format t "No such discharged sentence with name ~s." label)))
    res))

(defun find-discharged-sentences-with-label (list-labels)
  (let ((axs nil))
    (dolist (label list-labels)
      (setq axs (nconc axs
                       (get-discharged-sentence-with-label label))))
    axs))

;;;--------------------------------------------------------------------
;;; Support functions for introducing new constants used in the proof.
;;; 

;;; intro-const-returns-subst : module name variable -> (variable . constant-term)
;;; introduces a new constant of sort(variable) into a module.
;;; returns a pair (variable . constant-term)
;;;
(defun citp-intro-const (module name sort)
  (multiple-value-bind (op meth)
      (declare-operator-in-module (list name)
                                  nil   ; arity
                                  sort  ; coarity
                                  module ; 
                                  nil   ; constructor?
                                  nil   ; behavioural? always nil.
                                  nil   ; not coherent
                                  )
    (declare (ignore op))
    (prepare-for-parsing module t t)    ; force 
    meth))
  
(defun intro-const-returns-subst (module name variable)
  (cons variable (make-applform-simple (variable-sort variable)
                                       (citp-intro-const module name (variable-sort variable))
                                       nil)))

;;; make-tc-const-name : variable -> string
;;;
(defun make-tc-const-name (name sort)
  (format nil "~:@(~a~)@~a" name (string (sort-name sort))))

(defun make-tc-pconst-name (name)
  (format nil "`~:@(~a~)" name))

;;; introduces on-the-fly constant
;;;
(defun intro-fresh-pconstant (goal name-seed sort)
  (declare (ignore goal))
  (let ((name (make-tc-pconst-name name-seed)))
    (make-pvariable-term sort name)))

;;; variable->constant : goal variable -> term
;;; In the given goal, introduces fresh constant which should substitute the given varirable.
;;; used by tactic TC.
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
            (setq name (make-tc-const-name (variable-name variable) (variable-sort variable)))
            (push (cons variable name) (ptree-var-subst *proof-tree*)))
          (setq v-const (intro-const-returns-subst (goal-context goal)
                                                   name
                                                   variable))
          (push v-const (goal-constants goal))
          (cdr v-const)))))

;;; -----------------------------------------------------------
;;; Utils for constructors
;;;

;;; gather-constructor-ops : module -> List(constructor)
;;; list up all the constructor ops in a given module
;;;
(defun gather-constructor-ops (module)
  (flet ((method-is-user-defined-or-tf? (x)
           (or (eq x *bool-true-meth*)
               (eq x *bool-false-meth*)
               (and (not (sort= (method-coarity x) *sort-id-sort*))
                    (module-is-user-module (method-module x))))))
    (let ((res nil))
      (with-in-module (module)
        (dolist (opinfo (module-all-operators module))
          (dolist (meth (opinfo-methods opinfo))
            (when (and (method-is-constructor? meth)
                       (method-is-user-defined-or-tf? meth))
              (push meth res))))
        res))))

;;; get-constructors-of-sort : sort -> List[constructor]
;;; returns the list of constructors of sort.
;;;
(defun get-constructors-of-sort (sort &optional (context (get-context-module)))
  (let ((ops nil))
    (dolist (meth (ptree-constructor-ops *proof-tree*))
      (when (and (method-is-constructor? meth)
                 (sort<= (method-coarity meth) sort (module-sort-order context)))
        (push meth ops)))
    (reverse ops)))

;;; default-constructor-order
;;;
(defun default-constructor-order (constructors)
  (sort constructors 
        #'(lambda (x y) 
            ;; first precedence is number of arguments
            (let ((ax (method-num-args x))
                  (ay (method-num-args y)))
              (if (< ax ay)
                  t
                (if (> ax ay)
                    nil
                  (if (eq x *bool-true-meth*)
                      ;; this orders true > ... > false
                      t
                    (if (eq y *bool-true-meth*)
                        nil
                      (if (eq (op-lex-precedence x y) :greater)
                          nil
                        t)))))))))

;;; order-constructors : List[constructor] -> List[constructor]' 
;;;
(defun order-constructors (constructors &optional (order-spec nil))
  (cond ((null order-spec) (default-constructor-order constructors))
        (t 
         ;; order is specified by :order command
         ;; first initialize the order to default
         (let* ((pos-star (position :* order-spec))
                (first-half (subseq order-spec 0 pos-star))
                (second-half (subseq order-spec (1+ pos-star))))
           (setq constructors (set-difference constructors
                                                (append first-half second-half)))
           (setq constructors (default-constructor-order constructors))
           (append first-half constructors second-half)))))

;;; show-constructor-order : ptree -> void
;;;
(defun show-constructor-order (ptree)
  (let ((num 0))
    (with-output-msg ()
      (format t "Current order of constructors:")
      (dolist (op (ptree-constructor-ops ptree))
        (print-next)
        (format t "(~d) " (incf num))
        (print-method-brief op)))
    (terpri)))

;;; handler of :order command
;;; :order (<op>, ..., <op>)
;;;
(defun citp-eval-order (ast)
  (check-context-module-and-ptree)
  (with-in-module ((get-context-module))
    (let ((optokens (%pn-lex-ops ast)))
      (cond ((and (null (cdr optokens))
                  (null (car optokens)))
             (show-constructor-order *proof-tree*))
            (t (with-output-msg ()
                 (format t "start setting constructor ordering..."))
               (set-constructor-order *proof-tree* optokens)
               (format t "~%done.")
               (when-citp-verbose ()
                 (show-constructor-order *proof-tree*)))))))

(defun set-constructor-order (ptree optokens)
  (let ((prec-list nil))
    (dolist (e optokens)
      (cond ((equal e '("*"))
             (if (not (memq :* prec-list))
                 (setq prec-list (append prec-list '(:*)))
               (with-output-chaos-warning ()
                 (format t "* is already specified."))))
            (t (let ((parsedop (parse-op-name e)))
                 (multiple-value-bind (ops mod)
                     (resolve-operator-reference parsedop)
                   (with-in-module (mod)
                     (let ((overs nil))
                       (dolist (opinfo ops)
                         (dolist (meth (opinfo-methods opinfo))
                           (if (method-is-constructor? meth)
                               (if (member meth prec-list)
                                   (with-output-chaos-warning ()
                                     (format t "operator ~{~a~}/~d is already ordered, ignored." 
                                             (method-symbol meth)
                                             (method-num-args meth)))
                                 (push meth overs))
                             (unless (method-is-error-method meth)
                               (with-output-chaos-warning ()
                                 (format t "operator ~{~s~} is not a constructor, ignored." 
                                         (method-symbol meth)))))))
                       ;; order overloaded ops by number of arguments
                       (setq overs (sort overs #'(lambda (x y) 
                                                   (let ((x-num (method-num-args x))
                                                         (y-num (method-num-args y)))
                                                     (declare (type fixnum x-num y-num))
                                                     (< x-num y-num)))))
                       ;; set the result
                       (setq prec-list (append prec-list overs)))))))))
    (unless (memq :* prec-list)
      (setq prec-list (append prec-list '(:*))))
    (setf (ptree-constructor-ops ptree)
      (order-constructors (ptree-constructor-ops ptree)
                          prec-list))))

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

;;; intro-fresh-constant : goal -> term (introduced constant)
;;; introduces brand new constant in the current proof context
;;;
(defun intro-fresh-constant (goal name-seed sort)
  (let* ((name (make-ind-const-name name-seed sort))
         (meth (citp-intro-const (goal-context goal) name sort))
         (v-const (make-applform-simple sort meth nil)))
    (push (cons meth v-const) (goal-ind-constants goal))
    v-const))

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
          (make-ptree :root root 
                      :context context-module
                      :constructor-ops 
                      (order-constructors (gather-constructor-ops context-module) nil))))))

;;;
;;; check-success : ptree -> Bool
;;;
(defun check-success (ptree)
  (let ((unp (get-unproved-nodes ptree)))
    (when unp
      (format t "~%>> Next target goal is ~s." (goal-name (ptree-node-goal (car unp))))
      (setq *next-default-proof-node* (car unp))
      (format t "~%>> Remaining ~d goal~p.~%" (length unp) (length unp))
      (return-from check-success nil))
    (format t "~%** All goals are successfully discharged.~%")
    (save-discharged-sentences)
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

;;; get-unproved-goals : ptree -> List(goal)
;;;
(defun get-unproved-goals (ptree)
  (mapcar #'(lambda (y) (ptree-node-goal y)) (get-unproved-nodes ptree)))

;;; print-unproved-goals
;;;
(defun print-unproved-goals (ptree &optional (stream *standard-output*))
  (unless ptree
    (with-output-chaos-warning ()
      (format t "No goal is specified yet.")
      (return-from print-unproved-goals nil)))
  (dolist (goal (get-unproved-goals ptree))
    (pr-goal goal stream)))

;;; get-next-pfoof-context : ptree -> ptree-node
;;;
(defun get-next-proof-context (ptree)
  (and ptree (or *next-default-proof-node*
                 (car (get-unproved-nodes ptree)))))

(defun next-proof-target-is-specified? ()
  *next-default-proof-node*)

;;; get-target-goal-node
;;; given goal-name or NULL, returns the next targetted goal node.
;;;
(defun get-target-goal-node (&optional goal-name)
  (let ((next-goal-node (if goal-name
                            (find-goal-node *proof-tree* goal-name)
                          (get-next-proof-context *proof-tree*))))
    (unless next-goal-node
      (with-output-chaos-error ('no-target)
        (if goal-name
            (format t "Could not find the goal ~s." goal-name)
          (format t "No default target goal."))))
    next-goal-node))

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

;;; Getting TACTIC
;;; get-tactic : name -> LIST(tactic)
;;;
(defun get-tactic (name)
  (let ((context (get-next-proof-context *proof-tree*)))
    (let ((tactic (or (and context (get-defined-tactic (ptree-node-goal context) name))
                      (get-builtin-tactic name))))
    (unless tactic
      (with-output-chaos-error ('no-such-tactic)
        (format t "No such tactic is defined with the name ~s" name)))
    (if (atom tactic)
        (list tactic)
      tactic))))

;;; ====================
;;; TOP LEVEL FUNCTIONS
;;; ====================

;;; begin-proof
;;; starting the new proof
;;;
(defparameter .root-context-module. (%module-decl* "#Goal-root" :object :user nil))

(defun reset-proof-session ()
  (with-output-simple-msg ()
    (format t "!! Discarding the corrent proof..."))
  (setf (citp-proof-context *the-citp-proof*) nil
        (citp-proof-discharged *the-citp-proof*) nil)
  (reset-proof *proof-tree*)
  (setq *proof-tree* nil))

(defun save-discharged-sentences ()
  (setf (citp-proof-discharged *the-citp-proof*)
    (append (citp-proof-discharged *the-citp-proof*)
            (goal-targets (ptree-node-goal (ptree-root *proof-tree*))))))

(defun print-discharged-sentences ()
  (let ((discharged (citp-proof-discharged *the-citp-proof*)))
    (if discharged
        (with-in-module ((citp-proof-context *the-citp-proof*))
          (let ((*print-indent* (+ 2 *print-indent*)))
            (format t "** Discharged sentence~p" (length discharged))
            (dolist (ax discharged)
              (print-next)
              (print-axiom-brief ax)
              (princ " ."))))
      (format t "None~%"))))

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
  ;; if the context module is changed, we begin a brand new proof session
  (unless (eq (citp-proof-context *the-citp-proof*)
              context-module)
    (when-citp-verbose ()
      (with-output-simple-msg ()
        (princ "** Beginning a new proof.")))
    (setq *the-citp-proof*
      (make-citp-proof :context context-module :discharged nil)))
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

;;; --------
;;; PRiNTERS
;;; --------

;;; print-proof-tree
;;;
(defvar *show-proof-mode* :horizontal)

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
      (!print-proof-tree target-node (get-next-proof-context *proof-tree*) *show-proof-mode*))))

(defun !print-proof-tree (root-node next-target mode &optional (stream *standard-output*))
  (if (eq mode :horizontal)
      (!print-proof-horizontal root-node next-target stream)
    (!print-proof-vertical root-node next-target stream)))

(defun !print-proof-vertical (root-node next-target stream)
  (let* ((leaf? #'(lambda (node) (null (dag-node-subnodes node))))
         (leaf-name #'(lambda (node)
                        (with-output-to-string (s)
                          (let ((goal (ptree-node-goal node)))
                            (when (eq node next-target)
                              (princ ">" s))
                            (if (goal-tactic goal)
                                (format s "[~a] ~a" (tactic-name (goal-tactic goal)) (goal-name goal))
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

(defun !print-proof-horizontal (node next-target stream)
  (let ((*standard-output* stream))
    (let ((goal (ptree-node-goal node)))
      (with-in-module ((goal-context goal))
        (when (eq node next-target)
          (princ ">"))
        (if (goal-tactic goal)
            (format t "[~a]~6T~a" (tactic-name (goal-tactic goal)) (goal-name goal))
          (format t "~a" (goal-name goal)))
        (when (node-is-discharged? node)
          (princ "*"))))
    (let ((subnodes (ptree-node-subnodes node)))
      (when subnodes
        (let (;; (*print-indent* (+ 4 *print-indent*))
              )
          (dolist (sub subnodes)
            (print-next-prefix #\Space)
            (!print-proof-horizontal sub next-target stream)))))))


#||
(defun describe-proof-tree (node)
  (declare (type ptree-node node))
  (flet ((proved? ()
           (format nil "~:[unproved~;proved~]" (node-is-discharged? node))))
    (let ((goal (ptree-node-goal node))
          (*print-line-limit* 80)
          (*print-xmode* :fancy))
      (with-in-module ((goal-context goal))
        (if (goal-tactic goal)
            (format t "[~a]=> GOAL(~a) ~a" (tactic-name (goal-tactic goal)) (goal-name goal) (proved?))
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
                  (print-axiom-brief as)
                  (princ " .")))))
          (let ((proved (goal-proved goal)))
            (when proved
              (print-next)
              (format t "** discharged sentence~p:" (length proved))
              (let ((*print-indent* (+ 2 *print-indent*)))
                (dolist (ax proved)
                  (print-next)
                  (print-axiom-brief ax)
                  (princ " .")))))
          (let ((targets (goal-targets goal)))
            (when targets
              (print-next)
              (if (node-is-discharged? node)
                  (format t "** targeted sentence~p:" (length targets))
                (format t "** sentence~p to be proved:" (length targets)))
              (let ((*print-indent* (+ 2 *print-indent*)))
                (dolist (target targets)
                  (print-next)
                  (print-axiom-brief target)
                  (princ " .")))))))
      (let ((subnodes (ptree-node-subnodes node)))
        (when subnodes
          (let ((*print-indent* (+ 2 *print-indent*)))
            (dolist (sub subnodes)
              (print-next-prefix #\.)
              (describe-proof-tree sub))))))))
||#

(defparameter *proof-indent* 0)

(defun describe-proof-tree (node)
  (declare (type ptree-node node))
  (flet ((proved? ()
           ;; (format nil "~:[unproved~;proved~]" (node-is-discharged? node))
           (format nil "~:[ ~;*~]" (node-is-discharged? node))))
    (let ((goal (ptree-node-goal node))
          (*print-line-limit* 80)
          (*print-xmode* :fancy))
      (with-in-module ((goal-context goal))
        (if (goal-tactic goal)
            (format t "[~a]~8T~a~a" (tactic-name (goal-tactic goal)) (goal-name goal) (proved?))
          (format t "==> ~a~a" (goal-name goal) (proved?)))
        ;; (princ " ------------------------")
        (let ((*print-indent* (+ 4 *print-indent*)))
          (print-next)
          (format t "-- context module: ~a" (get-module-simple-name *current-module*))
          (let ((assumptions (goal-assumptions goal)))
            (when assumptions
              (print-next)
              (format t "-- assumption~p" (length assumptions))
              (let ((*print-indent* (+ 2 *print-indent*))
                    (*print-xmode* :fancy))
                (dolist (as assumptions)
                  (print-next)
                  (print-axiom-brief as)
                  (princ " .")))))
          (let ((proved (goal-proved goal)))
            (when proved
              (print-next)
              (format t "-- discharged sentence~p:" (length proved))
              (let ((*print-indent* (+ 2 *print-indent*)))
                (dolist (ax proved)
                  (print-next)
                  (print-axiom-brief ax)
                  (princ " .")))))
          (let ((targets (goal-targets goal)))
            (when targets
              (print-next)
              (if (node-is-discharged? node)
                  (format t "-- targeted sentence~p:" (length targets))
                (format t "-- sentence~p to be proved:" (length targets)))
              (let ((*print-indent* (+ 2 *print-indent*)))
                (dolist (target targets)
                  (print-next)
                  (print-axiom-brief target)
                  (princ " .")))))))
      (let ((subnodes (ptree-node-subnodes node)))
        (when subnodes
          (let ((*print-indent* (+ *proof-indent* *print-indent*)))
            (dolist (sub subnodes)
              (print-next-prefix #\.)
              (describe-proof-tree sub))))))))

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

;;; print-defs
;;; 
(defun print-defs (describe &optional goal-name)
  (declare (ignore describe))
  (let ((current (if goal-name
                     (find-goal-node *proof-tree* goal-name)
                   (get-next-proof-context *proof-tree*))))
    (if current
        (let* ((goal (ptree-node-goal current))
               (defs (goal-defs goal)))
          (unless defs
            (format t "~%The goal ~a has no defs.~%" (goal-name goal))
            (return-from print-defs nil))
          (dolist (def defs)
            (format t "~a = " (tactic-name def))
            (princ def)
            (print-next)))
      (with-output-chaos-warning ()
        (format t "No current goal.")))))

;;; EOF
