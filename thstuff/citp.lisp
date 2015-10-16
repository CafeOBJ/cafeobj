;;;-*-Mode:LISP; Package: CHAOS; Base:10; Syntax:Common-lisp -*-
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
#|=============================================================================
                                    System:CHAOS
                                   Module:thstuff
                                   File:citp.lisp
 =============================================================================|#
#-:chaos-debug
(declaim (optimize (speed 3) (safety 0) #-GCL (debug 0)))
#+:chaos-debug
(declaim (optimize (speed 1) (safety 3) #-GCL (debug 3)))

(defun check-context-module ()
  (unless *current-module*
    (with-output-chaos-error ('no-context)
      (format t "No context module is specified, please 'select' or 'open' a module."))))

(defun check-ptree ()
  (unless *proof-tree*
    (with-output-chaos-error ('no-proof-tree)
      (format t "No proof is ongoing."))))

(defun check-context-module-and-ptree ()
  (check-context-module)
  (check-ptree))

;;; ============================
;;; CITP related command parsers
;;; ============================

;;;
;;; :goal { <axiom> . <axiom> . .... <axiom> . }
;;;
(defun citp-parse-goal (args)
  (let ((ax-decls nil))
    (dolist (elem (third args))
      (push (parse-module-element-1 elem) ax-decls))
    (nreverse ax-decls)))

;;;
;;; :apply [to <goal-name>] (<tactic> ...)
;;;
;;; (":apply" ("(" ("tc" "rd" "si") ")"))
;;; (":apply" ("to" ("1-1-1")) ("(" ("RD") ")"))
;;;
(defun citp-parse-apply (args)
  (let ((tactic-forms nil)
        (tactics nil)
        (target nil))
    (cond ((string-equal (car (second args)) "to")
           (setq target (car (second (second args))))
           (setq tactic-forms (second (third args))))
          (t (setq tactic-forms (second (second args)))))
    (dolist (tac tactic-forms)
      (let ((tactic (get-tactic tac)))
        (setq tactics (nconc tactics tactic))))
    (cons target tactics)))

;;; citp-parse-ind-on
;;; :ind on (var ... var)
;;; (":ind" "on" "(" ("M:S-1" ... "N:S-N") ")")
;;;
(defun citp-parse-ind-on (args)
  (check-context-module)
  (with-in-module (*current-module*)
    (let ((vars nil))
      (dolist (var-decl (fourth args))
        (let ((var (simple-parse-from-string var-decl)))
          (when (term-ill-defined var)
            (with-output-chaos-error ('no-parse)
              (format t "Illegal variable form: ~s" var-decl)))
          (unless (term-is-variable? var)
            (with-output-chaos-error ('no-var)
              (format t "Invalid argument to ':ind' command: ~s" var-decl)))
          (push var vars)))
      (nreverse vars))))

;;;
;;; :auto
;;;
(defun citp-parse-auto (args)
  (declare (ignore args))
  (cons :auto (get-default-tactics)))

;;;
;;; :roll back
;;;
(defun citp-parse-roll-back (args)
  (declare (ignore args))
  :roll-back)

;;;
;;; :init {[<label>] | (<axiom>)} by { <var> <- <term>; ...<var> <- <term>; }
;;;
(defun make-axiom-pattern (target)
  (if (equal (first target) "[")
      (cons :label (second target))
    (cons :axiom (second target))))

(defun citp-parse-init (args)
  (let ((target-form (make-axiom-pattern (second args)))
        (subst-list (fifth args))
        (subst-pairs nil))
    (dolist (subst-form subst-list)
      (unless (atom subst-form)
        (push (cons (first subst-form) (third subst-form)) subst-pairs)))
    (with-citp-debug ()
      (format t "~%[:init] target = ~s" target-form)
      (format t "~%        subst  = ~s" subst-pairs))
    (list target-form subst-pairs)))

;;; :imply [<label>] by { <var> <- <term>; ...<var> <- <term>; }
;;;
(defun citp-parse-imp (args)
  (citp-parse-init args))

;;; :cp
;;; (":cp" ("[" ("label-1") "]") "><" ("[" ("label-2") "]")) 
;;; (":cp" ("(" ("ceq" ("LHS") "=" ("RHS") "if" ("C") ".") ")")
;;; "><" ("(" ("ceq" ("LHS-2") "=" ("RHS-2") "if" ("C-2") ".") ")")) 
;;;
(defun citp-parse-critical-pair (args)
  (let ((pat-1 (make-axiom-pattern (second args)))
        (pat-2 (make-axiom-pattern (fourth args))))
    (with-citp-debug ()
      (format t "~%[cp] ~s" pat-1)
      (format t "~%     ~s" pat-2))
    (list pat-1 pat-2)))

;;; :equation/:rule
;;;
(defun citp-parse-equation (args)
  (if (member (car args) '(":equation" "equation") :test #'equal)
      :equation
    :rule))

;;; :backward equation/rule
;;;
(defun citp-parse-backward (args)
  (if (member (second args) '(":equation" "equation") :test #'equal)
      :equation
    :rule))

;;; :select <GoalName>
;;;
(defun citp-parse-select (args)
  (let ((goal-name (car (second args))))
    goal-name))

;;;
;;; citp-parse-red
;;;
(defun citp-parse-red (e)
  (let (goal-name
        preterm
        mode)
    (case-equal (first e)
                ((":red" ":lred" "lred") (setq mode :red))
                ((":exec") (setq mode :exec))
                ((":bred") (setq mode :bred)))
    (if (= 4 (length e)) 
        (progn
          (setq goal-name (cadr (cadr e)))
          (setq preterm (nth 2 e)))
      (progn
        (setq goal-name nil)
        (setq preterm (nth 1 e))))
    (list mode goal-name preterm)))

;;;
;;; citp-parse-verbose
;;; :verbose {on | off}
(defun citp-parse-verbose (args)
  (second args))

;;;
;;; citp-parse-normalize-init
;;; :normalize {on | off}
(defun citp-parse-normalize (args)
  (second args))

;;; citp-parse-ctf
;;; :ctf { eq <term> = <term> .}
;;;   (":ctf" ("{" ("eq" ("1" ">" "2") "=" ("true") ".") "}"))
;;; :ctf [ <term> . ]
;;;   (":ctf" ("[" ("1" ">" "2") "." "]"))
;;; ==> (form . (term? . :ctf-?))
;;;
(defun citp-parse-ctf (args)
  (let ((form (second (second args)))
        (term? (equal (first (second args)) "[")))
    (if (equal (first args) ":ctf-")
        (cons form (cons term? :dash))
      (cons form (cons term? nil)))))

;;; citp-parse-csp
;;; :csp { <axiom> ... }
;;;
(defun citp-parse-csp (args)
  (let ((ax-decls nil)
        (dash? (equal (car args) ":csp-")))
    (dolist (elem (third args))
      (push elem ax-decls))
    (cons (nreverse ax-decls) dash?)))

;;; citp-parse-define
;;; :def <symbol> = <ctf> | <csp>
;;;
;;; (":def" "cf1" "=" (":ctf" ("[" (<Term>) "." "]")))
;;; ==> (:ctf "cf1" nil (:term (<Term>)))
;;; (":def" "cf2" "=" (":ctf-" ("{" (<Equation>) "." "}")))
;;; ==> (:ctf "cf2" t   (:eq (<Equation>)))
;;; (":def" "sp1" "=" (":csp" "{" ((<Equation> ".") (<Equation> ".")) "}"))
;;; ==> (:csp "sp1" nil ((<Equation> ".") (<Equation> ".")))
;;; (":def" "tactic-1" "=" ("(" ("si" "rd" "tc") ")"))
;;; ==> (:seq "tactic-1" ("si" "rd" "tc"))
;;;
(defun citp-parse-define (args)
  (flet ((name-to-com (name)
           (cond ((equal name "(")
                  :seq)
                 ((equal (subseq name 0 4) ":ctf")
                  :ctf)
                 ((equal (subseq name 0 4) ":csp")
                  :csp)
                 (t (with-output-chaos-error ('invalid-def)
                      (format t "Internal error, :def accepted ~a" name))))))
    (let* ((name (second args))
           (com-name (first (fourth args)))
           (command (name-to-com com-name))
           (dash (> (length com-name) 4))
           (body-form (if (eq command :ctf)
                          (if (equal "[" (first (second (fourth args))))
                              (list :term (second (second (fourth args))))
                            (list :eq (second (second (fourth args)))))
                        (if (eq command :csp)
                            (third (fourth args))
                          ;; :seq
                          (second (fourth args))))))
      (list command name dash body-form))))

;;; { :show | :describe } <something>
;;;
(defun citp-parse-show (inp)
  (let ((tag (car inp))
        (args (cdr inp))
        (com nil))
    (cond ((member tag '(":show" ":sh") :test #'equal)
           (setq com :show))
          ((member tag '(":describe" ":desc") :test #'equal)
           (setq com :describe))
          (t (with-output-chaos-error ('internal)
               (format t "Internal error, unknown citp command ~s" tag))))
    (cons com args)))

;;; :spoiler { on | off }
;;;
(defun citp-parse-spoiler (form)
  (let* ((on-off (second form))
         (value (if (equal on-off '("on"))
                    t
                  (if (equal on-off '("off"))
                      nil
                    (progn (format t "~&:spoiler flag is ~s" (if *citp-spoiler* "on" "off"))
                           (return-from citp-parse-spoiler nil))))))
    (setq *citp-spoiler* value)
    (setf (citp-flag citp-spoiler) value)
    t))

;;;
;;; {:binspect | binspect} [in <goal-name> : ] <boolean-term> .
;;;
(defun parse-citp-binspect (args)
  (let (mode
        goal-name
        preterm)
    (if (equal (first args) ":binspect")
        (setq mode :citp)
      (setq mode :general))
    (if (= 4 (length args))
        (progn
          (setq goal-name (cadr (cadr args)))
          (setq preterm (nth 2 args)))
      (progn
        (setq goal-name nil)
        (setq preterm (nth 1 args))))
    (list mode goal-name preterm)))

;;; bshow | :bshow
;;;
(defun citp-parse-bshow (args)
  (let ((param (cadr args)))
    (or param ".")))

;;; :set(<name>, {on | off | show | ? })
;;;
(defun citp-parse-set (inp)
  (declare (type list inp))
  (let ((name (third inp))
        (value (fifth inp)))
    (list name value)))



;;; ================================
;;; CITP related command evaluators
;;; ================================

;;; :goal
;;;
(defun eval-citp-goal (goal-ax-decls)
  (check-context-module)
  (with-in-module (*current-module*)
    (let ((axs nil))
      (dolist (a-decl goal-ax-decls)
        (cond ((eq (car a-decl) '%fax)
               (push (parse-fax-declaration a-decl) axs))
              (t (push (parse-axiom-declaration a-decl) axs))))
      (begin-proof *current-module* (nreverse axs)))))

;;; :apply/:auto
(defun eval-citp-apply (list-tactic)
  (check-ptree)
  (let ((target (car list-tactic))
        (tactics (cdr list-tactic)))
    (let ((*chaos-verbose* nil)
          (*chaos-quiet* t))
      (if target
          (case target
            (:auto (apply-auto *proof-tree*))
            (otherwise
             (apply-tactics-to-goal *proof-tree* target tactics)))
        (apply-tactics *proof-tree* tactics)))))

;;; :ind on
;;;
(defun eval-citp-ind-on (vars)
  (check-ptree)
  (with-in-module (*current-module*)
    (set-induction-variables vars)))

;;; :roll back
;;;
(defun eval-citp-roll-back (&rest com)
  (declare (ignore com))
  (check-ptree)
  (with-in-module (*current-module*)
    (roll-back *proof-tree*)))
  
;;; :init
;;;
(defun eval-citp-init (args)
  (check-ptree)
  (with-in-module (*current-module*)
    (instanciate-axiom (first args)     ; target
                       (second args)))) ; variable-term pairs

;;;
;;;
(defun eval-citp-imp (args)
  (check-ptree)
  (with-in-module (*current-module*)
    (introduce-implication-to-goal (first args)
                                   (second args))))

;;; :cp
(defun eval-citp-critical-pair (args)
  (check-ptree)
  (with-in-module (*current-module*)
    (apply-cp (first args) (second args))))

;;; :equation : {:equation| :rule} -> void
(defun eval-citp-equation (arg)
  (check-ptree)
  (add-critical-pairs arg :forward))

;;; :backward
(defun eval-citp-backward (arg)
  (check-ptree)
  (add-critical-pairs arg :backward))

;;; :select
(defun eval-citp-select (goal-name)
  (check-ptree)
  (select-next-goal goal-name))

;;; :red, :exec, :bred
(defun eval-citp-red (token-seq)
  (check-ptree)
  (let ((mode (first token-seq))
        (goal-name (second token-seq))
        (pre-term (third token-seq)))
    (reduce-in-goal mode goal-name pre-term)))

;;; :verbose
(defun eval-citp-verbose (token)
  (if (string-equal token "on")
      (setq *citp-verbose* t)
    (if (string-equal token "off")
        (setq *citp-verbose* nil)
      (if (string-equal token ".")
          (format t "~&:verbose flag is ~s" (if *citp-verbose* "on" "off"))
        (with-output-chaos-error ('invlid-value)
          (format t "Unknown parameter ~s." token))))))

;;; :normalize init
(defun eval-citp-normalize (token)
  (if (string-equal token "on")
      (setq *citp-normalize-instance* t)
    (if (string-equal token "off")
        (setq *citp-normalize-instance* nil)
      (if (string-equal token ".")
          (format t "~&:normalize flag is ~s" (if *citp-normalize-instance* "on" "off"))
        (with-output-chaos-error ('invalid-value)
          (format t ":nomalize instance: unknown parameter ~s." token))))))

;;; :ctf
;;; ax-form ::= (form . (term? . :ctf-?))
;;;
(defun eval-citp-ctf (ax-form)
  (check-ptree)
  (with-in-module (*current-module*)
    (reset-rewrite-counters)
    (begin-rewrite)
    (apply-ctf (car ax-form) (cadr ax-form) (cddr ax-form))
    (end-rewrite)
    (report-citp-stat)
    (check-success *proof-tree*)))

;;; :csp
(defun eval-citp-csp (goal-ax-decls)
  (check-ptree)
  (with-in-module (*current-module*)
    (reset-rewrite-counters)
    (begin-rewrite)
    (apply-csp (car goal-ax-decls) (cdr goal-ax-decls))
    (end-rewrite)
    (report-citp-stat)
    (check-success *proof-tree*)))

;;; :show, :describe
(defun eval-citp-show (token)
  (let* ((com (car token))
         (describe (eq com :describe))
         (target (cadr token))
         (rest-args (cddr token)))
    (cond ((member target '("unproved" "unp") :test #'equal)
           (check-ptree)
           (print-unproved-goals *proof-tree*))
          ((equal target "goal")
           (check-ptree)
           (let ((name (car rest-args)))
             (print-named-goal *proof-tree* name)))
          ((equal target "proof")
           (let ((name (car rest-args)))
             (when (or (null name) (equal name "."))
               (setq name "root"))
             (print-proof-tree name describe)))
          ((member target '("." "current") :test #'equal)
           (check-ptree)
           (print-current-goal describe))
          ((member target '(":def" ":define" "def" "define" ":defs" "defs") :test #'equal)
           (check-ptree)
           (let ((goal-name (first rest-args)))
             (print-defs describe goal-name)))
          (t (with-output-chaos-error ('unknown)
               (format t "Unknown parameter to :show/:describe ~S" target))))))

;;; :binspect
;;;
(defun eval-citp-binspect (args)
  (let ((mode (first args))
        (goal-or-mod (second args))
        (preterm (third args)))
  (binspect-in mode goal-or-mod preterm)))

;;; eval-citp-define : arg -> tactic-ctf or tactic-csp
;;; (:ctf "cf1" nil (:term (<Term>)))
;;; (:ctf "cf2" t   (:eq (<Equation>)))
;;; (:csp "sp1" nil ((<Equation> ".") ...))
;;; (:csp "sp2" t   ((<Equation> ".") ...))
;;; (:seq "tactic-1" nil (<tactic-name> ....))
;;;
(defun eval-citp-define (arg)
  (check-ptree)
  (let ((tactic-name (first arg))
        (name (second arg))
        (dash (third arg))
        (form (fourth arg))
        (tactic nil))
    (when (tactic-name-is-builtin? name)
      (with-output-chaos-error ('invalid-name)
        (format t "You can not use the name of builtin tactic ~a." name)))
    (when (existing-def-name? *proof-tree* name)
      (with-output-chaos-warning ()
        (format t "The name ~a is already defined in the current proof context." name)
        (format t "~%Please use the different name.")
        (return-from eval-citp-define nil)))
    (let ((current (get-next-proof-context *proof-tree*))
          (goal nil))
      (unless current
        (with-output-chaos-error ('no-context)
          (format t "No target goal.")))
      (setq goal (ptree-node-goal current))
      (with-in-module ((goal-context goal))
        (let ((*chaos-quiet* t))
          (cond ((eq tactic-name :ctf)
                 ;; ctf
                 (setq tactic (make-tactic-ctf :name name
                                               :form (parse-axiom-or-term (second form)
                                                                          (eq :term (first form)))
                                               :context *current-module*
                                               :minus dash)))
                ((eq tactic-name :csp)
                 ;; csp
                 (let ((forms nil))
                   (dolist (ax form)
                     (push (parse-axiom-declaration (parse-module-element-1 ax)) forms))
                   (setq tactic (make-tactic-csp :name name
                                                 :forms (nreverse forms)
                                                 :minus dash
                                                 :context *current-module*))))
                ((eq tactic-name :seq)
                 (setq tactic (make-tactic-seq :name name
                                               :tactics (mapcar #'(lambda (x)
                                                                    (or (get-defined-tactic goal x)
                                                                        (get-builtin-tactic x)
                                                                        (with-output-chaos-error ('no-such-tactic)
                                                                          (format t "No such tactic ~a" x))))
                                                                form))))
                (t ;; internal error
                 (with-output-chaos-error ('internal-error)
                   (format t "Invalid :def parameter ~s" tactic-name))))
          (format t "~&~a defined as " name)
          (princ tactic)
          (setf (goal-defs goal)
            (nconc (goal-defs goal) (list tactic)))))
          (push (canonicalize-tactic-name name) (ptree-defs-so-far *proof-tree*)))))

;;; 
;;; SET-FLAG/CLEAR-FLAG
;;;
(defun citp-eval-set (args)
  (let ((name (first args))
        (given-value (second args)))
    (let ((value nil)
          (index (find-citp-flag-index name)))
      (unless index
        (with-output-chaos-error ('no-such-flag)
          (format t "No such flag ~a" name)))
      (cond ((or (equal given-value "on")
                 (equal given-value "set"))
             (setq value t))
            ((equal given-value "show")
             (print-citp-flag index)
             (return-from citp-eval-set nil))
            ((equal given-value "?")
             (help-citp-flag index)
             (return-from citp-eval-set nil)))
      (when (citp-flag citp-print-message)
        (with-output-msg ()
          (format t "setting flag ~a to ~a" name given-value)))
      (if (= citp-all index)
          (dotimes (x *citp-max-flags*)
            (setf (citp-flag x) value))
        (setf (citp-flag index) value))
      ;; run hook
      (funcall (citp-flag-hook index) name value))))

;;; EOF
