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

(defun check-on-going()
  (unless (and *proof-tree* (get-unproved-nodes *proof-tree*))
    (with-output-chaos-error ('no-target)
      (format t "There are no unproved goals."))))

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
;;; (":ind" ("on" "(" ("A:S-1" "B:S-2" "C:S-3") ")"))
;;; (":ind" ("{" ("on" #1="(" ("L1:List") #2=")") 
;;;              ("base" #1# ("nil") "." nil #2#) 
;;;              ("step" #1# ("X:Elm" "T:List") "." nil #2#) "}"))
;;; (":ind" ("{" ("on" #1="(" ("S1:Seq") #2=")")
;;;              ("base" #1# ("nil") "." nil #2#)
;;;              ("hypo" #1# ("SQ:Seq") "." nil #2#) 
;;;              ("step" #1# ("EL:Elt" "SQ:Seq") "." nil #2#) "}"))
(defun citp-parse-seq-of-terms (module token-list)
  (let ((terms nil))
    (when (atom token-list)
      (return-from citp-parse-seq-of-terms nil))
    (dolist (term? token-list)
      ;; (format t "~%<<>> ~s" term?)
      (when (consp term?)
        (let* ((*parse-variables* nil)
               (target-term (simple-parse module term? *cosmos*)))
          (when (or (null (term-sort target-term))
                    (sort<= (term-sort target-term) *syntax-err-sort* *chaos-sort-order*))
            (with-output-chaos-error ('invalid-term)
              (format t "Could not parse ~s" term?)))
          (push target-term terms))))
    (nreverse terms)))

(defun citp-parse-ind-on (args)
  (check-context-module)
  (with-in-module (*current-module*)
    (let ((ind-type (first (second args))))
      (flet ((parse-vars (decls)
               (let ((vars nil))
                 (dolist (var-decl decls)
                   (let ((var (simple-parse-from-string var-decl)))
                     (when (term-is-an-error var)
                       (with-output-chaos-error ('no-parse)
                         (format t "Illegal variable form: ~a" var-decl)))
                     (unless (term-is-variable? var)
                       (with-output-chaos-error ('no-var)
                         (format t "Invalid argument to ':ind' command: ~a" var-decl)))
                     (push var vars)))
                 (nreverse vars))))
        (if (equal ind-type "on")
            (let ((vars (parse-vars (third (second args)))))
              (cons :simple vars))
          ;; :ind { on () base() [hypo ()] step() }
          (let* ((decl (second args))
                 (vars (parse-vars (third (second decl))))
                 (bases (citp-parse-seq-of-terms *current-module* (third decl)))
                 (hypo (citp-parse-seq-of-terms *current-module* (fourth decl)))
                 (steps (citp-parse-seq-of-terms *current-module* (fifth decl))))
            (if steps
                (list :user vars bases hypo steps)
              (list :user vars bases nil hypo))))))))

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
;;;   first        second       third four          fifth
;;; (":init" ("[" ("test1") "]") "by" "{" (("X:S" "<-" ("X#S")) ";") "}"))
;;;   first       second           third                                                            fourth
;;; (":init" ("as" "ts-ss-1") (#1="{" ("eq" ("ts.." "(" "SS:SeqSym" ")") "=" ("true") ".") #3="}") ("by" #1# (("SS:SeqSym" "<-" ("ss")) #2=";" ("XX:Bar" "<-" ("bb")) #2#) #3#)))
;;; (":init" ("as" "ts-ss-1") (#1="(" ("eq" ("ts.." #1# "SS:SeqSym" #2=")") "=" ("true") ".") #2#) "by"  ("{" ("SS:SeqSym" "<-" ("ss")) ";" "}"))
;;;
(defun make-axiom-pattern (target)
  (if (stringp target)
      (cons :label (list target))
    (cons :axiom target)))

(defun citp-parse-init (args)
  (let ((name (if (equal (first (second args)) "as")
                  (second (second args))
                nil)))
    (let ((target-form (make-axiom-pattern (if name 
                                               (second (third args))
                                             (second (second args)))))
          (subst-list (if name 
                          (third (fourth args))
                        (third (third args))))
          (subst-pairs nil))
      (dolist (subst-form subst-list)
        (unless (atom subst-form)
          (push (cons (first subst-form) (third subst-form)) subst-pairs)))
      (with-citp-debug ()
        (format t "~%[:init] target = ~s" target-form)
        (format t "~%        subst  = ~s" subst-pairs))
      (list (first args) target-form subst-pairs name))))

;;; :imply [<label>] by { <var> <- <term>; ...<var> <- <term>; }
;;;
;;; (":imp" ("[" ("test2") "]") ("by" "{" (("Y:S" "<-" ("X#S")) ";") "}"))
;;; (":imp" ("[" ("gt") "]") ("."))
;;;
(defun citp-parse-imp (args)
  (let ((target-form (make-axiom-pattern (second args)))
        (subst-list (third (third args)))
        (subst-pairs nil))
    (dolist (subst-form subst-list)
      (unless (atom subst-form)
        (push (cons (first subst-form) (third subst-form)) subst-pairs)))
    (list target-form subst-pairs)))

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

;;; citp-parse-verbose
;;; :verbose {on | off}
(defun citp-parse-verbose (args)
  (second args))

;;; citp-parse-normalize
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
;;; :def <symbol> = <ctf> | <csp> | <init> | 
;;;
;;; (":def" "cf1" "=" (":ctf" ("[" (<Term>) "." "]")))
;;; ==> (:ctf "cf1" nil (:term (<Term>)))
;;; (":def" "cf2" "=" (":ctf-" ("{" (<Equation>) "." "}")))
;;; ==> (:ctf "cf2" t   (:eq (<Equation>)))
;;; (":def" "sp1" "=" (":csp" "{" ((<Equation> ".") (<Equation> ".")) "}"))
;;; ==> (:csp "sp1" nil ((<Equation> ".") (<Equation> ".")))
;;; (":def" "tactic-1" "=" ("(" ("si" "rd" "tc") ")"))
;;; ==> (:seq "tactic-1" ("si" "rd" "tc"))
;;; (":define" "*disr" "=" (":init" ("[" ("*disr") "]") "by" "{" (("X:PNat.PNAT" "<-" ("X#PNat")) #1=";" ("Y:PNat.PNAT" "<-" ("Y@PNat")) #1# ("Z:PNat.PNAT" "<-" ("Z@PNat")) #1#) "}"))
;;; (":define" "ts-ss2" "="(":init" ("as" "ts-ss-1") (#1="(" ("eq" ("ts.." #1# "SS:SeqSym" #2=")") "=" ("true") ".") #2#) "by" ("{" ("SS:SeqSym" "<-" ("ss")) ";" "}")))
;;; ==> (:init "*disr" nil (":init" ("[" ("*disr") "]") "by" "{" (("X:PNat.PNAT" "<-" #) #1=";" ("Y:PNat.PNAT" "<-" #) #1# ("Z:PNat.PNAT" "<-" #) #1#) "}"))

(defun citp-parse-define (args)
  (flet ((name-to-com (name)
           (cond ((equal name "(")
                  :seq)
                 ((equal (subseq name 0 4) ":ctf")
                  :ctf)
                 ((equal (subseq name 0 4) ":csp")
                  :csp)
                 ((equal (subseq name 0 4) ":ini") 
                  :init)
                 (t (with-output-chaos-error ('invalid-def)
                      (format t "Internal error, :def accepted ~a" name))))))
    (let* ((name (second args))
           (com-name (first (fourth args)))
           (command (name-to-com com-name))
           (dash-or-bang (or (and (member command '(:ctf :csp))
                                  (> (length com-name) 4))
                             (and (eq command :init)
                                  (> (length com-name) 5))))
           (body-form (case command
                        (:ctf (if (equal "[" (first (second (fourth args))))
                                  (list :term (second (second (fourth args))))
                                (list :eq (second (second (fourth args))))))
                        (:csp (third (fourth args)))
                        (:init (citp-parse-init (fourth args)))
                        (:seq (second (fourth args)))
                        (otherwise (with-output-chaos-error ('invalid-command)
                                     (format t "Internal error, :def invalid ~s" command))))))
      (list command name dash-or-bang body-form))))

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
                           (return-from citp-parse-spoiler t))))))
    (setq *citp-spoiler* value)
    (setf (citp-flag citp-spoiler) value)
    t))

;;; {:binspect | binspect} [in {<goal-name> | <module-name>} : ] <boolean-term> .
;;;
(defun parse-citp-binspect (args)
  (parse-term-in-context args))

(defun parse-term-in-context (args)
  (let (mode
        goal-name
        preterm
        (type (first args)))
    (if (and (stringp type)
             (eql (elt type 0) #\:))
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

;;; {:bgrind | bgrind} [in {<goal-name> | <module-name>} : ] <boolean-term> .
;;;
(defun parse-citp-bgrind (args)
  (parse-term-in-context args))

;;; {bshow | :bshow} [ { tree | grind } ]
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

;;; {bstart | :bstart} <variable-name>
;;;
(defun citp-parse-bstart (arg)
  (cadr arg))

;;; {bguess | :bguess} <strategy> &optional args
;;; 'bguess <strategy>'
;;; <strategy> ::= { implies | and | or }
;;; p implies q = true (p and q = p)
;;; p and q = false
;;; p or q = true
(defun citp-parse-bguess (args)
  (cdr args))

;;; citp-parse-use
;;; :use (<label> ... <label>)
;;; :use [<label>] { assoc | comm | id: <term> }
;;; (":use" ("(" ("a" "b" "c") ")"))
;;; (":use" ("[" "foo" "]" "{" (("assoc")) "}"))
(defun citp-parse-use (args)
  (let* ((body (second args))
         (type (first body)))
    (cond ((equal type "(")
           (cons :use (second body)))
          ((equal type "[")
           (let ((label (second body))
                 (theory (fifth body)))
             (list* :use-theory label theory)))
          (t (with-output-chaos-error ('invalid-form)
               (format t "invalid form of :use ~s" type))))))

;;; citp-parse-embed
;;; :embed (<label> ... <label>) as <module_name>
;;; (":embed" ("(" ("a" "b" "c") ")" "as" "foo"))
;;; (":embed" ("[" "foo" "]" "{" (("assoc") ("comm")) "}" "as" "foo"))
(defun citp-parse-embed (args)
  (let* ((body (second args))
         (type (first body)))
    (cond ((equal type "(")
           (let ((labels (second body))
                 (mod-name (fifth body))
                 (into (equal (fourth body) "into")))
             (list :embed labels mod-name into)))
          ((equal type "[")
           (let ((label (second body))
                 (theory (fifth body))
                 (into (equal (seventh body) "into"))
                 (mod-name (eighth body)))
             (list :embed-theory label theory mod-name into)))
          (t (with-output-chaos-error ('invalid-form)
               (format t "invalid :embed type ~s" type))))))

;;; citp-parse-reset
;;; :reset
;;;
(defun citp-parse-reset (args)
  args)

;;; citp-process-opattr-declaration-form
;;;
(defun citp-process-opattr-declaration-form (args &rest ignore)
  (declare (ignore ignore))
  (format t "~s" args))
  



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
(defun eval-citp-ind-on (args)
  (check-ptree)
  (with-in-module ((get-context-module))
    (let ((type (car args))
          (ind-form (cdr args)))
      (if (eq type :simple)
          (set-induction-variables ind-form)
        ;; :user defined induction scheme
        (let ((vars (first ind-form))
              (bases (second ind-form))
              (hypo (third ind-form))
              (steps (fourth ind-form)))
          (check-on-going)
          (let ((target-node (get-next-proof-context *proof-tree*)))
            (set-induction-variables-and-scheme target-node vars bases hypo steps)
            ;; then do the job
            (apply-user-defined-induction-scheme target-node)))))))

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
  (let ((target-goal (ptree-node-goal (get-target-goal-node))))
    (instanciate-axiom target-goal
                       (second args)    ; target
                       (third args)     ; variable-term pairs
                       (fourth args)    ; label
                       )))

;;; :imp
;;;
(defun eval-citp-imp (args)
  (check-ptree)
  (with-in-module ((goal-context (ptree-node-goal (get-target-goal-node))))
    (introduce-implication-to-goal (first args) ; target
                                   (second args)))) ;variable-term pairs

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
  (with-in-module ((get-context-module))
    (reset-rewrite-counters)
    (begin-rewrite)
    (apply-ctf (car ax-form) (cadr ax-form) (cddr ax-form))
    (end-rewrite)
    (report-citp-stat)
    (check-success *proof-tree*)))

;;; :csp
(defun eval-citp-csp (goal-ax-decls)
  (check-ptree)
  (with-in-module ((get-context-module))
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
          ((member target '("proved" "discharged") :test #'equal)
           (check-ptree)
           (print-discharged-sentences))
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
          ((member target '("switch" "switches" "flag" "flags") :test #'equal)
           (print-citp-flag citp-all))
          (t (with-output-chaos-error ('unknown)
               (format t "Unknown parameter to :show/:describe ~S" target))))))

;;; { :binspect | binspect }
;;;
(defun eval-citp-binspect (args)
  (let ((mode (first args))
        (goal-or-mod (second args))
        (preterm (third args)))
  (binspect-in mode goal-or-mod preterm)))


;;; { :bgrind | bgrind }
;;;
(defun eval-citp-bgrind (args)
  (bgrind-in (first args)               ; mode
             (second args)              ; goal or module
             (third args)               ; term tokens
             ))

;;; eval-citp-define : arg -> tactic-ctf or tactic-csp
;;; (:ctf "cf1" nil (:term (<Term>)))
;;; (:ctf "cf2" t   (:eq (<Equation>)))
;;; (:csp "sp1" nil ((<Equation> ".") ...))
;;; (:csp "sp2" t   ((<Equation> ".") ...))
;;; (:init "ini1" nil (:init ....))
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
                ((eq tactic-name :init)
                 (let ((ax (get-target-axiom *current-module* (second form))))
                   (setq tactic (make-tactic-init :name name
                                                  :axiom ax
                                                  :subst (third form)
                                                  :context *current-module*
                                                  :kind (car (last form))))))
                ((eq tactic-name :ind)
                 ;; ind
                 (setq tactic (make-tactic-ind :name name
                                               :vars ()
                                               :base ()
                                               :step ())))
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

;;;
;;; :use
;;;
(defun citp-eval-use (args)
  (check-ptree)
  (let ((type (car args))
        (body (cdr args)))
    (case type
      (:use
       (use-discharged-goals body))
      (:use-theory
       (let ((label (car body))
             (theory (cdr body)))
         (use-theory label theory))))))

;;;
;;; :embed
;;;
(defun citp-eval-embed (args)
  (check-ptree)
  (let ((type (car args))
        (body (cdr args)))
    (case type
      (:embed
       (let ((labels (car body))
             (mod-name (cadr body))
             (into (caddr body)))
         (embed-discharged-goals labels mod-name into)))
      (:embed-theory
       (let ((label (first body))
             (theory (second body))
             (mod-name (third body))
             (into (fourth body)))
       (embed-theory label theory mod-name into))))))

;;;
;;; :reset
;;;
(defun citp-eval-reset (&rest args)
  (declare (ignore args))
  (check-ptree)
  (reset-proof-session))

;;;
;;; :theory <opname> : <arity> -> <coarity> { assoc | comm | id: <term> }
;;;
(defun add-method-theory (decl)
  (check-ptree)
  (let ((theory (%opattrs-theory (%theory-decl-attribute decl)))
        (name (%theory-decl-name decl))
        (arity (%theory-decl-arity decl))
        (coarity (%theory-decl-coarity decl))
        (goal (ptree-node-goal (get-next-proof-context *proof-tree*))))
    (with-in-module ((goal-context goal))
      (let ((r-arity (mapcar #'(lambda (x) (or (find-sort-in *current-module* x)
                                               (with-output-chaos-error ('no-sort)
                                                 (princ "No such sort ")
                                                 (print-sort-ref x))))
                              arity))
            (r-coarity (or (find-sort-in *current-module* coarity)
                           (with-output-chaos-error ('no-sort)
                             (princ "No such sort ")
                             (print-sort-ref coarity)))))
        (let ((meth (find-method-in *current-module* name r-arity r-coarity)))
          (unless meth
            (with-output-chaos-error ('no-op)
              (format t "No such operator ~s" name)))
          (add-and-merge-method-theory meth theory *current-module*)
          (set-needs-parse)
          (set-needs-rule))))))

;;; EOF
