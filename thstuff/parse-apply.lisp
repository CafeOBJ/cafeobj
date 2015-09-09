;;;-*- Mode:LISP; Package:CHAOS; Base:10; Syntax:Common-lisp -*-
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
#|==============================================================================
                                 System: CHAOS
                                Module: thstuff
                             File: parse-apply.lisp
==============================================================================|#
#-:chaos-debug
(declaim (optimize (speed 3) (safety 0) #-GCL (debug 0)))
#+:chaos-debug
(declaim (optimize (speed 1) (safety 3) #-GCL (debug 3)))

;;; === APPLY COMMAND FAMILY PARSERS
;;;     ----------------------------------------------------------------------

;;; *****
;;; START
;;; *****
;;; - Syntax -----------------------------------------------------------------
;;; <Start> ::= start <term> .
;;; --------------------------------------------------------------------------

;;; Chaos form

(defterm start (%script)
  :visible (target)                     ; target term
  :eval eval-start-command
  )

;;; parser

(defun parse-start-command (e)
  (%start* (cadr e)))

;;; ************
;;; APPLY FAMILY
;;; ************

;;; apply command of Chaos is the subset(but not a restriction) of OBJ(ver2.0) +
;;; some extensions.  
;;;-----------------------------------------------------------------------------
;;;  (1) don't have <retract>. no problem, we have operator with error sorts as
;;;      their rank.
;;;  (2) allow rule labels with digit chars at its head.
;;;      only labels consisting of all digit chars are considered as rule
;;;      numbers. 
;;;  (3) explicit forward direction specifier `+' allowing module with `-'
;;;      at head of their names and vise versa.
;;;  aboves are not so important.
;;;  (4) break down features of `apply' into more elementary ones.
;;;      `apply' of OBJ seems trying "do everything at once", or "to be a
;;;      powerful tool applicable to almost everything" like swiss army
;;;      knife. must agree(shouldn't we?), but this makes its syntax rather
;;;      heavy and prevents us from doing some simple tasks in a handy manner.  
;;;      Chaos supports full apply command of OBJ (without <retract> of course) 
;;;      in itself, and also provides some new command "do a simple thing at one
;;;      time", whose produced informations can be used in the later use of
;;;      apply command. 
;;;      also have some extensions to OBJ's apply.
;;;      hopefully, these would be useful for those who uses Chaos system
;;;      interactively.
;;; 
;;;      === NEW COMMANDS & EXTENSIONS to APPLY of OBJ =========================
;;;      *NOTE* ----------------------------------------------------------------
;;;      like `apply', some new commands assume a term which is the result of
;;;      `start' or `parse' (even of `reduce') commands. we refer this term as
;;;      "$$term" in the sequel. a specific subterm of $$term may be also
;;;      refered and/or set by some commands; this subterm will be denoted by
;;;      "$$subterm". initially, that is, just after `start', `parse', or
;;;      `reduce', $$subterm is identical to $$term(the whole). 
;;;      -----------------------------------------------------------------------
;;;      (4-1) subterm selection :
;;;         [a] choose command
;;;            - SYNTAX --------------------------------------------------------
;;;              <SubtermSelection> ::= choose <Selectors> 
;;;            -----------------------------------------------------------------
;;;            this selects a subterm specified by <Selectors>.
;;;            <Selectors> is just the same to `apply' command. here is its
;;;            summary (selector "subterm" is added, see `* NOTE (1)' below):
;;;              <Selectors> ::= { top | term | subterm } |
;;;                              <Selector> { of <Selector>}*
;;;              <Selector>  ::= <OccurSelection> |
;;;                              <SubseqSelection> | <SubsetSelection>
;;;              <OccurSelection>  ::= "(" <Nat>+ ")"
;;;              <SubseqSelection> ::= "[" <Nat> .. <Nat> "]" | "[" <Nat> "]"
;;;              <SubsetSelection> ::= "{" <Nat> [, <Nat>]* "}"
;;;            - BEHAVIOUR -----------------------------------------------------
;;;            the meaning of <Slectors> is the same as OBJ.
;;;            the target term of `choose' is $$subterm(see *NOTE* above), and
;;;            it will be reset to the selected subterm. thus, succeeding
;;;            applications of choose command selects a "subterm of subterm of
;;;            ... subterm of $$subterm". 
;;;            one can archive the same effect at onece by a <Slectors> form
;;;            like  "<Selector> of <Selector> of ...", but the former way 
;;;            is useful for selecting a subterm of a complex(large) term
;;;            incrementaly being with some checks that a subterm is correctly
;;;            selected at some steps of choices.  
;;;            if sole "top" or "term" is given as <Selectors>, original whole
;;;            term ($$term) is selected as subterm and is set to $$subterm.
;;;            this is a handy way to cancell of preceding selections. but
;;;            of cource, if one `applied' some rules to selected subterm, $$term
;;;            would be changed, and then the $$term can be quite different from
;;;            its original.  
;;;            -----------------------------------------------------------------
;;;            * NOTE: (1) for combined use of `choose' and `apply', the
;;;                    <Selector> of apply command is extended. it now accepts
;;;                    "subterm" as a <Selector> which refers to a subterm
;;;                    selected by the last `choose' command. 
;;;                    (2) once some rewrite rule is successfully applied
;;;                    to somewhere in $$term, $$subterm is reset to $$term. 
;;;
;;;         [b] show command extension.
;;;             - SYNTAX -------------------------------------------------------
;;;               <ShowSubterm> ::= show subterm [ tree ]
;;;             ----------------------------------------------------------------
;;;             we extended `show' command so that it can print out the subterm
;;;             chosen by the last `choose' command ($$term will be printed if
;;;             there has been any selected proper subterm). 
;;;             this can be used for cirtifying the subterm selected by choose
;;;             command. if optional "tree" is given, also prints out $$subterm
;;;             in a tree form. 
;;;             *NOTE* ordinal "show term" will pirnt out $$term. for tree form
;;;                    print of $$term, "show tree" (specific to Chaos) can be
;;;                    used. also prepared "show term tree" though.
;;;      (4-2) listing out applicable rewrite rules.
;;;         [a] find command
;;;             - SYNTAX -------------------------------------------------------
;;;               <FindRule> ::= find { rule | +rule | -rule }
;;;             ----------------------------------------------------------------
;;;             - BEHAVIOUR ----------------------------------------------------
;;;             print-outs all axioms which can be successfully applied
;;;             to $$subterm. the direction as a rewrite rule is specified by
;;;             the argument "rule", "+rule" or "-rule".
;;;             given "rule", `find' searches through the set of all axioms
;;;             of the current context(current module) including imported axioms
;;;             of submodules and system generated ones for associative and/or
;;;             commutative operators, and selects ones whose left OR right hand
;;;             side matches to $$subterm. "+rule" try matches only to left-hand
;;;             side of the axioms (forward direction), and "-rule" is used for
;;;             specifying backward direction.
;;;             ----------------------------------------------------------------
;;;             printing form is arranged to be giving useful informations for
;;;             later `apply' commands.  each printed axioms has the form
;;;               ------------------------------------------------------
;;;               (<Nat>) {<RuleSpec>}+ : LHS {-->|<--} RHS [SUBST-INFO]
;;;               ------------------------------------------------------
;;;             where <Nat> is a natural number assigned by find command and
;;;             can be directly used as rule specifier of our extended apply
;;;             command (see (4-3) below for the extension.)
;;;             <RuleSpec> is just the same to rule specifier of OBJ's apply
;;;             command, which is in a form of <ModId>.<Nat> or <ModId>.<Id>.
;;;             find always prints former form and if an axioms has a label,
;;;             it will also be printed. of course these also can be used for
;;;             rule specifier of apply command. following a separate mark `:'
;;;             axiom itself is printed. between left and right hand side side,
;;;             --> or <-- sign is printed showing the direction as a rewrite 
;;;             rule. an axiom can have match on its both side to $$subterm
;;;             (this can happen as giving "rule"), the same axiom is printed 2
;;;             times with different <Nat>, <RuleSpec>(backward direction has
;;;             preceding "-") and direction sign between LHS and RHS. optional
;;;             SUBST-INFO is printed when the RHS(LHS) has extra variable than
;;;             LHS(RHS) in the case of forward(backward) direction. 
;;;             SUBST-INFO has the form
;;;              -------------------------------------------------------------
;;;              with <VarId> = <PsudeVar>:<SortId> {, <VarId> =
;;;                                                    <PsudeVar>:<SortId> }*
;;;              -------------------------------------------------------------
;;;             where, <VarId> is the variable name occur in the axiom, 
;;;             <PsudeVar> is an identifier generated by `find' command, and
;;;             <SortId> is a name of a sort of the variable. this provides
;;;             a template for <VarSubst> for apply command. one can substitute
;;;             `<PsudeVar>:<SortId>' with appopreate term and can give it to
;;;             an argument to `apply'. 
;;;      (4-3) extensions to `apply' command:
;;;          [a] rule specifier of apply command
;;;             - Syntax -----------------------------------------------------
;;;             apply <Nat> [<VarSubst>] { at | within } <Selectors> .
;;;             --------------------------------------------------------------
;;;             apply now accepts simple natural number as a rule specifier
;;;             which refers the number assigned by preceding `find'command to
;;;             a rewrite rule (see (4-2) above). 
;;;          [b] new  <Selector> option -- "subterm"
;;;             as noted in (4-1)[a] above, apply accepts "subterm" as a subterm
;;;             selector. 
;;;          [c] can omit <VarSubst>
;;;             can omit <VarSubst> even if there exists some extra variables.
;;;             in this case, system generates pusude variables (constant terms)
;;;             on the fly, and uses them instead of extra variables. 
;;;             in a similar manner, one can `start' with a term with some
;;;             variables in it. also, in this case, system generates constant
;;;             terms and supply them istead. this is almost the same with
;;;             `open'ing a module and declare some constants and uses them. 
;;;
;;;     (4-4) some support commands:
;;;         [a] showing apply context
;;;            separating out the functions of apply command requires us to keep
;;;            some context(selected subterms, applicable rules) in mind.
;;;            the following extension to `show' can be used for this purpose. 
;;;            - Syntax --------------------------------------------------------
;;;            <SowConText> ::= show apply context
;;;            -----------------------------------------------------------------
;;;            print-outs informations useful for using apply command in a form
;;;            like this:
;;;              -------------------------------------------------------
;;;              current module : name of current module.
;;;              term           : whole target term ($$term).
;;;              subterm        : subterm selected by `choose' command,
;;;                               also prints <Selctors>.
;;;              rules          : set of rules found by `find' command.
;;;              -------------------------------------------------------
;;;              
;;;  *LIMITATION* : we don't have `abbriviated' module names for complex
;;;                 module expressions. thus we are restricted to perform
;;;                 `apply' only in modules with simple name.
;;;                 seems to need something like `abbrev' of OBJ.
;;; * some extensions planned *
;;;    (1) `step' option:
;;;         must do apply process in interactive manner.
;;;    (2) `stop' option:
;;;         stop reduction process when we meet the `pattern' specified.
;;;         might need some interactive process, `continue',`done'or .. ?

;;; *NOTE on Semantics of <RuleSpec>* 
;;; the semantics of rule specifier(rule identifier or rule number) of
;;; <RuleSpec> in OBJ is only loosely defined. at least for me, careful reading
;;; of throughout OBJ manual doesn't  give me an enough infos to implement this
;;; feature. 
;;; the aim of specifier is of course to select one specific rule to be applied,
;;; but there exists some ambiguities here. 
;;; the follwing is the problem summarized and its treatment of current
;;; Chaos implementation.
;;; (1) searching context:
;;;    *(1-1) semantics of <ModId> is loose. 
;;;     how about rules imported from sub-modules? <ModId> limits to the
;;;     OWN rules of <ModId> or including ones of submodules? 
;;;     my understanding is that <ModId> says "search in all rewrite rules 
;;;     in <ModId> including imported ones" limiting the search space
;;;     to a subset of current module. this seems reasonable, so Chaos follows
;;;     this line. (*note* the real implementation of OBJ is more complex one 
;;;     reflecting the value of a global flag set by users with `set' command,
;;;     but this can make the behaviour of apply command magical one. we want
;;;     to make things more simple).
;;;    *(1-2) what is the rule number?
;;;     what does "2.MOD" mean? this says `the second' rule of module `MOD',
;;;     but which is the `second'? 
;;;    *(1-3) system generated rules. 
;;;     should we consider rules generated by the system, eg. some rules for
;;;     associative/commutative operators? from the user side, full control
;;;     of reduction needs these rules to be choosed. but generated rules has
;;;     no rule identifier, thus user must select them by `number'. 
;;; (2) multiple rules with the same identifier:
;;;     there is no syntactical limitation on rule identifiers, they can be
;;;     overloaded, and there is no automatic selection machanisms for choosing
;;;     one among them. Chaos asks user to select one 
;;;     

;;; APPLY FAMILY ---------------------------------------------------------------
;;; forms and parsers
;;; ----------------------------------------------------------------------------

;;; ******
;;; CHOOSE
;;; ******
(defterm choose (%script)
  :visible (selectors)                  ; one of :top, :subterm or list of
                                        ; selectors. 
  :eval eval-choose-command)

;;; ************
;;; INSPECT-TERM
;;; ************
(defterm inspect-term (%script)
  :visible ()
  :eval eval-inspect-term-command)

;;; get-selectors : selector-token-seq -> { symbol | list(token)}
;;;
;;; <Selectors>    ::= subterm | term | top | <Selector> { of <Selector>}*
;;; <Selector>     ::= <OccurSelection> | <SubseqSelection > | <SubsetSelection> }
;;; <OccurSelection>  ::= "(" <Nat>+ ")"
;;; <SubseqSelection> ::= "[" <Nat> .. <Nat> "]" | "[" <Nat> "]"
;;; <SubsetSelection> ::= "{" <Nat> [, <Nat>]* "}"
;;;
(defun get-selectors (selector-toks)
  (case-equal (car selector-toks)
              (("top" "term") :top)
              ("subterm" :subterm)
              (("(" "{" "[")
               ;; *NOTE* discard the first token
               ;; because of stupid behaviour of our token reader. 
               (cdr selector-toks))
              (t (with-output-chaos-error ('invalid-selector)
                   (format t "unknown type of selectors ~a" selector-toks)
                   ))))

(defun parse-choose-command (tok)
  (%choose* (get-selectors (cadr tok))))

;;; *****
;;; MATCH
;;; *****
;;; - Syntax -------------------------------------------------------------------
;;; <MatchCommand> ::= match <Term1> to <Term2> .
;;; <Term1>        ::= { it | term | top | subterm | <Term> }
;;; <Term2>        ::= { rule | +rule | -rule | <Term> }
;;;-----------------------------------------------------------------------------
(defterm match (%script)
  :visible (type                        ; or :match, :unify, :xmatch
            target                      ; or :it pre-term
            pattern                     ; or :rule, +rule, -rule, pre-term
            )
  :eval eval-match-command)

(defun parse-match-command (toks)
  (let (type
        target
        pattern)
    ;; 
    (setq type
      (if (equal "match" (car toks))
          :match
        (if (equal "xmatch" (car toks))
            :xmatch
          :unify)))
    (setq toks (cdr toks))              ; arguments
    ;; get target
    (loop (when (or (null toks)
                    (or (equal "to" (car toks))
                        (equal "with" (car toks))))
            (return))
      (push (car toks) target)
      (setq toks (cdr toks)))
    (setq target (car (nreverse target)))
    ;; get pattern
    (setq pattern (cadr toks))
    ;; make ast
    (%match* type
             (case-equal target
                         ((("top") ("term")) :top)
                         ((("subterm")) :subterm)
                         ((("it")) :it)
                         (t target))
             (case-equal pattern
                         ((("rule") ("rules")) :rule)
                         ((("+rule") ("+rules")) :+rule)
                         ((("-rule") ("-rules")) :-rule)
                         (t pattern)))))

;;; ****
;;; FIND 
;;; ****
;;;- Syntax --------------------------------------------------------------------
;;; <FindCommand> ::= find <What>
;;; <What>        ::= { rule | +rule | -rule }
;;;-----------------------------------------------------------------------------
;;; *NOTE* just the alias of "match it to <What> . "
;;;
(defun parse-find-command (toks)
  (%match* :match
           :it
           (case-equal (cadr toks)
                       (("rule" "rules") :rule)
                       (("+rule" "+rules") :+rule)
                       (("-rule" "+rules") :-rule)
                       (t (with-output-chaos-error ('invalid-rule-spec)
                            (princ "only `rule', `+rule', or `-rule' is meaningful for
find,")
                            (print-next)
                            (format t "but ~a is given." (cadr toks)))))))
;;; *****
;;; APPLY
;;; *****
;;; - Syntax --------------------------------------------------------------------
;;; <ApplyCommand> ::= apply <Action> <WhereSpec> <Selectors> .
;;; <Action>       ::= {red | reduction | print | ? |
;;;                    <RuleSpec> [<VarSubst>]}
;;; <RuleSpec>     ::= <Nat> | [ + | - ] [<ModId>].{<Nat> | <RuleId>}
;;; <VarSubst>     ::= with <VarId> = <Term> {, <VarId> = <Term>}*
;;; <WhereSpec>    ::= { at | within }
;;; <Selectors>    ::= subterm | term | top | <Selector> { of <Selector>}*
;;; <Selector>     ::= <OccurSelection> | <SubseqSelection > | <SubsetSelection> }
;;; <OccurSelection>  ::= "(" <Nat>+ ")"
;;; <SubseqSelection> ::= "[" { <Nat> .. <Nat> | <Nat> } "]"
;;; <SubsetSelection> ::= "{" <Nat> [, <Nat>]* "}"
;;;
;;; *note* the syntax of <Selectors> of OBJ is defined as
;;;   <Selectors> ::= <Slector> { of <Selector> }*
;;;   <Selector>  ::= { term | top } | <OccurSelection> | <SubseqSelection> | 
;;;                   <SubseSelection>
;;; this seemes to be strange for me. 
;;; how about "top of top of top" or "top of { 1, 3 } of top of [ 1 .. 2 ]"?
;;; these are meaningful, but unneccessarily complex. 
;;;-----------------------------------------------------------------------------

(defterm apply (%script)
  :visible (action                      ; action to be performed, one-of
                                        ;  :apply, :reduce, :print, :help.
            rule-spec                   ; rule specifier to be applied.
            substitution                ; list of variable bindings.
            where-spec                  ; one of :at, :within.
            selectors)                  ; list of selectors.
  :eval eval-apply-command)

;;; get-apply-action : <Action> -> action keyword
;;;
;;; <Action> ::= { red | reduction | print | help | <RuleSpec> [<VarSubst>]}
;;; * "help" & <VarSubst> are specially treated elsewhere.
;;;
(defun get-apply-action (tok)
  ;; tok ::= { red | reduction | reduce | print | <RuleSpec> }
  (case-equal tok
              (("red" "reduction" "reduce") :reduce)
              (("bred" "breduce" "behavioural-reduction") :breduce)
              (("execute" "exec") :exec)
              ("print" :print)
              (t :apply)))

;;; NOTE: rules labels cannot contain .
;;; parse-rule-spec : <RuleSpec> -> (Module Rule Direction)
;;; 
;;; <RuleSpec> ::= <Nat> | [ - | + ][<ModId>].{<Nat> | <Id>}
;;; <RuleSpec> ::= [ - | + ][<ModId>.]{<Nat> | <Id>}
;;;
#||
(defun parse-rule-spec (tok)
  (declare (type string tok))
  (if (every #'digit-char-p tok)
      (let ((val (parse-integer tok)))
        (unless (> val 0)
          (with-output-chaos-error ('invalid-rule-number)
            (princ "rule index must be greater than 0.")
            ))
        val)
    (let* ((fwd (eql #\+ (char tok 0)))
           (rev (eql #\- (char tok 0)))
           (i (if (or rev fwd) 1 0))
           (dot-pos (position-if #'(lambda (x) (char= #\. x)) tok)))
      (if dot-pos
          (list (subseq tok i dot-pos) (subseq tok (1+ dot-pos)) rev)
        (list "" (subseq tok i) rev)))))
||#

(defun parse-rule-spec (tok)
  (declare (type string tok))
  (let* ((fwd (eql #\+ (char tok 0)))
         (rev (eql #\- (char tok 0)))
         (i (if (or rev fwd) 1 0))
         (dot-pos (position-if #'(lambda (x) (char= #\. x)) tok)))
    (if dot-pos
        (list (subseq tok i dot-pos) (subseq tok (1+ dot-pos)) rev)
      (list "" (subseq tok i) rev))))

;;; get-apply-where : <WhereSpec> -> where keyword
;;; <WhereSpec> ::= { at | within }
;;;
(defun get-apply-where (where)
  (if (equal where "at")
      :at
    (if (equal where "within")
        :within
      (with-output-chaos-error ('invalid-apply-place)
        (format t "<WhereSpec> must be either \"at\" or \"within\", but ~a is specified"
                where)))))

;;; parse-apply-command
;;; parse whole form

(defun parse-apply-command (e)
  (when (equal '(("?")) (cdr e))
    (return-from parse-apply-command (%apply* :help nil nil nil nil)))
  (let* ((ee (cadr e))                  ; eliminate "apply" and the last "."
         (act (nth 0 ee)))
    (let* ((action (get-apply-action act))
           (rule-spec (if (eq action :apply)
                          (parse-rule-spec act))))
      (let* ((no-subst (stringp (nth 1 ee)))
                                        ; "at" "within" -- no substitution.
             (substtoks (if no-subst
                            nil
                          (nth 1 ee)))  ; we don't syntactic check here.
             (where-spec (get-apply-where (nth (if no-subst 1 2) ee)))
             (selectors (get-selectors (car (subseq ee (if no-subst 2 3))))))
        (%apply* action rule-spec substtoks where-spec selectors)))))

;;; EOF
