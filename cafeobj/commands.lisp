;;;-*- Mode:LISP; Package:CHAOS; Base:10; Syntax:Common-lisp -*-
#|==============================================================================
                            System: CHAOS
                           Module: cafeobj
                         File: commands.lisp
==============================================================================|#
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
#-:chaos-debug
(declaim (optimize (speed 3) (safety 0) #-GCL (debug 0)))
#+:chaos-debug
(declaim (optimize (speed 1) (safety 3) #-GCL (debug 3)))

(eval-when (:execute :load-toplevel)

;;; ---------------------------------------------------------------------------
;;; these hash tables are used for register keywords, document strings.
;;; these are used by toplevel command interpreter
;;; and cafeobj language construct evaluators.
;;; ---------------------------------------------------------------------------

  ;; halds systems toplevel commands, declarations accepted by top level
  (clrhash *cafeobj-top-commands*)

  ;; holds all of the declaration forms 
  ;; this is moved to 'declarations.lisp', because every time we add a new command
  ;; we needed to re-load whole system. 
  ;; (clrhash *cafeobj-declarations*)

  ;; this holds each commands/language constructs document strings.
  ;; systems' doc-generator refers to this hash table.
 (clrhash *cafeobj-doc-db*)

;;; --------------------------------------------------------------------------
;;; all of the declarations/commands in alphabetical order.
;;; --------------------------------------------------------------------------

;;; Remarks concerning :title :mdkey :doc :example and the order of the keys:
;;; If :title is not given, the *first* entry of the keys is used
;;; between surrounding backticks. That means that a simple command 
;;; like version will have :title set to `version`
;;; If :mdkey is not given, the *first* entry of the keys is used.
;;; The :mdkey value is used when shipping out to markdown as label
;;; for the title
;;;
;;; Output to markdown is formatted as follows:
;;;   "## ~a ## {#~a}~2%~a~2%" :title :mdkey :doc
;;;
;;; Note: entries *without* a :doc key will not be handled by the doc system

(define (":is")
    :type :doc-only
    :doc "Boolean expression: `A :is B` where `A` is a term and
`B` is a sort. Returns true if `A` is of sort `B`."
)
  
(define ("!")
    :category :misc
    :parser parse-shell-command
    :evaluator eval-ast
    :title "`! <command>`"
    :mdkey "commandexec"
    :doc "On Unix only, forks a shell and executes the given `<command>`."
)

(define ("#define")
    :category :element
    :parser identity
    :title "`#define <symbol> := <term> .`"
    :mdkey "sharp-define"
    :evaluator cafeobj-eval-module-element-proc
    :doc "TODO"
)

(define ("--" "**")
    :category :decl
    :parser parse-comment-command
    :evaluator identity
    :title "`**`, `**>`"
    :mdkey "starstar"
    :related ("--" ("comments"))
    :doc "Starts a comment which extends to the end of the line. 
With the additional `>` the comment is displayed while
evaluated by the interpreter."
)


(define ("-->" "**>")
    :category :decl
    :parser parse-comment-command
    :evaluator eval-ast
    :title "`--`, `-->`"
    :mdkey "dashdash"
    :related ("**" ("comments"))
    :doc "Starts a comment which extends to the end of the line. 
With the additional `>` the comment is displayed while
evaluated by the interpreter."
)

(define ("=")
    :type :doc-only
    :mdkey "axeq"
    :related ("==" "eq")
    :doc "The syntax element `=` introduces an axiom of the equational theory,
and is different from `==` which specifies an equality based on
rewriting."
)

(define ("==")
    :type :doc-only
    :mdkey "equality"
    :doc "The predicate `==` is a binary operator defined for each visible sort
and is defined in terms of evaluation. That is, for ground terms `t`
and `t'` of the same sort, `t == t'` evaluates to `true` iff terms
reduce to a common term. This is different from the equational `=`
which specifies the equality of the theory."
)

(define ("=/=")
    :type :doc-only
    :mdkey "notequal"
    :related ("==")
    :doc "Negation of the predicate `==`."
)

(define ("==>")
    :type :doc-only
    :mdkey "transrel"
    :related ("trans" ("search predicates"))
    :doc "This binary predicate is defined on each visible sort, and defines the
transition relation, which is reflexive, transitive, and closed under
operator application. It expresses the fact that two states (terms)
are connected via transitions."
)

(define ("=*=")
    :type :doc-only
    :mdkey "bequality"
    :doc "The predicate for behavioral equivalence, written `=*=`, is a binary
operator defined on each hidden sort."
)

(define ("=(n)=>" "=(n,m)=>" "=()=>")
    :type :doc-only
    :mdkey "searchpredsymb"
    :title "`=(n)=>`, `=(n,m)=>`, `=()=>`"
    :doc "See [`search predicates`](#searchpredicate)"
)

(define ("accept =*= proof switch")
    :type :doc-only
    :title "`accept =*= proof` switch"
    :mdkey "switch-accept"
    :doc "accept system's automatic proof of congruency of `=*=`"
)

(define ("?" "??" "?ex" "?example")
    :category :help
    :parser identity
    :evaluator cafeobj-top-level-help
    :title "`? [<term>]`"
    :mdkey "help" 
    :doc "Without any argument, shows the brief guide of online help system.
With argument gives the reference manual description of `term`.
In addition to this, many commands allow for passing `?` as argument
to obtain further help.

In case examples are provided for the `<term>`, they can be displayed
using `?ex <term>`. In this case the normal help output will also contain
an informational message that examples are available.

When called as ?? both documentation and examples are shown."
)

(define ("?apropos" "?ap")
    :category :help
    :parser identity
    :mdkey "apropos"
    :evaluator cafeobj-top-level-help
    :title "`?apropos <term> [<term> ...]`"
    :example "`````
CafeOBJ> ?ap prec oper
`````
will search for all entries that contain both `prec` and `oper` as
sub-strings. Matching is done as simple sub-string match.

`````
CafeOBJ> ?ap foo att[er]
`````
will search for entries that contain the string `foo` as well as
either the string `atte` or `attr`.
"
    :doc "Searches all available online docs for the terms passed.
Terms are separated by white space. Each term is tested independently 
and all terms have to match. Testing is done either by simple sub-string 
search, or, if the term looks like a regular expression (Perl style), 
by regex matching. In case a regex-like term cannot be parsed as regular
expression, it is used in normal sub-string search mode.

Note: Fancy quoting with single and double quotes might lead to unexpected problems."
)

(define ("all axioms switch")
    :type :doc-only
    :title "`all axioms` switch" 
    :mdkey "switch-all-axioms" 
    :related ("show")
    :doc "Controls whether axioms from included modules are shown
during a `show` invocation."
)

(define ("always memo switch")
    :type :doc-only
    :title "`always memo` switch" 
    :mdkey "switch-always-memo" 
    :related ("memo" ("operator attributes"))
    :doc "Turns on memorization of computation also for operators without
the [`memo`](#opattr) operator attribute."
)

(define ("apply")
    :category :proof
    :parser parse-apply-command
    :evaluator eval-ast
    :title "`apply <action> [ <subst> ] <range> <selection>`"
    :related ("choose" "start")
    :doc "Applies one of the following actions `reduce`, `exec`, `print`, or a
rewrite rule to the term in focus. 

`reduce`, `exec`, `print`
  ~ the operation acts on the (sub)term specified by `<range>` and
    `<selection>`. 

rewrite rule
  ~ in this case a rewrite rule spec has to be given in the following
    form:

    `[+|-][<mod_name>].<rule-id>`

    where `<mod_name>` is the name of a module, and `<rule-id>` either
    a number n - in which case the n. equation in the current module
    is used, or the label of an equation. If the `<mod_name>` is not
    given, the equations of the current module are considered. If the
    leading `+` or no leading character is given, the equation is
    applied left-to-right, which with a leading `-` the equation is
    applied right-to-left.

The `<subst>` is of the form

`with { <var_name> = <term> } +,`

and is used when applying a rewrite rule. In this case the variables
in the rule are bound to the given term.

`<range>` is either `within` or `at`. In the former case the action is
applied at or inside the (sub)term specified by the following
selection. In the later case it means exactly at the (sub)term.

Finally, the `<selection>` is an expression

`<selector> { of <selector> } *`

where each `<selector>` is one of

`top`, `term`
  ~ Selects the whole term

`subterm`
  ~ Selects the pre-chosen subterm (see [`choose`](#choose))

`( <number_list> )`
  ~ A list of numbers separated by blanks as in `(2 1)` indicates a 
    subterm by tree search. `(2 1)` means the first argument of the
    second argument.

`[ <number1> .. <number2> ]`
  ~ This selector can only be used with associative operators. It
    indicates a subterm in a flattened structure and selects the
    subterm between and including the two numbers given. `[n .. n]`
    can be abbreviated to `[n]`. 

    Example: If the term is `a * b * c * d * e`, then the 
    expression `[2 .. 4]` selects the subterm `b * c * d`.

`{ <number_set> }`
  ~ This selector can only be used with associative and commutative
  operators. It indicates a subterm in a multiset structure obtained
  from selecting the subterms at position given by the numbers.

  Example: If the operator `_*_` is declared as associative and
  commutative, and the current term is `b * c * d * c * e`, then
  then the expression `{2, 4, 5}` selects the subterm `c * c * e`."
)

(define ("auto context switch")
    :type :doc-only
    :title "`auto context` switch"
    :mdkey "switch-auto-context"
    :doc "Possible values: `on` or `off`, default is `off`.

If this switch is `on`, the context will automatically switch to
the most recent module, i.e., defining a module or inspecting 
a module's content will switch the current module."
)

(define  ("autoload")
    :category :library
    :parser parse-autoload-command
    :evaluator eval-ast
    :title "`autoload <module-name> <file-name>`"
    :related ("no autoload")
    :doc "When evaluating a <module-name> and found that
it is not yet declared, the system read in <file-name> then 
retries the evaluation."
)

(define ("no-autoload")
    :category :library
    :parser parse-no-autoload-command
    :evaluator eval-ast
    :title "`no autoload <module-name>`"
    :related ("autoload")
    :doc "Stop `autoload` of module with the name <module-name> .
Please refer to `autoload` command."
)

(define ("axioms" "axiom" "axs")
    :category :element
    :parser identity
    :evaluator cafeobj-eval-module-element-proc
    :title "`axioms { <decls> }`"
    :related ("signature" "imports" "var" "eq" "trans")
    :doc "Block enclosing declarations of variables, equations, and 
transitions.
Other statements are not allowed within the `axioms` block.
Optional structuring of the statements in a module."
)

(define ("bceq" "bcq")
    :category :element
    :parser identity
    :evaluator cafeobj-eval-module-element-proc
    :title "`bceq [ <label-exp> ] <term> = <term> if <boolterm> .`"
    :related ("eq" "ceq" "beq")
    :doc "Defines a behavioral conditional equation. For details see [`ceq`](#ceq)."
)

(define ("beq")
    :category :element
    :parser identity
    :evaluator cafeobj-eval-module-element-proc
    :title "`beq [ <label-exp> ] <term> = <term> .`"
    :related ("eq" "ceq" "bceq")
    :doc "Defines a behavioral equation. For details see [`eq`](#eq)."
)

(define ("bctrans" "bctr")
    :category :element
    :parser identity
    :evaluator cafeobj-eval-module-element-proc
    :title "`bctrans [ <label-exp> ] <term> => <term> if <bool> .`"
    :related ("trans" "ctrans" "btrans")
    :doc "Defines a behavioral conditional transition. 
For details see [`ctrans`](#ctrans)."
)

(define ("bop" "bops")
    :category :element
    :parser identity
    :evaluator cafeobj-eval-module-element-proc
    :title "`bop <op-spec> : <sorts> -> <sort>`"
    :related ("op")
    :doc "Defines a behavioral operator by its domain, co-domain, and the term 
construct. `<sorts>` is a space separated list of sort names containing
*exactly* one hidden sort. `<sort>` is a single sort name.

For `<op-spec>` see the explanations of [`op`](#op)."
)

(define ("bpred" "bpreds" "bpd" "bpds")
    :category :element
    :parser identity
    :evaluator cafeobj-eval-module-element-proc
    :title "`bpred <op-spec> : <sorts>`"
    :related ("op" "bop" "pred")
    :doc "Short hand for `op <op-spec> : <sorts> -> Bool` defining a
behavioral predicate."
)

(define ("breduce" "bred")
    :category :rewrite
    :parser parse-bred-command
    :evaluator eval-ast
    :title "`breduce [ in <mod-exp> : ] <term> .`"
    :related ("execute" "reduce")
    :doc "Reduce the given term in the given module, if `<mod-exp>` is given, 
otherwise in the current module. 

For `breduce` equations, possibly conditional, possibly behavioral, are taken
into account for reduction."
)

(define ("btrans" "btr")
    :category :element
    :parser identity
    :evaluator cafeobj-eval-module-element-proc
    :title "`btrans [ <label-exp> ] <term> => <term> .`"
    :related ("trans" "ctrans" "bctrans")
    :doc "Defines a behavioral transition. For details see [`trans`](#trans)."
)

(define ("cbred")
    :category :rewrite
    :parser parse-cbred-command
    :evaluator eval-ast
    :title "`cbred [ in <mod-exp> :] <term> .`"
    :doc "circular coinductive reduction: see
_Goguen, Lin, Rosu: Circular Coinductive Rewriting_
(Proceedings of Automated Software Engineering 2000) for details."
)

(define  ("cd") 
    :category :misc
    :parser parse-cd-command
    :evaluator eval-ast
    :title "`cd <dirname>`"
    :related ("pwd" "ls")
    :doc "Change the current working directory, like the Unix counterpart.
The argument is necessary. No kind of expansion or substitution is done."
)

(define ("ceq" "cq")
    :category :element
    :parser identity
    :evaluator cafeobj-eval-module-element-proc
    :title "`ceq [ <label-exp> ] <term> = <term> if <boolterm> .`"
    :related ("eq" "beq" "bceq")
    :doc "Defines a conditional equation. Spaces around the `if` are obligatory.
`<boolterm>` needs to be a Boolean term. For other requirements
see [`eq`](#eq)."
)

(define ("check")
    :category :checker
    :parser   parse-check-command
    :evaluator eval-ast
    :title "`check <options>`"
    :related ("regularize")
    :doc "This command allows for checking of certain properties of modules and
operators. 

`check regularity <mod_exp>`
  ~ Checks whether the module given by the module expression
    `<mod_exp>` is regular. 

`check compatibility <mod_exp>`
  ~ Checks whether term rewriting system of the module given by the
    module expression `<mod_exp>` is compatible, i.e., every
    application of every rewrite rule to every well-formed term
    results in a well-formed term. (This is not necessarily the case
    in order-sorted rewriting!)

`check laziness <op_name>`
  ~ Checks whether the given operator can be evaluated lazily. If not
    `<op_name>` is given, all operators of the current module are
    checked."
)

(define ("check switch")
    :type :doc-only
    :title "`check <something>` switch"
    :mdkey "switch-check"
    :doc "These switches turn on automatic checking of certain properties:

`check coherency`
  ~ check whether transitions and equations are coherent

`check compatibility`
  ~ see the [`check`](#check) command

`check import`
  ~ check conflicting importing mode of submodules

`check regularity`
  ~ see the [`check`](#check) command

`check sensible`
  ~ check whether a signature is sensible"
)

(define  ("choose") 
    :category :proof
    :parser parse-choose-command
    :evaluator eval-ast
    :title "`choose <selection>`"
    :mdkey "choose"
    :related ("apply" "start" ("`strat` in operator attributes" "operator attributes"))
    :doc "Chooses a subterm by the given `<selection>`. See [`apply`](#apply)
for details on `<selection>`."
)

(define ("clean memo" "clean")
    :category :rewrite
    :parser identity
    :evaluator cafeobj-eval-clear-memo-proc
    :title "`clean memo`"
    :mdkey "cleanmemo"
    :related (("clean memo switch" "`clean memo` switch"))
    :doc "Resets (clears) the memo storage of the system. Memorized computations 
are forgotten."
)

(define ("clean memo switch")
    :type :doc-only
    :title "`clean memo` switch"
    :mdkey "switch-clean-memo"
    :doc "Possible values: `on`, `off`, default `off`.

tells the system to be forgetful."
)

(define ("close")
    :category :proof
    :parser parse-close-command
    :evaluator eval-ast
    :title "`close`"
    :related ("open")
    :doc "This command closes a modification of a module started by [`open`](#open)."
)

(define ("comments")
    :type :doc-only
    :title "comments"
    :related ("**" "--")
    :doc "The interpreter accepts the following strings as start of a comment
that extends to the end of the line: `--`, `-->`, `**`, `**>`.

The difference in the variants with `>` is that the comment is
displayed when run through the interpreter."
)

(define ("cond limit switch")
    :type :doc-only
    :title "`cond limit` switch"
    :mdkey "switch-cond-limit"
    :doc "TODO"
)

(define ("ctrans" "ctr")
    :category :element
    :parser identity
    :evaluator cafeobj-eval-module-element-proc
    :title "`ctrans [ <label-exp> ] <term> => <term> if <term> .`"
    :related ("trans" "btrans" "bctrans")
    :doc "Defines a conditional transition. For details see [`trans`](#trans)
and [`ceq`](#ceq)."
)

(define ("describe" "desc")
    :category :inspect
    :parser parse-show-command
    :evaluator eval-ast
    :title "`describe <something>`"
    :related ("show")
    :doc "Similar to the `show` command but with more details. Call `describe ?` for
the possible set of invocations."
)

(define ("eof")
    :type :doc-only
    :doc "Terminates reading of the current file. Allows for keeping
untested code or documentations below the `eof` mark. Has
to be on a line by itself without leading spaces."
)

(define ("eq")
    :category :element
    :parser identity
    :evaluator cafeobj-eval-module-element-proc
    :title "`eq [ <label-exp> ] <term> = <term> .`"
    :related ("ceq" "beq" "bceq")
    :doc "Declares an axiom, or equation.

Spaces around the `=` are necessary to separate the left from
the right hand side. The terms given must belong to the
same connected component in the graph defined by the sort ordering.

In simple words, the objects determined by the terms must be
interpretable as of the same sort.

The optional part `<label-exp>` serves two purposes, one is to give
an axiom an identifier, and one is to modify its behavior. The
`<label-exp>` is of the form:

` [ <modifier> <label> ] : `

Warning: The square brackets here are *not* specifying optional
components, but syntactical elements. Thus, a labeled axiom
can look like:

`eq[foobar] : foo = bar .`

The `<modifier>` part is used to change the rewriting behavior of
the axiom.  There are at the moment two possible 
modifiers, namely `:m-and (:m-and-also)` and `:m-or (:m-or-else)`.
Both make sense only for operators where the arguments come from an 
associative sort.
In this case both modifiers create all possible permutations
of the arguments and rewrite the original term to the conjunction
in case of `:m-and` or to the disjunction in case of `:m-or` of all
the generated terms.

Assume that `NatSet` is a sort with associative constructor modeling
a set of natural number, and let

`````
  pred p1: Nat .
  ops q1 q2 : NatSet -> Bool .
  eq [:m-and]: q1(N1:Nat NS:NatSet) = p1(N1) .
  eq [:m-or]:  q2(N1:Nat NS:NatSet) = p1(N1) .
`````

In this case an expression like `q1(1 2 3)` would reduce to 
`p1(1) and p1(2) and p1(3)` (modulo AC), and `q2(1 2 3)` into
the same term with `or` instead."
)

(define ("exec limit switch")
    :type :doc-only
    :title "`exec limit` switch"
    :mdkey "switch-exec-limit"
    :related ("reduce")
    :doc "Possible values: integers, default limit 4611686018427387903.

Controls the number of maximal transition steps."
)

(define ("exec trace switch")
    :type :doc-only
    :title "`exec trace` switch"
    :mdkey "switch-exec-trace"
    :related ("reduce")
    :doc "Possible values: `on` `off, default `off`.

controls whether further output is provided during reductions."
)


(define ("execute" "exec")
    :category :rewrite
    :parser parse-exec-command
    :evaluator eval-ast
    :title "`execute [ in <mod-exp> : ] <term> .`"
    :related ("breduce" "reduce")
    :doc "Reduce the given term in the given module, if `<mod-exp>` is given, 
otherwise in the current module. 

For `execute` equations and transitions, possibly conditional, are taken
into account for reduction."
)


(define ("extending" "ex")
    :category :element
    :parser identity
    :evaluator cafeobj-eval-module-element-proc
    :title "`extending ( <modexp> )`"
    :related ("including" "protecting" "using")
    :doc "Imports the object specified by `modexp` into the current
module, allowing models to be inflated, but not collapsing. 
See [`module expression`](#moduleexpression) for format of `modexp`."
)

(define  ("find")
    :category :proof
    :parser parse-find-command
    :evaluator eval-ast
    :doc "TODO"
)

(define ("find all rules switch")
    :type :doc-only
    :title "`find all rules` switch"
    :mdkey "switch-find-all-rules"
    :doc "If this switch is on, the [`apply`](#apply) command
will search for applicable rules not only in the set of
user-defined equations, but also in those added by the system."
)



(define ("full reset" "full-reset" "full") 
    :category :system
    :parser parse-full-reset-command
    :evaluator eval-ast
    :mdkey "fullreset"
    :related ("reset" "prelude")
    :doc "Reinitializes the internal state of the system. All supplied modules
definitions are lost."
)

(define ("gendoc")
    :category :io
    :parser parse-gendoc-command
    :evaluator eval-ast
    :title "`gendoc <pathname>`"
    :doc "generates reference manual from system's on line help documents, 
and save it to `pathname`."
)

(define ("imports")
    :category :element
    :parser identity
    :evaluator cafeobj-eval-module-element-proc
    :title "`imports { <import-decl> }`"
    :related ("signature" "axioms" "extending" "including" "protecting"
              "using")
    :doc "Block enclosing import of other modules (`protecting` etc). 
Other statements are not allowed within the `imports` block.
Optional structuring of the statements in a module."
)

(define ("include BOOL switch")
    :type :doc-only
    :title "`include BOOL` switch"
    :mdkey "switch-include-bool"
    :doc "Possible values: `on` `off`, default `on`.

By default a couple of built-in modules are implicitly imported with
protecting mode. In particular, BOOL is of practical importance. It
defines Boolean operators. It is imported to admit conditional
axioms.

This switch allows to disable automatic inclusion of BOOL."
)

(define ("include RWL switch")
    :type :doc-only
    :title "`include RWL` switch"
    :mdkey "switch-include-rwl"
    :doc "Possible values: `on` `off`, default `off`.

This switch allows to disable automatic inclusion of RWL."
)

(define ("including" "inc")
    :category :element
    :parser identity
    :evaluator cafeobj-eval-module-element-proc
    :title "`including ( <modexp> )`"
    :related ("extending" "protecting" "using" ("module expression"))
    :doc "Imports the object specified by `modexp` into the current
module. 

See [`module expression`](#moduleexpression) for format of `modexp`."
)

(define  ("input" "in")
    :category :misc
    :parser parse-input-command
    :evaluator cafeobj-eval-input-proc
    :title "`input <pathname>`"
    :doc "Requests the system to read the file specified by the
pathname. The file itself may contain `input` commands.
CafeOBJ reads the file up to the end, or until it encounters
a line that only contains (the literal) `eof`."
)

(define ("instantiation")
    :type :doc-only
    :title "instantiation of parameterized modules"
    :doc "Parameterized modules allow for instantiation. The process of
instantiation binds actual parameters to formal parameters. The result
of an instantiation is a new module, obtained by replacing occurrences
of parameter sorts and operators by their actual counterparts. If, as
a result of instantiation, a module is imported twice, it is assumed
to be imported once and shared throughout.

Instantiation is done by

`<module_name> ( <bindings> )`

where `<module_name>` is the name of a parameterized module, and
`<bindings>` is a comma-separated list of binding constructs.

using declared views
  ~ you may bind an already declared view to a parameter:
    
    `<parameter> <= <view_name>`

    If a module `M` has a parameter `X :: T` and a view `V` from `T`
    to `M'` is declared, `V` may be bound to `X`, with the effect that

    1. The sort and operator names of `T` that appear in the body
       of `M` are replaced by those in `M'`, in accordance with `V`,

    2. The common submodules of `M` and `M'` are shared.

using ephemeral views
  ~ In this case the view is declared and used at the same time.

    `<parameter> <= view to <mod_name> { <view_elements> }`

    See [`view`](#view) for details concerning `<view_elements>`. The
    `from` parameter in the `view` declaration is taken from
    `<parameter>`.


To make notation more succinct, parameters can be identified also by
position instead of names as in

`<mod_name> ( <view_name>, <view_name> )`

which would bind the `<view_name>`s to the respective parameters
of the parameterized module `<mod_name>`.

This can be combined with the ephemeral definition of a view like in
the following example (assume `ILIST` has two parameters):

~~~~~
module NAT-ILIST {
  protecting ( ILIST(SIMPLE-NAT { sort Elt -> Nat },
                     DATATYPE   { sort Elt -> Data }) )
}
~~~~~"
)


(define ("let") 
    :category :decl
    :parser process-let-declaration-form
    :evaluator eval-ast
    :title "`let <identifier> = <term> .`"
    :doc "Using `let` one can define aliases, or context variables. Bindings
are local to the current module. Variable defined with `let` can be
used in various commands like `reduce` and `parse`. 

Although `let` defined variable behave very similar to syntactic
shorthands, they are not. The right hand side `<term>` needs to
be a fully parsable expression."
)

(define ("libpath switch" "library path")
    :type :doc-only
    :title "`libpath` switch"
    :mdkey "switch-libpath"
    :doc "Possible values: list of strings.

The switch `libpath` contains a list of directories where CafeOBJ
searches for include files. Addition and removal of directories can be
done with

`````
set libpath + <path1>:<path2>:...
set libpath - <path1>:<path2>:...
`````

or the full libpath reset by `set libpath <path1>:<path2>:...`

The current directory has a privileged status: It is always searched
first and cannot be suppressed."
)


(define ("look" "look up")
    :category :inspect
    :parser parse-look-up-command
    :evaluator eval-ast
    :title "`look up <something>`"
    :mdkey "lookup"
    :doc "displays the location (module) and further information
where `<something>` has been defined."
    :example "~~~~~
open INT .
%INT> look up Nat .

Nat
  - sort declared in NAT-VALUE
  - operator:
    op Nat : -> SortId { constr prec: 0 }
    -- declared in module NAT-VALUE

%INT>
~~~~~"
)

(define ("ls")
    :category :misc
    :parser parse-ls-command
    :evaluator eval-ast
    :title "`ls <pathname>`"
    :related ("cd" "pwd")
    :doc "lists the given `pathname`. Argument is obligatory."
)

(define ("match" "unify")
    :category :inspect
    :parser parse-match-command
    :evaluator eval-ast
    :title "`match <term_spec> to <pattern> .`"
    :doc "Matches the term denoted by `<term_spec>` to the
pattern. `<term_spec>` is either `top` or `term` for the term set by
the `start` command; `subterm` for the term selected by the `choose`
command; `it` has the same meaning as `subterm` if `choose` was used,
otherwise the same meaning as `top`, or a normal term expression.

The given `<pattern>` is either `rules`, `-rules`, `+rules`, one of
these three prefixed by `all`, or a term. If one of the `rules` are
given, all the rules where the left side (for `+rules`), the right
side (for `-rules`), or any side (for `rules`) matches. If the `all`
(with separating space) is given all rules in the current context,
including those declared in built-in modules, are inspected.

If a term is given, then the two terms are matched, and if successful,
the matching substitution is printed."
)

(define ("module" "mod" "module*" "mod*" "module!" "mod!" "sys:mod!" "sys:module!" "sys:mod*" "sys:module*")
    :category :decl
    :parser process-module-declaration-form
    :evaluator eval-ast
    :title "`[sys:]module[!|*] <modname> [ ( <params> ) ] [ <principal_sort_spec> ] { mod_elements ... }`"
    :doc "Defines a module, the basic building block of CafeOBJ. Possible elements
are declarations of 

  - import - see `protecting`, `extending`, `including`, `using`
  - sorts - see `sort declaration`
  - variable - see `var`
  - equation - see `op`, `eq`, `ceq`, `bop`, `beq`, `bceq`
  - transition - see `trans`, `ctrans`, `btrans`, `bctrans`
  
`modname` is an arbitrary string.

`module*` introduces a loose semantic based module.

`module!` introduces a strict semantic based module.

`module` introduces a module without specified semantic type.

If `params` are given, it is a parameterized module. 
See [`parameterized module`](#parameterizedmodule) for more details.

If `principal_sort_spec` is given, it has to be of the form
`principal-sort <sortname>` (or `p-sort <sortname>`). The principal
sort of the module is specified, which allows more concise `view`s from
single-sort modules as the sort mapping needs not be given."
)

(define ("parameterized module")
    :type :doc-only
    :mdkey "parameterizedmodule"
    :related (("qualified sort"))
    :doc "A module with a parameter list (see `module`) is a parameterized module.
Parameters are given as a comma (`,`) separated list. Each parameter is
of the form `[ <import_mode> ] <param_name> :: <module_name>` 
(spaces around `::` are obligatory).

The parameter's module gives minimal requirements on the module
instantiation.

Within the module declaration sorts and operators of the parameter
are qualified with `.<parameter_name>` as seen in the example below."
    :example "~~~~~
mod* C {
  [A]
  op add : A A -> A .
}
mod! TWICE(X :: C) {
  op twice : A.X -> A.X .
  eq twice(E:A.X) = add.X(E,E) .
}
~~~~~"
)

(define ("memo switch")
    :type :doc-only
    :title "`memo` switch"
    :mdkey "switch-memo"
    :doc "controls the memorization of computations. The system memorizes 
evaluations of operators declared with the [`memo`](#opattr) operator
attribute. Turning this switch off disables all memorization."
)

(define ("module expression")
    :type :doc-only
    :mdkey "moduleexpression"
    :doc "In various syntax elements not only module names itself, but whole
module expressions can appear. A typical example is

`open <mod_exp> .`

which opens a module expression. The following constructs are
supported:

module name
  ~ using the name of a module

renaming
  ~ `<mod_exp> * { <mappings> }`

    This expressions describes a new module where sort and/or
    operators are renamed. 
    `<mappings>` are like in the case of [`view`](#view) a comma
    separated list of mappings of either sorts (`sort` and `hsort`) or
    operators (`op` and `bop`). Source names may be qualified, while
    target names are not, they are required to be new names. Renaming
    is often used in combination with [instantiation](#instantiation).

summation
  ~ `<mod_exp> + <mod_exp>`

    This expression describes a module consisting of all the module
    elements of the summands. If a submodule is imported more than
    once, it is assumed to be shared."
)

(define ("on-the-fly" "on the fly")
    :type :doc-only
    :title "on-the-fly declarations"
    :mdkey "onthefly"
    :related ("var")
    :doc "Variables and constants can be declared *on-the-fly* (or *inline*). If an 
equation contains a qualified variable (see [qualified term](#qualified)),
i.e., `<name>:<sort-name>`, then from this point on *within* the current
equation only `<name>` is declared as a variable of sort `<sort-name>`.

It is allowed to redeclare a previously defined variable name via
an on-the-fly declaration, but as mentioned above, not via an 
explicit redeclaration.

Using a predeclared variable name within an equation first as is,
that is as the predeclared variable, and later on in the same 
equation with an on-the-fly declaration is forbidden. That is, under
the assumption that `A` has been declared beforehand, the following
equation is *not* valid:

`eq foo(A, A:S) = A .`

On-the-fly declaration of constants are done the same way, where the
`<name>` is a constant name as in `\`a:Nat`. Using this construct is
similar to defining an operator

`op <name> : -> <sort>`

or in the above example, `op a : -> Nat .`, besides that the
on-the-fly declaration of constants, like to one of variables, is only
valid in the current context (i.e., term or axiom). These constant
definitions are quite common in proof scores."
)

(define ("op" "ops")
    :category :element
    :parser identity
    :evaluator cafeobj-eval-module-element-proc
    :title "`op <op-spec> : <sorts> -> <sort> { <attribute-list> }`"
    :doc "Defines an operator by its domain, co-domain, and the term construct.
`<sorts>` is a space separated list of sort names, `<sort>` is a 
single sort name.
`<op-spec>` can be of the following forms:

prefix-spec
  ~ the `<op-spec>` does not contain a literal `_`:
    This defines a normal prefix operator with domain `<sorts>` and
    co-domain `<sort>`

    Example: `op f : S T -> U`
mixfix-spec
  ~ the `<op-spec>` contains exactly as many literal `_` as there are
    sort names in `<sorts>`:
    This defines an arbitrary mixfix (including postfix) operator
    where the arguments are inserted into the positions designated 
    by the underbars.

    Example: `op _+_ : S S -> S`

For the description of `<attribute-list>` see the entry for
[operator attributes](#opattr)."
)


(define ("open")
    :category :proof
    :parser parse-open-command
    :evaluator eval-ast
    :title "`open <mod_exp> .`"
    :related ("close" "module expression" "select")
    :doc "This command opens the module specified by the module expression
`<mod_exp>` and allows for declaration of new sorts, operators, etc."
)

(define ("operator attributes" "assoc" "comm" "id" "idr" "strat" "constr")
    :type :doc-only
    :mdkey "opattr"
    :related ("bop")
    :doc "In the specification of an operator using the [`op`](#op) (and
related) keyword, attributes of the operator can be specified.
An `<attribute-list>` is a space-separate list of single
attribute definitions. Currently the following attributes are
supported

`associative`
  ~ specifies an associative operator, alias `assoc`

`commutative`
  ~ specifies a commutative operator, alias `comm`

`itempotence`
  ~ specifies an idempotent operator, alias `idem`

`id: <const>`
  ~ specifies that an identity of the operator exists and 
    that it is `<const>`

`prec: <int>`
  ~ specifies the parsing precedence of the operator, an integer <int>.
    Smaller precedence values designate stronger binding. See
    [operator precedence](#opprec) for details of the predefined
    operator precedence values.

`l-assoc` and `r-assoc`
  ~ specifies that the operator is left-associative or
  right-associative

`constr`
  ~ specifies that the operator is a constructor of the coarity sort.
    (not evaluated at the moment)


`strat: ( <int-list> )`
  ~ specifies the evaluation strategy. Each integer in the list refers
    to an argument of the operator, where `0` refers to the whole term,
    `1` for the first argument, etc. Evaluation proceeds in order of
    the `<int-list>`. Example:

    `op if_then_else_fi : Bool Int Int -> Int { strat: (1 0) }`
 
    In this case the first argument (the Boolean term) is tried to
    be evaluated, and depending on that either the second or third.
    But if the first (Boolean) argument cannot be evaluated, 
    no evaluation in the subterms will appear.

    Using negative values allows for lazy evaluation of the corresponding
    arguments.

`memo`
  ~ tells the system to remember the results of evaluations where the
    operator appeared. See [`memo` switch](#switch-memo) for details.

Remarks:

  - Several operators of the same arity/coarity can be defined by
    using `ops` instead of `op`:

    `ops f g : S -> S`

    For the case of mixfix operators the underbars have to be given
    and the expression surrounded by parenthesis:

    `ops (_+_) (_*_) : S S -> S`

  - Spaces *can* be part of the operator name, thus an operator 
  definition of `op foo op : S -> S` is valid, but not advisable,
  as parsing needs hints.

  - A single underbar cannot be an operator name."
)

(define ("operator precedence" "precedence")
    :type :doc-only
    :mdkey "opprec"
    :related (("operator attributes"))
    :doc "CafeOBJ allows for complete freedom of syntax, in particular infix
operators and overloading. To correctly parse terms that are ambiguous,
all operators have precedence values. These values can be adjusted
manually during definition of the operator 
(see [operator attributes](#opattr)). In absence of manual
specification of the operator precedence, the values are determined by
the following rules:

- standard prefix operators, i.e., those of the form `op f : S1 .. Sk -> S`,
  receive operator precedence value 0.
- unary operators, i.e., those of the form `op u_ : S1 -> S`, receive
  precedence 15.
- mix-fix operators with first and last token being arguments, i.e.,
  those of the form `op _ arg-or-op _ : S1 .. Sk -> S`, receive
  precedence 41.
- all other operators (constants, operators of the form `a _ b`, etc.)
  receive precedence 0."
)

(define ("parse")
    :category :parse
    :parser parse-parse-command
    :evaluator eval-ast
    :title "`parse [ in <mod-exp> : ] <term> .`"
    :related ("qualified term")
    :doc "Tries to parse the given term within the module specified by
the module expression `<mod-exp>`, or the current module if not given,
and returns the parsed and qualified term.

In case of ambiguous terms, i.e., different possible parse trees, the
command will prompt for one of the trees."
)

(define ("parser normalize switch")
    :type :doc-only
    :title "`parse normalize` switch"
    :mdkey "switch-parse-normalize"
    :doc "TODO"
)

(define ("pred" "pd" "preds" "pds")
    :category :element
    :parser identity
    :evaluator cafeobj-eval-module-element-proc
    :title "`pred <op-spec> : <sorts>`"
    :related ("op" "bpred")
    :doc "Short hand for `op <op-spec> : <sorts> -> Bool` defining a predicate."
)

(define ("print depth switch")
    :type :doc-only
    :title "`print depth` switch"
    :mdkey "switch-print-depth"
    :doc "Possible values: natural numbers, default `unlimited`.

Controls to which depth terms are printed."
)

(define ("print mode switch")
    :type :doc-only
    :title "`print mode` switch"
    :mdkey "switch-print-mode"
    :doc "Possible values: `normal` `fancy` `tree` `s-expr`

Selects one of the print modes."
)

(define ("print trs switch")
    :type :doc-only
    :title "`print trs` switch"
    :mdkey "switch-print-trs"
    :related ("search predicates")
    :doc "Possible values: `on` `off`, default `off`

If set to `on`, print the rules used during reduction of 
`=(_,_)=>+_if_suchThat_{_}`."
)


(define ("protect")
    :category :switch
    :parser parse-protect-command
    :evaluator eval-ast
    :title "`protect <module-name>`"
    :related ("unprotect")
    :doc "Protect a module from being overwritten.
Some modules vital for the system are initially protected.
Can be reversed with `unprotect`."
)

(define ("protecting" "pr")
    :category :element
    :parser identity
    :evaluator cafeobj-eval-module-element-proc
    :title "`protecting ( <modexp> )`"
    :related ("extending" "using" "including")
    :doc "Imports the object specified by `modexp` into the current
module, preserving all intended models as they are. 
See [`module expression`](#moduleexpression) for format of `modexp`."
)

(define  ("provide") 
    :category :library
    :parser parse-provide-command
    :evaluator eval-ast
    :title "`provide <feature>`"
    :related ("require")
    :doc "Discharges a feature requirement: once `provide`d, all the subsequent
`require`ments of a feature are assumed to have been fulfilled
already."
)


(define  ("pwd")
    :category :misc
    :parser parse-pwd-command
    :evaluator eval-ast
    :related ("cd" "ls" "pushd" "popd" "dirs")
    :doc "Prints the current working directory."
)

(define ("qualified sort" "qualified operator" "qualified parameter" "qualify")
    :type :doc-only
    :title "qualified sort/operator/parameter"
    :mdkey "qualifiedother"
    :related ("parameterized module" "qualified term")
    :doc "CafeOBJ allows for using the same name for different sorts,
operators, and parameters. One example is declaring the same sort in
different modules. In case it is necessary to qualify the sort,
operator, or parameter, the intended module name can be affixed after
a literal `.`: `<name>.<modname>`

Example: In case the same sort `Nat` is declared in both the module
`SIMPLE-NAT` and `PANAT`, one can use `Nat.SIMPLE-NAT` to reference
the sort from the former module.

Furthermore, a similar case can arise when operators of the same name
have been declared with different number of arguments. During operator
renaming (see [view](#view)) the need
for qualification of the number of parameters might arise. In this
case the number can be specified after an affixed `/`: 
`<opname>/<argnr>`"
)

(define ("qualified term")
    :type :doc-only
    :mdkey "qualified"
    :example "`(1):NzNat` `(2):Nat`"
    :related ("parse")
    :doc "In case that a term can be parsed into different sort, it is possible to
qualify the term to one of the possible sorts by affixing it with 
`: <sort-name>` (spaces before and after the `:` are optional)."
)

(define ("quiet switch")
    :type :doc-only
    :title "`quiet` switch"
    :mdkey "switch-quiet"
    :related ("verbose")
    :doc "Possible values: `on` `off`, default `off`

If set to `on`, the system only issues error messages."
)

(define ("quit")
    :type :doc-only
    :doc "Leaves the CafeOBJ interpreter."
)

(define ("reduce" "red")
    :category :rewrite
    :parser parse-reduce-command
    :evaluator eval-ast
    :title "`reduce [ in <mod-exp> : ] <term> .`"
    :mdkey "reduce"
    :related ("execute" "breduce")
    :doc "Reduce the given term in the given module, if `<mod-exp>` is given, 
otherwise in the current module. 

For `reduce` only equations and conditional equations are taken into
account for reduction."
)

(define ("reduce conditions")
    :type :doc-only
    :title "`reduce conditions` switch"
    :mdkey "switch-reduce-conditions"
    :related ("apply")
    :doc "Possible values: `on` `off`, default `off`.

When using [`apply`](#apply) to step through a reduction, this switch
allows to turn on automatic reduction of conditions in conditional
equations. "
)

(define ("regularize")
    :category :misc
    :parser parse-regularize-command
    :evaluator eval-ast
    :title "`regularize <mod-name>`"
    :doc "Regularizes the signature of the given module, ensuring that every
term has exactly one minimal parse tree. In this process additional
sorts are generated to ensure unique least sort of all terms.

Modules can be automatically regularized by the interpreter if the
`regularize signature` switch is turn to `on`."
)

(define ("regularize signature switch" "reg signature")
    :type :doc-only
    :title "`regularize signature` switch"
    :mdkey "switch-regularize-signature"
    :doc "See [`regularize](#regularize)"
)

(define  ("require") 
    :category :library
    :parser parse-require-command
    :evaluator eval-ast
    :title "`require <feature> [ <pathname> ]`"
    :related ("provide")
    :doc "Requires a feature, which usually
denotes a set of module definitions. Given this command, the
system searches for a file named the feature, and read the file
if found. If the `<feature>` contains `::`, they are treated as
path separators.

If a pathname is given, the system searches for a file
named the pathname instead.
"
    :example "
~~~~~
CafeOBJ> require foo::bar
~~~~~
would search for `foo/bar.cafe` in the pathes from `libpath`"
)


(define ("reset")
    :category :system
    :parser parse-reset-command
    :evaluator eval-ast
    :related ("full reset" "prelude")
    :doc "Restores the definitions of built-in modules and preludes,  but does not
affect other modules."
)

(define ("rewrite limit switch" "rew limit")
    :type :doc-only
    :title "`rewrite limit` switch"
    :mdkey "switch-rewrite"
    :related ("step switch")
    :doc "Possible values: positive integers, default not specified.

Allows limiting the number of rewrite steps during a step-wise
execution."
)

(define ("search predicates")
    :type :doc-only
    :mdkey "searchpredicate"
    :doc "CafeOBJ provides a whole set of search predicates, that searches
the reachable states starting from a given state, optionally checking
additional conditions. All of them based on the following three basic ones:

  - `S =(n,m)=>* SS [if Pred]` search states reachable by 0 or more transitions;
  - `S =(n,m)=>+ SS [if Pred]` search states reachable by 1 or more transitions;
  - `S =(n,m)=>! SS [if Pred]` search states reachable by 0 or more transitions, and
    require that the reached state is a final state, i.e., no further
    transitions can be applied.

To allow for conditional transitions, a transition is only considered
in the search if `Pred` holds.

The parameters `n` and `m` in these search predicates:

  - `n`, a natural number or `*`, gives the maximal number of solutions
     to be searched. If `*` is given all solutions are searched
     exhaustively.
  - `m`, a natural number but not `*`, gives the maximal depth up to
     which search is performed.

The predicates return true if there is a (chain of) transitions
that fits the parameters (`n`,`m`, and `*`, `+`, `!`) and connects `S`
with `SS`.

There are two orthogonal extension to this search predicate, one
adds a `suchThat` clause, one adds a `withStateEq` clause.

`S =(n,m)=>* SS [if Pred1] suchThat Pred2`
  ~ (and similar for `!` and `+`) In this case not only the existence,
    of a transition sequence is tested, but also whether the predicate
    `Pred2`, which normally takes `S` and `SS` as arguments, holds.

`S =(n,m)=>* SS [if Pred1] withStateEq Pred2`
  ~ (and similar for `!` and `+`) `Pred2` is used to determine whether
    a search continues at `SS` or not, by comparing `SS` with all
    states that have been traversed in the current search. If the
    predicate `Pred2` returns true on the combination of `SS` as
    first argument, and any of the previously visited states as
    second argument, then the search is *not* continued after `SS`.
    (This is a kind of loop detection.)

These two cases can also be combined into 

`S =(n,m)=>* SS [if Pred1] suchThat Pred2 withStateEq Pred3`"
)


(define ("select")
    :category :proof
    :parser parse-show-command
    :evaluator eval-ast
    :title "`select <mod_exp> . `"
    :related ("open" "module expression")
    :doc "Selects a module given by the module expression `<mod_exp>` as the
current module. All further operations are carried out within the
given module. In contrast to `open` this does not allow for
modification of the module, e.g., addition of new sorts etc."
)


(define  ("set")
    :category :switch
    :parser parse-set-command
    :evaluator eval-ast
    :title "`set <name> [option] <value>`"
    :related ("show" "switches")
    :doc "Depending on the type of the switch, options and value specification varies.
Possible value types for switches are Boolean (`on`, `off`), string (`\"value\"`),
integers (5434443), lists (lisp syntax).

For a list of all available switches, use `set ?`. To see the current
values, use `show switches`. To single out two general purpose switches,
`verbose` and `quiet` tell the system to behave in the respective way."
)


(define  ("show" "sh")
    :category :inspect
    :parser parse-show-command
    :evaluator eval-ast
    :title "`show <something>`"
    :related ("switches" "describe")
    :doc "The `show` command provides various ways to inspect all kind of objects
of the CafeOBJ language. For a full list call `show ?`.

Some of the more important (but far from complete list) ways to call
the `show` command are:

  - `show [ <modexp> ]` - describes the current modules of the one specified
        as argument
  - `show module tree [ <modexp> ]` - displays submodules of <modexp> in tree format
  - `show switches` - lists all possible switches
  - `show term [ tree ]` - displays a term, possible in tree format

See the entry for [`switches`](#switches) for a full list."
)

(define ("show mode switch")
    :type :doc-only
    :title "`show mode` switch"
    :mdkey "switch-show-mode"
    :doc "Possible values for `set show mode <mode>` are `cafeobj` and `meta`."
)


(define ("signature" "sig")
    :category :element
    :parser identity
    :evaluator cafeobj-eval-module-element-proc
    :title "`signature { <sig-decl> }`"
    :related ("axioms" "imports" "sort" "op")
    :doc "Block enclosing declarations of sorts and operators.
Other statements are not allowed within the `signature` block.
Optional structuring of the statements in a module."
)

(define ("sort declaration")
    :type :doc-only
    :title "sort declaration"
    :mdkey "sort"
    :doc "CafeOBJ supports two kind of sorts, visible and hidden sorts. Visible 
sorts are introduced between `[` and `]`, while hidden sorts are introduced
between `*[` and `]*`.

~~~~
  [ Nat ]
  *[ Obs ]*
~~~~

Several sorts can be declared at the same time, as in `[ Nat Int ]`.

Since CafeOBJ is based on order sorting, sorts can form a partial order.
Definition of the partial order can be interleaved by giving

~~~~
  [ <sorts> < <sorts> ]
~~~~

Where `sorts` is a list of sort names. This declaration defines an inclusion
relation between each pair or left and right sorts."
    :example "~~~~
  [ A B , C D < A < E, B < D ]
~~~~

defines five sorts `A`,...,`E`, with the following relations:
`C < A`, `D < A`, `A < E`, `B < D`."
)

(define ("start")
    :category :proof
    :parser parse-start-command
    :evaluator eval-ast
    :title "`start <term> .`"
    :related ("apply" "choose" "match")
    :doc "Sets the focus onto the given term `<term>` of the currently opened
module or context. Commands like `apply`, `choose`, or `match` will
then operate on this term."
)

(define ("statistics")
    :type :doc-only
    :title "`statistics` switch"
    :mdkey "switch-statistics"
    :doc "Possible values: `on` `off`, default `on`.

After each reduction details about the reduction are
shown. Information shown are the time for parsing the expression, the
number of rewrites and run time during rewriting, and the number of
total matches performed during the reduce."
)

(define ("step switch")
    :type :doc-only
    :title "`step` switch"
    :mdkey "switch-step"
    :doc "Possible values: `on` `off`, default `off`.

With this switch turned on, rewriting proceeds in steps and prompts
the user interactively. At each prompt the following commands can be
given to the stepper (with our without leading colon `:`): 

`help`
:   (`h`, `?`) print out help page
`next`
:   (`n`) go one step
`continue`
:   (`c`) continue rewriting without stepping
`quit`
:   (`q`) leave stepper continuing rewrite
`abort`
:   (`a`) abort rewriting
`rule`
:   (`r`) print out current rewrite rule
`subst`
:   (`s`) print out substitution
`limit`
:   (`l`) print out rewrite limit count
`pattern`
:   (`p`) print out stop pattern
`stop [<term>] .`
:   set (or unset) stop pattern
`rwt [<number>] .`
:   set (or unset) max number of rewrite

Other standard CafeOBJ commands that can be used are [`show`](#show),
[`describe`](#describe), [`dirs`](#dirs), [`set`](#set), [`cd`](#cd), 
[`ls`](#ls), [`pwd`](#pwd), [`pushd`](#pushd), [`popd`](#popd), 
[`lisp`](#lisp), [`lispq`](#lisp), and (on Unix only)
[`!`](#commandexec)."
)

(define ("stop pattern switch")
    :type :doc-only
    :title "`stop pattern` switch"
    :mdkey "switch-stop-pattern"
    :related ("step switch")
    :doc "In [step mode](#switch-step), this command causes reductions to stop when the reductants get to
containing subterms that match the given term. If no term is given,
this restriction is lifted."
    :example "
~~~~~
CafeOBJ> open NAT .
%NAT> set step on .
%NAT> set stop pattern s 2 .
%NAT> red s s s s s s s s s 0 .
>> target: (s 0)
STEP[1]? c
>> term matches to stop pattern: (s 2)
<< will stop rewriting
>> stop because matches stop pattern.
>> target: (s 2)
STEP[3]? c
(9):NzNat
~~~~~"
)

(define ("switches")
    :type :doc-only
    :title "switches"
    :related ("set" "show")
    :doc "Switches control various aspects of the computations and behavior
of CafeOBJ. The current list of switches and their values can be
shown with 

`````
show switches
`````

The single switches are described separately in this manual."
)

(define ("trace whole switch")
    :type :doc-only
    :title "`trace [whole]` switch"
    :mdkey "switch-trace"
    :doc "During evaluation, it is sometimes desirable to see the rewrite
sequences, not just the results. Setting the switch `trace whole` will
result in the resultant term of each rewrite step being
printed. Setting the switch `trace` will result in the display of
which rule, substitution, and replacement are used."
)

(define ("trans" "tr")
    :category :element
    :parser identity
    :evaluator cafeobj-eval-module-element-proc
    :title "`trans [ <label-exp> ] <term> => <term> .`"
    :doc "Defines a transition, which is like an equation but without
symmetry. 

See [`eq`](#eq) for specification of requirements on `<label-exp>`
and the terms.

Transitions and equations server similar, but different purpose. In
particular, reductions (both with or without behavior axioms used) do
not take transitions into account. Only [`exec`](#execute) also uses
transitions. On the other hand, the built-in 
[search predicate](#searchpredicate) searches all possible transitions
from a given term."
)

(define ("unprotect") 
    :category :switch
    :parser parse-unprotect-command
    :evaluator eval-ast
    :title "`unprotect <module-name>`"
    :related ("protect")
    :doc "Remove overwrite protection from a module that has been protected
with the `protect` call. Some modules vital for the system
are initially protected."
)

(define ("using" "us")
    :category :element
    :parser identity
    :evaluator cafeobj-eval-module-element-proc
    :title "`using ( <modexp> )`"
    :related ("extending" "including" "protecting")
    :doc "Imports the object specified by `modexp` into the current
module without any restrictions on the models.
See [`module expression`](#moduleexpression) for format of `modexp`."
)

(define ("var" "vars")
    :category :element
    :parser identity
    :evaluator cafeobj-eval-module-element-proc
    :title "`var <var-name> : <sort-name>`"
    :related ("op" "qualified term" "on-the-fly")
    :doc "Declares a variable `<var-name>` to be of sort `<sort-name>`.
The scope of the variable is the current module.
Redeclarations of variable names are not allowed.
Several variable of the same sort can be declared at the same time
using the `vars` construct:

`vars <var-name> ... : <sort-name>`"
)

(define ("verbose switch")
    :type :doc-only
    :title "`verbose` switch"
    :mdkey "switch-verbose"
    :related ("quiet switch")
    :doc "Possible values: `on` `off`, default `off`.

If turn `on`, the system is much more verbose in many commands."
)


(define ("version")
    :category :misc
    :parser parse-version-command
    :evaluator princ
    :doc "Prints out the version of CafeOBJ."
)

(define ("view")
    :category :decl
    :parser process-view-declaration-form
    :evaluator eval-ast
    :title "`view <name> from <modname> to <modname> { <viewelems> }`"
    :doc "A view specifies ways to bind actual parameters to formal parameters
(see [parameterized module](#parameterizedmodule)). The view has to
specify the mapping of the sorts as well as the operators. 

The `<viewelems>` is a comma-separated list of expressions specifying
these mappings:

~~~~
sort <sortname> -> <sortname>
hsort <sortname> -> <sortname>
op <opname> -> <opname>
bop <opname> -> <opname>
~~~~

and also can contain variable declarations. 

Infix operators are represented as terms containing the operator with
either literal underscores `_`, or variables: `_*_` or `X * Y`.
The `<opname>` can be qualified.

In specifying views some rules can be omitted:

1. If the source and target modules have common submodules, all the
  sorts and modules declared therein are assumed to be mapped to
  themselves;

2. If the source and target modules have sorts and/or operators with
  identical names, they are mapped to their respective counterparts;

3. If the source module has a single sort and the target has a 
  principal sort, the single sort is mapped to the principal sort.
"
    :example "Assume a module `MONOID` with sort `M` and ops `e` and `*`
are given, and another `SIMPLE-NAT` with sort `Nat` and operators `0`
and `+` (with the same arity). Then the following expression
constitutes a view:

~~~~~
view NAT-AS-MONOID from MONOID to SIMPLE-NAT {
  sort M -> Nat,
  op   e -> 0,
  op _*_ -> _+_
}
~~~~~"
)


(define  ("dribble")
    :category :misc
    :parser parse-dribble-command
    :evaluator eval-ast
    :doc "TODO"
)

(define ("exec!" "execute!")
    :category :rewrite
    :parser parse-exec+-command
    :evaluator eval-ast
    :title "`exec! [ in <mod-exp> : ] <term> .`"
    :mdkey "execute-dash"
    :doc "TODO"
)

(define  ("stop")
    :category :rewrite
    :parser parse-stop-at
    :evaluator eval-ast
    :doc "Equivalent to [`stop pattern switch`](#switch-stop-pattern)"
)


(define ("lisp" "ev") 
    :category :system
    :parser parse-eval-lisp
    :evaluator cafeobj-eval-lisp-proc
    :doc "Evaluates the following lisp expression."
    :example "`````
CafeOBJ> lisp (+ 4 5)
(+ 4 5) -> 9
`````"
)

(define ("lispq" "evq")
    :category :system
    :parser parse-eval-lisp
    :evaluator cafeobj-eval-lisp-q-proc
    :doc "Evaluates the following lisp expression, but does not
display the result (q for quiet)."
)

(define ("make")
    :category :decl
    :parser parse-make-command
    :evaluator eval-ast
    :title "`make <mod_name> ( <mod_exp> )`"
    :related ("module expression")
    :doc "This commands defines a new module `<mod_name>` by evaluating the
module expression `<mod_exp>`."
)

(define  ("prelude")
    :category :library
    :parser parse-prelude-command
    :evaluator cafeobj-eval-prelude-proc
    :related ("reset" "full reset")
    :title "`prelude <file>`"
    :doc "Loads the given `<file>` as prelude. That is, a call to
[`reset`](#reset) will reset the definitions made in this file."
)

(define ("[")
    :category :element
    :parser identity
    :mdkey "sortsymbol"
    :evaluator cafeobj-eval-module-element-proc
    :doc "Starts a sort declaration. See [sort declaration](#sort) for details."
)

(define ("*")
    :category :element
    :parser identity
    :evaluator cafeobj-eval-module-element-proc
)

(define ("bsort")
    :category :element
    :parser identity
    :evaluator cafeobj-eval-module-element-proc
    :doc "TODO"
)


; seems these are obsolete, 
; (define ("dpred")             ; only for pignose
;     :category :element
;     :parser identity
;     :evaluator cafeobj-eval-module-element-proc
;     :doc "(pignose)
; ")

; (define ("dbpred")            ; only for pignose
;     :category :element
;     :parser identity
;     :evaluator cafeobj-eval-module-element-proc
;     :doc "(pignose)
; ")

(define ("ax")                  ; pignose
    :category :element
    :parser identity
    :evaluator cafeobj-eval-module-element-proc
    :title "`ax [ <label-exp> ] <term> = <term>` ."
    :doc "(pignose)"
)

(define ("bax")                 ; pignose
    :category :element
    :parser identity
    :evaluator cafeobj-eval-module-element-proc
    :title "`bax [ <label-exp> ] <term> = <term>` ."
    :doc "(pignose)"
)

(define ("goal")                ; pignose
    :category :element
    :parser identity
    :evaluator cafeobj-eval-module-element-proc
    :title "`goal <term> .`"
    :doc "(pignose)"
)

(define ("bgoal")               ; pignose
    :category :element
    :parser identity
    :evaluator cafeobj-eval-module-element-proc
    :title "`bgoal <term> .`"
    :doc "(pignose)"
)

(define ("pvar" "pvars")
    :category :element
    :parser identity
    :evaluator cafeobj-eval-module-element-proc
    :title "`pvar <var-name> : <sort-name>`"
    :related ("var" "vars")
    :doc "(pignose)"
)
  

(define ("rule" "rl" )
    :category :element
    :parser identity
    :evaluator cafeobj-eval-module-element-proc
    :title "`rule [ <label-exp> ] <term> => <term> .`"
    :related ("trans")
    :doc "Synonym of [`trans`](#trans)."
)

(define ("crule" "crl")
    :category :element
    :parser identity
    :evaluator cafeobj-eval-module-element-proc
    :title "`crule [ <label-exp> ] <term> => <term> if <term> .`"
    :related ("ctrans" "rule")
    :doc "Synonym of [`ctrans`](#ctrans)"
)

(define ("brule" "brl")
    :category :element
    :parser identity
    :evaluator cafeobj-eval-module-element-proc
    :related ("btrans")
    :title "`brule [ <label-exp> ] <term> => <term> .`"
    :doc "Synonym of [`btrans`](#btrans)."
)

(define ("bcrule" "bcrl")
    :category :element
    :parser identity
    :evaluator cafeobj-eval-module-element-proc
    :related ("bctrans")
    :title "`bcrule [ <label-exp> ] <term> => <term> if <term> .`"
    :doc "Synonym of [`bctrans`](#bctrans)"
)

(define ("inspect" "inspect-term")
    :category :proof
    :parser parse-inspect-term-command
    :evaluator eval-ast
    :title "`inspect <term>`"
    :doc "Inspect the internal structure of `<term>`."
)

(define ("pushd")
    :category :misc
    :parser parse-pushd-command
    :evaluator eval-ast
    :related ("ls" "cd" "popd" "pwd" "dirs")
    :title "`pushd <directory>`"
    :doc "Changes the working directory to `<directory>`, and puts the
current directory onto the push stack. Going back can be done with `pop`."
)

(define  ("popd")
    :category :misc
    :parser parse-popd-command
    :evaluator eval-ast
    :related ("ls" "cd" "pushd" "pwd" "dirs")
    :title "`popd`"
    :doc "Changes the current working directory to the last on on the push stack."
)

(define  ("dirs")
    :category :misc
    :parser parse-dirs-command
    :evaluator eval-ast
    :related ("ls" "cd" "pushd" "pwd" "popd")
    :doc "Displays the current push stack."
)

(define ("") 
    :category :misc
    :parser identity
    :evaluator cafeobj-eval-control-d
    :title "Ctrl-D"
    :mdkey "ctrld"
    :doc "Terminates the input and exit from the interpreter."
)

(define ("cont" "continue")
    :category :rewrite
    :parser parse-continue-command
    :evaluator eval-ast
    :doc "In [step mode](#switch-step), continues the reduction until
a [stop pattern](#switch-stop-pattern) has been found."
)

(define ("names" "name")
    :category :inspect
    :parser parse-name-command
    :evaluator eval-ast
    :title "`names <mod-exp>` ."
    :doc "List up all the named objects in module <mod-exp>."
)

(define ("scase")
    :category :proof
    :parser parse-case-command
    :evaluator eval-ast
    :title "`scase (<term>) in (<mod-exp>) as <name> { <decl> ..} : <term> .`"
    :doc "TODO"
)

(define ("sos" "passive")
    :category :proof
    :parser pignose-parse-sos
    :evaluator eval-ast
    :title "`sos { = | + | - } { <clause> , ... }`"
    :doc "(pignose)"
)

(define ("db")
    :category :proof
    :parser pignose-parse-db
    :evaluator eval-ast
    :title "`db reset`"
    :doc "(pignose)"
)

(define  ("clause")
    :category :proof
    :parser pignose-parse-clause
    :evaluator eval-ast
    :title "`clause <term> .`"
    :doc "(pignose)"
)

(define  ("list")
    :category :proof
    :parser pignose-parse-list-command
    :evaluator eval-ast
    :title "`list { axiom | sos | usable | flag | param | option | demod }`"
    :doc "(pignose)"
)

(define ("flag")
    :category :proof
    :parser pignose-parse-flag
    :evaluator eval-ast
    :title "`flag(<name>, { on | off })`"
    :doc "(pignose)"
)

(define  ("param")
    :category :proof
    :parser pignose-parse-param
    :evaluator eval-ast
    :title "`param(<name>, <value>)`"
    :doc "(pignose)"
)

(define ("option")
    :category :proof
    :parser pignose-parse-option
    :evaluator eval-ast
    :title "`option { reset | = <name> }`"
    :doc "(pignose)"
)

(define ("resolve")
    :category :proof
    :parser pignose-parse-resolve
    :evaluator eval-ast
    :title "`resolve {. | <file-path> }`"
    :doc "(pignose)"
)

(define  ("demod")
    :category :proof
    :parser pignose-parse-demod
    :evaluator eval-ast
    :doc "(pignose)"
)

(define ("save-option")
    :category :proof
    :parser pignose-parse-save-option
    :evaluator eval-ast
    :title "`save-option <name>`"
    :doc "(pignose)"
)

(define ("sigmatch")
  :category :proof
  :parser pignose-parse-sigmatch
  :evaluator eval-ast
  :title "`sigmatch (<mod-exp>) to (<mod-exp>)`"
  :doc "(pignose)"
)

(define  ("lex")
    :category :proof
    :parser pignose-parse-lex
    :evaluator eval-ast
    :title "`lex (<op>, ..., <op>)`"
    :doc "(pignose)"
)

(define (".")
    :category :misc
    :parser identity
    :evaluator cafeobj-nop
    :title "`.`"
    :mdkey "dotsep"
    :doc "Input separator"
)

;;; CITP commands
(define ("citp")
    :type :doc-only
    :title "CITP"
    :related (":goal" ":apply" ":ind" ":auto" ":roll" ":init" ":cp" ":equation" ":rule" ":backward" ":select" ":red" ":csp" ":csp-" ":ctf" ":ctf-" ":def" ":imp" ":ord")
    :doc "Constructor Based Induction Theorem Prover

The sub-system provides a certain level of automatization for theorem proving.

Please see the accompanying manual for CITP for details."
)

(define (":goal")
    :category :proof
    :parser citp-parse-goal
    :evaluator eval-citp-goal
    :related ("citp")
    :title "`:goal { <sentence> . ... }`"
    :doc "Define the initial goal for CITP"
    :example "
~~~~~
CafeOBJ> select PNAT .
PNAT> :goal { 
   eq [lemma-1]: M:PNat + 0 = M . 
   eq [lemma-2]: M:PNat + s N:PNat = s( M + N ) . 
}
~~~~~"
    )

(define (":apply")
    :category :proof
    :parser citp-parse-apply
    :evaluator eval-citp-apply
    :related ("citp")
    :title "`:apply (<tactic> ...) [to <goal-name>]`"
    :doc "Apply the list of tactics given within parenthesis to either
the current goal, or the goal given as `<goal-name>`."
)

(define (":ind")
    :category :proof
    :parser citp-parse-ind-on
    :evaluator eval-citp-ind-on
    :related ("citp")
    :title "`:ind on <variable> ... .`"
    :doc "Defines the variable for the induction tactic of CITP."
    :example "
~~~~~
:ind on (M:PNat)
~~~~~"
)

(define (":auto")
    :category :proof
    :parser citp-parse-auto
    :evaluator eval-citp-apply
    :related ("citp")
    :title "`:auto`"
    :doc "Applies the following set of tactics: `(SI CA TC IP RD)`."
)

(define (":roll")
    :category :proof
    :parser citp-parse-roll-back
    :evaluator eval-citp-roll-back
    :related ("citp")
    :title "`:roll back`"
    :doc "Reverts the strategy that led to the current target goal.
The current target goal is removed from the proof tree."
)

(define (":init")
    :category :proof
    :parser citp-parse-init
    :evaluator eval-citp-init
    :related ("citp")
    :title "`:init { \"[\" <label> \"]\" | \"(\" <sentence> \"\")} by \"{\" <variable> <- <term>; ... \"}\"`"
    :doc "Instantiates an equation specified by `<label>` by replacing the `<variable>`s 
in the equation with the respective `<term>`s. The resulting equation is added
to the set of axioms."
)

(define ("init")
    :category :proof
    :parser citp-parse-init
    :evaluator eval-citp-init
    :related ("open")
    :title "`init { \"[\" <label> \"]\" | \"(\" <sentence> \"\")} by \"{\" <variable> <- <term>; ... \"}\"`"
    :doc "Instantiates an equation specified by `<label>` by replacing the `<variable>`s 
in the equation with the respective `<term>`s. The resulting equation is added
to the set of axioms."
    )

(define (":imply" ":imp")
    :category :proof
    :parser citp-parse-imp
    :evaluator eval-citp-imp
    :related ("citp")
    :title "`:imp \"[\" <label> \"]\" by \"{\" <variable> <- <term>; ...\"}\"`"
    :doc "TODO (future extension)"
)

(define (":cp")
    :category :proof
    :parser citp-parse-critical-pair
    :evaluator eval-citp-critical-pair
    :related ("citp")
    :title "`:cp { \"[\" <label> \"]\" | \"(\" <sentence> . \")\" } >< { \"[\" <label> \"]\" | \"(\" <sentence> .\")\" }`"
    :doc "Computes the critical pair of the two given equations.
Here either a label or a full equation can be used to specify the equations."
    :example "
~~~~~
:cp (ceq top(sq(S@Sys)) = I@Pid if pc(S@Sys,I@Pid) = cs .)
><
(ceq top(sq(S@Sys)) = J@Pid if pc(S@Sys,J@Pid) = cs .)
~~~~~"
)

(define (":equation")
    :category :proof
    :parser citp-parse-equation
    :evaluator eval-citp-equation
    :title "`:equation`"
    :related ("citp" ":cp" ":rule")
    :doc "Adds the critical pair computed by the last [`:cp`](#citp-cp) command
as equation to the current goal."
)

(define (":rule")
    :category :proof
    :parser citp-parse-equation
    :evaluator eval-citp-equation
    :title "`:rule`"
    :related ("citp" ":cp" ":equation")
    :doc "Adds the critical pair computed by the last [`:cp`](#citp-cp) command
as rule to the current goal."
)

(define (":backward")
    :category :proof
    :parser citp-parse-backward
    :evaluator eval-citp-backward
    :title "`:backward equation|rule`"
    :related ("citp" ":cp" ":equation" ":rule")
    :doc "Like [`:equation`](#citp-equation) and [`:rule`](#citp-rule), but exchange the left and right side."
)

(define (":select")
    :category :proof
    :parser citp-parse-select
    :evaluator eval-citp-select
    :title "`:select <goal-name>`"
    :related ("citp")
    :doc "Select a goal for further application of tactics."
)

(define (":red" ":exec" ":bred")
    :category :proof
    :parser citp-parse-red
    :evaluator eval-citp-red
    :title "`{ :red | :exec | :bred } [in <goal-name> :] <term> .`"
    :related ("citp")
    :doc "reduce the term in specified goal <goal-name>."
)

(define (":verbose")
    :category :proof
    :parser citp-parse-verbose
    :evaluator eval-citp-verbose
    :title "`:verbose { on | off }`"
    :related ("citp")
    :doc "Turns on verbose reporting of the CITP subsystem."
)

(define (":normalize")
    :category :proof
    :parser citp-parse-normalize
    :evaluator eval-citp-normalize
    :title "`:normalize { on | off}`"
    :related ("citp")
    :doc "Normalize the LHS of an instance of the axiom generated by :init command."
)

(define (":ctf")
    :category :proof
    :parser citp-parse-ctf
    :evaluator eval-citp-ctf
    :related ("citp" ":ctf-")
    :title "`:ctf { eq [ <label-exp> ] <term> = <term> .}`"
    :doc "Applies case splitting after a set of boolean expressions.
Not discharged sub-goals will remain in the reduced form."
)

(define (":ctf-")
    :category :proof
    :parser citp-parse-ctf
    :evaluator eval-citp-ctf
    :related ("citp" ":ctf")
    :title "`:ctf- { eq [ <label-exp> ] <term> = <term> .}`"
    :doc "Like [`:ctf`](#citp-ctf), but if sub-goals are not discharged, the
CITP prover returns to the original state before the reduce action."
)

(define (":csp")
    :category :proof
    :parser citp-parse-csp
    :evaluator eval-citp-csp
    :related ("citp" ":csp-")
    :title "`:csp { eq [ <label-exp>] <term> = <term> . ...}`"
    :doc "Applies case splitting after a set of equations. Each of these
equations creates one new sub-goal with the equation added.

The system does not check whether given set of equations exhausts all 
possible values.

Not discharged sub-goals will remain in the reduced form."
)

(define (":csp-")
    :category :proof
    :parser citp-parse-csp
    :evaluator eval-citp-csp
    :related ("citp" ":csp")
    :title "`:csp- { eq [ <label-exp>] <term> = <term> . ...}`"
    :doc "Like [`:csp`](#citp-csp), but if sub-goals are not discharged, the
CITP prover returns to the original state before the reduce action."
)

(define (":def" ":define")
    :category :proof
    :parser citp-parse-define
    :evaluator eval-citp-define
    :related ("citp")
    :title "`:def <symbol> = { <ctf> | <csp>}`"
    :doc "Assigns a name to a specific case splitting (`ctf` or `csp`),
so that it can be used as tactics in `:apply`."
    :example "~~~~~
:def name-1 = ctf [ <Term> . ]
:def name-2 = ctf-{ eq LHS = RHS . }
:def name-3 = csp { eq lhs1 = rhs1 . eq lhs2 = rhs2 . }
:def name-4 = csp-{ eq lhs3 = rhs3 . eq lhs4 = rhs4 . }
:apply(SI TC name-1 name-2 name-3 name-4)
~~~~~"
)

(define  (":show" ":sh")
    :category :inspect
    :parser citp-parse-show
    :evaluator eval-citp-show
    :title "`:show goal|unproved|proof`"
    :related ("citp" ":describe")
    :doc "Shows the current goal, the up-to-now unproven (sub-)goals, and the current proof."
    :example "
~~~~~
PNAT> :show proof 
root*
[si]  1*
[ca]  1-1*
[ca]  1-2*
[tc]  1-2-1*
[si]  2*
[ca]  2-1*
[ca]  2-2*
[tc]  2-2-1*
PNAT>
~~~~~"
)

(define (":describe" ":desc")
    :category :inspect
    :parser citp-parse-show
    :evaluator eval-citp-show
    :title "`:describe proof`"
    :related ("citp" ":show")
    :doc "Describes the current proof in more detail."
    :example "
~~~~~
PNAT> :describe proof
==> root*
    -- context module: #Goal-root
    -- targeted sentences:
      eq [lemma-1]: M:PNat + 0 = M .
      eq [lemma-2]: M:PNat + s N:PNat = s (M + N) .
[si]    1*
    -- context module: #Goal-1
    -- targeted sentences:
      eq [lemma-1]: 0 + 0 = 0 .
      eq [lemma-2]: 0 + s N:PNat = s (0 + N) .
...
~~~~~"
)

(define (":spoiler")
    :category :proof
    :parser citp-parse-spoiler
    :evaluator identity
    :related ("citp")
    :title "`:spoiler { on | off}`"
    :doc "If the spoiler flag is on, after a strategy other than RD and SI
has been applied, the generated sub-goals are automatically checked for
provability using the RD strategy. Defaults to `off`."
)

(define (":set")
    :category :proof
    :parser citp-parse-set
    :evaluator citp-eval-set
    :title "`:set(<name>, { on | off | show })`"
    :related ("citp")
    :doc "Set or show various flags of CITP CafeOBJ."
)

(define (":order")
    :category :proof
    :parser pignose-parse-lex
    :evaluator citp-eval-order
    :title "`:order (<op>, ..., <op>)`"
    :doc ""
    )

(define (":binspect")
    :category :proof
    :parser parse-citp-binspect
    :evaluator eval-citp-binspect
    :title "`:binspect [in <goal-name> :] <boolean-term> .`"
    :doc "Used during [CITP](#citp) proofs instead of [`binspect`](#binspect)"
)

(define ("binspect")
    :category :proof
    :parser parse-citp-binspect
    :evaluator eval-citp-binspect
    :title "`binspect [in <module-name> :] <boolean-term> .`"
    :doc "Start an inspection of a Boolean term, that is, and abstracted
form of the Boolean term is constructed. The abstracted term is shown (like calling [`bshow`](#bshow)."
    :example "
~~~~~
CafeOBJ> module BTE { [S]
  preds p1 p2 p3 p4 p5 p6 p7 : S
  ops a b c :  -> S .
}
CafeOBJ> binspect in BTE : (p1(X:S) or p2(X)) and p3(Y:S) or (p4(Y) and p1(Y)) .
...
--> ((p4(Y:S) and p1(Y)) xor ((p3(Y) and p1(X:S)) xor ((p2(X) and (p3(Y) and p1(X))) xor ((p3(Y) and p2(X)) xor ((p3(Y) and (p2(X) and (p4(Y) and p1(Y)))) xor ((p3(Y) and (p2(X) and (p1(X) and (p1(Y) and p4(Y))))) xor (p1(X) and (p3(Y) and (p1(Y) and p4(Y))))))))))
...
~~~~~"
)

(define ("bresolve" ":bresolve")
    :category :proof
    :parser identity
    :evaluator bresolve 
    :title "`{bresolve | :bresolve} [<limit>] [all]`"
    :doc "Computes all possible variable assignments that render an abstracted
term `true`. The variant with leading colon is for usage during a [CITP](#citp) proof.
If an optional argument 'all' is specified, all solutions will be searched.
Optional <limit> specifies maximal number of variable combination, i.e. 
if there are 3 variables v1, v2, and v3, and <limit> is 2, 
the following cases are examined:
(1) v1 : true/false
(2) v2 : true/false
(3) v3 : true/false
(4) v1/v2 : combinations of true/false of two variables
(5) v1/v3 : combinations of true/false of two variables
(6) v2/v3 : combinations of true/false of two variables"
    :example "
~~~~~
CafeOBJ> bresolve 2 all

** (1) The following assignment(s) makes the term to be 'true'.
[1] { P-3:Bool |-> true }
where
  p-3 = P4(Y:S)
  
[2] { P-4:Bool |-> true }
where
  p-4 = P1(X:S)
  
** (2) The following assignment(s) makes the term to be 'true'.
[1] { P-1:Bool |-> true, P-2:Bool |-> true }
where
  p-1 = P3(Y:S)
  p-2 = P2(X:S)
...
~~~~~"
)

(define ("bshow" ":bshow")
    :category :proof
    :parser citp-parse-bshow
    :evaluator bshow
    :title "`{bshow | :bshow} [{ tree | grind }]`"
    :doc "Shows the abstracted Boolean term computed by [`binspect`](#binspect).
If the argument `tree` is given, prints out a the abstracted term in tree form.
The variant with leading colon is for usage during a [CITP](#citp) proof."
    :example "
~~~~~
CafeOBJ> bshow
((P-1:Bool and (P-2:Bool and (P-3:Bool and P-4:Bool))) xor ((P-1 and (P-2 and (P-4 and (P-5:Bool and P-3)))) xor ((P-2 and (P-1 and (P-5 and P-3))) xor ((P-5 and P-3) xor ((P-4 and (P-3 and P-5)) xor ((P-4 and P-3) xor (P-2 and P-1)))))))
where
  P-1:Bool |-> p4(Y:S)
  P-2:Bool |-> p1(Y:S)
  P-3:Bool |-> p3(Y:S)
  P-4:Bool |-> p1(X:S)
  P-5:Bool |-> p2(X:S)
~~~~~"
)

(define ("bguess" ":bguess" "bg" ":bg")
    :category :proof
    :parser citp-parse-bguess
    :evaluator bguess
    :title "`{bguess | :bguess} {imply|and|or} [ with <predicate name> ]`"
    :doc "TODO")

;;;

(define ("commands" "com")
    :category :help
    :parser identity
    :evaluator show-cafeobj-main-commands
    :title "`commands`"
    :mdkey "comshelp"
    :doc "Print outs the list of main toplevel commands."
)

(define ("?com" "?command")
    :category :help
    :parser identity
    :evaluator cafeobj-top-level-help
    :mdkey "help-commands"
    :title "`?com [ <term> ]`"
    :doc "List commands or declarations categorized by the key <term>.
<term> is one of 'decl', 'module', 'parse', 'rewrite', 
'inspect', 'switch', 'proof', 'system', 'inspect', 'library', 'help', 'io' or 'misc'.
If <term> is omitted, the list of available <term> will be printed."
)

;;;
)                                      ; end eval-when
;;; EOF
