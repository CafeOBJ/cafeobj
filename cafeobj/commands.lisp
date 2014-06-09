;;;-*- Mode:LISP; Package:CHAOS; Base:10; Syntax:Common-lisp -*-
#|==============================================================================
                            System: CHAOS
                           Module: cafeobj
                         File: commands.lisp
==============================================================================|#
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
  (clrhash *cafeobj-declarations*)

  ;; this holds each commands/language constructs document strings.
  ;; systems' doc-generator refers to this hash table.
 (clrhash *cafeobj-doc-db*)

;;; --------------------------------------------------------------------------
;;; all of the declarations/commands in alphabetical order.
;;; --------------------------------------------------------------------------
  
(define ("??" "?")
    :category :help
    :parser identity
    :evaluator cafeobj-top-level-help
        :doc "
## `?` ## {#help}

lists all top-level commands. The `?` can be used after many of the
top-level commands to obtain help.
")


(define ("!")
    :category :misc
    :parser parse-shell-command
    :evaluator eval-ast
        :doc "
## `! <command>` ## {#commandexec}

TODO Currently not working!! 

On Unix only, forks a shell and executes the given `<command>`.
")


(define ("--" "**")
    :category :decl-toplevel
    :parser parse-comment-command
    :evaluator identity
    :doc "
")


(define ("-->" "**>")
    :doc "
"
    :category :decl-toplevel
    :parser parse-comment-command
    :evaluator eval-ast)

(define ("=")
    :type :doc-only
    :doc "
## `=` ## {#axeq}

The syntax element `=` introduces an axiom of the equational theory,
and is different from `==` which specifies an equality based on
rewriting. 

Related: [`==`](#equality) [`eq`](#eq)
")

(define ("==")
    :type :doc-only
    :doc "
## `==` ## {#equality}

The predicate `==` is a binary operator defined for each visible sort
and is defined in terms of evaluation. That is, for ground terms `t`
and `t'` of the same sort, `t == t'` evaluates to `true` iff terms
reduce to a common term. This is different from the equational `=`
which specifies the equality of the theory.
")

(define ("=>")
    :type :doc-only
    :doc
    "
## `==>` ## {#transrel}

This binary predicate is defined on each visible sort, and defines the
transition relation, which is reflexive, transitive, and closed under
operator application. It expresses the fact that two states (terms)
are connected via transitions.
Related: [`trans`](#trans) [`=(*)=>`](#transsearch)
")

(define ("=*=")
    :type :doc-only
    :doc "
## `=*=` ## {#bequality}

The predicate for behavioural equivalence, written `=*=`, is a binary
operator defined on each hidden sort. 

TODO: old manual very unclear ... both about `=*=` and 
`accept =*= proof` ??? (page 46 of old manual)
")

(define  ("dribble")
    :category :misc
    :parser parse-dribble-command
    :evaluator eval-ast
    :doc "
")

(define ("mod" "module" "module*" "mod*" "module!" "mod!" "sys:mod!" "sys:module!" "sys:mod*" "sys:module*")
    :category :decl-toplevel
    :parser process-module-declaration-form
    :evaluator eval-ast
    :doc "
## `module[!|*] <modname> [ ( <params> ) ] [ <principal_sort_spec> ] { mod_elements ... }` ## {#module}

Alias: `mod`

defines a module, the basic building block of \_cafeobj. Possible elements
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

If `params` are given, it is a parametrized module. See `parametrized module`
for more details.

If `principal_sort_spec` is given, it has to be of the form
`principal-sort <sortname>` (or `p-sort <sortname>`). The principal
sort of the module is specified, which allows more concise `view`s from
single-sort modules as the sort mapping needs not be given.
")

(define ("view")
    :category :decl-toplevel
    :parser process-view-declaration-form
    :evaluator eval-ast
    :doc "
## `view <name> from <modname> to <modname> { <viewelems> }` ## {#view}

A view specifies ways to bind actual parameters to formal parameters
(see [parametrized module](#parametrizedmodule)). The view has to
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

Example: Assume a module `MONOID` with sort `M` and ops `e` and `*`
are given, and another `SIMPLE-NAT` with sort `Nat` and operators `0`
and `+` (with the same arity). Then the following expression
constitutes a view:

~~~~~
view NAT-AS-MONOID from MONOID to SIMPLE-NAT {
  sort M -> Nat,
  op   e -> 0,
  op _*_ -> _+_
}
~~~~~

In specifying views some rules can be omitted:

1. If the source and target modules have common submodules, all the
  sorts and modules decalred therein are assumed to be mapped to
  themselves;

2. If the source and target modules have sorts and/or operators with
  identical names, they are mapped to their respective counterparts;

3. If the source module has a single sort and the target has a 
  principal sort, the single sort is mapped to the principal sort.
")

(define ("check")
    :category :checker
    :parser   parse-check-command
    :evaluator eval-ast
    :doc "
## `check <options>` ## {#check}

This command allows for checking of certain properties of modules and
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
    checked. 

Related: [`regularize`](#regularize)
")

(define ("regularize")
    :category :module
    :parser parse-regularize-command
    :evaluator eval-ast
    :doc "
## `regularize <mod-name>` ## {#regularize}

Regularizes the signature of the given module, ensuring that every
term has exactely one minimal parse tree. In this process additional
sorts are generated to ensure unique least sort of all terms.

Modules can be automatically regularized by the interpreter if the
`regularize signature` switch is turn to `on`.

TODO -- should we give more details here -- unclear to me.
")

(define ("exec" "execute")
    :category :rewrite
    :parser parse-exec-command
    :evaluator eval-ast
    :doc "
## `execute [ in <mod-exp> : ] <term> .` ## {#execute}

Alias: `exec`

Reduce the given term in the given module, if `<mod-exp>` is given, 
otherwise in the current module. 

For `execute` equations and transitions, possibly conditional, are taken
into account for reduction.

Related: [`breduce`](#breduce) [`reduce`](#reduce)
")

(define ("red" "reduce")
  :category :rewrite
  :parser parse-reduce-command
  :evaluator eval-ast
  :doc "
reduce [in <Modexpr> :] <Term> . ~%Rewrite <Term> by axioms of the module.
")

(define ("exec!" "execute!")
    :category :rewrite
    :parser parse-exec+-command
    :evaluator eval-ast
    :doc "
exec! [in <Modexpr> :] <Term> .
")

(define ("bred" "breduce")
    :category :rewrite
    :parser parse-bred-command
    :evaluator eval-ast
    :doc "
")

(define ("version")
    :category :misc
    :parser parse-version-command
    :evaluator princ
    :doc "
prints version number of the system.
")

(define ("cbred")
    :category :rewrite
    :parser parse-cbred-command
    :evaluator eval-ast
    :doc "
")

(define  ("stop")
    :category :rewrite
    :parser parse-stop-at
    :evaluator eval-ast
    :doc "
")

(define ("parse")
    :category :parse
    :parser parse-parse-command
    :evaluator eval-ast
    :doc "
")

(define ("match" "unify")
    :category :inspect
    :parser parse-match-command
    :evaluator eval-ast
    :doc "
")

(define ("lisp" "ev") 
    :category :system
    :parser parse-eval-lisp
    :evaluator cafeobj-eval-lisp-proc
    :doc "
")

(define ("lispq" "evq")
    :category :system
    :parser parse-eval-lisp
    :evaluator cafeobj-eval-lisp-q-proc
    :doc "
")

(define ("make")
    :category :decl-toplevel
    :parser parse-make-command
    :evaluator eval-ast
    :doc "
")

(define  ("in" "input")
    :category :misc
    :parser parse-input-command
    :evaluator cafeobj-eval-input-proc
    :doc "
")

(define ("save")
    :category :io
    :parser parse-save-command
    :evaluator eval-ast
    :doc "
")

(define ("restore")
    :category :io
    :parser parse-restore-command
    :evaluator eval-ast
    :doc "
")

(define ("reset")
    :category :system
    :parser parse-reset-command
    :evaluator eval-ast
    :doc (("reset"
	   "
remove declarations of user defined modules and views from the system.
")))

(define ("full" "full-reset") 
    :doc ((("full reset" "full-reset") "reset system to initial status."))
    :category :system
    :parser parse-full-reset-command
    :evaluator eval-ast)

(define ("clean")
    :category :rewrite
    :parser identity
    :evaluator cafeobj-eval-clear-memo-proc
    :doc "
")

(define  ("prelude")
    :category :library
    :parser parse-prelude-command
    :evaluator cafeobj-eval-prelude-proc
    :doc "
")

(define ("let") 
    :category :decl-toplevel
    :parser process-let-declaration-form
    :evaluator eval-ast
    :doc "
")

(define ("imports")
    :category :module-element
    :parser identity
    :evaluator cafeobj-eval-module-element-proc
    :doc "
## `imports { <import-decl> }` ## {#imports}

Block enclosing import of other modules (`protecting` etc). 
Other statements are not allowed within the `imports` block.
Optional structuring of the statements in a module.

Related: [`signature`](#signature) [`axioms`](#axioms)
  [`extending`](#extending)   [`including`](#including) 
  [`protecting`](#protecting) [`using`](#using)
")

(define ("ex" "extending")
    :category :module-element
    :parser identity
    :evaluator cafeobj-eval-module-element-proc
    :doc "
## `extending ( <modexp> )` ## {#extending}

Alias: `ex`

imports the object specified by `modexp` into the current
module, allowing models to be inflated, but not collapsing. 
See [`module expression`](#moduleexpression) for format of `modexp`.

Related: [`including`](#including) [`protecting`](#protecting) 
	 [`using`](#using)
")

(define ("pr" "protecting")
    :category :module-element
    :parser identity
    :evaluator cafeobj-eval-module-element-proc
    :doc "
")

(define ("us" "using")
    :category :module-element
    :parser identity
    :evaluator cafeobj-eval-module-element-proc
    :doc "
")

(define ("inc" "including")
    :category :module-element
    :parser identity
    :evaluator cafeobj-eval-module-element-proc
    :doc "
")

(define ("[")
    :category :module-element
    :parser identity
    :evaluator cafeobj-eval-module-element-proc
    :doc "
")

(define ("*")
    :category :module-element
    :parser identity
    :evaluator cafeobj-eval-module-element-proc
    :doc "
")

(define ("bsort")
    :category :module-element
    :parser identity
    :evaluator cafeobj-eval-module-element-proc
    :doc "
")

(define ("op" "ops")
    :category :module-element
    :parser identity
    :evaluator cafeobj-eval-module-element-proc
    :doc "
")

(define ("bop" "bops")
    :category :module-element
    :parser identity
    :evaluator cafeobj-eval-module-element-proc
    :doc "
")

(define ("pred")
    :category :module-element
    :parser identity
    :evaluator cafeobj-eval-module-element-proc
    :doc "
")

(define ("bpred")
    :category :module-element
    :parser identity
    :evaluator cafeobj-eval-module-element-proc
    :doc "
")

(define ("dpred")		; only for pignose
    :category :module-element
    :parser identity
    :evaluator cafeobj-eval-module-element-proc
    :doc "
")

(define ("dbpred")		; only for pignose
    :category :module-element
    :parser identity
    :evaluator cafeobj-eval-module-element-proc
    :doc "
")

(define ("sig" "signature")
    :category :module-element
    :parser identity
    :evaluator cafeobj-eval-module-element-proc
    :doc "
")

(define ("axiom" "ax")
    :category :module-element
    :parser identity
    :evaluator cafeobj-eval-module-element-proc
    :doc "
")

(define ("axioms" "axs")
    :category :module-element
    :parser identity
    :evaluator cafeobj-eval-module-element-proc
    :doc "
")

(define ("ax")			; pignose
    :category :module-element
    :parser identity
    :evaluator cafeobj-eval-module-element-proc
    :doc "
")

(define ("bax")			; pignose
    :category :module-element
    :parser identity
    :evaluator cafeobj-eval-module-element-proc
    :doc "
")

(define ("goal")		; pignose
    :category :module-element
    :parser identity
    :evaluator cafeobj-eval-module-element-proc
    :doc "
")

(define ("bgoal")		; pignose
    :category :module-element
    :parser identity
    :evaluator cafeobj-eval-module-element-proc
    :doc "
")

(define ("#define")
    :category :module-element
    :parser identity
    :evaluator cafeobj-eval-module-element-proc
    :doc "
")
  
(define ("var" "vars")
    :category :module-element
    :parser identity
    :evaluator cafeobj-eval-module-element-proc
    :doc "
")

(define ("pvar" "pvars")
    :category :module-element
    :parser identity
    :evaluator cafeobj-eval-module-element-proc
    :doc "
")

(define ("eq"  "ceq" "cq")
    :category :module-element
    :parser identity
    :evaluator cafeobj-eval-module-element-proc
    :doc "
")

(define ("beq" "bceq" "bcq")
    :category :module-element
    :parser identity
    :evaluator cafeobj-eval-module-element-proc
    :doc "
")

(define ("trans" "ctrans")
    :category :module-element
    :parser identity
    :evaluator cafeobj-eval-module-element-proc
    :doc "
")
    
(define ("trns" "ctrns")
    :category :module-element
    :parser identity
    :evaluator cafeobj-eval-module-element-proc
    :doc "
")

(define ("rule" "crule")
    :category :module-element
    :parser identity
    :evaluator cafeobj-eval-module-element-proc
    :doc "
")

(define ("rl" "crl")
    :category :module-element
    :parser identity
    :evaluator cafeobj-eval-module-element-proc
    :doc "
")

(define ("btrans" "bctrans")
    :category :module-element
    :parser identity
    :evaluator cafeobj-eval-module-element-proc
    :doc "
")

(define ("brule" "bcrule")
    :category :module-element
    :parser identity
    :evaluator cafeobj-eval-module-element-proc
    :doc "
")

(define ("btrns" "bctrns")
    :category :module-element
    :parser identity
    :evaluator cafeobj-eval-module-element-proc
    :doc "
")

(define ("brl" "bcrl")
    :category :module-element
    :parser identity
    :evaluator cafeobj-eval-module-element-proc
    :doc "
")

(define ("open")
    :category :proof
    :parser parse-open-command
    :evaluator eval-ast
    :doc "
")

(define ("close")
    :category :proof
    :parser parse-close-command
    :evaluator eval-ast
    :doc "
")

(define ("start")
    :category :proof
    :parser parse-start-command
    :evaluator eval-ast
    :doc "
")

(define ("apply")
    :category :proof
    :parser parse-apply-command
    :evaluator eval-ast
    :doc "
")

(define  ("choose") 
    :category :proof
    :parser parse-choose-command
    :evaluator eval-ast
    :doc "
")

(define ("inspect")
    :category :proof
    :parser parse-inspect-term-command
    :evaluator eval-ast
    :doc "
")

(define  ("find")
    :category :proof
    :parser parse-find-command
    :evaluator eval-ast
    :doc "
")

(define  ("show" "sh")
    :category :inspect
    :parser parse-show-command
    :evaluator eval-ast
    :doc "
")

(define  ("set")
    :category :switch
    :parser parse-set-command
    :evaluator eval-ast
    :doc "
")

(define ("protect")
    :category :system
    :parser parse-protect-command
    :evaluator eval-ast
    :doc "
")

(define ("unprotect") 
    :category :system
    :parser parse-unprotect-command
    :evaluator eval-ast
    :doc "
")

(define ("select")
    :category :proof
    :parser parse-show-command
    :evaluator eval-ast
    :doc "
")

(define ("describe" "desc")
    :category :inspect
    :parser parse-show-command
    :evaluator eval-ast
    :doc "
")

(define  ("autoload")
    :category :library
    :parser parse-autoload-command
    :evaluator eval-ast
    :doc "
")

(define  ("provide") 
    :category :library
    :parser parse-provide-command
    :evaluator eval-ast
    :doc "
")

(define  ("require") 
    :category :library
    :parser parse-require-command
    :evaluator eval-ast
    :doc "
")

(define  ("pwd")
    :category :misc
    :parser parse-pwd-command
    :evaluator eval-ast
    :doc "
")

(define  ("cd") 
    :category :misc
    :parser parse-cd-command
    :evaluator eval-ast
    :doc "
")

(define ("pushd")
    :category :misc
    :parser parse-pushd-command
    :evaluator eval-ast
    :doc "
")

(define  ("popd")
    :category :misc
    :parser parse-popd-command
    :evaluator eval-ast
    :doc "
")

(define  ("dirs")
    :category :misc
    :parser parse-dirs-command
    :evaluator eval-ast
    :doc "
")

(define ("ls")
    :category :misc
    :parser parse-ls-command
    :evaluator eval-ast
    :doc "
")

(define ("") 
    :category :misc
    :parser identity
    :evaluator cafeobj-eval-control-d
    :doc "
")

(define ("cont" "continue")
    :category :rewrite
    :parser parse-continue-command
    :evaluator eval-ast
    :doc "
")

(define ("look")
    :category :inspect
    :parser parse-look-up-command
    :evaluator eval-ast
    :doc "
")

(define ("names" "name")
    :category :inspect
    :parser parse-name-command
    :evaluator eval-ast
    :doc "
show
")


(define ("scase")
    :category :proof
    :parser parse-case-command
    :evaluator eval-ast
    :doc "
")

(define ("sos" "passive")
    :category :proof
    :parser pignose-parse-sos
    :evaluator eval-ast
    :doc "
")

(define ("db")
    :category :proof
    :parser pignose-parse-db
    :evaluator eval-ast
    :doc "
")

(define  ("clause")
    :category :proof
    :parser pignose-parse-clause
    :evaluator eval-ast
    :doc "
")

(define  ("list")
    :category :proof
    :parser pignose-parse-list-command
    :evaluator eval-ast
    :doc "
")

(define ("flag")
    :category :proof
    :parser pignose-parse-flag
    :evaluator eval-ast
    :doc "
")

(define  ("param")
    :category :proof
    :parser pignose-parse-param
    :evaluator eval-ast
    :doc "
")

(define ("option")
    :category :proof
    :parser pignose-parse-option
    :evaluator eval-ast
    :doc "
")

(define ("resolve")
    :category :proof
    :parser pignose-parse-resolve
    :evaluator eval-ast
    :doc "
")

(define  ("demod")
    :category :proof
    :parser pignose-parse-demod
    :evaluator eval-ast
    :doc "
")

(define ("save-option")
    :category :proof
    :parser pignose-parse-save-option
    :evaluator eval-ast
    :doc "
")

(define ("sigmatch")
  :category :proof
  :parser pignose-parse-sigmatch
  :evaluator eval-ast
  :doc "
")

(define  ("lex")
    :category :proof
    :parser pignose-parse-lex
    :evaluator eval-ast
    :doc "
")

(define (".")
    :category :misc
    :parser identity
    :evaluator cafeobj-nop
    :doc "
")


;;;
)					; end eval-when
;;; EOF
