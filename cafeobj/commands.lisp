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
(define ("!refman")
     :type :doc-only
     :doc "
Gory Details {#gorydetails}
============

This chapter presents all syntactic elements of \_cafeobj as
well as several meta-concepts in alphabetic order. Concepts are
cross-linked for easy accessibility.
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

(define ("#define")
    :category :module-element
    :parser identity
    :evaluator cafeobj-eval-module-element-proc
    :doc "
")
  

(define ("--" "**")
    :category :decl-toplevel
    :parser parse-comment-command
    :evaluator identity
    :doc "
## `**`, `**>` ## {#starstar}

Starts a comment which extends to the end of the line. 
With the additional `>` the comment is displayed while
evaluated by the interpreter.

Related: [`--`](#dashdash) [comments](#comments)
")


(define ("-->" "**>")
    :doc "
## `--`, `-->` ## {#dashdash}

Starts a comment which extends to the end of the line. 
With the additional `>` the comment is displayed while
evaluated by the interpreter.

Related: [`**`](#starstar) [comments](#comments)
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

(define ("=(n)=>" "=(n,m)=>" "=()=>" "search" "search predicate")
    :type :doc-only
    :doc "
\_cafeobj provides a whole set of search predicates `=(n,m)=>` for
searching transitions starting from a given term. The first value `n`
specifies the maximum number of solutions searched, and can be either
a natural number of `*`, in which case all solutions are searched. The
second value `m` is the maximum depth, and can be a natural number
(but not `*`).

TODO: `=(n,m)=>+` ??? other specifiers?
")

(define ("accept" "accept =*=" "accept =*= proof")
    :type :doc-only
    :doc "
TODO missing documentation
difficult - see TODO for [`=*=`](#bequality)
")

(define ("?")
    :category :help
    :parser identity
    :evaluator cafeobj-top-level-help
        :doc "
## `?` ## {#help}

lists all top-level commands. The `?` can be used after many of the
top-level commands to obtain help.
")

(define ("all axioms")
    :type :doc-only
    :doc "
Controls whether axioms from included modules are shown
during a `show` invocation.

Related: [`show`](#show)
")

(define ("always" "always memo")
    :type :doc-only
    :doc "
Turns on memorization of computation also for operators without
the [`memo`](#opattr) operator attribute.

Related: [`memo` switch](#switch-memo) [operator attributes](#opattr)
")

(define ("apply")
    :category :proof
    :parser parse-apply-command
    :evaluator eval-ast
    :doc "
## `apply <action> [ <subst> ] <range> <selection>` ## {#apply}

Applies one of the following actions `reduce`, `exec`, `print`, or a
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
selection. In the later case it means exactely at the (sub)term.

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
  then the expression `{2, 4, 5}` selects the subterm `c * c * e`.


Related: [`choose`](#choose)
         [`start`](#start) 
")

(define ("auto" "auto context")
    :type :doc-only
    :doc "
## `auto context` switch ## {#switch-auto-context}

Possible values: `on` or `off`, default is `off`.

If this switch is `on`, the context will automatically switch to
the most recent module, i.e., defining a module or inspecting 
a module's content will switch the current module.
")

(define  ("autoload")
    :category :library
    :parser parse-autoload-command
    :evaluator eval-ast
    :doc "
## `autoload` ## {#autoload}

TODO No documentation in original manual, no idea!
")

(define ("axioms" "axiom" "axs")
    :category :module-element
    :parser identity
    :evaluator cafeobj-eval-module-element-proc
    :doc "
## `axioms { <decls> }` ## {#axioms}

Block enclosing declarations of variables, equations, and 
transitions.
Other statements are not allowed within the `axioms` block.
Optional structuring of the statements in a module.

Related: [`signature`](#signature)
         [`imports`](#imports)
	 [`var`](#var)
         [`eq`](#eq)
         [`trans`](#trans)
")

(define ("beq" "bceq" "bcq")
    :category :module-element
    :parser identity
    :evaluator cafeobj-eval-module-element-proc
    :doc "
## `bceq [ <op-exp> ] <term> = <term> if <boolterm> .` ## {#bceq}

Alias: `bcq`

Defines a behaviour conditional equation. For details see [`ceq`](#ceq).

Related: [`eq`](#eq) [`ceq`](#ceq) [`beq`](#beq)
")

(define ("beq")
    :category :module-element
    :parser identity
    :evaluator cafeobj-eval-module-element-proc
    :doc "
## `beq [ <op-exp> ] <term> = <term> .` ## {#beq}

Defines a behaviour equation. For details see [`eq`](#eq).

Related: [`eq`](#eq) [`ceq`](#ceq) [`bceq`](#bceq)
")

(define ("bctrans")
    :category :module-element
    :parser identity
    :evaluator cafeobj-eval-module-element-proc
    :doc "
## `bctrans [ <label-exp> ] <term> => <term> if <bool> .` ## {#bctrans}

Defines a behaviour conditional transition. 
For details see [`ctrans`](#ctrans).

Related [`trans`](#trans) [`ctrans`](#ctrans) [`btrans`](#btrans)
")

(define ("bop" "bops")
    :category :module-element
    :parser identity
    :evaluator cafeobj-eval-module-element-proc
    :doc "
## `bop <op-spec> : <sorts> -> <sort>` ## {#bop}

Defines a behavioural operator by its domain, codomain, and the term 
construct. `<sorts>` is a space separated list of sort names containing
*exactely* one hidden sort. `<sort>` is a single sort name.

For `<op-spec>` see the explanations of [`op`](#op).

Related: [`op`](#op)
")

(define ("bpred")
    :category :module-element
    :parser identity
    :evaluator cafeobj-eval-module-element-proc
    :doc "
## `bpred <op-spec> : <sorts>` ## {#bpred}

Short hand for `op <op-spec> : <sorts> -> Bool` defining a
behavioural predicate.

Related: [`op`](#op)
         [`bop`](#op)
         [`pred`](#bpred)
")

(define ("bred" "breduce")
    :category :rewrite
    :parser parse-bred-command
    :evaluator eval-ast
    :doc "
## `breduce [ in <mod-exp> : ] <term> .` ## {#breduce}

Alias: `bred`

Reduce the given term in the given module, if `<mod-exp>` is given, 
otherwise in the current module. 

For `breduce` equations, possibly conditional, possibly behavioural, are taken
into account for reduction.

Related: [`execute`](#execute) [`reduce`](#reduce)
")

(define ("btrans" "bctrans")
    :category :module-element
    :parser identity
    :evaluator cafeobj-eval-module-element-proc
    :doc "
## `btrans [ <label-exp> ] <term> => <term> .` ## {#btrans}

Defines a behaviour transition. For details see [`trans`](#trans).

Related [`trans`](#trans) [`ctrans`](#ctrans) [`bctrans`](#bctrans)
")

(define ("cbred")
    :category :rewrite
    :parser parse-cbred-command
    :evaluator eval-ast
    :doc "
## `cbred` ## {#cbred}

TODO no documentation

")

(define  ("cd") 
    :category :misc
    :parser parse-cd-command
    :evaluator eval-ast
    :doc "
## `cd <dirname>` ## {#cd}

Change the current working directory, like the Unix counterpart.
The argument is necessary. No kind of expansion or substitution is done.

Related: [`pwd`](#pwd) [`ls`](#ls)
")

(define ("ceq" "cq")
    :category :module-element
    :parser identity
    :evaluator cafeobj-eval-module-element-proc
    :doc "
## `ceq [ <op-exp> ] <term> = <term> if <boolterm> .` ## {#ceq}

Defines a conditional equation. Spaces around the `if` are obligatory.
`<boolterm>` needs to be a Boolean term. For other requirements
see [`eq`](#eq).

Related: [`eq`](#eq) [`beq`](#beq) [`bceq`](#bceq)
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

(define  ("choose") 
    :category :proof
    :parser parse-choose-command
    :evaluator eval-ast
    :doc "
## `choose <selection>` ## {#choose}

Chooses a subterm by the given `<selection>`. See [`apply`](#apply)
for details on `<selection>`.

Related: [`apply`](#apply) [`start`](#start)
	 [`strat` in operator attributes](#opattr)
")

(define ("clean" "clean memo")
    :category :rewrite
    :parser identity
    :evaluator cafeobj-eval-clear-memo-proc
    :doc "
## `clean memo` ## {#cleanmemo}

Resets (clears) the memo storages of the system. Memorized computations 
are forgotten. 

Related: [`clean memo` switch](#switch-clean-memo)
")

(define ("close")
    :category :proof
    :parser parse-close-command
    :evaluator eval-ast
    :doc "
## `close` ## {#close}

This command closes a modification of a module started by `open`.

Related: [`open`](#open)
")

(define ("comments" "comment")
    :type :doc-only
    :doc "
## comments ## {#comments}

The interpreter accepts the following strings as start of a comment
that extends to the end of the line: `--`, `-->`, `**`, `**>`.

The difference in the variants with `>` is that the comment is
displayed when run through the interpreter.

Related: [`**`](#starstar) [`--`](#dashdash)
")

(define ("cond" "cond limit")
    :type :doc-only
    :doc "
## `cond limit` switch ## {#switch-cond-limit}

TODO missing documentation

")

(define ("ctrans")
    :category :module-element
    :parser identity
    :evaluator cafeobj-eval-module-element-proc
    :doc "
## `ctrans [ <label-exp> ] <term> => <term> .` ## {#ctrans}

Defines a conditional transition. For details see [`trans`](#trans)
and [`ceq`](#ceq).

Related [`trans`](#trans) [`btrans`](#ctrans) [`bctrans`](#bctrans)
")

(define ("describe" "desc")
    :category :inspect
    :parser parse-show-command
    :evaluator eval-ast
    :doc "
## `describe <something>` ## {#describe}

like the `show` command with more details. See `describe ?` for
the possible set of invocations.

Related: [`show`](#show)
")

(define ("eof")
    :type :doc-only
    :doc "
## `eof` ## {#eof}

Terminates reading of the current file. Allows for keeping
untested code or documentations below the `eof` mark. Has
to be on a line by itself without leading spaces.
")

(define ("eq")
    :category :module-element
    :parser identity
    :evaluator cafeobj-eval-module-element-proc
    :doc "
## `eq [ <op-exp> ] <term> = <term> .` ## {#eq}

Declares an axiom, or equation.

Spaces around the `=` are necessary to separate the left from
the right hand side. The terms given must belong to the
same connected component in the graph defined by the sort ordering.

In simple words, the objects determined by the terms must be
interpretable as of the same sort.

The optional part `<op-exp>` serves two purposes, one is to give
an axiom an identifier, and one is to modify its behaviour. The
`<op-exp>` is of the form:

` [ <modifier> <label> ] : `

Warning: The square brackets here are *not* specifying optional
components, but syntactical elements. Thus, a labeled axiom
can look like:

`eq[foobar] : foo = bar .`

The `<modifier>` part is used to change the rewriting behaviour of
the axiom.  There are at the moment two possible 
modifiers, namely `:m-and` and `:m-or`. Both make sense only for
operators where the arguments come from an associative sort.
In this case both modifiers create all possible permutations
of the arguments and rewrite the original term to the conjunction
in case of `:m-and` or to the disjunction in case of `:m-or` of all
the generated terms.

Assume that `NatSet` is a sort with associative constructor modelling
a set of natural number, and let

`````
  pred p1: Nat .
  ops q1 q2 : NatSet -> Bool .
  eq [:m-and]: q1(N1:Nat NS:NatSet) = p1(N1) .
  eq [:m-or]:  q2(N1:Nat NS:NatSet) = p1(N1) .
`````

In this case an expression like `q1(1 2 3)` would reduce to 
`p1(1) and p1(2) and p1(3)` (modulo AC), and `q2(1 2 3)` into
the same term with `or` instead.

Related: [`ceq`](#ceq) [`beq`](#beq) [`bceq`](#bceq)
")

(define ("exec limit")
    :type :doc-only
    :doc "
## `exec limit` switch ## {#switch-exec-limit}

Possible values: integers, default limit 4611686018427387903.

Controls the number of maximal transition steps.

Related: [`reduce`](#reduce)
")

(define ("exec trace")
    :type :doc-only
    :doc "
## `exec trace` switch ## {#switch-exec-trace}

Possible values: `on` `off, default `off`.

controls whether further output is provided during reductions.

Related: [`reduce`](#reduce)
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

(define  ("find")
    :category :proof
    :parser parse-find-command
    :evaluator eval-ast
    :doc "
## `find` ## {#find}

TODO missing documentation
")

(define ("find all" "find all rules")
    :type :doc-only
    :doc "
## `find all rules` switch ## {#switch-find-all-rules}

TODO missing documentation
")



(define ("full" "full-reset" "full reset") 
    :doc ((("full reset" "full-reset") "reset system to initial status."))
    :category :system
    :parser parse-full-reset-command
    :evaluator eval-ast
    :doc ((("full reset" "full-reset") "
## `full reset` ## {#fullreset}

Reinitializes the internal state of the system. All supplied modules
definitions are lost.

Related: [`reset`](#reset)
")))

(define ("gendoc")
    :category :io
    :parser parse-gendoc-command
    :evaluator eval-ast
    :doc "
## `gendoc <pathname>` ## {#gendoc}

generates reference manual from system's on line help documents, 
and save it to `pathname`.
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

(define ("include BOO")
    :type :doc-only
    :doc "
## `include BOOL` switch ## {#switch-include-bool}

Possible values: `on` `off`, default `on`.

By default a couple of built-in modules are implicitly imported with
protecting mode. In particular, BOOL is of practical importance. It
defines Boolean operators. It is imported to admit conditional
axioms.

This switch allows to disable automatic inclusion of BOOL.
")

(define ("include RWL")
    :type :doc-only
    :doc "
## `include RWL` switch ## {#switch-include-rwl}

Possible values: `on` `off`, default `off`.

This switch allows to disable automatic inclusion of RWL.
")

(define ("inc" "including")
    :category :module-element
    :parser identity
    :evaluator cafeobj-eval-module-element-proc
    :doc "
## `including ( <modexp> )` ## {#including}

Alias: `in`

imports the object specified by `modexp` into the current
module. 

See [`module expression`](#moduleexpression) for format of `modexp`.

Related: [`extending`](#including) [`protecting`](#protecting) 
	 [`using`](#using) [`module expression`](#moduleexpression)

")

(define  ("in" "input")
    :category :misc
    :parser parse-input-command
    :evaluator cafeobj-eval-input-proc
    :doc "
## `input <pathname>` ## {#input}

requests the system to read the file specified by the
pathname. The file itself may contain `input` commands.
\_cafeobj reads the file up to the end, or until it encounters
a line that only contains (the literal) `eof`.

")

(define ("instant" "instatiation")
    :type :doc-only
    :doc "
## instantiation of parametrised modules ## {#instantiation}

Parametrized modules allow for instantiation. The process of
instantiation binds actual parameters to formal parameters. The result
of an instantiation is a new module, obtained by replacing occurrences
of parameter sorts and operators by their actual counterparts. If, as
a result of instantiation, a module is imported twice, it is assumed
to be imported once and shared throughout.

Instantiation is done by

`<module_name> ( <bindings> )`

where `<module_name>` is the name of a parametrized module, and
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
of the parametrized module `<mod_name>`.

This can be combined with the ephemeral defintion of a view like in
the following example (assume `ILIST` has two parameters):

~~~~~
module NAT-ILIST {
  protecting ( ILIST(SIMPLE-NAT { sort Elt -> Nat },
                     DATATYPE   { sort Elt -> Data }) )
}
~~~~~

")


(define ("let") 
    :category :decl-toplevel
    :parser process-let-declaration-form
    :evaluator eval-ast
    :doc "
## `let <identifier> = <term> .` ## {#let}

Using `let` one can define aliases, or context variables. Bindings
are local to the current module. Variable defined with `let` can be
used in various commands like `reduce` and `parse`. 

Although `let` defined variable behave very similar to syntactic
shorthands, they are not. The right hand side `<term>` needs to
be a fully parsable expression.
")

(define ("libpath" "libarary path")
    :type :doc-only
    :doc "
## `libpath` switch ## {#switch-libpath}

Possible values: list of strings.

The switch `libpath` contains a list of directories where \_cafeobj
searches for include files. Addition and removal of directories can be
done with

`````
set libpath + <path1>:<path2>:...
set libpath - <path1>:<path2>:...
`````

or the full libpath reset by `set libpath <path1>:<path2>:...`

The current directory has a privileged status: It is always searched
first and cannot be suppressed.
")


(define ("look" "look up")
    :category :inspect
    :parser parse-look-up-command
    :evaluator eval-ast
    :doc "
## `look up <something>` ## {#lookup}

TODO to be written, currently segfaults

")

(define ("ls")
    :category :misc
    :parser parse-ls-command
    :evaluator eval-ast
    :doc "
## `ls <pathname>` ## {#ls}

lists the given `pathname`. Argument is obligatory.

Related: [`cd`](#ls) [`pwd`](#pwd)


## `make <mod_name> ( <mod_exp> )` ## {#make}

This commands defines a new module `<mod_name>` by evaluating the
module expression `<mod_exp>`.

Related: [module expressions](#moduleexpression)
")

(define ("match" "unify")
    :category :inspect
    :parser parse-match-command
    :evaluator eval-ast
    :doc "
## `match <term_spec> to <pattern> .` ## {#match}

Matches the term denoted by `<term_spec>` to the
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
the matching substitution is printed.
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

(define ("parameter" "parameterized" "parameterized module")
    :type :doc-only
    :doc "
## parametrized module ## {#parametrizedmodule}

A module with a parameter list (see `module`) is a parametrized module.
Parameters are given as a comma (`,`) separated list. Each parameter is
of the form `[ <import_mode> ] <param_name> :: <module_name>` 
(spaces around `::` are obligatory).

The parameter's module gives minimal requirements on the module
instantiation.

Within the module declaration sorts and operators of the parameter
are qualified with `.<parameter_name>` as seen in the example below.

Example:

~~~~~
mod* C {
  [A]
  op add : A A -> A .
}
mod! TWICE(X :: C) {
  op twice : A.X -> A.X .
  eq twice(E:A.X) = add.X(E,E) .
}
~~~~~

Related: [qualified sort etc](#qualifiedother)
")

(define ("memo")
    :type :doc-only
    :doc "
## `memo` switch ## {#switch-memo}

controls the memorization of computations. The system memorizes 
evaluations of operators declared with the [`memo`](#opattr) operator
attribute. Turning this switch off disables all memorization.
")

(define ("on-the-fly" "on the fly")
    :type :doc-only
    :doc "
## on-the-fly declarations ## {#onthefly}

Variables and constants can be declared *on-the-fly* (or *inline*). If an 
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
definitions are quite common in proof scores.

Related: [`var`](#var)
")

(define ("op" "ops")
    :category :module-element
    :parser identity
    :evaluator cafeobj-eval-module-element-proc
    :doc "
## `op <op-spec> : <sorts> -> <sort> { <attribute-list> }` ## {#op}

Defines an operator by its domain, codomain, and the term construct.
`<sorts>` is a space separated list of sort names, `<sort>` is a 
single sort name.
`<op-spec>` can be of the following forms:

prefix-spec
  ~ the `<op-spec>` does not contain a literal `_`:
    This defines a normal prefix operator with domain `<sorts>` and
    codomain `<sort>`

    Example: `op f : S T -> U`
mixfix-spec
  ~ the `<op-spec>` contains exactely as many literal `_` as there are
    sort names in `<sorts>`:
    This defines an arbitrary mixfix (including postfix) operator
    where the arguments are inserted into the positions designated 
    by the underbars.

    Example: `op _+_ : S S -> S`

For the description of `<attribute-list>` see the entry for
[operator attributes](#opattr).
")


(define ("open")
    :category :proof
    :parser parse-open-command
    :evaluator eval-ast
    :doc "
## `open <mod_exp> .` ## {#open}

This command opens the module specified by the module expression
`<mod_exp>` and allows for declaration of new sorts, operators, etc.

Related: [`close`](#close) [module expression](#moduleexpression)
	 [`select`](#select)
")

(define ("operator attributes" "operator attribute" "operator" "assoc" "comm" "id" "idr" "strat" "constr")
    :type :doc-only
    :doc "
## operator attributes ## {#opattr}

In the specification of an operator using the [`op`](#op) (and
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
 
    In this case the first argument (the boolean term) is tried to
    be evaluated, and depending on that either the second or third.
    But if the first (boolean) argument cannot be evaluated, 
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

  - A single underbar cannot be an operator name.

Related: [`bop`](#bop)
")

(define ("operator precedence" "prec")
    :type :doc-only
    :doc "
## operator precedence ## {#opprec}

\_cafeobj allows for complete freedom of syntax, in particular infix
operators and overloading. To correctly parse terms that are ambigous,
all operators have precedence values. These values can be adjusted
manually during definition of the operator 
(see [operator attributes](#opattr)). In absence of manual
specification of the operator precedence, the values are determined by
the following rules:

- standard prefix operators, i.e., those of the form `op f : S1 .. Sk -> S`,
  receive operator precedence value 0.
- unary operators, i.e., those of the form `op u_ : S1 -> S`, receive
  precedence 15.
- mix-fix operators with forst and last token being arguments, i.e.,
  those of the form `op _ arg-or-op _ : S1 .. Sk -> S`, receive
  precedence 41.
- all other operators (constants, operators of the form `a _ b`, etc.)
  receive precedence 0.

Related: [operator attributes](#opattr)
")

(define ("parse")
    :category :parse
    :parser parse-parse-command
    :evaluator eval-ast
    :doc "
## `parse [ in <mod-exp> : ] <term> .` ## {#parse}

Tries to parse the given term within the module specified by
the module expression `<mod-exp>`, or the current module if not given,
and returns the parsed and qualified term.

In case of ambiguous terms, i.e., different possible parse trees, the
command will prompt for one of the trees.

Related: [qualified term](#qualified)

")

(define ("parser normalize")
    :type :doc-only
    :doc "
## `parse normalize` switch ## {#switch-parse-normalize}

TODO missing documentation
")

(define ("pred")
    :category :module-element
    :parser identity
    :evaluator cafeobj-eval-module-element-proc
    :doc "
## `pred <op-spec> : <sorts>` ## {#pred}

Short hand for `op <op-spec> : <sorts> -> Bool` defining a predicate.

Related: [`op`](#op) [`bpred`](#bpred)
")

(define ("print depth")
    :type :doc-only
    :doc "
## `print depth` switch ## {#switch-print-depth}

Possible values: natural numbers, default `unlimited`.

Controls to which depth terms are printed.
")

(define ("print mode")
    :type :doc-only
    :doc "
## `print mode` switch ## {#switch-print-mode}

Possible values: `normal` `fancy` `tree` `s-expr`

Selects one of the print modes.
")

(define ("protect")
    :category :system
    :parser parse-protect-command
    :evaluator eval-ast
    :doc "
## `protect <module-name>` ## {#protect}

Protect a module from being overwritten.
Some modules vital for the system are initially protected.
Can be reversed with `unprotect`.

Related: [`unprotect`](#unprotect)
")

(define ("protecting" "pr")
    :category :module-element
    :parser identity
    :evaluator cafeobj-eval-module-element-proc
    :doc "
## `protecting ( <modexp> )` ## {#protecting}

Alias: `pr`

imports the object specified by `modexp` into the current
module, preserving all intended models as they are. See `module expression`
for format of `modexp`.

Related: [`extending`](#extending) [`using`](#using) [`including`](#including)
")

(define  ("provide") 
    :category :library
    :parser parse-provide-command
    :evaluator eval-ast
    :doc "
## `provide <feature>` ## {#provide}

discharges a feature requirement: once `provide`d, all the subsequent
`require`ments of a feature are assumed to have been fulfilled
already.

Related: [`require`](#require)
")


(define  ("pwd")
    :category :misc
    :parser parse-pwd-command
    :evaluator eval-ast
    :doc "
## `pwd` ## {#pwd}

Prints the current working directory.

Related: [`cd`](#cd) [`ls`](#ls)
")

(define ("qualified sort" "qualified operator" "qualified parameter" "qualify")
    :type :doc-only
    :doc "
## qualified sort/operator/parameter ## {#qualifiedother}

\_cafeobj allows for using the same name for different sorts,
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
`<opname>/<argnr>`

Related: [parametrized module](#parametrizedmodule) [qualified term](#qualified) 
")

(define ("qualified term")
    :type :doc-only
    :doc "
## qualified term ## {#qualified}

In case that a term can be parsed into different sort, it is possible to
qualify the term to one of the possible sorts by affixing it with 
`: <sort-name>` (spaces before and after the `:` are optional).

Example: `1:NzNat` `2:Nat`

Related: [`parse`](#parse)
")

(define ("quiet")
    :type :doc-only
    :doc "
## `quiet` switch ## {#switch-quiet}

Possible values: `on` `off`, default `off`

If set to `on`, the system only issues error messages.

Related: [`verbose` switch](#switch-verbose)
")

(define ("quit" "q")
    :type :doc-only
    :doc "
## `quit` ## {#quit}

Leaves the CafeOBJ interpreter.
")

(define ("red" "reduce")
  :category :rewrite
  :parser parse-reduce-command
  :evaluator eval-ast
  :doc "
## `reduce [ in <mod-exp> : ] <term> .` ## {#reduce}

Alias: `red`

Reduce the given term in the given module, if `<mod-exp>` is given, 
otherwise in the current module. 

For `reduce` only equations and conditional equations are taken into
account for reduction.

Related: [`execute`](#execute) [`breduce`](#breduce)
")

(define ("reduce conditions" "reduce condition")
    :type :doc-only
    :doc "
## `reduce conditions` switch ## {#switch-reduce-conditions}

Possible values: `on` `off`, default `off`.

When using [`apply`](#apply) to step through a reduction, this switch
allows to turn on automatic reduction of conditions in conditional
equations. 

Related: [`apply`](#apply)

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

(define ("regularize signature" "reg signature")
    :type :doc-only
    :doc "
## `regularize signature` switch ## {#switch-regularize-signature}

See [`regularize](#regularize)
")

(define  ("require") 
    :category :library
    :parser parse-require-command
    :evaluator eval-ast
    :doc "
## `require <feature> [ <pathname> ]` ## {#require}

requires a feature, which usually
denotes a set of module definitions. Given this command, the
system searches for a file named the feature, and read the file
if found. If a pathname is given, the system searches for a file
named the pathname instead.

Related: [`provide`](#provide)
")


(define ("reset")
    :category :system
    :parser parse-reset-command
    :evaluator eval-ast
    :doc "
## `reset` ## {#reset}

Restores the definitions of built-in modules and preludes, but does not
affect other modules.

Related: [`full reset`](#fullreset)
")

(define ("restore")
    :category :io
    :parser parse-restore-command
    :evaluator eval-ast
    :doc "
## `restore <pathname>` ## {#restore}

restores module definitions from the designated file `pathname` which 
has been saved with the `save` command. `input` can also be used but
the effects might be different.

TODO -- should we keep the different effects? What is the real difference?

Related: [`input`](#input) [`save`](#save) 
	 [`save-system`](#save-system)

")

(define ("rewrite limit" "rew limit")
    :type :doc-only
    :doc "
## `rewrite limit` switch ## {#switch-rewrite}

Possible values: positive integers, default not specified.

Allows limiting the number of rewrite steps during a stepwise
execution.

Related: [`step` switch](#switch-step)
")


(define ("save")
    :category :io
    :parser parse-save-command
    :evaluator eval-ast
    :doc "
## `save <pathname>` ## {#save}

saves module definitions into the designated file `pathname`.
File names should be suffixed with `.bin`. 

`save` also saves the contents of prelude files as well as module definitions
given in the current session.

Related: [`input`](#input) [`restore`](#restore) [`save-system`](#save-system)
")


(define ("save-system" "save system")	; NOTE. this is obsolete.
    :type :doc-only
    :doc "
## `save-system <pathname>` ## {#save-system}

dumps the image of the whole system into a file. This is functionality
provided by the underlying Common Lisp system and might carry some 
restrictons.

Related: [`input`](#input) [`save`](#save) [`restore`](#restore)
")

(define ("search predicates" "search predicate" "search")
    :type :doc-only
    :doc "
## search predicates ## {#searchpredicate}

\_cafeobj provides a whole set of search predicates `=(n,m)=>` for
searching transitions starting from a given term. The first value `n`
specifies the maximum number of solutions searched, and can be either
a natural number of `*`, in which case all solutions are searched. The
second value `m` is the maximum depth, and can be a natural number
(but not `*`).

TODO: `=(n,m)=>+` ??? other specifiers?
")


(define ("select")
    :category :proof
    :parser parse-show-command
    :evaluator eval-ast
    :doc "
## `select <mod_exp> . ` ## {#select}

Selects a module given by the module expression `<mod_exp>` as the
current module. All further operations are carried out within the
given module. In constrast to `open` this does not allow for
modification of the module, e.g., addition of new sorts etc.

Related: [`open`](#open) [module expression](#moduleexpression)
")


(define  ("set")
    :category :switch
    :parser parse-set-command
    :evaluator eval-ast
    :doc "
## `set <name> [option] <value>` ## {#set}

Depending on the type of the switch, options and value specification varies.
Possible value types for switches are boolean (`on`, `off`), string (`\"value\"`),
integers (5434443), lists (lisp syntax).

For a list of all available switches, use `set ?`. To see the current
values, use `show switches`. To single out two general purpose switches,
`verbose` and `quiet` tell the system to behave in the respective way.

Related: [`show`](#show) [`switches`](#switches)
")


(define  ("show" "sh")
    :category :inspect
    :parser parse-show-command
    :evaluator eval-ast
    :doc "
## `show <something>` ## {#show}

The `show` command provides various ways to inspect all kind of objects
of the \_cafeobj language. For a full list call `show ?`.

Some of the more important (but far from complete list) ways to call
the `show` command are:

  - `show [ <modexp> ]` - describes the current modules of the one specified
	as argument
  - `show switches` - lists all possible switches
  - `show <term>` - displays a term, posible in tree format

See the entry for `switches` for a full list.

Related: [`switches`](#switches) [`describe`](#describe)
")

(define ("show mode")
    :type :doc-only
    :doc "
## `show mode` switch ## {#switch-show-mode}

Possible values for `set show mode <mode>` are `cafeobj` and `meta`.

TODO no further information on what this changes
")


(define ("signature" "sig")
    :category :module-element
    :parser identity
    :evaluator cafeobj-eval-module-element-proc
    :doc "
## `signature { <sig-decl> }` ## {#signature}

Block enclosing declarations of sorts and operators.
Other statements are not allowed within the `signature` block.
Optional structuring of the statements in a module.

Related: [`axioms`](#axioms) [`imports`](#imports)
	 [`sort`](#sort) [`op`](#op)
")

(define ("sort declaration" "sort" "[" "*[")
    :type :doc-only
    :doc "
## sort declaration ## {#sort}

\_cafeobj supports two kind of sorts, visible and hidden sorts. Visible 
sorts are introduced between `[` and `]`, while hidden sorts are introduced
between `*[` and `]*`.

~~~~
  [ Nat ]
  *[ Obs ]*
~~~~

Several sorts can be declared at the same time, as in `[ Nat Int ]`.

Since \_cafeobj is based on order sorting, sorts can form a partial order.
Definition of the partial order can be interleaved by giving

~~~~
  [ <sorts> < <sorts> ]
~~~~

Where `sorts` is a list of sort names. This declaration defines an inclusion
relation between each pair or left and right sorts.

Example:

~~~~
  [ A B , C D < A < E, B < D ]
~~~~

defines five sorts `A`,...,`E`, with the following relations:
`C < A`, `D < A`, `A < E`, `B < D`.
")

(define ("start")
    :category :proof
    :parser parse-start-command
    :evaluator eval-ast
    :doc "
## `start <term> .` ## {#start}

Sets the focus onto the given term `<term>` of the currently opened
module or context. Commands like `apply`, `choose`, or `match` will
then operate on this term.

Related: [`apply`](#apply) [`choose`](#choose) [`match`](#match)

")

(define ("statistics" "stat")
    :type :doc-only
    :doc "
## `statistics` switch ## {#switch-statistics}

Possible values: `on` `off`, default `on`.

After each reduction details about the reduction are
shown. Information shown are the time for parsing the expression, the
number of rewrites and run time during rewriting, and the number of
total matches performed during the reduce.

TODO: verify
")

(define ("step")
    :type :doc-only
    :doc "
## `step` switch ## {#switch-step}

Possible values: `on` `off`, default `off`.

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

Other standard \_cafeobj commands that can be used are [`show`](#show),
[`describe`](#describe), [`set`](#set), [`cd`](#cd), [`ls`](#ls),
[`pwd`](#pwd), [`lisp`](#lisp), [`lispq`](#lisp), and (on Unix only)
[`!`](#commandexec).
")

(define ("stop pattern" "stop")
    :type :doc-only
    :doc "
## `stop pattern` switch ## {#switch-stop-pattern}

This command causes reductions to stop when the reductants get to
containing subterms that match the given term. If no term is given,
this restriction is lifted. 

TODO does not work as far as I see -- shouldn't the following code
fragment stop at the occurrence of `(s 2)`, before rewriting it to
the final 3?

`````
CafeOBJ> open NAT .

-- opening module NAT.. done.

%NAT> set stop pattern (s 2) .

%NAT> red (s (s (s 0))) .
-- reduce in %NAT : (s (s (s 0))):NzNat
(3):NzNat
(0.000 sec for parse, 3 rewrites(0.000 sec), 3 matches)

%NAT> 
`````

Related: [`step` switch](#switch-step)
")

(define ("switches" "switch")
    :type :doc-only
    :doc "
## switches ## {#switches}

Switches control various aspects of the computations and behaviour
of \_cafeobj. The current list of switches and their values can be
shown with 

`````
show switches
`````

The single switches are described separately in this manual.

Related: [`set`](#set) [`show`](#show)
")

(define ("trace" "trace whole")
    :type :doc-only
    :doc "
## `trace [whole]` switch ## {#switch-trace}

During evaluation, it is sometimes desirable to see the rewrite
sequences, not just the results. Setting the switch `trace whole` will
result in the resultant term of each rewrite step being
printed. Setting the switch `trace` will result in the display of
which rule, substitution, and replacement are used.
")

(define ("trans")
    :category :module-element
    :parser identity
    :evaluator cafeobj-eval-module-element-proc
    :doc "
## `trans [ <label-exp> ] <term> => <term> .` ## {#trans}

Defines a transition, which is like an equation but without
symmetry. 

See [`eq`](#eq) for specification of requirements on `<label-exp>`
and the terms.

Transitions and equations server similar, but different purpose. In
particular, reductions (both with or without behavior axioms used) do
not take transitions into account. Only [`exec`](#execute) also uses
transitions. On the other hand, the built-in 
[search predicate](#searchpredicate) searches all possible transitions
from a given term.
")

(define ("unprotect") 
    :category :system
    :parser parse-unprotect-command
    :evaluator eval-ast
    :doc "
## `unprotect <module-name>` ## {#unprotect}

Remove overwrite protection from a module that has been protected
with the `protect` call. Some modules vital for the system
are initially protected.

Related: [`protect`](#protect)
")

(define ("using" "us")
    :category :module-element
    :parser identity
    :evaluator cafeobj-eval-module-element-proc
    :doc "
## `using ( <modexp> )` ## {#using}

Alias: `us`

imports the object specified by `modexp` into the current
module without any restrictions on the models.
See `module expression` for format of `modexp`.

Related: [`extending`](#extending) [`including`](#including) 
	 [`protecting`](#protecting)
")

(define ("var" "vars")
    :category :module-element
    :parser identity
    :evaluator cafeobj-eval-module-element-proc
    :doc "
## `var <var-name> : <sort-name>` ## {#var}

Declares a variable `<var-name>` to be of sort `<sort-name>`.
The scope of the variable is the current module.
Redeclarations of variable names are not allowed.
Several variable of the same sort can be declared at the same time
using the `vars` construct:

`vars <var-name> ... : <sort-name>`

Related: [`op`](#op) [qualified term](#qualified) [on-the-fly](#onthefly)
")

(define ("verbose")
    :type :doc-only
    :doc "
## `verbose` switch ## {#switch-verbose}

Possible values: `on` `off`, default `off`.

If turn `on`, the system is much more verbose in many commands.

Related: [`quiet` switch](#switch-quiet)
")


(define ("version")
    :category :misc
    :parser parse-version-command
    :evaluator princ
    :doc "
## `version` ## {#version}

Prints out the version of CafeOBJ.
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


  

;;;
;;;*** TODO *** 
;;;

(define  ("dribble")
    :category :misc
    :parser parse-dribble-command
    :evaluator eval-ast
    :doc "
")

(define ("exec!" "execute!")
    :category :rewrite
    :parser parse-exec+-command
    :evaluator eval-ast
    :doc "
exec! [in <Modexpr> :] <Term> .
")

(define  ("stop")
    :category :rewrite
    :parser parse-stop-at
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

(define  ("prelude")
    :category :library
    :parser parse-prelude-command
    :evaluator cafeobj-eval-prelude-proc
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

(define ("pvar" "pvars")
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


(define ("inspect")
    :category :proof
    :parser parse-inspect-term-command
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
Do nothing.
")


;;;
)					; end eval-when
;;; EOF
