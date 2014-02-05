Gory Details {#gorydetails}
============

This chapter presents all syntactic elements of \_cafeobj as
well as several meta-concepts in alphabetic order. Concepts are
cross-linked for easy accessibility.

## `?` ## {#help}

lists all top-level commands. The `?` can be used after many of the
top-level commands to obtain help.

## `**`, `**>` ## {#starstar}

Starts a comment which extends to the end of the line. 
With the additional `>` the comment is displayed while
evaluated by the interpreter.

Related: [`--`](#dashdash) [comments](#comments)

## `--`, `-->` ## {#dashdash}

Starts a comment which extends to the end of the line. 
With the additional `>` the comment is displayed while
evaluated by the interpreter.

Related: [`**`](#starstar) [comments](#comments)

## `==` ## {#equality}

The predicate `==` is a binary operator defined for each visible sort
and is defined in terms of evaluation. That is, for ground terms `t`
and `t'` of the same sort, `t == t'` evaluates to `true` iff terms
reduce to a common term.

## `=/=` ## {#ineq}

Negation of the predicate [`==`](#equality).


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


Related: [`choose`](#choose) [`start`](#start) 


## `axioms { <decls> }` ## {#axioms}

Block enclosing declarations of variables, equations, and 
transitions.
Other statements are not allowed within the `axioms` block.
Optional structuring of the statements in a module.

Related: [`signature`](#signature) [`imports`](#imports)
	 [`var`](#var) [`eq`](#eq) [`trans`](#trans)


## `bceq [ <label-exp> ] <term> = <term> if <boolterm> .` ## {#bceq}

Alias: `bcq`

Defines a behaviour conditional equation. For details see [`ceq`](#ceq).

Related: [`eq`](#eq) [`ceq`](#ceq) [`beq`](#beq)

## `beq [ <label-exp> ] <term> = <term> .` ## {#beq}

Defines a behaviour equation. For details see [`eq`](#eq).

Related: [`eq`](#eq) [`ceq`](#ceq) [`bceq`](#bceq)


## `bctrans [ <label-exp> ] <term> => <term> if <boolterm> .` ## {#bctrans}

Defines a behaviour conditional transition. 
For details see [`ctrans`](#ctrans).

Related [`trans`](#trans) [`ctrans`](#ctrans) [`btrans`](#btrans)

## `bop <op-spec> : <sorts> -> <sort>` ## {#bop}

Defines a behavioural operator by its domain, codomain, and the term 
construct. `<sorts>` is a space separated list of sort names containing
*exactely* one hidden sort. `<sort>` is a single sort name.

For `<op-spec>` see the explanations of [`op`](#op).

Related: [`op`](#op)

## `bpred <op-spec> : <sorts>` ## {#bpred}

Short hand for `op <op-spec> : <sorts> -> Bool` defining a
behavioural predicate.

Related: [`op`](#op) [`bop`](#op) [`pred`](#bpred)


## `breduce [ in <mod-exp> : ] <term> .` ## {#breduce}

Alias: `bred`

Reduce the given term in the given module, if `<mod-exp>` is given, 
otherwise in the current module. 

For `breduce` equations, possibly conditional, possibly behavioural, are taken
into account for reduction.

Related: [`execute`](#execute) [`reduce`](#reduce)


## `btrans [ <label-exp> ] <term> => <term> .` ## {#btrans}

Defines a behaviour transition. For details see [`trans`](#trans).

Related [`trans`](#trans) [`ctrans`](#ctrans) [`bctrans`](#bctrans)


## `cd <dirname>` ## {#cd}

Change the current working directory, like the Unix counterpart.
The argument is necessary. No kind of expansion or substitution is done.

Related: [`pwd`](#pwd) [`ls`](#ls)

## `ceq [ <label-exp> ] <term> = <term> if <boolterm> .` ## {#ceq}

Defines a conditional equation. Spaces around the `if` are obligatory.
`<boolterm>` needs to be a Boolean term. For other requirements
see [`eq`](#eq).

Related: [`eq`](#eq) [`beq`](#beq) [`bceq`](#bceq)


## `check <options>` ## {#check}

This command allows for checking of certain properties of modules and
operators. 

`check regularity <mod_exp>`
  ~ Checks whether the module given by the module expression
  `<mod_exp>` is regular. 

`check compatibility <mod_exp>`
  ~ Checks whether term rewriting system of the module given by the
  module expression `<mod_exp>` is compatible, i.e., every application
  of every rewrite rule to every well-formed term results in a
  well-formed term. (This is not necessarily the case in order-sorted
  rewriting!)

`check laziness <op_name>`
  ~ Checks whether the given operator can be evaluated lazily. If not
  `<op_name>` is given, all operators of the current module are
  checked. 

Related: [`regularize`](#regularize) 


## `choose <selection>` ## {#choose}

Chooses a subterm by the given `<selection>`. See [`apply`](#apply)
for details on `<selection>`.

Related: [`apply`](#apply) [`start`](#start)
	 [`strat` in operator attributes](#opattr)


## `close` ## {#close}

This command closes a modification of a module started by `open`.

Related: [`open`](#open)


## comments ## {#comments}

The interpreter accepts the following strings as start of a comment
that extends to the end of the line: `--`, `-->`, `**`, `**>`.

The difference in the variants with `>` is that the comment is
displayed when run through the interpreter.

Related: [`**`](#starstar) [`--`](#dashdash)


## `ctrans [ <label-exp> ] <term> => <term> .` ## {#ctrans}

Defines a conditional transition. For details see [`trans`](#trans)
and [`ceq`](#ceq).

Related [`trans`](#trans) [`btrans`](#ctrans) [`bctrans`](#bctrans)


## `describe <something>` ## {#describe}

like the `show` command with more details. See `describe ?` for
the possible set of invocations.

Related: [`show`](#show)

## `eof` ## {#eof}

Terminates reading of the current file. Allows for keeping
untested code or documentations below the `eof` mark. Has
to be on a line by itself without leading spaces.


## `eq [ <label-exp> ] <term> = <term> .` ## {#eq}

Declares an axiom, or equation.

Spaces around the `=` are necessary to separate the left from
the right hand side. The terms given must belong to the
same connected component in the graph defined by the sort ordering.

In simple words, the objects determined by the terms must be
interpretable as of the same sort.

One can give an equation a name by providing an optional 
`<label-exp>` which is:

` [ <label-name> ] : `

Warning: The square brackets here are *not* specifying optional
components, but syntactical elements. Thus, a named equation
can look like:

`eq[foobar] : foo = bar .`

Related: [`ceq`](#ceq) [`beq`](#beq) [`bceq`](#bceq)



## `execute [ in <mod-exp> : ] <term> .` ## {#execute}

Alias: `exec`

Reduce the given term in the given module, if `<mod-exp>` is given, 
otherwise in the current module. 

For `execute` equations and transitions, possibly conditional, are taken
into account for reduction.

Related: [`breduce`](#breduce) [`reduce`](#reduce)


## `extending ( <modexp> )` ## {#extending}

Alias: `ex`

imports the object specified by `modexp` into the current
module, allowing models to be inflated, but not collapsing. 
See [`module expression`](#moduleexpression) for format of `modexp`.

Related: [`including`](#including) [`protecting`](#protecting) 
	 [`using`](#using)


## `imports { <import-decl> }` ## {#imports}

Block enclosing import of other modules (`protecting` etc). 
Other statements are not allowed within the `imports` block.
Optional structuring of the statements in a module.

Related: [`signature`](#signature) [`axioms`](#axioms)
  [`extending`](#extending)   [`including`](#including) 
  [`protecting`](#protecting) [`using`](#using)


## `including ( <modexp> )` ## {#including}

Alias: `in`

imports the object specified by `modexp` into the current
module. TODO what are the consequences for the models? TODO
See [`module expression`](#modulesexpression) for format of `modexp`.

Related: [`extending`](#including) [`protecting`](#protecting) 
	 [`using`](#using) [`module expression`](#modulesexpression)

## `input <pathname>` ## {#input}

requests the system to read the file specified by the
pathname. The file itself may contain `input` commands.
\_cafeobj reads the file up to the end, or until it encounters
a line that only contains (the literal) `eof`.


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


## `let <identifier> = <term> .` ## {#let}

Using `let` one can define aliases, or context variables. Bindings
are local to the current module. Variable defined with `let` can be
used in various commands like `reduce` and `parse`. 

Although `let` defined variable behave very similar to syntactic
shorthands, they are not. The right hand side `<term>` needs to
be a fully parsable expression.


## `ls <pathname>` ## {#ls}

lists the given `pathname`. Argument is obligatory.

Related: [`cd`](#ls) [`pwd`](#pwd)


## `make <mod_name> ( <mod_exp> )` ## {#make}

This commands defines a new module `<mod_name>` by evaluating the
module expression `<mod_exp>`.

Related: [module expressions](#moduleexpression)


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


## `module[!|*] <modname> [ ( <params> ) ] [ <principal_sort_spec> ] { mod_elements ... }` ## {#module}

Alias: `mod`

defines a module, the basic building block of \_cafeobj. Possible elements
are declarations of 

  - import - see `protecting`, `extending`, `including`, `using`
  - sorts - see `sort declaration`
  - records - TODO delete?
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

## module expression ## {#moduleexpression}

In various syntax elements not only module names itself, but whole
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
    is often used in combination with [instantiantion](#instantiation).

summation
  ~ `<mod_exp> + <mod_exp>`

    This expression describes a module consisting of all the module
    elements of the summands. If a submodule is imported more than
    once, it is assumed to be shared.

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
equivalent to defining an operator

`op <name> : -> <sort>`

or in the above example, `op a : -> Nat .` These constant definitions
are quite common in proof scores.

Related: [`var`](#var)

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

## `open <mod_exp> .` ## {#open}

This command opens the module specified by the module expression
`<mod_exp>` and allows for declaration of new sorts, operators, etc.

Related: [`close`](#close) [module expression](#moduleexpression)
	 [`select`](#select)

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

## operator precedence ## {opprec}

TODO list the rules for operator precedence

## `parse [ in <mod-exp> : ] <term> .` ## {#parse}

Tries to parse the given term within the module specified by
the module expression `<mod-exp>`, or the current module if not given,
and returns the parsed and qualified term.

In case of ambiguous terms, i.e., different possible parse trees, the
command will prompt for one of the trees.

Related: [qualified term](#qualified)

## `pred <op-spec> : <sorts>` ## {#pred}

Short hand for `op <op-spec> : <sorts> -> Bool` defining a predicate.

Related: [`op`](#op) [`bpred`](#bpred)

## `protect <module-name>` ## {#protect}

Protect a module from being overwritten.
Some modules vital for the system are initially protected.
Can be reversed with `unprotect`.

Related: [`unprotect`](#unprotect)


## `protecting ( <modexp> )` ## {#protecting}

Alias: `pr`

imports the object specified by `modexp` into the current
module, preserving all intended models as they are. See `module expression`
for format of `modexp`.

Related: [`extending`](#extending) [`using`](#using) [`including`](#including)

## `provide <feature>` ## {#provide}

discharges a feature requirement: once `provide`d, all the subsequent
`require`ments of a feature are assumed to have been fulfilled
already.

Related: [`require`](#require)

## `pwd` ## {#pwd}

Prints the current working directory.

Related: [`cd`](#cd) [`ls`](#ls)

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

## qualified term ## {#qualified}

In case that a term can be parsed into different sort, it is possible to
qualify the term to one of the possible sorts by affixing it with 
`: <sort-name>` (spaces before and after the `:` are optional).

Example: `1:NzNat` `2:Nat`

Related: [`parse`](#parse)


## `reduce [ in <mod-exp> : ] <term> .` ## {#reduce}

Alias: `red`

Reduce the given term in the given module, if `<mod-exp>` is given, 
otherwise in the current module. 

For `reduce` only equations and conditional equations are taken into
account for reduction.

Related: [`execute`](#execute) [`breduce`](#breduce)



## `regularize <mod-name>` ## {#regularize}

Regularizes the signature of the given module, ensuring that every
term has exactely one minimal parse tree. In this process additional
sorts are generated to ensure unique least sort of all terms.

Modules can be automatically regularized by the interpreter if the
`regularize signature` switch is turn to `on`:

`set regularize signature on`

TODO -- should we give more details here -- unclear to me.

## `require <feature> [ <pathname> ]` ## {#require}

requires a feature, which usually
denotes a set of module definitions. Given this command, the
system searches for a file named the feature, and read the file
if found. If a pathname is given, the system searches for a file
named the pathname instead.

Related: [`provide`](#provide)


## `restore <pathname>` ## {#restore}

restores module definitions from the designated file `pathname` which 
has been saved with the `save` command. `input` can also be used but
the effects might be different.

TODO -- should we keep the different effects? What is the real difference?

Related: [`input`](#input) [`save`](#save) 
	 [`save-system`](#save-system)

## `save <pathname>` ## {#save}

saves module definitions into the designated file `pathname`.
File names should be suffixed with `.bin`. 

`save` also saves the contents of prelude files as well as module definitions
given in the current session.

Related: [`input`](#input) [`restore`](#restore) [`save-system`](#save-system)

## `save-system <pathname>` ## {#save-system}

dumps the image of the whole system into a file. This is functionality
provided by the underlying Common Lisp system and might carry some 
restrictons.

Related: [`input`](#input) [`save`](#save) [`restore`](#restore)


## `select <mod_exp> . ` ## {#select}

Selects a module given by the module expression `<mod_exp>` as the
current module. All further operations are carried out within the
given module. In constrast to `open` this does not allow for
modification of the module, e.g., addition of new sorts etc.

Related: [`open`](#open) [module expression](#moduleexpression)


## `set <name> [option] <value>` ## {#set}

Depending on the type of the switch, options and value specification varies.
Possible value types for switches are boolean (`on`, `off`), string (`"value"`),
integers (5434443), lists (lisp syntax).

For a list of all available switches, use `set ?`. To see the current
values, use `show switches`. To single out two general purpose switches,
`verbose` and `quiet` tell the system to behave in the respective way.

Related: [`show`](#show) [`switches`](#switches)

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

## `signature { <sig-decl> }` ## {#signature}

Block enclosing declarations of sorts and operators.
Other statements are not allowed within the `signature` block.
Optional structuring of the statements in a module.

Related: [`axioms`](#axioms) [`imports`](#imports)
	 [`sort`](#sort) [`op`](#op)


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

## switches ## {#switches}

The following list is the full set of switches at the time of writing:

TODO subsections of all the switches with explanations for each one

~~~~~
trace  whole            off
trace                   off
step                    off
memo                    on
always  memo            off
clean  memo             off
statistics|stats        on
rewrite|rwt  limit      = not specified
stop  pattern           = not specified
reduce  conditions      off
exec  trace             off
exec  limit             = 536870911
exec  normalize         on
include  BOOL           on
include  RWL            on
include  FOPL-CLAUSE    on
auto  context           off
accept  term            on
regularize|reg  signature  off
check  import           off
check  regularity       off
check  coherency        off
check  sensible         off
check  compatibility    off
check  builtin          on
select  term            off
verbose                 off
quiet                   off
all  axioms             off
show  mode              = :cafeobj
show  var sorts         off
print  mode             = :normal
libpath                 = ("/usr/local/cafeobj-1.4/lib" "/usr/local/cafeobj-1.4/exs")
tram|compiler  path     = "tram"
tram|compiler  options  = ""
print  depth            = not specified
accept  =*= proof       off
find  all rules         off
~~~~~

Related: [`set`](#set) [`show`](#show)


## `start <term> .` ## {#start}

Sets the focus onto the given term `<term>` of the currently opened
module or context. Commands like `apply`, `choose`, or `match` will
then operate on this term.

Related: [`apply`](#apply) [`choose`](#choose) [`match`](#match)


## `tram <options>` ## {#tram}

TODO - do we have a tram compiler still available???


## `trans [ <label-exp> ] <term> => <term> .` ## {#trans}

Defines a transition, which is like an equation but without
symmetry. 

See [`eq`](#eq) for specification of requirements on `<label-exp>`
and the terms.

TODO: should we write more here


## `unprotect <module-name>` ## {#unprotect}

Remove overwrite protection from a module that has been protected
with the `protect` call. Some modules vital for the system
are initially protected.

Related: [`protect`](#protect)


## `using ( <modexp> )` ## {#using}

Alias: `us`

imports the object specified by `modexp` into the current
module without any restrictions on the models.
See `module expression` for format of `modexp`.

Related: [`extending`](#extending) [`including`](#including) 
	 [`protecting`](#protecting)


## `var <var-name> : <sort-name>` ## {#var}

Declares a variable `<var-name>` to be of sort `<sort-name>`.
The scope of the variable is the current module.
Redeclarations of variable names are not allowed.
Several variable of the same sort can be declared at the same time
using the `vars` construct:

`vars <var-name> ... : <sort-name>`

Related: [`op`](#op) [qualified term](#qualified) [on-the-fly](#onthefly)

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
equivalent to defining an operator

`op <name> : -> <sort>`

or in the above example, `op a : -> Nat .` These constant definitions
are quite common in proof scores.

Related: [`var`](#var)


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


Related: [instantiation](#instantiation)




MISSING UNCLEAR
---------------

chapter 4.4

TO BE REMOVED DISCUSSION
------------------------
stop command, can be done with set stop pattern ...
