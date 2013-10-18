Gory Details {#gorydetails}
============

This chapter presents all syntactic elements of \_cafeobj as
well as several meta-concepts in alphabetic order. Concepts are
cross-linked for easy accessibility.

### `?` ### {#help}

lists all top-level commands. The `?` can be used after many of the
top-level commands to obtain help.

### `**`, `**>` ### {#starstar}

Starts a comment which extends to the end of the line. 
With the additional `>` the comment is displayed while
evaluated by the interpreter.

Related: [`--`](#dashdash) [comments](#comments)

### `--`, `-->` ### {#dashdash}

Starts a comment which extends to the end of the line. 
With the additional `>` the comment is displayed while
evaluated by the interpreter.

Related: [`**`](#starstar) [comments](#comments)


### `axioms { <decls> }` ### {#axioms}

Block enclosing declarations of variables, equations, and 
transitions.
Other statements are not allowed within the `axioms` block.
Optional structuring of the statements in a module.

Related: [`signature`](#signature) [`imports`](#imports)
	 [`var`](#var) [`eq`](#eq) [`trans`](#trans)


### `bceq [ <label-exp> ] <term> = <term> if <boolterm> .` ### {#bceq}

Alias: `bcq`

Defines a behaviour conditional equation. For details see [`ceq`](#ceq).

Related: [`eq`](#eq) [`ceq`](#ceq) [`beq`](#beq)

### `beq [ <label-exp> ] <term> = <term> .` ### {#beq}

Defines a behaviour equation. For details see [`eq`](#eq).

Related: [`eq`](#eq) [`ceq`](#ceq) [`bceq`](#bceq)


### `bctrans [ <label-exp> ] <term> => <term> if <boolterm> .` ### {#bctrans}

Defines a behaviour conditional transition. 
For details see [`ctrans`](#ctrans).

Related [`trans`](#trans) [`ctrans`](#ctrans) [`btrans`](#btrans)

### `bop <op-spec> : <sorts> -> <sort>` ### {#bop}

Defines a behavioural operator by its domain, codomain, and the term 
construct. `<sorts>` is a space separated list of sort names containing
*exactely* one hidden sort. `<sort>` is a single sort name.

For `<op-spec>` see the explanations of [`op`](#op).

Related: [`op`](#op)

### `bpred <op-spec> : <sorts>` ### {#bpred}

Short hand for `op <op-spec> : <sorts> -> Bool` defining a
behavioural predicate.

Related: [`op`](#op) [`bop`](#op) [`pred`](#bpred)


### `breduce [ in <mod-exp> : ] <term> .` ### {#breduce}

Alias: `bred`

Reduce the given term in the given module, if `<mod-exp>` is given, 
otherwise in the current module. 

For `breduce` equations, possibly conditional, possibly behavioural, are taken
into account for reduction.

Related: [`execute`](#execute) [`reduce`](#reduce)


### `btrans [ <label-exp> ] <term> => <term> .` ### {#btrans}

Defines a behaviour transition. For details see [`trans`](#trans).

Related [`trans`](#trans) [`ctrans`](#ctrans) [`bctrans`](#bctrans)


### `cd <dirname>` ### {#cd}

Change the current working directory, like the Unix counterpart.
The argument is necessary. No kind of expansion or substitution is done.

Related: [`pwd`](#pwd) [`ls`](#ls)

### `ceq [ <label-exp> ] <term> = <term> if <boolterm> .` ### {#ceq}

Defines a conditional equation. Spaces around the `if` are obligatory.
`<boolterm>` needs to be a Boolean term. For other requirements
see [`eq`](#eq).

Related: [`eq`](#eq) [`beq`](#beq) [`bceq`](#bceq)


### comments ### {#comments}

The interpreter accepts the following strings as start of a comment
that extends to the end of the line: `--`, `-->`, `**`, `**>`.

The difference in the variants with `>` is that the comment is
displayed when run through the interpreter.

Related: [`**`](#starstar) [`--`](#dashdash)


### `ctrans [ <label-exp> ] <term> => <term> .` ### {#ctrans}

Defines a conditional transition. For details see [`trans`](#trans)
and [`ceq`](#ceq).

Related [`trans`](#trans) [`btrans`](#ctrans) [`bctrans`](#bctrans)


### `describe <something>` ### {#describe}

like the `show` command with more details. See `describe ?` for
the possible set of invocations.

Related: [`show`](#show)

### `eof` ### {#eof}

Terminates reading of the current file. Allows for keeping
untested code or documentations below the `eof` mark. Has
to be on a line by itself without leading spaces.


### `eq [ <label-exp> ] <term> = <term> .` ### {#eq}

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



### `execute [ in <mod-exp> : ] <term> .` ### {#execute}

Alias: `exec`

Reduce the given term in the given module, if `<mod-exp>` is given, 
otherwise in the current module. 

For `execute` equations and transitions, possibly conditional, are taken
into account for reduction.

Related: [`breduce`](#breduce) [`reduce`](#reduce)


### `extending ( <modexp> )` ### {#extending}

Alias: `ex`

imports the object specified by `modexp` into the current
module, allowing models to be inflated, but not collapsing. 
See `module expression` for format of `modexp`.

Related: [`including`](#including) [`protecting`](#protecting) 
	 [`using`](#using)


### `imports { <import-decl> }` ### {#imports}

Block enclosing import of other modules (`protecting` etc). 
Other statements are not allowed within the `imports` block.
Optional structuring of the statements in a module.

Related: [`signature`](#signature) [`axioms`](#axioms)
  [`extending`](#extending)   [`including`](#including) 
  [`protecting`](#protecting) [`using`](#using)


### `including ( <modexp> )` ### {#including}

Alias: `in`

imports the object specified by `modexp` into the current
module. TODO what are the consequences for the models? TODO
See `module expression` for format of `modexp`.

Related: [`extending`](#including) [`protecting`](#protecting) 
	 [`using`](#using)

### `input <pathname>` ### {#input}

requests the system to read the file specified by the
pathname. The file itself may contain `input` commands.
\_cafeobj reads the file up to the end, or until it encounters
a line that only contains (the literal) `eof`.


### `ls <pathname>` ### {#ls}

lists the given `pathname`. Argument is obligatory.

Related: [`cd`](#ls) [`pwd`](#pwd)

### `module[!|*] <modname> [ ( <params> ) ] [ <principal_sort_spec> ] { mod_elements ... }` ### {#module}

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

### module expression ### {#moduleexpression}

TODO syntax 65, section 8.4 ff

### parametrized module ### {#parametrizedmodule}

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

### on-the-fly variable declaration ### {#onthefly}

See [`var`](#var)

### `op <op-spec> : <sorts> -> <sort>` ### {#op}

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

### `parse [ in <mod-exp> : ] <term> .` ### {#parse}

Tries to parse the given term within the module specified by
the module expression `<mod-exp>`, or the current module if not given,
and returns the parsed and qualified term.

In case of ambiguous terms, i.e., different possible parse trees, the
command will prompt for one of the trees.

Related: [qualified term](#qualified)

### `pred <op-spec> : <sorts>` ### {#pred}

Short hand for `op <op-spec> : <sorts> -> Bool` defining a predicate.

Related: [`op`](#op) [`bpred`](#bpred)

### `protect <module-name>` ### {#protect}

Protect a module from being overwritten.
Some modules vital for the system are initially protected.
Can be reversed with `unprotect`.

Related: [`unprotect`](#unprotect)


### `protecting ( <modexp> )` ### {#protecting}

Alias: `pr`

imports the object specified by `modexp` into the current
module, preserving all intended models as they are. See `module expression`
for format of `modexp`.

Related: [`extending`](#extending) [`using`](#using) [`including`](#including)

### `provide <feature>` ### {#provide}

discharges a feature requirement: once `provide`d, all the subsequent
`require`ments of a feature are assumed to have been fulfilled
already.

Related: [`require`](#require)

### `pwd` ### {#pwd}

Prints the current working directory.

Related: [`cd`](#cd) [`ls`](#ls)

### qualified term ### {#qualified}

In case that a term can be parsed into different sort, it is possible to
qualify the term to one of the possible sorts by affixing it with 
`: <sort-name>` (spaces before and after the `:` are optional).

Example: `1:NzNat` `2:Nat`

Related: [`parse`](#parse)


### `reduce [ in <mod-exp> : ] <term> .` ### {#reduce}

Alias: `red`

Reduce the given term in the given module, if `<mod-exp>` is given, 
otherwise in the current module. 

For `reduce` only equations and conditional equations are taken into
account for reduction.

Related: [`execute`](#execute) [`breduce`](#breduce)



### `regularize <mod-name>` ### {#regularize}

Regularizes the signature of the given module, ensuring that every
term has exactely one minimal parse tree. In this process additional
sorts are generated to ensure unique least sort of all terms.

Modules can be automatically regularized by the interpreter if the
`regularize signature` switch is turn to `on`:

`set regularize signature on`

TODO -- should we give more details here -- unclear to me.

### `require <feature> [ <pathname> ]` ### {#require}

requires a feature, which usually
denotes a set of module definitions. Given this command, the
system searches for a file named the feature, and read the file
if found. If a pathname is given, the system searches for a file
named the pathname instead.

Related: [`provide`](#provide)


### `restore <pathname>` ### {#restore}

restores module definitions from the designated file `pathname` which 
has been saved with the `save` command. `input` can also be used but
the effects might be different.

TODO -- should we keep the different effects? What is the real difference?

Related: [`input`](#input) [`save`](#save) 
	 [`save-system`](#save-system)

### `save <pathname>` ### {#save}

saves module definitions into the designated file `pathname`.
File names should be suffixed with `.bin`. 

`save` also saves the contents of prelude files as well as module definitions
given in the current session.

Related: [`input`](#input) [`restore`](#restore) [`save-system`](#save-system)

### `save-system <pathname>` ### {#save-system}

dumps the image of the whole system into a file. This is functionality
provided by the underlying Common Lisp system and might carry some 
restrictons.

Related: [`input`](#input) [`save`](#save) [`restore`](#restore)

### `set <name> [option] <value>` ### {#set}

Depending on the type of the switch, options and value specification varies.
Possible value types for switches are boolean (`on`, `off`), string (`"value"`),
integers (5434443), lists (lisp syntax).

For a list of all available switches, use `set ?`. To see the current
values, use `show switches`. To single out two general purpose switches,
`verbose` and `quiet` tell the system to behave in the respective way.

Related: [`show`](#show) [`switches`](#switches)

### `show <something>` ### {#show}

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

### `signature { <sig-decl> }` ### {#signature}

Block enclosing declarations of sorts and operators.
Other statements are not allowed within the `signature` block.
Optional structuring of the statements in a module.

Related: [`axioms`](#axioms) [`imports`](#imports)
	 [`sort`](#sort) [`op`](#op)


### sort declaration ### {#sort}

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

### switches ### {#switches}

The following list is the full set of switches at the time of writing:

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


### `trans [ <label-exp> ] <term> => <term> .` ### {#trans}

Defines a transition, which is like an equation but without
symmetry. 

See [`eq`](#eq) for specification of requirements on `<label-exp>`
and the terms.

TODO: should we write more here


### `unprotect <module-name>` ### {#unprotect}

Remove overwrite protection from a module that has been protected
with the `protect` call. Some modules vital for the system
are initially protected.

Related: [`protect`](#protect)


### `using ( <modexp> )` ### {#using}

Alias: `us`

imports the object specified by `modexp` into the current
module without any restrictions on the models.
See `module expression` for format of `modexp`.

Related: [`extending`](#extending) [`including`](#including) 
	 [`protecting`](#protecting)


### `var <var-name> : <sort-name>` ### {#var}

Declares a variable `<var-name>` to be of sort `<sort-name>`.
The scope of the variable is the current module.
Redeclarations of variable names are not allowed.
Several variable of the same sort can be declared at the same time
using the `vars` construct:

`vars <var-name> ... : <sort-name>`

Variable can also be declared *on-the-fly* (or *inline*). If an 
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

Related: [`op`](#op) [qualified term](#qualified)












MISSING UNCLEAR
---------------

chapter 4.4

TO BE REMOVED DISCUSSION
------------------------
stop command, can be done with set stop pattern ...
