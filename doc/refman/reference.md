## Ctrl-D ## {#ctrld}

Terminates the input and exit from the interpreter.

## `! <command>` ## {#commandexec}

On Unix only, forks a shell and executes the given `<command>`.

## `#define <pattern> := <term> .` ## {#sharp-define}

Defines <pattern> to be <term>, that is, when <pattern>
appers in term, it is expanded to <term> and then parsed.

## `**`, `**>` ## {#starstar}

Starts a comment which extends to the end of the line. 
With the additional `>` the comment is displayed while
evaluated by the interpreter.

Related: [comments](#comments), [`--`](#starstar)

## `--`, `-->` ## {#dashdash}

Starts a comment which extends to the end of the line. 
With the additional `>` the comment is displayed while
evaluated by the interpreter.

Related: [comments](#comments), [`**`](#starstar)

## `.` ## {#dotsep}

Input separator

## `=` ## {#axeq}

The syntax element `=` introduces an axiom of the equational theory,
and is different from `==` which specifies an equality based on
rewriting.

Related: [`eq`](#eq), [`==`](#equality)

## `=(n)=>`, `=(n,m)=>`, `=()=>` ## {#searchpredsymb}

See [`search predicates`](#searchpredicate)

## `=*=` ## {#bequality}

The predicate for behavioral equivalence, written `=*=`, is a binary
operator defined on each hidden sort.

## `=/=` ## {#notequal}

Negation of the predicate `==`.

Related: [`==`](#equality)

## `==` ## {#equality}

The predicate `==` is a binary operator defined for each visible sort
and is defined in terms of evaluation. That is, for ground terms `t`
and `t'` of the same sort, `t == t'` evaluates to `true` iff terms
reduce to a common term. This is different from the equational `=`
which specifies the equality of the theory.

## `==>` ## {#transrel}

This binary predicate is defined on each visible sort, and defines the
transition relation, which is reflexive, transitive, and closed under
operator application. It expresses the fact that two states (terms)
are connected via transitions.

Related: [search predicates](#searchpredicate), [`trans`](#trans)

## `? [<term>]` ## {#help}

Without any argument, shows the brief guide of online help system.
With argument gives the reference manual description of `term`.
In addition to this, many commands allow for passing `?` as argument
to obtain further help.

In case examples are provided for the `<term>`, they can be displayed
using `?ex <term>`. In this case the normal help output will also contain
an informational message that examples are available.

When called as ?? both documentation and examples are shown.

## `?apropos <term> [<term> ...]` ## {#apropos}

Searches all available online docs for the terms passed.
Terms are separated by white space. Each term is tested independently 
and all terms have to match. Testing is done either by simple sub-string 
search, or, if the term looks like a regular expression (Perl style), 
by regex matching. In case a regex-like term cannot be parsed as regular
expression, it is used in normal sub-string search mode.

Note: Fancy quoting with single and double quotes might lead to unexpected problems.

### Example ###

`````
CafeOBJ> ?ap prec oper
`````
will search for all entries that contain both `prec` and `oper` as
sub-strings. Matching is done as simple sub-string match.

`````
CafeOBJ> ?ap foo att[er]
`````
will search for entries that contain the string `foo` as well as
either the string `atte` or `attr`.


## `?com [ <term> ]` ## {#help-commands}

List commands or declarations categorized by the key <term>.
<term> is one of 'decl', 'module', 'parse', 'rewrite', 
'inspect', 'switch', 'proof', 'system', 'inspect', 'library', 'help', 'io' or 'misc'.
If <term> is omitted, the list of available <term> will be printed.

## `[` ## {#sortsymbol}

Starts a sort declaration. See [sort declaration](#sort) for details.

## `accept =*= proof` switch ## {#switch-accept}

accept system's automatic proof of congruency of `=*=`

## `all axioms` switch ## {#switch-all-axioms}

Controls whether axioms from included modules are shown
during a `show` invocation.

Related: [`show`](#show)

## `always memo` switch ## {#switch-always-memo}

Turns on memorization of computation also for operators without
the [`memo`](#opattr) operator attribute.

Related: [operator attributes](#opattr), [`memo`](#switch-memo)

## `:apply (<tactic> ...) [to <goal-name>]` ## {#citp-apply}

Apply the list of tactics given within parenthesis to either
the current goal, or the goal given as `<goal-name>`.

Related: [`citp`](#citp)

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
  then the expression `{2, 4, 5}` selects the subterm `c * c * e`.

Related: [`start`](#start), [`choose`](#choose)

## `:auto` ## {#citp-auto}

Applies the following set of tactics: `(SI CA TC IP RD)`.

Related: [`citp`](#citp)

## `auto context` switch ## {#switch-auto-context}

Possible values: `on` or `off`, default is `off`.

If this switch is `on`, the context will automatically switch to
the most recent module, i.e., defining a module or inspecting 
a module's content will switch the current module.

## `autoload <module-name> <file-name>` ## {#autoload}

When evaluating a <module-name> and found that
it is not yet declared, the system read in <file-name> then 
retries the evaluation.

Related: [`no autoload`](#no-autoload)

## `ax [ <label-exp> ] <term> = <term>` . ## {#ax}

(pignose)

## `axioms { <decls> }` ## {#axioms}

Block enclosing declarations of variables, equations, and 
transitions.
Other statements are not allowed within the `axioms` block.
Optional structuring of the statements in a module.

Related: [`trans`](#trans), [`eq`](#eq), [`var`](#var), [`imports`](#imports), [`signature`](#signature)

## `:backward equation|rule` ## {#citp-backward}

Like [`:equation`](#citp-equation) and [`:rule`](#citp-rule), but exchange the left and right side.

Related: [`:rule`](#citp-rule), [`:equation`](#citp-equation), [`:cp`](#citp-cp), [`citp`](#citp)

## `bax [ <label-exp> ] <term> = <term>` . ## {#bax}

(pignose)

## `bceq [ <label-exp> ] <term> = <term> if <boolterm> .` ## {#bceq}

Defines a behavioral conditional equation. For details see [`ceq`](#ceq).

Related: [`beq`](#beq), [`ceq`](#ceq), [`eq`](#eq)

## `bcrule [ <label-exp> ] <term> => <term> if <term> .` ## {#bcrule}

Synonym of [`bctrans`](#bctrans)

Related: [`bctrans`](#bctrans)

## `bctrans [ <label-exp> ] <term> => <term> if <bool> .` ## {#bctrans}

Defines a behavioral conditional transition. 
For details see [`ctrans`](#ctrans).

Related: [`btrans`](#btrans), [`ctrans`](#ctrans), [`trans`](#trans)

## `beq [ <label-exp> ] <term> = <term> .` ## {#beq}

Defines a behavioral equation. For details see [`eq`](#eq).

Related: [`bceq`](#bceq), [`ceq`](#ceq), [`eq`](#eq)

## `bgoal <term> .` ## {#bgoal}

(pignose)

## `{bguess | :bguess} {imply|and|or} [ with <predicate name> ]` ## {#bguess}

Try to find true/false assignments which satisfies the Bool term
specified by 'binspect' or ':binspect'.

## `binspect [in <module-name> :] <boolean-term> .` ## {#binspect}

Start an inspection of a Boolean term, that is, and abstracted
form of the Boolean term is constructed. The abstracted term is shown (like calling [`bshow`](#bshow).

### Example ###


~~~~~
CafeOBJ> module BTE { [S]
  preds p1 p2 p3 p4 p5 p6 p7 : S
  ops a b c :  -> S .
}
CafeOBJ> binspect in BTE : (p1(X:S) or p2(X)) and p3(Y:S) or (p4(Y) and p1(Y)) .
...
--> ((p4(Y:S) and p1(Y)) xor ((p3(Y) and p1(X:S)) xor ((p2(X) and (p3(Y) and p1(X))) xor ((p3(Y) and p2(X)) xor ((p3(Y) and (p2(X) and (p4(Y) and p1(Y)))) xor ((p3(Y) and (p2(X) and (p1(X) and (p1(Y) and p4(Y))))) xor (p1(X) and (p3(Y) and (p1(Y) and p4(Y))))))))))
...
~~~~~

## `:binspect [in <goal-name> :] <boolean-term> .` ## {#citp-binspect}

Used during [CITP](#citp) proofs instead of [`binspect`](#binspect)

## `bop <op-spec> : <sorts> -> <sort>` ## {#bop}

Defines a behavioral operator by its domain, co-domain, and the term 
construct. `<sorts>` is a space separated list of sort names containing
*exactly* one hidden sort. `<sort>` is a single sort name.

For `<op-spec>` see the explanations of [`op`](#op).

Related: [`op`](#op)

## `bpred <op-spec> : <sorts>` ## {#bpred}

Short hand for `op <op-spec> : <sorts> -> Bool` defining a
behavioral predicate.

Related: [`pred`](#pred), [`bop`](#bop), [`op`](#op)

## `breduce [ in <mod-exp> : ] <term> .` ## {#breduce}

Reduce the given term in the given module, if `<mod-exp>` is given, 
otherwise in the current module. 

For `breduce` equations, possibly conditional, possibly behavioral, are taken
into account for reduction.

Related: [`reduce`](#reduce), [`execute`](#execute)

## `{bresolve | :bresolve} [<limit>] [all]` ## {#bresolve}

Computes all possible variable assignments that render an abstracted
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
(6) v2/v3 : combinations of true/false of two variables

### Example ###


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
~~~~~

## `brule [ <label-exp> ] <term> => <term> .` ## {#brule}

Synonym of [`btrans`](#btrans).

Related: [`btrans`](#btrans)

## `{bshow | :bshow} [{ tree | grind }]` ## {#bshow}

Shows the abstracted Boolean term computed by [`binspect`](#binspect).
If the argument `tree` is given, prints out a the abstracted term in tree form.
The variant with leading colon is for usage during a [CITP](#citp) proof.

### Example ###


~~~~~
CafeOBJ> bshow
((P-1:Bool and (P-2:Bool and (P-3:Bool and P-4:Bool))) xor ((P-1 and (P-2 and (P-4 and (P-5:Bool and P-3)))) xor ((P-2 and (P-1 and (P-5 and P-3))) xor ((P-5 and P-3) xor ((P-4 and (P-3 and P-5)) xor ((P-4 and P-3) xor (P-2 and P-1)))))))
where
  P-1:Bool |-> p4(Y:S)
  P-2:Bool |-> p1(Y:S)
  P-3:Bool |-> p3(Y:S)
  P-4:Bool |-> p1(X:S)
  P-5:Bool |-> p2(X:S)
~~~~~

## `bsort token-predicate creater printer term-predicate` ## {#bsort}

Defines a built-in sort. Internal use only.

## `btrans [ <label-exp> ] <term> => <term> .` ## {#btrans}

Defines a behavioral transition. For details see [`trans`](#trans).

Related: [`bctrans`](#bctrans), [`ctrans`](#ctrans), [`trans`](#trans)

## `cbred [ in <mod-exp> :] <term> .` ## {#cbred}

circular coinductive reduction: see
_Goguen, Lin, Rosu: Circular Coinductive Rewriting_
(Proceedings of Automated Software Engineering 2000) for details.

## `cd <dirname>` ## {#cd}

Change the current working directory, like the Unix counterpart.
The argument is necessary. No kind of expansion or substitution is done.

Related: [`ls`](#ls), [`pwd`](#pwd)

## `ceq [ <label-exp> ] <term> = <term> if <boolterm> .` ## {#ceq}

Defines a conditional equation. Spaces around the `if` are obligatory.
`<boolterm>` needs to be a Boolean term. For other requirements
see [`eq`](#eq).

Related: [`bceq`](#bceq), [`beq`](#beq), [`eq`](#eq)

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

## `check <something>` switch ## {#switch-check}

These switches turn on automatic checking of certain properties:

`check coherency`
  ~ check whether transitions and equations are coherent

`check compatibility`
  ~ see the [`check`](#check) command

`check import`
  ~ check conflicting importing mode of submodules

`check regularity`
  ~ see the [`check`](#check) command

`check sensible`
  ~ check whether a signature is sensible

## `choose <selection>` ## {#choose}

Chooses a subterm by the given `<selection>`. See [`apply`](#apply)
for details on `<selection>`.

Related: [`strat` in operator attributes](#opattr), [`start`](#start), [`apply`](#apply)

## CITP ## {#citp}

Constructor Based Induction Theorem Prover

The sub-system provides a certain level of automatization for theorem proving.

Please see the accompanying manual for CITP for details.

Related: [`:attr`](#target_not_found), [`:reset`](#citp-reset), [`:embed`](#citp-embed), [`:use`](#citp-use), [`:ord`](#citp-order), [`:imp`](#citp-imply), [`:def`](#citp-def), [`:ctf-`](#citp-ctf-), [`:ctf`](#citp-ctf), [`:csp-`](#citp-csp-), [`:csp`](#citp-csp), [`:red`](#citp-red), [`:select`](#citp-select), [`:backward`](#citp-backward), [`:rule`](#citp-rule), [`:equation`](#citp-equation), [`:cp`](#citp-cp), [`:init`](#citp-init), [`:roll`](#citp-roll), [`:auto`](#citp-auto), [`:ind`](#citp-ind), [`:apply`](#citp-apply), [`:goal`](#citp-goal)

## `clause <term> .` ## {#clause}

(pignose)

## `clean memo` ## {#cleanmemo}

Resets (clears) the memo storage of the system. Memorized computations 
are forgotten.

Related: [clean memo switch](#switch-clean-memo)

## `clean memo` switch ## {#switch-clean-memo}

Possible values: `on`, `off`, default `off`.

tells the system to be forgetful.

## `close` ## {#close}

This command closes a modification of a module started by [`open`](#open).

Related: [`open`](#open)

## `commands` ## {#comshelp}

Print outs the list of main toplevel commands.

## comments ## {#comments}

The interpreter accepts the following strings as start of a comment
that extends to the end of the line: `--`, `-->`, `**`, `**>`.

The difference in the variants with `>` is that the comment is
displayed when run through the interpreter.

Related: [`--`](#starstar), [`**`](#starstar)

## `cond limit` switch ## {#switch-cond-limit}

Setting maximal number of evaluation of condition part 
of an axiom. This is useful for detecting a kind of inifinite loop
of rewriting.

## `cont` ## {#cont}

In [step mode](#switch-step), continues the reduction until
a [stop pattern](#switch-stop-pattern) has been found.

## `:cp { "[" <label> "]" | "(" <sentence> . ")" } >< { "[" <label> "]" | "(" <sentence> .")" }` ## {#citp-cp}

Computes the critical pair of the two given equations.
Here either a label or a full equation can be used to specify the equations.

Related: [`citp`](#citp)

### Example ###


~~~~~
:cp (ceq top(sq(S@Sys)) = I@Pid if pc(S@Sys,I@Pid) = cs .)
><
(ceq top(sq(S@Sys)) = J@Pid if pc(S@Sys,J@Pid) = cs .)
~~~~~

## `crule [ <label-exp> ] <term> => <term> if <term> .` ## {#crule}

Synonym of [`ctrans`](#ctrans)

Related: [`rule`](#rule), [`ctrans`](#ctrans)

## `:csp { eq [ <label-exp>] <term> = <term> . ...}` ## {#citp-csp}

Applies case splitting after a set of equations. Each of these
equations creates one new sub-goal with the equation added.

The system does not check whether given set of equations exhausts all 
possible values.

Not discharged sub-goals will remain in the reduced form.

Related: [`:csp-`](#citp-csp-), [`citp`](#citp)

## `:csp- { eq [ <label-exp>] <term> = <term> . ...}` ## {#citp-csp-}

Like [`:csp`](#citp-csp), but if sub-goals are not discharged, the
CITP prover returns to the original state before the reduce action.

Related: [`:csp`](#citp-csp), [`citp`](#citp)

## `:ctf { eq [ <label-exp> ] <term> = <term> .}` ## {#citp-ctf}

Applies case splitting after a set of boolean expressions.
Not discharged sub-goals will remain in the reduced form.

Related: [`:ctf-`](#citp-ctf-), [`citp`](#citp)

## `:ctf- { eq [ <label-exp> ] <term> = <term> .}` ## {#citp-ctf-}

Like [`:ctf`](#citp-ctf), but if sub-goals are not discharged, the
CITP prover returns to the original state before the reduce action.

Related: [`:ctf`](#citp-ctf), [`citp`](#citp)

## `ctrans [ <label-exp> ] <term> => <term> if <term> .` ## {#ctrans}

Defines a conditional transition. For details see [`trans`](#trans)
and [`ceq`](#ceq).

Related: [`bctrans`](#bctrans), [`btrans`](#btrans), [`trans`](#trans)

## `db reset` ## {#db}

(pignose)

## `:def <symbol> = { <ctf> | <csp> | <init> }` ## {#citp-def}

Assigns a name to a specific case splitting (`:ctf` or `:csp`)
 or induction `:ind`),
so that it can be used as tactics in `:apply`.

Related: [`citp`](#citp)

### Example ###

~~~~~
:def name-0 = :ind { :on (<Variable>...) :base <Term> . :step <Term> . }
:def name-1 = :ctf [ <Term> . ]
:def name-2 = :ctf-{ eq LHS = RHS . }
:def name-3 = :csp { eq lhs1 = rhs1 . eq lhs2 = rhs2 . }
:def name-4 = :csp-{ eq lhs3 = rhs3 . eq lhs4 = rhs4 . }
:apply(name-0 TC name-1 name-2 name-3 name-4)
~~~~~

## `demod` ## {#demod}

(pignose)

## `:describe proof` ## {#citp-describe}

Describes the current proof in more detail.

Related: [`:show`](#citp-show), [`citp`](#citp)

### Example ###


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
~~~~~

## `describe <something>` ## {#describe}

Similar to the `show` command but with more details. Call `describe ?` for
the possible set of invocations.

Related: [`show`](#show)

## `dirs` ## {#dirs}

Displays the current push stack.

Related: [`popd`](#popd), [`pwd`](#pwd), [`pushd`](#pushd), [`cd`](#cd), [`ls`](#ls)

## `dribble { <file-name> | .}` ## {#dribble}

If <file-name> is give, the evaluation process of the system is
output to the <file-name> in internal form. '.' stops the recording. 
Only usefule for developer of the system.

## `:embed (<label> ... <label>) as <module_name>` ## {#citp-embed}

Incorporate proved goals into the module specified by <module_name>
which will import the current proof context module.

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
the same term with `or` instead.

Related: [`bceq`](#bceq), [`beq`](#beq), [`ceq`](#ceq)

## `:equation` ## {#citp-equation}

Adds the critical pair computed by the last [`:cp`](#citp-cp) command
as equation to the current goal.

Related: [`:rule`](#citp-rule), [`:cp`](#citp-cp), [`citp`](#citp)

## `esc return` ## {#help}

There would be a situation that you hit return expecting some 
feed-back from the interpreter, but it does not respond.
When this happen, try type in esc(escape key) and return, 
it will immediately be back to you discarding preceding input 
and makes a fresh start.

## `exec limit` switch ## {#switch-exec-limit}

Possible values: integers, default limit 4611686018427387903.

Controls the number of maximal transition steps.

Related: [`reduce`](#reduce)

## `exec trace` switch ## {#switch-exec-trace}

Possible values: `on` `off, default `off`.

controls whether further output is provided during reductions.

Related: [`reduce`](#reduce)

## `exec! [ in <mod-exp> : ] <term> .` ## {#execute-dash}

Obsolete command. Implicitly invokes RWL search predicate in a 
specific manner. 

## `execute [ in <mod-exp> : ] <term> .` ## {#execute}

Reduce the given term in the given module, if `<mod-exp>` is given, 
otherwise in the current module. 

For `execute` equations and transitions, possibly conditional, are taken
into account for reduction.

Related: [`reduce`](#reduce), [`breduce`](#breduce)

## `extending ( <modexp> )` ## {#extending}

Imports the object specified by `modexp` into the current
module, allowing models to be inflated, but not collapsing. 
See [`module expression`](#moduleexpression) for format of `modexp`.

Related: [`using`](#using), [`protecting`](#protecting), [`including`](#including)

## `find {+rule | -rule}` ## {#find}

Find all axioms which possibly rewrite the current term.

## `find all rules` switch ## {#switch-find-all-rules}

If this switch is on, the [`apply`](#apply) command
will search for applicable rules not only in the set of
user-defined equations, but also in those added by the system.

## `flag(<name>, { on | off })` ## {#flag}

(pignose)

## `full reset` ## {#fullreset}

Reinitializes the internal state of the system. All supplied modules
definitions are lost.

Related: [`prelude`](#prelude), [`reset`](#reset)

## `gendoc <pathname>` ## {#gendoc}

generates reference manual from system's on line help documents, 
and save it to `pathname`.

## `:goal { <sentence> . ... }` ## {#citp-goal}

Define the initial goal for CITP

Related: [`citp`](#citp)

### Example ###


~~~~~
CafeOBJ> select PNAT .
PNAT> :goal { 
   eq [lemma-1]: M:PNat + 0 = M . 
   eq [lemma-2]: M:PNat + s N:PNat = s( M + N ) . 
}
~~~~~

## `goal <term> .` ## {#goal}

(pignose)

## `:imp "[" <label> "]" by "{" <variable> <- <term>; ..."}"` ## {#citp-imply}

TODO (future extension)

Related: [`citp`](#citp)

## `imports { <import-decl> }` ## {#imports}

Block enclosing import of other modules (`protecting` etc). 
Other statements are not allowed within the `imports` block.
Optional structuring of the statements in a module.

Related: [`using`](#using), [`protecting`](#protecting), [`including`](#including), [`extending`](#extending), [`axioms`](#axioms), [`signature`](#signature)

## `include BOOL` switch ## {#switch-include-bool}

Possible values: `on` `off`, default `on`.

By default a couple of built-in modules are implicitly imported with
protecting mode. In particular, BOOL is of practical importance. It
defines Boolean operators. It is imported to admit conditional
axioms.

This switch allows to disable automatic inclusion of BOOL.

## `include RWL` switch ## {#switch-include-rwl}

Possible values: `on` `off`, default `off`.

This switch allows to disable automatic inclusion of RWL.

## `including ( <modexp> )` ## {#including}

Imports the object specified by `modexp` into the current
module. 

See [`module expression`](#moduleexpression) for format of `modexp`.

Related: [module expression](#moduleexpression), [`using`](#using), [`protecting`](#protecting), [`extending`](#extending)

## `:ind { on (<variable> ...) | 
'{' on (<variable> ...) 
    base (<Term> . ... <Term> .)
    step (<Term> . ... <Term> .)
'}'` ## {#citp-ind}

':ind on (<variable> ...)' defines the variable for the induction tactic of CITP.
':ind { ... }' defines induction variable(s) and base pattern and step pattern specified by <Term>s.

Related: [`citp`](#citp)

### Example ###


~~~~~
:ind on (M:PNat)
:ind { on (M:PNat) 
       base (<Term> . ... <Term> .) 
       step (<Term> . ... <Term> .)
     }
~~~~~

## `init [as <name>] { "[" <label> "]" | "(" <sentence> "")} by "{" <variable> <- <term>; ... "}"` ## {#init}

Instantiates an equation specified by `<label>` by replacing the `<variable>`s 
in the equation with the respective `<term>`s. The resulting equation is added
to the set of axioms.
If optional `as <name>` is given, label of the instantiated axiom is overwritten by <name>.

Related: [`open`](#open)

## `:init [as <name>] { "[" <label> "]" | "(" <sentence> "")} by "{" <variable> <- <term>; ... "}"` ## {#citp-init}

Instantiates an equation specified by `<label>` by replacing the `<variable>`s 
in the equation with the respective `<term>`s. The resulting equation is added
to the set of axioms.
If optional `as <name>` is given, label of the instantiated axiom is overwritten by <name>.

Related: [`citp`](#citp)

## `input <pathname>` ## {#input}

Requests the system to read the file specified by the
pathname. The file itself may contain `input` commands.
CafeOBJ reads the file up to the end, or until it encounters
a line that only contains (the literal) `eof`.

## `inspect <term>` ## {#inspect}

Inspect the internal structure of `<term>`.

## instantiation of parameterized modules ## {#instantiation}

Parameterized modules allow for instantiation. The process of
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
~~~~~

## `:is` ## {#citp-is}

Boolean expression: `A :is B` where `A` is a term and
`B` is a sort. Returns true if `A` is of sort `B`.

## `let <identifier> = <term> .` ## {#let}

Using `let` one can define aliases, or context variables. Bindings
are local to the current module. Variable defined with `let` can be
used in various commands like `reduce` and `parse`. 

Although `let` defined variable behave very similar to syntactic
shorthands, they are not. The right hand side `<term>` needs to
be a fully parsable expression.

## `lex (<op>, ..., <op>)` ## {#lex}

(pignose)

## `libpath` switch ## {#switch-libpath}

Possible values: list of strings.

The switch `libpath` contains a list of directories where CafeOBJ
searches for include files. Addition and removal of directories can be
done with

`````
set libpath + <path1>:<path2>:...
set libpath - <path1>:<path2>:...
`````

or the full libpath reset by `set libpath <path1>:<path2>:...`

The current directory has a privileged status: It is always searched
first and cannot be suppressed.

## `lisp` ## {#lisp}

Evaluates the following lisp expression.

### Example ###

`````
CafeOBJ> lisp (+ 4 5)
(+ 4 5) -> 9
`````

## `lispq` ## {#lispq}

Evaluates the following lisp expression, but does not
display the result (q for quiet).

## `list { axiom | sos | usable | flag | param | option | demod }` ## {#list}

(pignose)

## `look up <something>` ## {#lookup}

displays the location (module) and further information
where `<something>` has been defined.

### Example ###

~~~~~
open INT .
%INT> look up Nat .

Nat
  - sort declared in NAT-VALUE
  - operator:
    op Nat : -> SortId { constr prec: 0 }
    -- declared in module NAT-VALUE

%INT>
~~~~~

## `ls <pathname>` ## {#ls}

lists the given `pathname`. Argument is obligatory.

Related: [`pwd`](#pwd), [`cd`](#cd)

## `make <mod_name> ( <mod_exp> )` ## {#make}

This commands defines a new module `<mod_name>` by evaluating the
module expression `<mod_exp>`.

Related: [`module expression`](#moduleexpression)

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

## `memo` switch ## {#switch-memo}

controls the memorization of computations. The system memorizes 
evaluations of operators declared with the [`memo`](#opattr) operator
attribute. Turning this switch off disables all memorization.

## `[sys:]module[!|*] <modname> [ ( <params> ) ] [ <principal_sort_spec> ] { mod_elements ... }` ## {#module}

Defines a module, the basic building block of CafeOBJ. Possible elements
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
single-sort modules as the sort mapping needs not be given.

## `module expression` ## {#moduleexpression}

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
    is often used in combination with [instantiation](#instantiation).

summation
  ~ `<mod_exp> + <mod_exp>`

    This expression describes a module consisting of all the module
    elements of the summands. If a submodule is imported more than
    once, it is assumed to be shared.

## `names <mod-exp>` . ## {#names}

List up all the named objects in module <mod-exp>.

## `no autoload <module-name>` ## {#no-autoload}

Stop `autoload` of module with the name <module-name> .
Please refer to `autoload` command.

Related: [`autoload`](#autoload)

## `:normalize { on | off}` ## {#citp-normalize}

Normalize the LHS of an instance of the axiom generated by :init command.

Related: [`citp`](#citp)

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
`<name>` is a constant name as in ``a:Nat`. Using this construct is
similar to defining an operator

`op <name> : -> <sort>`

or in the above example, `op a : -> Nat .`, besides that the
on-the-fly declaration of constants, like to one of variables, is only
valid in the current context (i.e., term or axiom). These constant
definitions are quite common in proof scores.

Related: [`var`](#var)

## `op <op-spec> : <sorts> -> <sort> { <attribute-list> }` ## {#op}

Defines an operator by its domain, co-domain, and the term construct.
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
[operator attributes](#opattr).

## `open <mod_exp> .` ## {#open}

This command opens the module specified by the module expression
`<mod_exp>` and allows for declaration of new sorts, operators, etc.

Related: [`select`](#select), [`module expression`](#moduleexpression), [`close`](#close)

## `operator attributes` ## {#opattr}

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

  - A single underbar cannot be an operator name.

Related: [`bop`](#bop)

## `operator precedence` ## {#opprec}

CafeOBJ allows for complete freedom of syntax, in particular infix
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
  receive precedence 0.

Related: [operator attributes](#opattr)

## `option { reset | = <name> }` ## {#option}

(pignose)

## `:order (<op>, ..., <op>)` ## {#citp-order}



## `param(<name>, <value>)` ## {#param}

(pignose)

## `parameterized module` ## {#parameterizedmodule}

A module with a parameter list (see `module`) is a parameterized module.
Parameters are given as a comma (`,`) separated list. Each parameter is
of the form `[ <import_mode> ] <param_name> :: <module_name>` 
(spaces around `::` are obligatory).

The parameter's module gives minimal requirements on the module
instantiation.

Within the module declaration sorts and operators of the parameter
are qualified with `.<parameter_name>` as seen in the example below.

Related: [qualified sort](#qualifiedother)

### Example ###

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

## `parse [ in <mod-exp> : ] <term> .` ## {#parse}

Tries to parse the given term within the module specified by
the module expression `<mod-exp>`, or the current module if not given,
and returns the parsed and qualified term.

In case of ambiguous terms, i.e., different possible parse trees, the
command will prompt for one of the trees.

Related: [`qualified term`](#qualified)

## `parse normalize` switch ## {#switch-parse-normalize}

If this switch is 'on' (defalult is 'off'), terms with
associative operators are always parsed as right associative.

## `popd` ## {#popd}

Changes the current working directory to the last on on the push stack.

Related: [`dirs`](#dirs), [`pwd`](#pwd), [`pushd`](#pushd), [`cd`](#cd), [`ls`](#ls)

## `pred <op-spec> : <sorts>` ## {#pred}

Short hand for `op <op-spec> : <sorts> -> Bool` defining a predicate.

Related: [`bpred`](#bpred), [`op`](#op)

## `prelude <file>` ## {#prelude}

Loads the given `<file>` as prelude. That is, a call to
[`reset`](#reset) will reset the definitions made in this file.

Related: [`full reset`](#fullreset), [`reset`](#reset)

## `print depth` switch ## {#switch-print-depth}

Possible values: natural numbers, default `unlimited`.

Controls to which depth terms are printed.

## `print mode` switch ## {#switch-print-mode}

Possible values: `normal` `fancy` `tree` `s-expr`

Selects one of the print modes.

## `print trs` switch ## {#switch-print-trs}

Possible values: `on` `off`, default `off`

If set to `on`, print the rules used during reduction of 
`=(_,_)=>+_if_suchThat_{_}`.

Related: [`search predicates`](#searchpredicate)

## `protect <module-name>` ## {#protect}

Protect a module from being overwritten.
Some modules vital for the system are initially protected.
Can be reversed with `unprotect`.

Related: [`unprotect`](#unprotect)

## `protecting ( <modexp> )` ## {#protecting}

Imports the object specified by `modexp` into the current
module, preserving all intended models as they are. 
See [`module expression`](#moduleexpression) for format of `modexp`.

Related: [`including`](#including), [`using`](#using), [`extending`](#extending)

## `provide <feature>` ## {#provide}

Discharges a feature requirement: once `provide`d, all the subsequent
`require`ments of a feature are assumed to have been fulfilled
already.

Related: [`require`](#require)

## `pushd <directory>` ## {#pushd}

Changes the working directory to `<directory>`, and puts the
current directory onto the push stack. Going back can be done with `pop`.

Related: [`dirs`](#dirs), [`pwd`](#pwd), [`popd`](#popd), [`cd`](#cd), [`ls`](#ls)

## `pvar <var-name> : <sort-name>` ## {#pvar}

(pignose)

Related: [`vars`](#var), [`var`](#var)

## `pwd` ## {#pwd}

Prints the current working directory.

Related: [`dirs`](#dirs), [`popd`](#popd), [`pushd`](#pushd), [`ls`](#ls), [`cd`](#cd)

## qualified sort/operator/parameter ## {#qualifiedother}

CafeOBJ allows for using the same name for different sorts,
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

Related: [`qualified term`](#qualified), [`parameterized module`](#parameterizedmodule)

## `qualified term` ## {#qualified}

In case that a term can be parsed into different sort, it is possible to
qualify the term to one of the possible sorts by affixing it with 
`: <sort-name>` (spaces before and after the `:` are optional).

Related: [`parse`](#parse)

### Example ###

`(1):NzNat` `(2):Nat`

## `quiet` switch ## {#switch-quiet}

Possible values: `on` `off`, default `off`

If set to `on`, the system only issues error messages.

Related: [`verbose`](#switch-verbose)

## `quit` ## {#quit}

Leaves the CafeOBJ interpreter.

## `{ :red | :exec | :bred } [in <goal-name> :] <term> .` ## {#citp-red}

reduce the term in specified goal <goal-name>.

Related: [`citp`](#citp)

## `reduce [ in <mod-exp> : ] <term> .` ## {#reduce}

Reduce the given term in the given module, if `<mod-exp>` is given, 
otherwise in the current module. 

For `reduce` only equations and conditional equations are taken into
account for reduction.

Related: [`breduce`](#breduce), [`execute`](#execute)

## `reduce conditions` switch ## {#switch-reduce-conditions}

Possible values: `on` `off`, default `off`.

When using [`apply`](#apply) to step through a reduction, this switch
allows to turn on automatic reduction of conditions in conditional
equations. 

Related: [`apply`](#apply)

## `regularize <mod-name>` ## {#regularize}

Regularizes the signature of the given module, ensuring that every
term has exactly one minimal parse tree. In this process additional
sorts are generated to ensure unique least sort of all terms.

Modules can be automatically regularized by the interpreter if the
`regularize signature` switch is turn to `on`.

## `regularize signature` switch ## {#switch-regularize-signature}

See [`regularize](#regularize)

## `require <feature> [ <pathname> ]` ## {#require}

Requires a feature, which usually
denotes a set of module definitions. Given this command, the
system searches for a file named the feature, and read the file
if found. If the `<feature>` contains `::`, they are treated as
path separators.

If a pathname is given, the system searches for a file
named the pathname instead.


Related: [`provide`](#provide)

### Example ###


~~~~~
CafeOBJ> require foo::bar
~~~~~
would search for `foo/bar.cafe` in the pathes from `libpath`

## `:reset` ## {#citp-reset}

Discard the current proof session.

## `reset` ## {#reset}

Restores the definitions of built-in modules and preludes,  but does not
affect other modules.

Related: [`prelude`](#prelude), [`full reset`](#fullreset)

## `resolve {. | <file-path> }` ## {#resolve}

(pignose)

## `restore <pathname>` ## {#restore}

Restores module definitions from the designated file `pathname` which 
has been saved with the `save` command. `input` can also be used but
the effects might be different.

TODO -- should we keep the different effects? What is the real difference?


Related: [`save-system`](#target_not_found), [`save`](#save), [`input`](#input)

## `rewrite limit` switch ## {#switch-rewrite}

Possible values: positive integers, default not specified.

Allows limiting the number of rewrite steps during a step-wise
execution.

Related: [`step switch`](#switch-step)

## `:roll back` ## {#citp-roll}

Reverts the strategy that led to the current target goal.
The current target goal is removed from the proof tree.

Related: [`citp`](#citp)

## `:rule` ## {#citp-rule}

Adds the critical pair computed by the last [`:cp`](#citp-cp) command
as rule to the current goal.

Related: [`:equation`](#citp-equation), [`:cp`](#citp-cp), [`citp`](#citp)

## `rule [ <label-exp> ] <term> => <term> .` ## {#rule}

Synonym of [`trans`](#trans).

Related: [`trans`](#trans)

## `save <pathname>` ## {#save}

Saves module definitions into the designated file `pathname`.
File names should be suffixed with `.bin`. 

`save` also saves the contents of prelude files as well as module definitions
given in the current session.


Related: [`save-system`](#target_not_found), [`restore`](#restore), [`input`](#input)

## `save-option <name>` ## {#save-option}

(pignose)

## `scase (<term>) in (<mod-exp>) as <name> { <decl> ..} : <term> .` ## {#scase}

Obsolete citp command. Split the goal by user specified cases.

## `search predicates` ## {#searchpredicate}

CafeOBJ provides a whole set of search predicates, that searches
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

`S =(n,m)=>* SS [if Pred1] suchThat Pred2 withStateEq Pred3`

## `:select <goal-name>` ## {#citp-select}

Select a goal for further application of tactics.

Related: [`citp`](#citp)

## `select <mod_exp> . ` ## {#select}

Selects a module given by the module expression `<mod_exp>` as the
current module. All further operations are carried out within the
given module. In contrast to `open` this does not allow for
modification of the module, e.g., addition of new sorts etc.

Related: [`module expression`](#moduleexpression), [`open`](#open)

## `:set(<name>, { on | off | show })` ## {#citp-set}

Set or show various flags of CITP CafeOBJ.

Related: [`citp`](#citp)

## `set <name> [option] <value>` ## {#set}

Depending on the type of the switch, options and value specification varies.
Possible value types for switches are Boolean (`on`, `off`), string (`"value"`),
integers (5434443), lists (lisp syntax).

For a list of all available switches, use `set ?`. To see the current
values, use `show switches`. To single out two general purpose switches,
`verbose` and `quiet` tell the system to behave in the respective way.

Related: [`switches`](#switches), [`show`](#show)

## `:show goal|unproved|proof|discharged` ## {#citp-show}

Shows the current goal, the up-to-now unproven (sub-)goals, and the current proof.

Related: [`:describe`](#citp-describe), [`citp`](#citp)

### Example ###


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
~~~~~

## `show <something>` ## {#show}

The `show` command provides various ways to inspect all kind of objects
of the CafeOBJ language. For a full list call `show ?`.

Some of the more important (but far from complete list) ways to call
the `show` command are:

  - `show [ <modexp> ]` - describes the current modules of the one specified
        as argument
  - `show module tree [ <modexp> ]` - displays submodules of <modexp> in tree format
  - `show switches` - lists all possible switches
  - `show term [ tree ]` - displays a term, possible in tree format

See the entry for [`switches`](#switches) for a full list.

Related: [`describe`](#describe), [`switches`](#switches)

## `show mode` switch ## {#switch-show-mode}

Possible values for `set show mode <mode>` are `cafeobj` and `meta`.

## `sigmatch (<mod-exp>) to (<mod-exp>)` ## {#sigmatch}

(pignose)

## `signature { <sig-decl> }` ## {#signature}

Block enclosing declarations of sorts and operators.
Other statements are not allowed within the `signature` block.
Optional structuring of the statements in a module.

Related: [`op`](#op), [`sort`](#sort), [`imports`](#imports), [`axioms`](#axioms)

## sort declaration ## {#sort}

CafeOBJ supports two kind of sorts, visible and hidden sorts. Visible 
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
relation between each pair or left and right sorts.

### Example ###

~~~~
  [ A B , C D < A < E, B < D ]
~~~~

defines five sorts `A`,...,`E`, with the following relations:
`C < A`, `D < A`, `A < E`, `B < D`.

## `sos { = | + | - } { <clause> , ... }` ## {#sos}

(pignose)

## `:spoiler { on | off}` ## {#citp-spoiler}

If the spoiler flag is on, after a strategy other than RD and SI
has been applied, the generated sub-goals are automatically checked for
provability using the RD strategy. Defaults to `off`.

Related: [`citp`](#citp)

## `start <term> .` ## {#start}

Sets the focus onto the given term `<term>` of the currently opened
module or context. Commands like `apply`, `choose`, or `match` will
then operate on this term.

Related: [`match`](#match), [`choose`](#choose), [`apply`](#apply)

## `statistics` switch ## {#switch-statistics}

Possible values: `on` `off`, default `on`.

After each reduction details about the reduction are
shown. Information shown are the time for parsing the expression, the
number of rewrites and run time during rewriting, and the number of
total matches performed during the reduce.

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

Other standard CafeOBJ commands that can be used are [`show`](#show),
[`describe`](#describe), [`dirs`](#dirs), [`set`](#set), [`cd`](#cd), 
[`ls`](#ls), [`pwd`](#pwd), [`pushd`](#pushd), [`popd`](#popd), 
[`lisp`](#lisp), [`lispq`](#lisp), and (on Unix only)
[`!`](#commandexec).

## `stop` ## {#stop}

Equivalent to [`stop pattern switch`](#switch-stop-pattern)

## `stop pattern` switch ## {#switch-stop-pattern}

In [step mode](#switch-step), this command causes reductions to stop when the reductants get to
containing subterms that match the given term. If no term is given,
this restriction is lifted.

Related: [`step switch`](#switch-step)

### Example ###


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
~~~~~

## switches ## {#switches}

Switches control various aspects of the computations and behavior
of CafeOBJ. The current list of switches and their values can be
shown with 

`````
show switches
`````

The single switches are described separately in this manual.

Related: [`show`](#show), [`set`](#set)

## `:theory <op_name> : <arity> -> <coarity> { assoc | comm | id: <term> }` ## {#citp-theory}

Adds operator theory 'associativity', 'commutativity', and/or 'identity' to 
an operator specfied by '<op_name> : <arity> -> <coarity> .

## `trace [whole]` switch ## {#switch-trace}

During evaluation, it is sometimes desirable to see the rewrite
sequences, not just the results. Setting the switch `trace whole` will
result in the resultant term of each rewrite step being
printed. Setting the switch `trace` will result in the display of
which rule, substitution, and replacement are used.

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

## `unprotect <module-name>` ## {#unprotect}

Remove overwrite protection from a module that has been protected
with the `protect` call. Some modules vital for the system
are initially protected.

Related: [`protect`](#protect)

## `:use (<label> ... <label>)` ## {#citp-use}

Incorporate discharged goal sentences as new axioms.

## `using ( <modexp> )` ## {#using}

Imports the object specified by `modexp` into the current
module without any restrictions on the models.
See [`module expression`](#moduleexpression) for format of `modexp`.

Related: [`protecting`](#protecting), [`including`](#including), [`extending`](#extending)

## `var <var-name> : <sort-name>` ## {#var}

Declares a variable `<var-name>` to be of sort `<sort-name>`.
The scope of the variable is the current module.
Redeclarations of variable names are not allowed.
Several variable of the same sort can be declared at the same time
using the `vars` construct:

`vars <var-name> ... : <sort-name>`

Related: [`on-the-fly`](#onthefly), [`qualified term`](#qualified), [`op`](#op)

## `:verbose { on | off }` ## {#citp-verbose}

Turns on verbose reporting of the CITP subsystem.

Related: [`citp`](#citp)

## `verbose` switch ## {#switch-verbose}

Possible values: `on` `off`, default `off`.

If turn `on`, the system is much more verbose in many commands.

Related: [`quiet switch`](#switch-quiet)

## `version` ## {#version}

Prints out the version of CafeOBJ.

## `view <name> from <modname> to <modname> { <viewelems> }` ## {#view}

A view specifies ways to bind actual parameters to formal parameters
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


### Example ###

Assume a module `MONOID` with sort `M` and ops `e` and `*`
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

