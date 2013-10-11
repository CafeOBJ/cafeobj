% CafeOBJ Reference Manual
% Ataru T. Nakagawa, Toshimi Sawada, Kokichi Futatsugi, Norbert Preining

\include{macros.gpp}

Introduction
============

(present a module (idea: stripped down version of the bank-account.mod)
which contains most important and often used constructs
describe the fundamental concepts of \_cafeobj 
(algebraic spec, order sort, model spec, ...)
also contains a quick intro to interaction [Ch 1] but much shorter)

\_cafeobj as TRS specification system, background, algebraic specification
based on equational theory. 

Overview of the system
======================

alternative title: Main concepts (?)

discuss the following topics in bit more details (parts of the
current manual, stripped down)

- sorts [Ch 3]
- operators [Ch 4, Ch 7]
- module [Ch 2, Ch 8]

do not contain the syntactic definition in all the details,
but explain these important items in more detail

Sorts
-----

use [Ch 3]

### Normal sorts ###

~~~
[ NzNat Zero < Nat ]
~~~

### Hidden sorts ###

Not to be included in the introduction

~~~
*[ Foo ]*
~~~

Term structure
--------------

use [Ch 4 and 7]

### Variable declarations ###

== vars M N : Nat ==

== N:Nat ==

### Records ###

~~~~
Record {
  ...
}
~~~~

### Operators ###

~~~
op 0 : -> Zero
op s_ : Nat -> NzNat
op _+_ : Nat Nat -> Nat
~~~

Rewriting - Equations
---------------------

### Equations ###

~~~
eq N:Nat + 0 = N .
eq N:Nat + s(M:Nat) = s(N + M) .
~~~

### Transitions ###

~~~
trans ...
~~~

Glueing it together - modules
-----------------------------

use [Ch 2 and 8]

~~~
module {
  ...sort definitions...
  ...operators...
  ...axioms and transitions...
}
~~~

### Views/Parametrization ###


The full module
---------------
~~~ {#mycode .cafeobj .numberLines startFrom="10"}
mod! SIMPLE-NAT {
  [ NzNat Zero < Nat ]
  op 0 : -> Zero
  op s_ : Nat -> NzNat
  op _+_ : Nat Nat -> Nat {comm}
  
  eq N:Nat + s(M:Nat) = s(N + M) .
  eq N:Nat + 0 = N . 
}
~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~

Gory Details {#gorydetails}
============

starting with the BNF definition of [Ch 12], go through
alphabetic list of syntax elements (care has to be taken for
infix ops etc) with explanations, taken from and adapted from
the current manual. Combining similar items. 
Full syntactic definition and semantics
(extraction/unification for the current manual):

list as in the attached pdf (extraction of current manual), but
merging following items (at least) (numbers also refer to the
Syntax elements in the current manual)

  - done 12,13
  - done 14,15
  - done 17,23,24,61,64-69 parts of module expressin todo
  - done 26-28
  - 29-31
  - 32,33
  - 39,40
  - 42,43
  - 44,46,47
  - 49,50

From the currently not treated chapters we would

- [Ch 5,6] -> part of the "part 3" (inspecting, evaluating, ...)
- [Ch 9,10]-> merged into either "part 2" or appendix on proving
- [Ch 11] -> part of the "part 3"

### `?` ### {#help}

lists all top-level commands. The `?` can be used after many of the
top-level commands to obtain help.

### `cd <dirname>` ### {#cd}

Change the current working directory, like the Unix counterpart.
The argument is necessary. No kind of expansion or substitution is done.

Related: [`pwd`](#pwd) [`ls`](#ls)

### `describe <something>` ### {#describe}

like the `show` command with more details. See `describe ?` for
the possible set of invocations.

Related: [`show`](#show)

### `eof` ### {#eof}

Terminates reading of the current file. Allows for keeping
untested code or documentations below the `eof` mark. Has
to be on a line by itself without leading spaces.

### `extending ( <modexp> )` ### {#extending}

Alias: `ex`

imports the object specified by `modexp` into the current
module, allowing models to be inflated, but not collapsing. 
See `module expression` for format of `modexp`.

Related: [`including`](#including) [`protecting`](#protecting) 
	 [`using`](#using)

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

### `using ( <modexp> )` ### {#using}

Alias: `us`

imports the object specified by `modexp` into the current
module without any restrictions on the models.
See `module expression` for format of `modexp`.

Related: [`extending`](#extending) [`including`](#including) 
	 [`protecting`](#protecting)



Testing
=======

Macros
------
Usage of macros in the code can be used like `\_cafeobj` and produces
\_cafeobj, depending on the definitions in `latex.gpp` and `html.gpp`.

References
----------
References are used like `@osa` this and produces this: @osa, so it
is better used in brackets [@osa-survey, p.23] or similar.

`biblatex` and `biber` is needed.

Definition lists
----------------

Order-sorted logic
  : [@osa]
    A sort may be a subset of another sort...

Rewriting logic
  : [@rew-logic]
	In addition to equality, which is subject to the law of symmetry, ...

and so on and so on

Literal blocks
--------------

A literal block, we could use it for syntax definitions or
so?

>  input command
>     input pathnam

Block quotes are quoted elements

>  Never give up, never surrender!
>
>  -- Someone in a funny movie

Here now comes a transition, something we normally don't use in
LaTeX as it is an evil thing:

-------

And here we continue after the transition

Option lists are very special, they are funny program like
stuff ahdnling a lot of cases:

~~~
  -a           a nice option
  -b arg       another option
  --long       long options supported
  --very-long-options-are-still-supported
               but how will it look?
               I don't know
~~~

Another funny thing are those quoted literal blocls

> hello world
> what is going on
> lets have a cup of thee

A completely different thing are those things called ``admonition``
which are really funny

.. note:: This is a note admonition
   It can continue for a long time

   - and even contain
   - bullet lists

Now we are back at writting normally


