Testing
=======

Macros
------
Usage of macros in the code can be used like `CafeOBJ` and produces
CafeOBJ, depending on the definitions in `latex.gpp` and `html.gpp`.

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

