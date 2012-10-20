** -*- Mode:CafeOBJ -*-
--
-- TINY-IPL ==========================================================
-- A definition of a very simple imperative programming language.
-- The language has only one built-in type `nat' (natural number).
-- The literal value is represented by 0 (for zero), and application 
-- forms of successor function (s(0) for 1 and so on).
-- PROGRAM: a program is a sequence of statement connected by ','
--          ( st1, st2, ...)
-- STATEMENT: a statement is either 
--  - assignment : "var := expr",
--  - conditional : "if(expr, program, program)" or
--  - loop : "while expr { program }"
-- where, 
-- var : variable, written like v(N), N is a value of nat.
-- expr: expression. there are four types of expressions
--     (1) le : less than or equal to
--     (2) if : conditional
--     (3) inc : increment a value by one
-- Truth values are represented by values of type nat:
--  0         : false
--  otherwise : true
-- ==================================================================

** module TINY-IPL-SYNTAX defines the syntax of the language
-- to be defined.
-- 
module! TINY-IPL-SYNTAX
{
  ** The syntax of the language -------------------------
  ** 
  -- sorts for program constructs.
  [ nat var < expr, 
    assignment conditional loop < statement < program ]

  -- expressions ---------------------------------------
  -- natural number
  op 0 : -> nat
  op s : nat -> nat
  -- variable form
  op v : nat -> var
  -- le : less than or equal.
  op le : expr expr -> expr { prec: 10 }
  -- increment a value by one.
  op inc : expr -> expr { prec: 8 }
  -- statements ----------------------------------------
  -- assignment
  op (_:=_) : var expr -> assignment { prec: 20 }
  -- conditional
  op if : expr program program -> conditional { prec: 20 }
  -- loop
  op while_{_} : expr program -> loop { prec: 20 }
  -- program -------------------------------------------
  op _,_ : program program -> program { r-assoc prec: 30 }
}

module! TINY-IPL {
  protecting (TINY-IPL-SYNTAX)
  ** The semantics of the language TINY-IPL :
  ** 
  ** 
  -- env : represents variable binding (environment).
  [ env ]
  op empty : -> env
  op env : var nat env -> env
  op update : env var nat -> env

  -- supporting function
  op _<=_ : nat nat -> Bool
  eq 0 <= N:nat = true .
  eq s(N:nat) <= 0 = false .
  eq s(N:nat) <= s(N':nat) = N <= N' .

  ** evaluators
  -- program
  op evalp : program env -> env
  -- expression
  op evale : expr env -> nat

  eq [assignment]: evalp((X:var := E:expr), C:env) 
     = update(C,X,evale(E,C)) .
  eq [if]: evalp((if(E:expr, P:program, P':program)), C:env)
     = if evale(E,C) == 0 then evalp(P',C)
       else evalp(P,C) fi .
  eq [while]: evalp((while E:expr { P:program }), C:env)
     = if evale(E,C) == s(0)
       then evalp((P , while E { P }), C) 
       else C fi .
  eq [program]: evalp((S:statement, P:program), C:env)
     = evalp(P, evalp(S,C)) .

  eq [value]: evale(N:nat, C:env) = N .
  eq [variable]: evale(V:var, env(V':var,N:nat,C:env))
     = if V == V' then N
       else evale(V,C) fi .
  eq [le]: evale(le(E:expr,E':expr), C:env) 
     = if evale(E,C) <= evale(E',C) then s(0)
       else 0 fi .
  eq [inc]: evale(inc(E:expr), C:env) = s(evale(E,C)) .

  -- update environment.
  eq update(empty, V:var, N:nat) = env(V,N,empty) .
  eq update(env(V:var,N:nat,C:env), V':var, N':nat)
     = if V == V' then env(V,N',C)
       else env(V,N,update(C,V',N')) fi .

}


red in TINY-IPL :
evalp((v(0) := 0, while le(v(0), s(s(s(s(s(0)))))) { v(0) := inc(v(0)) }), empty) .

--
eof
**
$Id: implang.mod,v 1.1.1.1 2003-06-19 08:30:16 sawada Exp $
