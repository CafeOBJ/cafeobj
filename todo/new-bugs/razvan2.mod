-- FILE: f-exp-comp
-- CONTENTS: proof of the correctness of an arithmetic expression compiler
--           with if and fn (lambda expression) 
-- AUTHORS:  Kokichi Futatsugi; modified by Razvan Diaconescu
-- DIFFICULTY: ****

--> binary operation symbols
mod! OPsym {  
  [ Opsym ]  
  ops ++ -- x : -> Opsym 
}

--> Expressions
--> BOOL is automatically imported to any module
mod! EXP { 
  protecting(INT + OPsym)

  -- values
  [ Int < Exp ]

  --> arithmetic binary operation expressions
  op (_ _ _)  : Exp Opsym Exp -> Exp
}

--> application of operations
mod! APP { protecting(EXP) 

  --> arithmetic operation applications
  op apply_to_ _ : Opsym Int Int -> Int
  vars I J : Int 

  eq apply ++ to I J = I + J .
  eq apply -- to I J = I - J .
  eq apply x to I J = I * J .
}

--> eval for expressions
mod! EVAL { protecting(APP) 

  --> evaluator
  op eval_ : Exp -> Int

  vars E1 E2 : Exp

  --> bases: Int, Bool, Name, Fval are evaluated to themselves
  eq eval (V:Int) = V .

  --> arithmetic expression eval
  eq eval(E1 Op:Opsym E2) = apply Op to eval(E1) eval(E2) .
}

-- testing of eval_
-- it should be 1
red eval(((2 -- 3) x 5) ++ (3 x 2)) .

**  *********************************************************
**> definition of Execution Machine for running compiled code
**  *********************************************************

--> parameterized list
mod! LIST (ELT :: TRIV) {
  [ Elt < List ]
  op nil : -> List

  --> append operation on List
  op (_@_) : List List -> List   {assoc} -- append
  eq nil @ L:List = L .
}

--> instructions
mod! INST { protecting(OPsym + INT)
  [ Inst ]

  op Load_ : Int -> Inst
  op Apply_ : Opsym  -> Inst
}

--> value stack for storing intermediate computation results
make VALUE-STACK (LIST(ELT <= view to INT { sort Elt -> Int })
		      * {sort List -> ValStack,
		         op nil -> empty,
		         op _@_ -> _|_ })

--> list of instructions
make INST-LIST (LIST(ELT <= view to INST {sort Elt -> Inst}) 
                           * {sort List -> InstList})

-- %%%%%%%%%%%%%%%%%%%%
-- %% Compiler
-- %%%%%%%%%%%%%%%%%%%%

mod! COMPILER {
 protecting (EXP + INST-LIST)

 --> compile operation
 op compile_ : Exp -> InstList

 --> basics: Int, Bool, Name, Fval
 eq compile V:Int = (Load V) @ nil .

 --> arithmetic expressions
 eq compile (E1:Exp Op:Opsym E2:Exp) = 
       compile(E1) @ compile(E2) @ (Apply Op) @ nil .
}

-- testing of compiler
red compile (((2 -- 3) x 5) ++ (3 x 2)) .

-- %%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
-- %% machine executing instructions
-- %%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

--> abstract machine for executing/running 
--> the binary operations,if operation, 
--> and function-closure application
mod! EXEC-MACHINE {
 protecting (VALUE-STACK + APP + COMPILER)

 [ Config ]
 op do_on_od : InstList ValStack -> Config 

 op exec_ : Config -> Config

 vars Is : InstList 
 vars Vs : ValStack

 eq exec do ((Load E:Int) @ Is) on Vs od = do Is on (E | Vs) od .

 eq exec do ((Apply Op:Opsym) @ Is) on (I:Int | J:Int | Vs) od = 
            do Is on ((apply Op to J I) | Vs) od .
 --> run
 op run_ :  Config -> Config
 eq run do nil on Vs:ValStack od = do nil on Vs od .

 eq run do (I:Inst @ Is:InstList) on Vs:ValStack od = 
 	run exec do (I:Inst @ Is:InstList) on Vs:ValStack od .
}

-- red run do compile(((2 -- 3) x 5) ++ (3 x 2)) on nil od .
red run do compile(((2 -- 3) x 5) ++ (3 x 2)) on empty od .
** ---------------------------
eof

This reduction gets blocked before end. I get the following:

-- reduce in EXEC-MACHINE : (run (do (compile (((2 -- 3) x 5) ++ (3 x 2))) on nil od))
(run (exec (do (((Apply --) @ (Load 5)) @ ((Apply x) @ ((Load 3) @
((Load 2) @ ((Apply x) @ ((Apply ++) @ nil)))))) on ((3 @ 2) @ nil)
od)))  :Config

========
Thanks,
Razvan
