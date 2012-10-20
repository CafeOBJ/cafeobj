** -*- Mode:CafeOBJ -*-
--

**> An example of precedence declaration.===============================
--> The higher the prec: vlaue, the lower the precedence of an operator. 
--> The range of `prec:' attribute is 0 .. 255 .
--> --------------------------------------------------------------------
module PREC-EX {
  protecting (CHAOS)
  op _op1_ : Identifier Identifier -> Identifier { prec: 0 l-assoc }
  op _op2_ : Identifier Identifier -> Identifier { prec: 1 r-assoc }
  op _op3_ : Identifier Identifier -> Identifier { prec: 2 l-assoc }
  op _op4_ : Identifier Identifier -> Identifier { prec: 3 r-assoc }
  op _op5_ : Identifier Identifier -> Identifier { prec: 4 l-assoc }
  op _op6_ : Identifier Identifier -> Identifier { prec: 5 r-assoc }
  op _op7_ : Identifier Identifier -> Identifier { prec: 6 l-assoc }
  op _op8_ : Identifier Identifier -> Identifier { prec: 7 r-assoc }
  op _op9_ : Identifier Identifier -> Identifier { prec: 8 }
}

show PREC-EX 
select PREC-EX
--> Some example parses _______________________________________________
**>
--> parse a op1 b op2 c op3 d op4 e op5 f op6 g op7 h op8 i op9 j . 
**>
parse a op1 b op2 c op3 d op4 e op5 f op6 g op7 h op8 i op9 j . 
show tree .
**>
--> parse a op9 b op8 c op7 d op6 e op5 f op4 g op3 h op2 i op1 j . 
**>
parse a op9 b op8 c op7 d op6 e op5 f op4 g op3 h op2 i op1 j . 
show tree .
**>
--> parse a op1 b op9 c op2 d op8 e op3 f op7 g op4 h op6 i op5 j .
**>
parse a op1 b op9 c op2 d op8 e op3 f op7 g op4 h op6 i op5 j .
show tree .
**> 
--> parse b op1 c op2 d op2 e op3 f op3 g op4 h op4 i op5 j op5 k op6 l op6 m op7 n op7 o  op8 p op8 q op9 r .
**>
parse b op1 c op2 d op2 e op3 f op3 g op4 h op4 i op5 j op5 k op6 l op6 m op7 n op7 o  op8 p op8 q op9 r .
show tree .
**>
--> parse a op1 b op3 c op5 d op7 e op9 f op2 g op4 h op6 i op8 j .
**>
parse a op1 b op3 c op5 d op7 e op9 f op2 g op4 h op6 i op8 j .
show tree .
**>
--> parse a op2 b op4 c op6 d op8 e op9 f op1 g op3 h op5 i op7 j .
**>
parse a op2 b op4 c op6 d op8 e op9 f op1 g op3 h op5 i op7 j .
show tree .
**>
--> parse a op1 b op3 c op5 d op7 e op9 f op8 g op6 h op4 i op2 j .
**>
parse a op1 b op3 c op5 d op7 e op9 f op8 g op6 h op4 i op2 j .
show tree .
**>
--> parse a op7 b op5 c op3 d op1 e op9 f op2 g op4 h op6 i op8 j .
parse a op7 b op5 c op3 d op1 e op9 f op2 g op4 h op6 i op8 j .
**>
show tree .
**>
--> parse a op7 b op5 c op3 d op1 e op9 f op8 g op4 h op6 i op2 j .
**>
parse a op7 b op5 c op3 d op1 e op9 f op8 g op4 h op6 i op2 j .
show tree .

--> 
**> Associativity properties (l-assoc or r-assoc) are neccessarly for 
**> parsing the following terms without syntax errors.
--> 
**>
--> parse a op1 b op2 c op3 d op4 e op5 f op6 g op7 h op8 i op9 j op8 k op7 l op6 m op5 n op4 o op3 p op2 q op1 r .
**>
parse a op1 b op2 c op3 d op4 e op5 f op6 g op7 h op8 i op9 j op8 k op7 l op6 m op5 n op4 o op3 p op2 q op1 r .
show tree .
**>
--> parse a op9 b op8 c op7 d op6 e op5 f op4 g op3 h op2 i op1 j op2 k op3 l op4 m op5 n op6 o op7 p op8 q .
**>
parse a op9 b op8 c op7 d op6 e op5 f op4 g op3 h op2 i op1 j op2 k op3 l op4 m op5 n op6 o op7 p op8 q .
show tree .

--
eof
-- 
$Id: prec.mod,v 1.1.1.1 2003-06-19 08:30:17 sawada Exp $
