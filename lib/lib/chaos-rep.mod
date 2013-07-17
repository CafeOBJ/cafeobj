** -*- Mode:CafeOBJ -*-
** $Id: chaos-form.mod,v 1.1 2007-01-26 10:39:12 sawada Exp $
** system: Chaos
** module: library
** file: chaos-form.mod
** -------------------------------------------------------------

**
** ChaosForm
**

sys:mod! CHAOS:REP
{
  protecting(CHAOS:EXPR)
  [ ChaosForm ]
  op read : String -> ChaosForm
  op eval : ChaosForm -> ChaosExpr
  op print : ChaosExpr -> ChaosObject
  op rep : String -> ChaosObject
  eq rep(S:String) = print(eval(read S)) .

  
}

