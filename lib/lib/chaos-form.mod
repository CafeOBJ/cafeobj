** -*- Mode:CafeOBJ -*-
** $Id: chaos-form.mod,v 1.1 2007-01-26 10:39:12 sawada Exp $
** system: Chaos
** module: library
** file: chaos-form.mod
** -------------------------------------------------------------

**
** ChaosForm
**

sys:mod! CHAOS:FORM 
{
  protecting(CHAOS:EXPR)
  protecting(NAT)

  op nil : -> ChaosVoid
  op _;_ : ChaosExpr ChaosExpr -> ChaosList {r-assoc}
  op !_ : ChaosExpr -> ChaosExpr
  op nth : Nat ChaosList -> ChaosExpr 
  op append : ChaosList ChaosList -> ChaosList
  eq nil = #! nil .
  eq ! X:ChaosExpr = #!(eval-ast X) .
  eq nth(N:Nat, L:ChaosList) = #!(nth N L) .
  eq append(L1:ChaosList, L2:ChaosList) = #!(append L1 L2) .

}

