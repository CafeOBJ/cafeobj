** -*- Mode:CafeOBJ -*-
** $Id: chaos-script.mod,v 1.1 2007-01-26 10:39:12 sawada Exp $
** system: Chaos
** module: library
** file: chaos-script.mod
** -------------------------------------------------------------

sys:mod! CHAOS:SCRIPT
{
  protecting(CHAOS:FORM)
  op eval : ChaosExpr -> ChaosExpr
  op lisp-eval : ChaosExpr -> ChaosExpr
  eq eval(X:ChaosExpr) = #!(%eval* X) .
  eq lisp-eval(X:ChaosExpr) = #!(%lisp-eval* X) .
  
}
