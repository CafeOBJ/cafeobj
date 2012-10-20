**
** $Id: term.mod,v 1.2 2007-01-27 00:41:09 sawada Exp $
**

mod! CHAOS:TERM
{
  protecting(CHAOS:MODULE)

  [ String ChaosList < TermExpr ]

  ** constructors
  op :appl-form : Operator ChaosList -> ApplForm
  op :var : String ChaosSort -> Variable
  op :bconst : ChaosExpr ChaosSort -> BconstTerm
  op :pvar : String ChaosSort -> PVariable
  op :slisp : ChaosExpr -> SlispTerm
  op :glisp : ChaosExpr -> GlispTerm
  op :parse : TermExpr -> Term
  op :parse : TermExpr Module -> Term

  ** accessors
  op subterms : ApplForm -> ChaosList
  op term-op  : ApplForm -> Operator
  op var-name : Variable  -> String
  op term-sort : Term -> ChaosSort
  op term-arg-n : Term Nat -> Term
  op bconst-value : BconstTerm -> ChaosExpr
  op lisp-form  : LispTerm -> ChaosExpr
    
  ** axioms
  eq :appl-form(O:Operator, L:ChaosList) = #!(make-applform (method-coarity O)
					                   O L) .
  eq :var(N:String, S:ChaosSort) = #!(make-variable-term S N) .
  eq :bconst(V:ChaosExpr, S:ChaosSort) = #!(make-bconst-term S V) .
  eq :parse(S:TermExpr) = #!(simple-parse *current-module* S) .
  eq :parse(S:TermExpr, M:Module) = #!(simple-parse M S) .
  eq term-sort(X:Term) = #!(term-sort X) .
}
  
