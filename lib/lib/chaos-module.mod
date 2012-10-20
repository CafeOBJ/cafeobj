mod! CHAOS:MODULE
{
  protecting(CHAOS:FORM)
  op ?mod  : String -> Module
  op ?mod  : ModExpr -> ChaosExpr
  op :modexpr : String -> ModExpr
  op modexpr-is-error : ModExpr -> Bool
  eq ?mod(X:String) = #!(eval-modexp+
			   (normalize-modexp (parse-modexp (read-modexp-from-string x)))) .
  eq ?mod(X:ModExpr) = #!(eval-modexp+ X) .
  eq :modexpr(X:String) = #!(normalize-modexp (parse-modexp (read-modexp-from-string X))) .
  eq modexpr-is-error(X:ModExpr) = #! (modexp-is-error X) .
}
