-- $id$
module MODEXPR {
  [ Identifier < ModExpr ]
  [ Idetifier < ViewMap < ViewArg,
    SortMap OpMap <  MapList ]

  signature {
    op _+_  : ModExpr ModExpr -> ModExpr
    op _*_  : ModExpr MapList -> ModExpr
    op _[_] : ModExpr ViewArg -> ModExpr
    attr _+_ : [ assoc comm idem l-assoc prec: 3 ]
    attr _*_ : [ l-assoc prec: 2 ]
    attr _[_] : [ l-assoc prec: 1 ]

    op (sort_->_) : Identifier Identifier -> SortMap
    op (op_->_) : Identifier Identifier -> OpMap
    op null-map : -> MapList
    op _,_ : MapList MapList -> MapList
    attr _,_ : [ assoc comm id: null-map ]
 
    op (view from_to_is_) : ModExpr ModExpr MapList -> ViewMap

    }

   axioms {
     vars X Y Z : Identifier
     var L : MapList

     eq sort X -> Y, L, sort X -> Z
	= L, sort X -> Z  .
     eq op X -> Y, L, op X -> Z
	= L, op X -> Z .
    }
  
  }

