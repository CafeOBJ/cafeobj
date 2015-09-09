**
** Copyright (c) 2000-2015, Toshimi Sawada. All rights reserved.
**
** Redistribution and use in source and binary forms, with or without
** modification, are permitted provided that the following conditions
** are met:
**
**   * Redistributions of source code must retain the above copyright
**     notice, this list of conditions and the following disclaimer.
**
**   * Redistributions in binary form must reproduce the above
**     copyright notice, this list of conditions and the following
**     disclaimer in the documentation and/or other materials
**     provided with the distribution.
**
** THIS SOFTWARE IS PROVIDED BY THE AUTHOR 'AS IS' AND ANY EXPRESSED
** OR IMPLIED WARRANTIES, INCLUDING, BUT NOT LIMITED TO, THE IMPLIED
** WARRANTIES OF MERCHANTABILITY AND FITNESS FOR A PARTICULAR PURPOSE
** ARE DISCLAIMED.  IN NO EVENT SHALL THE AUTHOR BE LIABLE FOR ANY
** DIRECT, INDIRECT, INCIDENTAL, SPECIAL, EXEMPLARY, OR CONSEQUENTIAL
** DAMAGES (INCLUDING, BUT NOT LIMITED TO, PROCUREMENT OF SUBSTITUTE
** GOODS OR SERVICES; LOSS OF USE, DATA, OR PROFITS; OR BUSINESS
** INTERRUPTION) HOWEVER CAUSED AND ON ANY THEORY OF LIABILITY,
** WHETHER IN CONTRACT, STRICT LIABILITY, OR TORT (INCLUDING
** NEGLIGENCE OR OTHERWISE) ARISING IN ANY WAY OUT OF THE USE OF THIS
** SOFTWARE, EVEN IF ADVISED OF THE POSSIBILITY OF SUCH DAMAGE.
**
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

