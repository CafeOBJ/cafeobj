** translated from example of OTTER3.0.5 examples/salt.in
-- Propositional version of the Salt and Mustard puzzle from Lewis Carroll.

module! SALT
{ 
  protecting (FOPL-CLAUSE)

  pred sl :
  pred mb :
  pred sb :
  pred sm :
  pred ml :
  pred sc :
  pred mc :
  pred sd :
  pred md :
  pred mm :

  ax sl | ~ mb | ~ sb | ~ sm | ~ ml | sc | mc | sd | md | mm .
  ax ~ sm | mb | ml .
  ax ~ sm | mb | sl .
  ax ~ sm | sb | ml .
  ax ~ sm | sb | sl .
  ax ~ ml | ~ mc | ~ mm .
  ax ~ ml | ~ mc | ~ sm .
  ax ~ ml | ~ sc | ~ mm .
  ax ~ ml | ~ sc | ~ sm .
  ax ~ md | ~ ml | ~ mm .
  ax ~ md | ~ ml | ~ sm .
  ax ~ md | ~ sl | ~ mm .
  ax ~ md | ~ sl | ~ sm .
  ax ~ sd | ~ mb | mc .
  ax ~ sd | ~ mb | sc .
  ax ~ sd | ~ sb | mc .
  ax ~ sd | ~ sb | sc .
  ax ~ mc | md | ml .
  ax ~ mc | md | sl .
  ax ~ mc | sd | ml .
  ax ~ mc | sd | sl .
  ax ~ mb | ~ md | mm .
  ax ~ mb | ~ md | sm .
  ax ~ mb | ~ sd | mm .
  ax ~ mb | ~ sd | sm .
  ax sd | ~ md | mm .
  ax ~ sd | md | mm .
  ax sc | ~ mc | mm .
  ax ~ sc | mc | mm .
  ax ~ sl | ~ ml | sm .
  ax ~ sb | ~ mb | sm .
  ax sd | ~ md | sl .
  ax ~ sd | md | sl .
  ax sb | ~ mb | sl .
  ax ~ sb | mb | sl .
  ax ~ sc | ~ mc | sd .
  ax ~ sl | ~ ml | mc .
  ax ~ sd | ~ md | mc .
  ax sb | ~ mb | sc .
  ax ~ sb | mb | sc .
  ax ~ sm | ~ mm | mb .
  ax sl | ~ ml | sb .
  ax ~ sl | ml | sb .
  ax sc | ~ mc | sb .
  ax ~ sc | mc | sb .
  ax ~ sc | ~ mb | ~ sb | ~ mm .
  ax ~ sc | ~ mb | ~ sb | ~ sm .
  ax ~ sc | sb | mb | ~ mm .
  ax ~ sc | sb | mb | ~ sm .
  ax ~ mm | ~ mc | ~ sc | ~ md | ~ sd .
  ax ~ mm | sc | mc | sd | md .
  ax ~ sl | ~ mb | ~ sb | ~ md | ~ sd .
  ax ~ sl | ~ mb | ~ sb | sd | md .
  ax ~ sl | sb | mb | ~ md | ~ sd .
  ax ~ sb | ~ mc | ~ sc | ~ ml | ~ sl .
  ax ~ sb | ~ mc | ~ sc | sl | ml .
  ax sm | mm | ml .
  ax sc | mc | ml .
  ax sm | mm | md .
  ax sl | ml | md .
  ax sb | mb | sd .
  ax sm | mm | sc .
  ax sd | md | mb .
}

open SALT .
option reset
flag (auto,on)
resolve .
close
--
eof
--
$Id:
