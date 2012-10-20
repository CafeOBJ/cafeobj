** translated from examples/auto Otter3.0 examples/auto/pigeon.in
-- % Pigeon hole problem -- 5 pigeons into 4 holes.

module PIGEON
{
  protecting (FOPL-CLAUSE)
  -- ops p00 p01 p02 p03 p04 p05 p06 p07 p08 p09 : -> FoplSentence
  -- ops p10 p11 p12 p13 p14 p15 p16 p17 p18 p19 : -> FoplSentence
  ops p00 p01 p02 p03 p04 p05 p06 p07 p08 p09 : -> Bool
  ops p10 p11 p12 p13 p14 p15 p16 p17 p18 p19 : -> Bool

  ** Every pigeon flies ito a hole.
  ax p00 | p01 | p02 | p03  .
  ax p04 | p05 | p06 | p07  .
  ax p08 | p09 | p10 | p11  .
  ax p12 | p13 | p14 | p15  .
  ax p16 | p17 | p18 | p19  .
  **  Each hole holds at most one piegeon.
  ax ~ p00 | ~ p04  .
  ax ~ p00 | ~ p08  .
  ax ~ p00 | ~ p12  .
  ax ~ p00 | ~ p16  .
  ax ~ p04 | ~ p08  .
  ax ~ p04 | ~ p12  .
  ax ~ p04 | ~ p16  .
  ax ~ p08 | ~ p12  .
  ax ~ p08 | ~ p16  .
  ax ~ p12 | ~ p16  .
  ax ~ p01 | ~ p05  .
  ax ~ p01 | ~ p09  .
  ax ~ p01 | ~ p13  .
  ax ~ p01 | ~ p17  .
  ax ~ p05 | ~ p09  .
  ax ~ p05 | ~ p13  .
  ax ~ p05 | ~ p17  .
  ax ~ p09 | ~ p13  .
  ax ~ p09 | ~ p17  .
  ax ~ p13 | ~ p17  .
  ax ~ p02 | ~ p06  .
  ax ~ p02 | ~ p10  .
  ax ~ p02 | ~ p14  .
  ax ~ p02 | ~ p18  .
  ax ~ p06 | ~ p10  .
  ax ~ p06 | ~ p14  .
  ax ~ p06 | ~ p18  .
  ax ~ p10 | ~ p14  .
  ax ~ p10 | ~ p18  .
  ax ~ p14 | ~ p18  .
  ax ~ p03 | ~ p07  .
  ax ~ p03 | ~ p11  .
  ax ~ p03 | ~ p15  .
  ax ~ p03 | ~ p19  .
  ax ~ p07 | ~ p11  .
  ax ~ p07 | ~ p15  .
  ax ~ p07 | ~ p19  .
  ax ~ p11 | ~ p15  .
  ax ~ p11 | ~ p19  .
  ax ~ p15 | ~ p19  .

}

open PIGEON .
option reset
flag(auto,on)
resolve .
close
eof
**
$Id:
