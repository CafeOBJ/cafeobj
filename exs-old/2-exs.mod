--	                           -*- Mode:CafeOBJ -*-
--
--
require 2 ./2

module! FNS
     principal-sort Int
{
  protecting ( INT )
  ops (sq_) (dbl_) (_*3) : Int -> Int 
  var N : Int 
  eq sq N = N * N .
  eq dbl N = N + N .
  eq N *3 = N * 3 .
}

make EX1 (2(F <= FNS { op f -> sq_ }))

select EX1

**> should be 81 
reduce  xx(3) .  
**> should be 256
reduce  xx(4) .  
**> does not work select 2(F <= view to FNS { op f -> dbl_ })
-- select 2(F <= view to FNS { op f -> dbl_ })
open 2(F <= view to FNS { op f -> dbl_ }) .
**> should be 12
reduce xx(3) . 
close

-- select 2((2(FNS { op f -> sq_ })*{ op xx -> f }){ sort S -> Int, op f -> f })
open 2((2(FNS { op f -> sq_ })*{ op xx -> f }){ sort S -> Int, op f -> f }) .
**> should be 65536
reduce xx(2) . 
**> should be 43046721
reduce xx(3) . 

close
--
eof
--
$Id: 2-exs.mod,v 1.1.1.1 2003-06-19 08:30:11 sawada Exp $
