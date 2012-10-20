** -*- Mode:CafeOBJ -*-
-- -----------------------------------------------------------------------------
-- Simple Date package : 
-- does not handle leap year
-- -----------------------------------------------------------------------------

module! MONTH {
  [ Month ]
  ops Jan Feb Mar Apr May Jun : -> Month
  ops Jul Aug Sep Oct Nov Dec : -> Month
  op next_ : Month -> Month 
  eq next Jan = Feb .   eq next Feb = Mar .
  eq next Mar = Apr .   eq next Apr = May .
  eq next May = Jun .   eq next Jun = Jul .
  eq next Jul = Aug .   eq next Aug = Sep .
  eq next Sep = Oct .   eq next Oct = Nov .
  eq next Nov = Dec .   eq next Dec = Jan .

  protecting (INT) 
  op #days_ : Month -> NzNat 
  eq #days Jan = 31 .   eq #days Feb = 28 .  
  eq #days Mar = 31 .   eq #days Apr = 30 .  
  eq #days May = 31 .   eq #days Jun = 30 .  
  eq #days Jul = 31 .   eq #days Aug = 31 .  
  eq #days Sep = 30 .   eq #days Oct = 31 .  
  eq #days Nov = 30 .   eq #days Dec = 31 .  
}

module! DATE {
  extending (INT)
  extending (MONTH)  

  record Date {
    day   : Int
    month : Month
    year  : Int
  }
  op next_ : Date -> Date
  axioms {
    var DT : Date          var D : NzInt
    var M  : Month         var Y : NzInt
    -- -----------------------------------
    ceq next DT = makeDate(day   = 1 + day(DT),
			   month = month(DT),
			   year  = year(DT))
		  if day(DT) < #days month(DT) .
    ceq next DT = makeDate(day   = 1,
			   month = next month(DT),
			   year  = year(DT))
		  if month(DT) =/= Dec and day(DT) == #days month(DT) .
    ceq next DT = makeDate(day   = 1,
			   month = next month(DT),
			   year  = 1 + year(DT))
		  if month(DT) == Dec and day(DT) == 31 .
    }
}		             

module DATE2 {
  protecting (DATE)
  record Date2 [Date * (day -> day2)] {
  }
}

eof
**
$Id: date.mod,v 1.1.1.1 2003-06-19 08:30:12 sawada Exp $
