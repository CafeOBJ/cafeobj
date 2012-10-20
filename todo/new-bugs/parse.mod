-- Date: Mon, 20 Jul 1998 00:30:56 +0900
-- From: Kokichi Futatsugi <kokichi@shin.sra.co.jp>
-- Message-Id: <199807191530.AAA01201@shin>
-- To: sawada@sra.co.jp
-- Subject: parsing time
-- Cc: kokichi@jaist.ac.jp
-- Reply-to: kokichi@jaist.ac.jp
-- Content-Type: text
-- Content-Length: 9805

-- 澤田さん

-- 二木です

-- calendarの仕様（program?)を書いてみたのですが，
-- 不自然にparsingに時間がかかります．最後のopenの中を見て下さい．

-- 何か基本的な勘違いをしているのか知りたいので，
-- 原因が分かったら教えて下さい．

-- codeとlogの一部を添付します．

-- %%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
-- FILE: calendar.mod
-- CONTENTS: behavioural specification of a calendar objcet as concurrent
--           composition with synchronization of 2 objects and 1 data
-- AUTHOR: Kokichi Futatsugi
-- DIFFICULTY: **

set tram path brute
set verbose on

-- the following command should be on in the final version
-- in watch.mod

--> day of the week data
mod! DAY-OF-WEEK { 
  [ DayOfWeek ]
  ops Sunday Monday Tuesday Wednesday Thursday Friday Saturday :
                   -> DayOfWeek

  op next : DayOfWeek -> DayOfWeek 
  eq next(Sunday) = Monday .
  eq next(Monday) = Tuesday .
  eq next(Tuesday) = Wednesday .
  eq next(Wednesday) = Thursday .
  eq next(Thursday) = Friday .
  eq next(Friday) = Saturday .
  eq next(Saturday) = Sunday .
}

-- the week object
mod* WEEK {
  protecting (DAY-OF-WEEK)
  *[ Week ]*  
  
  op init : -> Week
  bop dayOfWeek : Week -> DayOfWeek 
  -- bop incDay : Week -> Week 
  bop incWeek : Week -> Week 

  eq dayOfWeek(incWeek(W:Week)) = next(dayOfWeek(W)) .
}

--> Month date
mod MONTH  { 
  protecting (NAT)
  [ Month ]
  ops January February March 
      April May June 
      July August September 
      October November December : -> Month 

  ops next previous : Month -> Month

  eq next(January) = February .
  eq next(February) = March .
  eq next(March) = April .
  eq next(April) = May .
  eq next(May) = June .
  eq next(June) = July .
  eq next(July) = August .
  eq next(August) = September .
  eq next(September) = October .
  eq next(October) = November .
  eq next(November) = December .
  eq next(December) = January .

  eq previous(January) = December .
  eq previous(February) = January .
  eq previous(March) = February .
  eq previous(April) = March .
  eq previous(May) = April .
  eq previous(June) = May .
  eq previous(July) = June .
  eq previous(August) = July .
  eq previous(September) = August .
  eq previous(October) = September .
  eq previous(November) = October .
  eq previous(December) = November .

  op numberOfDays : Month -> Nat
  op numberOfFebDays : -> Nat

  eq numberOfDays(January) = 31 .
  eq numberOfDays(March) = 31 .
  eq numberOfDays(April) = 30 .
  eq numberOfDays(May) = 31 .
  eq numberOfDays(June) = 30 .
  eq numberOfDays(July) = 31 .
  eq numberOfDays(August) = 31 .
  eq numberOfDays(September) = 30 .
  eq numberOfDays(October) = 31 .
  eq numberOfDays(November) = 30 .
  eq numberOfDays(December) = 31 .

  op numberOfDaysForLeap : Month -> Nat 
  op numberOfDaysForOrd : Month -> Nat 

  ceq numberOfDaysForLeap(M:Month) = numberOfDays(M) if M =/= February .
  ceq numberOfDaysForLeap(M:Month) = 29 if M == February .

  ceq numberOfDaysForOrd(M:Month) = numberOfDays(M) if M =/= February .
  ceq numberOfDaysForOrd(M:Month) = 28 if M == February .
}	   

-- generic date object
mod* DATE {
  protecting (MONTH)

  [ Day < Nat ]

  *[ Date ]*  

  op initOrd : -> Date                 -- init date for ordinary year
  op initLeap : -> Date                -- init date for leap year
  bop month :  Date -> Month    {memo}        -- current Month attribute
  bop day : Date -> Day         {memo}        -- current Day of Month attribute
  bop lastDay? : Date -> Bool   {memo}          -- be in the last day of the year
  bop leap? : Date -> Bool      {memo}        -- be date in a leap year
  bop incDate : Date -> Date             -- increase one day method

  var D : Date

  eq day(initOrd) = 1 .
  eq month(initOrd) = January .
  eq leap?(initOrd) = false .

  eq day(initLeap) = 1 .
  eq month(initLeap) = January .
  eq leap?(initLeap) = true .

  ceq day(incDate(D)) = day(D) + 1 
                         if not(leap?(D) == true) and
                            (day(D) =/= numberOfDaysForOrd(month(D))) .
  ceq day(incDate(D)) = day(D) + 1 
                         if leap?(D) and
                            day(D) =/=
                            numberOfDaysForLeap(month(D)) .

  ceq day(incDate(D)) = 1          
                         if not(leap?(D) == true) and
                         day(D) == numberOfDaysForOrd(month(D)) .
  ceq day(incDate(D)) = 1          
                         if leap?(D) and
                         day(D) == numberOfDaysForLeap(month(D)) .

  ceq month(incDate(D)) = month(D)       
                               if not(leap?(D) == true) and
                               day(D) =/= numberOfDaysForOrd(month(D)) .
  ceq month(incDate(D)) = month(D)       
                               if leap?(D) and
                               day(D) =/= numberOfDaysForLeap(month(D)) .

  ceq month(incDate(D)) = next(month(D)) 
                               if not(leap?(D) == true) and
                               day(D) == numberOfDaysForOrd(month(D)) .
  ceq month(incDate(D)) = next(month(D)) 
                               if leap?(D) and
                               day(D) == numberOfDaysForLeap(month(D)) .

  eq lastDay?(D) = (month(D) == December) and (day(D) == 31) .

  eq leap?(incDate(D)) = leap?(D) .

}

--> year data
mod! YEAR {
  protecting (NAT)
  [ Year < Nat ]

  op leap? : Nat -> Bool
  ceq leap? (Y:Year) = true if ((Y rem 4) == 0) and ((Y rem 100) =/= 0) .
}

-- the composed calendar object
mod* CALENDAR {
  protecting (YEAR + DATE +  WEEK)
  protecting (4TUPLE(NAT, MONTH, NAT, DAY-OF-WEEK)
	      * { sort 4Tuple -> FullDate,
  		  op <<_;_;_;_>> -> (_ _ _ : _) })
	      -- the FullDate resentations are like:
	      -- (19 July 1998 : Sunday)

  *[ Calendar ]*

  -- op init : -> Calendar 
  bop incDay : Calendar -> Calendar   -- method to increment a day

  bop week :  Calendar -> Week   {memo}  -- projection
  bop date : Calendar ->  Date   {memo}  -- projection
  bop year : Calendar -> Year    {memo}  -- projection

  bop WEEK : Calendar -> DayOfWeek
  bop DAY : Calendar ->  Day     
  bop MONTH : Calendar -> Month  
  bop YEAR : Calendar -> Year       

  bop FULL-DATE : Calendar -> FullDate -- a derived operator

  var C : Calendar

  eq WEEK(C) = dayOfWeek(week(C)) .
  eq DAY(C) = day(date(C)) .
  eq MONTH(C) = month(date(C)) .
  eq YEAR(C) = year(C) .

  eq FULL-DATE(C) = (DAY(C) MONTH(C) YEAR(C) : WEEK(C)) .

  eq week(incDay(C)) = incWeek(week(C)) .

  ceq date(incDay(C)) = incDate(date(C)) if not (true == lastDay?(date(C))) .
  ceq date(incDay(C)) = initOrd
                          if (lastDay?(date(C)) and leap?(year(C) + 1)) .
  ceq date(incDay(C)) = initLeap
                          if lastDay?(date(C)) and not (true == leap?(year(C) + 1)) .

  ceq year(incDay(C)) = year(C) if not(true == lastDay?(date(C))) .
  ceq year(incDay(C)) = (year(C) + 1) if lastDay?(date(C)) .

}

-- some testing
open CALENDAR
op cd : -> Calendar .
--> Date is (19 July 1998 : Sunday)
eq year(cd) = 1998 .
eq day(date(cd)) = 19 .
eq month(date(cd)) = July .
eq dayOfWeek(week(cd)) = Sunday .
red FULL-DATE(cd) .

-- 2
red FULL-DATE(incDay(incDay(cd))) .

-- parse 5  <=== log あり
parse FULL-DATE(incDay(incDay(incDay(incDay(incDay(cd)))))) .
-- 5        <=== log あり
red FULL-DATE(incDay(incDay(incDay(incDay(incDay(cd)))))) .

-- parse 10 <=== 不自然に時間がかかる； それほど複雑な項とは思えない
--          <=== log あり
parse FULL-DATE(incDay(incDay(incDay(incDay(incDay(
                incDay(incDay(incDay(incDay(incDay(cd))))))))))) .
-- 10  <=== statistics あり
--     <=== log あり
 red FULL-DATE(incDay(incDay(incDay(incDay(incDay(
               incDay(incDay(incDay(incDay(incDay(cd))))))))))) .

-- parse 15 <=== これは500秒以上かかる？？？
--          <=== log なし
parse FULL-DATE(incDay(incDay(incDay(incDay(incDay(
              incDay(incDay(incDay(incDay(incDay(
              incDay(incDay(incDay(incDay(incDay(cd)))))))))))))))) .
-- 15
red FULL-DATE(incDay(incDay(incDay(incDay(incDay(
              incDay(incDay(incDay(incDay(incDay(
              incDay(incDay(incDay(incDay(incDay(cd)))))))))))))))) .

eof


%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
%%%%part of log of the above code%%%%%%%
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

%CALENDAR> FULL-DATE(incDay(incDay(incDay(incDay(incDay(cd)))))) : FullDate
FULL-DATE:FullDate
         |         
  incDay:Calendar 
         |         
  incDay:Calendar 
         |         
  incDay:Calendar 
         |         
  incDay:Calendar 
         |         
  incDay:Calendar 
         |         
    cd:Calendar   
                   
%CALENDAR> %CALENDAR> -- reduce in % : FULL-DATE(incDay(incDay(incDay(incDay(incDay(cd)
    )))))
24 July 1998 : Friday : FullDate
(0.130 sec for parse, 136 rewrites(0.520 sec), 276 matches, 57 memo hits)

%CALENDAR> FULL-DATE(incDay(incDay(incDay(incDay(incDay(incDay(incDay(incDay(
incDay(incDay(cd))))))))))) : FullDate
FULL-DATE:FullDate
         |         
  incDay:Calendar 
         |         
  incDay:Calendar 
         |         
  incDay:Calendar 
         |         
  incDay:Calendar 
         |         
  incDay:Calendar 
         |         
  incDay:Calendar 
         |         
  incDay:Calendar 
         |         
  incDay:Calendar 
         |         
  incDay:Calendar 
         |         
  incDay:Calendar 
         |         
    cd:Calendar   
                   
%CALENDAR> %CALENDAR> -- reduce in % : FULL-DATE(incDay(incDay(incDay(incDay(incDay(incDay(
    incDay(incDay(incDay(incDay(cd)))))))))))
29 July 1998 : Wednesday : FullDate
(61.830 sec for parse, 220 rewrites(0.580 sec), 455 matches, 89 memo hits)
%CALENDAR> 

%%%%%%%%end end end%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
