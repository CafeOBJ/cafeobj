mod TRANSwithDifAcMatch {
  [Data, Element < Struct]
  ops 1 2 3 : -> Data
  ops (a:_) (b:_) : Data -> Element
  ops A  B : -> Element
  op (_ _) : Struct Struct -> Struct {assoc comm}
  trans [ab-AB]: (a: D:Data) (b: D) => A B .
}

open TRANSwithDifAcMatch .
-- 1
red ((a: 1) (b: 1) (a: 2) (b: 2) (a: 3) (b: 3))
     =(*,1)=>* S:Struct .
-- 2
red ( (b: 1) (a: 1)  (b: 2) (a: 2) (a: 3) (b: 3))
     =(*,1)=>* S:Struct .
-- 3
red ( (b: 1) (a: 1) (a: 2) (a: 3) (b: 3)  (b: 2) )
     =(*,1)=>* S:Struct .
-- 4
red ((a: 1) (a: 2) (a: 3) (b: 1) (b: 2) (b: 3) )
     =(*,1)=>* S:Struct .
--
close
