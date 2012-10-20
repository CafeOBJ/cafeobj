mod! VENDING-MACHINE-SIGNATURE {
  [ Coin Item < Marking ]
  op null : -> Marking
  op __ : Marking Marking -> Marking { assoc comm id: null }
  op $ : -> Coin
  op q : -> Coin
  op a : -> Item
  op c : -> Item
}


mod VENDING-MACHINE {
  pr(VENDING-MACHINE-SIGNATURE)
  var M : Marking 
  -- trans [add-q]: M => M q .
  -- trans [add-$]: M => M $ .
  trans [add-q]: M null => M q .
  trans [add-$]: M null => M $ .
  trans [buy-c]: $ => c .
  trans [buy-a]: $ => a q .
  trans [change]: q q q q => $ .
}

mod VENDING-MACHINE-TOP {
  pr(VENDING-MACHINE-SIGNATURE)
  var M : Marking
  trans [add-q]: M => M q .
  trans [add-$]: M => M $ .
  trans [buy-c]: $ M => c M .
  trans [buy-a]: $ M => a q M .
  trans [change]: q q q q => $ .
}

mod SIMPLE-VENDING-MACHINE {
  pr(VENDING-MACHINE-SIGNATURE)
  trans [buy-c]: $ => c .
  trans [buy-a]: $ => a q .
  trans [change]: q q q q => $ .
}



