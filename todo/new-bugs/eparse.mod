-- violation of unique parse rule
mod OStest1 {
  [S1 S2 < S0]
  [S1' S2']
  op a : -> S0 .
  op f_ : S1 -> S1' .
  op f_ : S2 -> S2' .
}
parse in OStest1 : f a .

-- violation of unique parse rule
mod OStest2 {
  [S1 S2 < S0]
  [S1' S2']
  [S1' < S1'']
  op a : -> S0 .
  op f_ : S1 -> S1' .
  op f_ : S2 -> S2' .
}
parse in OStest2 : f a .

mod OStest3 {
  [S1 S2 < S0]
  [S1' S2']
  [S1' S2' < S0']
  op a : -> S0 .
  op f_ : S1 -> S1' .
  op f_ : S2 -> S2' .
}
parse in OStest3 : f a .
open OStest3 .
op b : -> S1 .
eq a = b .
parse f a .
red f a .
close

mod OStest4 {
  [S1 S2 < S0]
  [S1' S2']
  [S1' < S1'']
  [S1' S2' < S0']
  op a : -> S0 .
  op f_ : S1 -> S1' .
  op f_ : S2 -> S2' .
}

mod OStest5 {
  [S1 S2 S3 < S0]
  [S1' S2']
  [S1' < S1'']
  [S1' S2' < S0']
  op a : -> S0
  op f_ : S1 -> S1'
  op f_ : S2 -> S2'
  op f_ : S3 -> S1''
}

