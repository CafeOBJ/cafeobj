module! DATA
{
  protecting(FOPL-CLAUSE)
  [ Data Flag ]
  ops t f : -> Flag
  op not_ : Flag -> Flag
  eq not t = f .
  eq not f = t .
  ax ~((not X:Flag) = X) .
}

mod* SENDER {
  *[ Sender ]*  -- [ Data ]
  protecting (DATA)
  bop bit : Sender -> Flag
  bop val : Sender -> Data
  bop in : Data Flag Sender -> Sender
  op init : -> Sender
  var D : Data   var B : Flag   var S : Sender
  eq bit(init) = t .   -- valid initial state
  ceq val(in(D,B,S)) = D if bit(S) == B . -- new data for right ack
  ceq bit(in(D,B,S)) = not bit(S) if bit(S) == B . -- alternates bit
  bceq in(D,B,S) = S if bit(S) =/= B .  -- stays put for wrong ack
}

mod* RECEIVER {
  *[ Receiver ]* -- [ Data ]
  protecting (DATA)
  bop bit : Receiver -> Flag
  bop val : Receiver -> Data
  bop get : Data Flag Receiver -> Receiver
  op init : -> Receiver
  var D : Data   var B : Flag   var R : Receiver
  eq bit(init) = t .   -- valid initial state
  ceq val(get(D,B,R)) = D if bit(R) =/= B . -- output value
  ceq bit(get(D,B,R)) = not bit(R) if bit(R) =/= B . -- alternates bit
  bceq get(D,B,R) = R if bit(R) == B . -- stays put for wrong bit
}

--
eof
--
$Id:
