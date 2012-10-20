** Lazy Functional Programming Examples
** based on www.cs.ucsd.edu.groups/tatami/bobj/fpl.html
** adapted to CafeOBJ by sawada@sra.co.jp

mod* DATA {
  [ Data ]
}

mod* STREAM[ X :: DATA ]
{
  *[ Stream ]*
  bop head_ : Stream -> Data
  bop tail_ : Stream -> Stream
  bop _&_ : Data Stream -> Stream { constr }
  var D : Data
  var S : Stream
  eq head(D & S) = D .
  eq tail(D & S) = S .
}

mod* ZIP(X :: DATA)
{
  pr(STREAM(X))
  op zip : Stream Stream -> Stream
  vars S S' : Stream
  eq head zip(S,S') = head S .
  eq tail zip(S,S') = zip(S', tail S) .
}

** 1: Blink

mod* BLINK
{
  pr(ZIP(NAT))
  ops zero one blink : -> Stream {constr}
  eq head zero = 0 .
  eq tail zero = zero .
  eq head one = 1 .
  eq tail one = one .
  eq head blink = 0 .
  eq head tail blink = 1 .
  eq tail tail blink = blink .
}

set trace on
cbred in BLINK : blink == zip(zero, one) .
set trace off


** 2: An Iterative Stream

mod* FDATA{
  pr(DATA)
  op f_ : Data -> Data
}

mod* ITER(X :: FDATA)
{
  pr(STREAM(X))
  op iter1_ : Data -> Stream
  var D : Data
  var S : Stream
  eq head iter1 D = D .
  eq tail iter1 D = iter1 f D .

  op mapf_ : Stream -> Stream
  eq head mapf S = f head S .
  eq tail mapf S = mapf tail S .
  
  op iter2_ : Data -> Stream
  eq head iter2 D = D .
  eq tail iter2 D = mapf iter2 D .
}

set trace on
cbred in ITER : iter1 D == iter2 D .
set trace off

** 3: Natural Number Stream

mod* NATSTREAM
{
  pr (STREAM(NAT))
  op nats_ : Nat -> Stream { constr }
  var N : Nat
  var S : Stream
  eq head nats N = N .
  eq tail nats N = nats (N + 1) .
  
  bop succ_ : Stream -> Stream
  eq head succ S = 1 + head S .
  eq tail succ S = succ tail S .
  
  op nats'_ : Nat -> Stream { constr }
  eq head nats' N = N .
  eq tail nats' N = succ nats' N .
}

set trace on
cbred in NATSTREAM : nats N == nats' N .
set trace off

** 4: Fibonnacci Number Stream

mod* NAT-FIBO
     principal-sort Nat
{
  pr(NAT)
  op f _ : Nat -> Nat 
  eq f(0) = 0 .
  eq f(1) = 1 .
  eq f(N:Nat + 2) = f(N + 1) + f(N) .
}

mod* STREAM-FIBO
{
  pr(ZIP(NAT-FIBO))
  var N : Nat
  var S : Stream

  op nats_ : Nat -> Stream
  eq head nats N = N .
  eq tail nats N = nats (N + 1) .
  
  op mapf_ : Stream -> Stream
  eq head mapf S = f head S .
  eq tail mapf S = mapf tail S .
  op fib_ : Nat -> Stream
  eq fib N = mapf nats N .

  op addl2_ : Stream -> Stream
  eq head addl2 S = head S + head tail S .
  eq tail addl2 S = addl2 tail tail S .
  op fib'_ : Nat -> Stream 
  eq head fib' N = f N .
  eq head tail fib' N = f(N + 1) .
  eq tail tail fib' N = addl2 zip(fib' N, tail fib' N) .
}

set trace on
cbred in STREAM-FIBO : fib N == fib' N .
set trace off

** 5: Double Negation

mod* NEG
{
  pr(STREAM(BOOL))
  op neg_ : Stream -> Stream
  var S : Stream
  eq head neg S = not head S .
  eq tail neg S = neg tail S .
}

set trace on
cbred in NEG : neg neg S == S .
set trace off

-- 
eof
