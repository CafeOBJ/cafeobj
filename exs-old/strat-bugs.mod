** -*- Mode:CafeOBJ -*-

module! NZ-STRAT-BUG { 
  [ Foo ] 
  op f : Foo -> Foo { strat: (0 1 0) }
  ops g h k : Foo -> Foo
  ops a b c success : -> Foo
  var X : Foo
  eq a = b .
  eq f(b) = c .
  eq g(h(X)) = k(X) .
  eq k(c) = success .
}

set trace on .
reduce in NZ-STRAT-BUG : g(h(f(a))) .

module! NON-LINEAR-BUG {
  [ Foo ]
  op f : Foo Foo -> Foo
  ops a b : -> Foo
  op success : -> Foo
  var X : Foo
  eq a = b .
  eq f(X,X) = success .
}

reduce in NON-LINEAR-BUG : f(a,b) .

module! SHARE-STRAT-BUG {
  [ Foo ]  op l : Foo -> Foo { strat: (0) }
  op s : Foo -> Foo { strat: (0) }
  op f : Foo Foo -> Foo
  ops a b : -> Foo
  op success : -> Foo
  var X : Foo
  eq a = b .
  eq f(l(b), X) = success .
  eq s(X) = f(l(X), X) .
}

reduce in SHARE-STRAT-BUG : s(a) .

module! CONDITIONAL-BUG {
  [ Foo Bar ]
  -- op l : Foo -> Bar { strat: (0) }  
  op l : Foo -> Bar { strat: (0 1) }
  ops a b c : -> Foo
  ops success fail : -> Bar
  var X : Foo
  eq a = b .
  eq l(b) = success .
  ceq l(X) = fail if X == c .
  eq l(a) = success .
}

reduce in CONDITIONAL-BUG : l(a) .

-- does not work now ...
module! SIDE-EFFECT-BUG {
  [ Foo ]
  ops s l : Foo -> Foo { strat: (0 1 0) }
  op f : Foo Foo -> Foo { strat: (1 2 0) }
  ops a b success : -> Foo
  var X : Foo
  eq a = b .
  eq l(b) = success .
  eq s(X) = f(l(X), X) .
}

reduce in SIDE-EFFECT-BUG : s(a) .

-- does not work now ...
module! REDUCE-BUG {
  [ Foo ]
  -- ops s l : Foo -> Foo { strat: (0) }
  ops s l : Foo -> Foo { strat: (0 1) }
  op f : Foo Foo -> Foo { strat: (1 2 0) }
  op k : Foo -> Foo
  ops a b c success : -> Foo
  var X : Foo
  eq a = b .
  eq l(b) = c .
  eq f(X, b) = k(X) .
  eq k(c) = success . 
  eq s(X) = f(l(X), X) .
}

reduce in REDUCE-BUG : s(a) .

module! SORT-BUG {
  [ Bar < Foo, Baz ]
  op l : Foo -> Foo { strat: (0 1) }
  op l : Bar -> Bar { strat: (0 1) }
  op s : Foo -> Baz { strat: (0 1) }
  op f : Foo Foo -> Baz { strat: ( 1 2 0 ) }
  op a : -> Foo
  op b : -> Bar
  op success : -> Baz
  var X : Bar
  var Y : Foo
  eq a = b .
  eq f(X, Y) = success .
  eq s(Y) = f(l(Y), Y) .
}

reduce in SORT-BUG : s(a) .

set trace off .
--
eof
--
$Id: strat-bugs.mod,v 1.1.1.1 2003-06-19 08:30:17 sawada Exp $
