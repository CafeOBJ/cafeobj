-- ==========================================================
--> qlockTrans.mod
-- ==========================================================

in qlock.mod

mod* QLOCKconfig {
  inc(QLOCK)
  [ Config ]
  op <_> : Sys -> Config .
}

-- pre-transiton system with an agent/process p
mod* QLOCKpTrans {
  inc(QLOCKconfig)
  op p : -> PidConst .
  var S : Sys .
  -- possible transitions
  ctrans < S > => < want(S,p) > if c-want(S,p) .
  ctrans < S > => < try(S,p) >  if c-try(S,p) .
  ctrans < S > => < exit(S,p) > if c-exit(S,p) .
}

-- transition system which simulates QLOCK of 2 agents i j
mod* QLOCKijTrans {
  -- 2 QLOCKpTrans-es  corresponding to two different 
  -- PidConst-s i j are declared
  -- by using renaming of modules
 inc((QLOCKpTrans * {op p -> i}) +
      (QLOCKpTrans * {op p -> j}))
}

-- transition system which simulates QLOCK of 3 agents i j k
mod* QLOCKijkTrans {
  -- 3 QLOCKpTrans-es  corresponding to three different 
  -- PidConst-s i j k are declared
  -- by using renaming of modules
 inc(QLOCKijTrans +
     (QLOCKpTrans * {op p -> k}))
}

-- transition system which simulates QLOCK of 4 agents i j k l
mod* QLOCKijklTrans {
  -- 4 QLOCKpTrans-es  corresponding to four different 
  -- PidConst-s i j k l are declared
  -- by using renaming of modules
 inc(QLOCKijkTrans +
     (QLOCKpTrans * {op p -> l}))
}
