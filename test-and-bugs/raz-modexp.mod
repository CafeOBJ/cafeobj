-- From: Razvan Diaconescu <diacon@jaist.ac.jp>
-- Date: Fri, 3 Oct 97 08:48:08 GMT
-- Message-Id: <9710030848.AA11050@is27e0s07.jaist.ac.jp>
-- To: sawada@sra.co.jp
-- Subject:  renaming problem
-- Content-Type: text
-- Content-Length: 1090

-- Dear Toshimi,

-- I am playing a bit with the module system nowadays. I have the
-- following problem, which looks like a bug (but maybe I am doing some
-- silly mistake).

-- Consider this:

mod* DATA {
  [ Data ]
  op _+_ : Data Data -> Data 
}  

mod* COUNTER(X :: DATA) {
  *[ Counter ]*                        -- hidden sort

  bop add : Data Counter -> Counter    -- method
  bop read_ : Counter -> Data          -- attribute

  eq read add(N:Data, C:Counter) = read(C) + N .  
}

-- Then I want to do:

view subtract from DATA to INT {
  sort Data -> Int,
  op _+_ -> _-_ 
}
mod* COUNTER-SUB { protecting(COUNTER(subtract) *
                                 { bop add -> sub })
}

-- and the system breaks down in a bad way:

-- -- defining view subtract 
-- [Warning]: redefining view subtract  done.
-- -- defining module* COUNTER-SUB
-- [Warning]: redefining module COUNTER-SUB 
-- Error: LSIT is invalid as a function.
-- Fast links are on: do (si::use-fast-links nil) for debugging
-- Error signalled by EVAL-IMPORT-MODEXP.
-- Broken at EVAL-IMPORT-MODEXP.  Type :H for Help.
-- CHAOS>>:q

-- Do you know why?

-- Thanks,
-- Razvan
