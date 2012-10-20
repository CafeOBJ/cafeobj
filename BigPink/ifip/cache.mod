** --------------------------------------------------------------------------
** cache.mod
** --------------------------------------------------------------------------

-- cache coherence problem by A.Mori
-- as of 13 Aug 2000
set include FOPL-CLAUSE on

module* DATA
{
  [ Index Data ]
}
module! FLAG
{
  [ Flag ]

  ops invalid vex dirty shared : -> Flag
  -- vex stand for valid-exclusive

  ax F:Flag = invalid | F = vex | F = shared | F = dirty .
  ax ~(invalid = vex).
  ax ~(invalid = dirty).
  ax ~(invalid = shared).
  ax ~(shared  = vex).
  ax ~(shared  = dirty).
  ax ~(dirty   = vex).
}

module* PROTOCOL
{
  protecting(DATA + FLAG)

  *[ Protocol ]*
  bop flag  : Index Protocol -> Flag    -- cache state
  bop cdata : Index Protocol -> Data    -- cache value
  bop mdata : Protocol -> Data         -- memory value
  bop read  : Index Protocol -> Protocol
  bop write : Index Data Protocol -> Protocol
  op init   : -> Protocol

  vars I J K : Index   vars M N : Data   var P : Protocol

** initial state
  eq flag(I, init) = invalid .

** write hit
  eq cdata(I, write(I,M,P)) = M .
  ceq cdata(J,write(I,M,P)) = cdata(J,P) if not(I == J).
  eq flag(J, write(J,M,P)) = dirty .
** invalidation
  ceq flag(J, write(I,M,P)) = invalid if not(I == J).
  eq mdata(write(I,M,P)) = mdata(P).

** read hit
  bceq read(I,P) = P if not(flag(I,P) == invalid).
  -- if there is a dirty copy Cj then
  eq cdata(I, read(I, write(J,M,P))) = M . -- Cj provides the missig block.
  eq mdata(read(I, write(J,M,P))) = mdata(P).
  ceq flag(I,read(I,write(J,M,P))) = shared if not(I == J).
  ceq flag(J,read(I,write(J,M,P))) = shared if not(I == J).
  -- if there is a clean copy Cj then
  ceq cdata(I,read(I,read(J,P))) = cdata(J,read(J,P)) if not(I == J).
  -- Cj provides the missing block
  ceq flag(I,read(I,read(J,P))) = shared if not(I == J).
  ceq flag(J,read(I,read(J,P))) = shared if not(I == J).
  -- and both end up shared
** independence
  beq read(I,read(I,P)) = read(I,P).
  ceq flag(I,read(J,read(K,P))) = flag(I, read(K,P))
      if not(I == J) and not(I == K).
  ceq cdata(I,read(J,P)) = cdata(I,P) if not(I == J).
  eq mdata(read(I,P)) = mdata(P).

** if there is no cached copy (i.e., only in initial state)
  eq cdata(I,read(I,init)) = mdata(init).
  eq flag(I,read(I,init)) = vex .
  eq mdata(read(I,init)) = mdata(init).
}

module PROOF
{
  protecting (PROTOCOL)

  pred P : Protocol .
  #define P(X:Protocol)
     ::= \A[I:Index, J:Index] flag(I,X) = shared & flag(J,X) = shared
         -> cdata(I,X) = cdata(J,X).

  op p : -> Protocol

  -- goal [GOAL]: P(p) .
  -- goal [GOAL]: P(init) .
  -- goal [GOAL]: \A[I:Index] P(read(I,p)) .
  -- goal [GOAL]: \A[I:Index,M:Data] P(write(I,M,p)) .
}

option reset
flag(quiet,on)
flag(hyper-res,on)
flag(unit-deletion,on)
flag(factor,on)
flag(kb2,on)
flag(universal-symmetry,on)
flag(dist-const,off)
flag(print-stats,on)
flag(print-proofs,on)

select PROOF
sos = { :SYSTEM-GOAL }
check safety P of p from init .

**
eof
**
$Id: cache.mod,v 1.2 2003-11-04 03:11:26 sawada Exp $
