**
** cache coherence problem by A.Mori
**

module* DATA
{
  [ Index Data ]
}
module! FLAG
{
  [Flag]
  ops invalid vex dirty shared : -> Flag -- { constr }
  -- vex == valid exclusive
}

module* PROTOCOL
{
  protecting (BOOL + DATA + FLAG)
  *[Protocol]*
  bop flag  : Index Protocol -> Flag    -- cache state
  bop cdata : Index Protocol -> Data    -- cache value
  bop mdata : Protocol -> Data         -- memory value
  bop read  : Index Protocol -> Protocol
  bop write : Index Data Protocol -> Protocol
  op init   : -> Protocol

  vars I J K : Index
  vars M N : Data
  var P : Protocol
  -- initial state
  eq flag(I, init) = invalid .
  -- write
  eq cdata(I, write(I,M,P)) = M .
  ceq cdata(J,write(I,M,P)) = cdata(J,P) if not(I == J) .
  eq flag(J, write(J,M,P)) = dirty .
    -- invalidation
  ceq flag(J, write(I,M,P)) = invalid if not(I == J) .
  eq mdata(write(I,M,P)) = mdata(P) .
  -- read
    -- read hit
  bceq read(I,P) = P if not(flag(I,P) == invalid) .
    -- if there is a dirty copy Cj then
  eq cdata(I, read(I, write(J,M,P))) = M . -- Cj provides the missig block.
  eq mdata(read(I, write(J,M,P))) = mdata(P) .
  ceq flag(I,read(I,write(J,M,P))) = shared if not(I == J) .
  ceq flag(J,read(I,write(J,M,P))) = shared if not(I == J) .
    -- if there is a clean copy Cj then
  ceq cdata(I,read(I,read(J,P))) = cdata(J,read(J,P)) if not(I == J) .
    -- Cj provides the missing block
  ceq flag(I,read(I,read(J,P))) = shared if not(I == J) .
  ceq flag(J,read(I,read(J,P))) = shared if not(I == J) .
  -- independence
  beq read(I,read(I,P)) = read(I,P) .
  ceq flag(I,read(J,read(K,P))) = flag(I, read(K,P))
      if not(I == J) and not(I == K) .
  ceq cdata(I,read(J,P)) = cdata(I,P) if not(I == J) .
  eq mdata(read(I,P)) = mdata(P) .
  -- if there is no cached copy (i.e., only in initial state)
  eq cdata(I,read(I,init)) = mdata(init) .
  eq flag(I,read(I,init)) = vex .
  eq mdata(read(I,init)) = mdata(init) .
}

module PROOF
{
  protecting (PROTOCOL)
  protecting (FOPL-CLAUSE)
  ** need additional axioms for some inductive theorems.
  ** no junk
  ax flag(I:Index, P:Protocol) = invalid | 
     flag(I,P)                 = vex     |
     flag(I,P)                 = shared  |
     flag(I,P)                 = dirty   .
  ** want to be explicit, all states are different from each other.
  ** no confusion
  -- ax ~(invalid = vex).
  -- ax ~(invalid = dirty).
  -- ax ~(invalid = shared).
  -- ax ~(shared  = vex) .
  -- ax ~(shared  = dirty) .
  -- ax ~(dirty   = vex).

  ** definition of invariant:
  -- use P(X) as macro like manner by using "#dfine" command:
  pred P : Protocol .         -- the predicate for invariant.
  #define P(X:Protocol)
     ::= \A[I:Index, J:Index] flag(I,X) = shared & flag(J,X) = shared
         -> cdata(I,X) = cdata(J,X) .
}

** ============
** start proof
** ============
** there are 3 goals.
-- (1) P must be satisfied at the initial sate:
-- P(init) .
-- (2,3) also after applying read and write oprations.
-- \A[S:Protocol]\A[I:Index] P(S) -> P(read(I,S)) .
-- \A[S:Protocol]\A[I:Index, M:Data] P(S) -> P(write(I,M,S)) .
** (1)

** preset pignose option flags & parameters
option reset
flag (quiet,on)
flag (auto,on)
flag (universal-symmetry,on)
flag (dist-const,on)
flag (new-variable-name,off)
param (max-weight,14)
** save the option-set as `ccp-quiet-set'
save-option ccp-quiet-set

option reset
flag (auto,on)
flag (universal-symmetry,on)
flag (dist-const,on)
param (max-weight,14)
save-option ccp-set

option = ccp-quiet-set


open PROOF .

-- **> show P(init)
-- goal P(init) .
-- resolve .
-- close
-- **

-- open PROOF .
-- **> show P(X) is invariant w.r.t. read operation.
-- goal \A[S:Protocol]\A[I:Index] P(S) -> P(read(I,S)) .
-- ** it's safe to reset options because some parameters may
-- ** have been changed during the previous run in automatic manner
-- ** (max-weight, for example).
-- ** use preset option set `ccp-set'.
-- option = ccp-set
-- -- flag(no-back-demod,on)
-- resolve .
-- close

-- open PROOF .
-- **> show P(X) is invariant w.r.t. write operation.
-- goal \A[S:Protocol]\A[I:Index, M:Data] P(S) -> P(write(I,M,S)) .
-- option = ccp-set
-- resolve .
-- close

-- **> the same job can be done in full automatic by `check' command.
-- --> it's cool!
open PROOF .
option = ccp-quiet-set
check safety P from init
close

**
eof
--
$Id
