** -*- Mode:CafeOBJ -*-
-- =============================================================================
-- An example definition of Labled Transition System.
-- NOTE: the current implementation does not support parameterization,
--       thus we fix the sort for labels & state.
--
-- =============================================================================
require state ./state
-- -----------------------------------------------------------------------------
-- LTS : Labeled Transition System
-- -----------------------------------------------------------------------------
module LTS {
  -- Set : set of states.
  protecting (STATE-SET) 
  
  -- we use built-in Identifier for Labels
  [ Identifier < Label ]
  
  signature {
    [ Label < LabelSeq ]
    op empty-label : -> LabelSeq
    op _^_ : LabelSeq LabelSeq -> LabelSeq
    attr _^_ { r-assoc id: empty-label }
    -- Tras     : transition rule
    -- TransSet : setf of transition rules
    [ Trans < TransSet ]
    op _[_]->_ : State Label State -> Trans
    attr _[_]->_ { prec: 0 }
    op empty-trans : -> TransSet
    op _|_ : TransSet TransSet -> TransSet
    attr _|_ { r-assoc id: empty-trans }
  }
  -- Definition of class Lts:
  class Lts {
    current : Set			 -- current status of Lts
      rules   : TransSet		 -- set of transition rules
  }

  signature {				 -- Behaviour of Lts
    -- 1 step state transition
    op transOne : Label Lts -> Lts
    op transOne : LabelSeq Lts -> Lts 
    -- state transition according to a given sequenceof labels:
    op trans : LabelSeq Lts -> Lts
    attr trans/2 { strat: (1 2 0) }
    ** support functions
    -- nextState : returns possible set of states reachable from current status.
    op nextState : LabelSeq Set TransSet -> Set
    op nextState : Label Set TransSet -> Set 
    op nextStateAux : Label Set TransSet Set -> Set
  }

  axioms {				 -- Behaviour of Lts -- 
    var  Id     : ObjectId   var CId    : ClassLts
    vars L L'   : Label      var LL     : LabelSeq
    vars S S'   : State      vars CS SS : Set
    vars R Ts   : TransSet    
    -- ----------------------------------------------
    eq nextState(L, CS, R) = nextStateAux(L,CS,R,{ nil }) .
    eq nextState(empty-label, CS, R) = CS .
    eq nextStateAux(L, CS, empty-trans, SS) = SS .
    eq nextStateAux(L, CS, S[L']-> S' | Ts, SS)
       = if (S in CS) and (L == L') 
	 then nextStateAux(L, CS, Ts, { S' } U SS)
         else nextStateAux(L, CS, Ts, SS) fi .
    ** NOTE: we omit empty transition for simplifying the problem.
    trans transOne(L, < Id : CId | current = CS, rules = R >)
      => < Id : CId | current = nextState(L, CS, R), rules = R > .
    trans transOne(empty-label, LTS:Lts) => LTS .
    trans trans(L ^ LL, LTS:Lts) => trans(LL, transOne(L, LTS)) .
    trans trans(empty-label, LTS:Lts) => LTS .
  }
}



-- =============================================================================
-- NFA : Nondeterministic Finite Automata
-- =============================================================================

module NFA {
  extending (LTS)
    
  class Nfa [Lts] {
    start : Set			 -- initial state
    final : Set			 -- final state
  }

  op trans : LabelSeq Nfa -> Nfa
    
    -- Additional operations on Nfa
  op finalState? : Nfa -> Bool		 -- checks Nfa is in final state
  attr finalState?/1 { strat: (1 0) }

  op accepts?    : LabelSeq Nfa -> Bool	 -- acceptance check 

  -- Axioms ------------------------------------------------
  -- 
  var Id   : ObjectId      var CId  : ClassNfa
  var SS   : Set           var Aux  : Attributes
  var NFA  : Nfa           var LSeq : LabelSeq

  eq finalState?(NFA) = (current(NFA) & final(NFA)) =/= ({ nil }) .
  eq accepts?(LSeq, NFA) = finalState?(trans(LSeq, NFA)) .

}


provide lts
--
eof
**
$Id: lts.mod,v 1.1.1.1 2003-06-19 08:30:16 sawada Exp $
--

