-- From: Razvan Diaconescu <diacon@jaist.ac.jp>
-- Date: Sat, 4 Oct 97 05:53:26 GMT
-- Message-Id: <9710040553.AA11275@is27e0s07.jaist.ac.jp>
-- To: sawada@sra.co.jp
-- Subject:  bug in parameterised modules concerning sharing ?
-- Cc: diacon@stoilow.imar.ro, ishisone@sra.co.jp, kokichi@jaist.ac.jp,
--         mitihiro@jaist.ac.jp, nakagawa@sra.co.jp, ogata@jaist.ac.jp,
--         s_iida@jaist.ac.jp
-- Content-Type: text
-- Content-Length: 3296

-- Dear Toshimi,

-- I have the feeling that some inadequate sharing might happening in the
-- implementation of parameterised modules.

-- Consider:

mod* MON {
  -- protecting(TRIV)
  [ Elt ]

  op _;_ : Elt Elt -> Elt {assoc}
  op null :  ->  Elt
  
  eq m:Elt ; null = m .   eq null ; m:Elt = m .
}

mod* VCT-MON (S :: MON, V :: MON) {
  
  op _^_ : Elt.S Elt.V -> Elt.V

  vars s s' : Elt.S
  vars v v' : Elt.V 
    
  eq s ^ (v ; v') = (s ^ v) ; (s ^ v') .
  eq (s ; s') ^ v = s ^ (s' ^ v) .
  eq null ^ v = v .
  eq s ^ null = null .
}

-- The system give some strange parsing errors for the equations, but it
-- should not be any ambiguity. Also, when I do *describe* I see only one
-- sort Elt and one operator _;_ and one null. Is MON shared? If yes,
-- then this is wrong since I cannot properly instantiate it to two
-- different modules like

view plus from MON to NAT {
  sort Elt -> Nat, 
  op _;_ -> _+_,  
  op null -> 0 
}
view times from MON to NAT {
  sort Elt -> NzNat,
  op _;_ -> _*_,
  op null -> 1 
}

mod* VCT-NAT { protecting(VCT-MON(times,plus)) }

-- In fact this gives a strange warning:

-- -- defining module* VCT-NAT
-- [Warning]: redefining module VCT-NAT 
-- [Warning]: in instantiation of module,  combined view has inconsistent mappings for: Elt
--             images are: NzNat
--               and: Nat,,,,,,_,,*._* done.

-- I think the sharing principle should be applied only to "ground"
-- modules (instantiated), not to parameters.

-- This problem can even result in a strange error too. Take for example
-- the initial specification

mod! VCT-MON-FREE (S :: MON,  extending V :: MON) {

  op _^_ : Elt.S Elt.V -> Elt.V

  vars s s' : Elt.S
  vars v v' : Elt.V 
    
  eq s ^ (v ; v') = (s ^ v) ; (s ^ v') .
  eq (s ; s') ^ v = s ^ (s' ^ v) .
  eq null ^ v = v .
  eq s ^ null = null .
}

-- which has the monomial expression as models. V should be in extending
-- mode since the denotations are free extensions which generate these
-- monomials in the sort Nat. But CafeOBJ gives an error:

-- CafeOBJ> describe VCT-MON-FREE(times,plus) .
-- [Warning]: in instantiation of module,  combined view has inconsistent mappings for: Elt
--             images are: NzNat
--               and: Nat,
-- [Error]: module NAT is already imported into VCT-MON-FREE(S, V)(S <= times,
--              V <= plus)
--          with the effective mode : protecting,
--          this conflicts to the new mode : extending.
-- -- could not evaluate instantiation: VCT-MON-FREE(S <= times, V <= 
--    plus)

-- In this case there is no conflict, extending overides protecting
-- in the denotations.

-- BTW, I think there should be absolutely no support from the system
-- about importation/paramteterisation modes, these are purely semantic
-- declarations. There is no concept of confilct either, it just may
-- happen that the denoation (i.e., the set of models) is empty (hence
-- inconsistent specification). But this is just anotehr story. For
-- example in this case, if I write "protecting V" instead of "extending V"
-- CafeOBJ gives only the warning but the denotation is empty. 

-- I apologise for the long message and for the big amount of module
-- system related messages, but I am now wotrking full time on the
-- structuring specification chapter of Cafe Rep and slowly slowly get to
-- all corners of the module system implementation from the
-- design/semantics perspective. 

-- Best regards,
-- Razvan
