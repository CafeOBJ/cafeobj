-- From: Razvan Diaconescu <diacon@jaist.ac.jp>
-- Date: Mon, 1 Jun 98 21:25:06 JST
-- Message-Id: <9806011225.AA05667@is27e0s07.jaist.ac.jp>
-- To: sawada@sra.co.jp
-- Subject:  bug in reduction
-- Cc: kokichi@jaist.ac.jp, s_iida@jaist.ac.jp
-- Content-Type: text
-- Content-Length: 1417

-- Dear Toshimi,

-- I think found a bad bug related to CafeOBJ reductions.
-- Consider the following example:

mod! TRIV+(X :: TRIV) {
  op err :  -> ?Elt 
}

mod* BUF {
  protecting(TRIV+)

  *[ Buf ]*

  op init :  -> Buf 
  op put : Elt Buf -> Buf
  bop get_ : Buf -> ?Elt
  bop take_ : Buf -> Buf
  op empty? : Buf -> Bool   {coherent}

  var E : Elt
  var B : Buf 
        
  eq empty?(init) = true .
  cq empty?(take B) = true if empty?(B) .
  eq empty?(put(E, B)) = false .

  -- 
  bceq take put(E, B) = put(E, take B) if not empty?(B) .
  bceq take(put(E, B)) = B             if empty?(B) .

  ceq get B = err if empty?(B) .
  cq get put(E, B) = E if empty?(B) .
  cq get put(E, B) = get B if not empty?(B) .
}

open BUF
ops b b' : -> Buf .
op e : -> Elt .
beq b = b' .
eq empty?(b') = false .
red get(take(put(e, b))) .

eof

The result is very surprising:

get put(e,take b') : ?Elt
(0.000 sec for parse, 7 rewrites(0.040 sec), 38 matches)

because of the occurence of b'. The beq should not be applied in this
reduction since put is neither bop nor coherent. So there is no chance
for b' to appear in the result.  I would be grateful that besides
repairing this bug you will also explain me what it was, since I could
not understand from the trace and I have a strange feeling that it
might not be related to coherence but to how conditional rewriting is
implemented (but this is just a feeling).

With thanks,
Razvan
