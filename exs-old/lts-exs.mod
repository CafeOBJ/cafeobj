** -*- Mode:CafeOBJ -*-
--
-- parse < Ex1 : Lts | current = { A, B, C}, 
--                    rules = ( A[p]-> B | A[q]-> B | B[r]-> B | B[s]-> C |
--                              C[t]-> B | C[u]-> C | C[v]-> A | C[w]-> A ) > .

-- exec nextState(q, {A, B, C}, ( A[p]-> B | A[q]-> B )) .
require lts ./lts

select LTS
exec delete < Ex1 : Lts > .
exec makeLts(Ex1, (current = { A },
		   rules = ( A[p]-> B | A[q]-> B | B[r]-> B | B[s]-> C |
		             C[t]-> B | C[u]-> C | C[v]-> A | C[w]-> A ))) .	 

exec set-current( < Ex1 : Lts >, { C } ) .
exec transOne(v, < Ex1 : Lts >) .

exec set-current( < Ex1 : Lts >, { A } ) .
exec trans(p,  < Ex1 : Lts >) .

exec set-current( < Ex1 : Lts > , { A } ) .
exec trans(p ^ r ^ s ^ v , < Ex1 : Lts >) .

--> Some example reduction in NFA .
select NFA
exec delete < Nfa-1 : Nfa > .
exec in NFA : makeNfa( Nfa-1, ( start = { S0 }, 
			        final = { S3 }, 
			        current = { S0 }, 
			        rules = ( S0[a]-> S0 | S0[a]-> S1 | S0[b]-> S0 | 
				    	  S1[b]-> S2 | S2[b]-> S3 ) )) .

exec trans(a ^ b ^ b ,< Nfa-1 : Nfa > ) .

exec set-current ( < Nfa-1 : Nfa >, { S0 } ) .
exec accepts? (a ^ b ^ a ^ b ^ b , < Nfa-1 : Nfa >) .
--
eof
**
$Id: lts-exs.mod,v 1.1.1.1 2003-06-19 08:30:16 sawada Exp $
