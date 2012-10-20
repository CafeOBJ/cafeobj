** -*- Mode:CafeOBJ -*-

" This is an example for multi line comment.
  you can "

module FOO { " this is an example"
 [ X ] "this is a
           sort of aho "
 op _+_ : X X -> X { assoc } "this
                              is also"
 signature { "this is a test comment.
              multi line comment ." }
 axioms {
   var X : X "sort of "
   eq X + X = X . " this is also"
 }
}

module BAR {
 protecting (STRING) "this does not introduce
             ambiguity."
 op trans : String -> String
 eq trans("aho") = "baka" .
}

 
eof
**
$Id: multi-comment.mod,v 1.1.1.1 2003-06-19 08:30:16 sawada Exp $
--
