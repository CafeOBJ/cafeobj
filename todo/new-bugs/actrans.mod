--> ** ** ** TEST ** ** ** 
--> Elt:  0, 1 or nil.
--> String: a sequence of elements of Elt. 
--> e.g. (0 1 0 1 0 0 nil)
--> List: a multiset of strings. 
--> e.g. (0 1 0 1 0 0 nil) | (0 1 0 nil) | (1 nil) .
--> TRANSITION RULE:
--> for a given list, if the head of one string is same with the head of another string,
--> then the transition rule consumes those two heads.
--> ** ** ** ** ** ** ** **
mod! TEST{
  [Elt < String < List]
  ops 0 1 nil : -> Elt
  op __ : String String -> String {assoc}
  op _|_ : List List -> List {assoc comm}
  trans (X:Elt S:String) | (X:Elt S':String) | L:List => S | S' | L .
}
--> Try to prove that all 0 and 1 of a given list are consumed in all possible transition paths. 
select TEST .
exec (0 1 nil) | (0 1 nil) | (0 0 nil) . 
red (0 1 nil) | (0 1 nil) | (0 0 nil) ==>! L:List .
--> Only (nil | nil | nil) has been found, 
--> and it should imply all 0 and 1 should be consumed in ALL possible paths.
--> However there exists a case in which 
--> all 0 and 1 are not consumed (as follows)
exec (0 1 nil) | (0 0 nil) | (0 1 nil) .
red (0 1 nil) | (0 0 nil) | (0 1 nil) ==>! L:List .
--> Only (nil | nil | 0 0 nil) has been found.
