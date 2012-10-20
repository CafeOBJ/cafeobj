mod* GRAPH {
  [ Node Edge ]

  ops (s_) (t_) : Edge -> Node 
}

mod! PATH1 (X :: GRAPH) {
  [ Edge < Path ]

  op _;_ : ?Path ?Path -> ?Path  { assoc }
  ops (s_) (t_) : Path -> Node 

  pred _ is Path : ?Path

  var E : Edge 
  var P : Path
  var EP : ?Path 

  eq P is Path = true .
  ceq (E ; EP) is Path = true   if (EP is Path) and (s EP) == (t E) .
  ceq s(E ; EP) = s(E) if (E ; EP) is Path .
  ceq t(E ; EP) = t(EP) if (E ; EP) is Path .
}

