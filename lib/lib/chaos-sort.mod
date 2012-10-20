**
** $Id: chaos-sort.mod,v 1.1 2007-01-26 10:39:12 sawada Exp $
**
mod! CHAOS:SORT
{
  protecting(CHAOS:FORM)
  ** sort reference
  op ?sort : String -> ChaosSort
  op ?sort : String Module -> ChaosSort
  op sort-name : ChaosSort -> Id
  ** predicates
  op sort< : ChaosSort ChaosSort -> Bool
  op sort= : ChaosSort ChaosSort -> Bool
  op is-visible : ChaosSort -> Bool
  op is-hidden  : ChaosSort -> Bool
  op is-error   : ChaosSort -> Bool
  op is-and     : ChaosSort -> Bool
  op is-or      : ChaosSort -> Bool
  op is-inhabited : ChaosSort -> Bool
  ** sort constructors
  op :sort : String -> Sort
  op :hsort : String -> Sort
  op :and-sort : ChaosList -> AndSort
  op :or-sort  : ChaosList -> OrSort
  ** subsort relation
  op :sort-rel : ChaosList ChaosList -> ChaosList
  op :hsort-rel : ChaosList ChaosList -> ChaosList
  ** sort order
  op ?supers : ChaosSort -> ChaosList
  op ?subs   : ChaosSort -> ChaosList

  vars X Y Z : ChaosSort
  eq ?sort(S:String) = #!(find-qual-sort S) .
  eq ?sort(S:String, M:Module) = #!(find-qual-sort S M) .
  eq sort-name(X) = #!(sort-name X) .
  eq sort<(X, Y) = #!(sort<* X Y) .
  eq sort=(X, Y) = #!(sort=* X Y) .
  eq is-visible(X) = #!(sort-is-visible X) .
  eq is-hidden(X) = #!(sort-is-hidden X) .
  eq is-inhabited(X) = #!(sort-is-inhabited X) .
}
**
eof
