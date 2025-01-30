module Flap.Parser.Sequence

public export
record Stage (state : Type) where
  constructor MkStage
  family : state -> Type
  update : (s : state) -> family s -> state

public export
data Sequence :
  (s : state) -> List (Stage state) -> Type
  where
  Nil : Sequence s []
  (::) :
    (x : stage .family s) ->
    Sequence (stage .update s x) seq ->
    Sequence s (stage :: seq)
