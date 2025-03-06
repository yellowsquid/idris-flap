module Flap.Parser.Sequence

public export
record Stage (state : Type) where
  constructor MkStage
  family : state -> Type
  update : Maybe ((s : state) -> family s -> state)

public export
doUpdate :
  {0 a : state -> Type} ->
  Maybe ((s : state) -> a s -> state) -> (s : state) -> a s -> state
doUpdate Nothing s x = s
doUpdate (Just f) s x = f s x

public export
(.run) : (stage : Stage state) -> (s : state) -> stage .family s -> state
stage .run = doUpdate (stage .update)

public export
data Sequence :
  (s : state) -> List (Stage state) -> Type
  where
  Nil : Sequence s []
  (::) :
    (x : stage .family s) ->
    Sequence (stage .run s x) seq ->
    Sequence s (stage :: seq)
