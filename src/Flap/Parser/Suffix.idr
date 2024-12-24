module Flap.Parser.Suffix

import Control.WellFounded
import Data.So
import Flap.Data.List

||| Relation between lists where the first is a suffix of the second.
|||
||| @param equal whether the two lists may be equal
||| @param xs suffix list
||| @param ys original list which contains `xs`
|||
||| # Examples
||| ```
||| prf1 : SuffixOf True [1, 2] [1, 2]
||| prf1 = Refl
|||
||| prf2 : SuffixOf b [5, 6, 7] [4, 5, 6, 7]
||| prf2 = Step Refl
||| ```
public export
data SuffixOf : (equal: Bool) -> (xs, ys : List a) -> Type where
  ||| Two lists are equal and hence the first is a suffix of the second.
  Refl : SuffixOf True xs xs
  ||| Consing an element onto the second list preserves being a suffix.
  |||
  ||| As `y :: ys` is definitely not equal to `xs`, the equalness of the lists
  ||| can be arbitrary.
  Step : SuffixOf b1 xs ys -> SuffixOf b2 xs (y :: ys)

%name SuffixOf prf

export
Uninhabited (SuffixOf False xs []) where
  uninhabited Refl impossible
  uninhabited (Step prf) impossible

||| Change the equalness of a `SuffixOf` proof.
export
wkn : (0 f : So b1 -> So b2) -> (prf : SuffixOf b1 xs ys) -> SuffixOf b2 xs ys
wkn f Refl = rewrite soToEq (f Oh) in Refl
wkn f (Step prf) = Step prf

export
trans : SuffixOf b1 xs ys -> SuffixOf b2 ys zs -> SuffixOf (b2 && b1) xs zs
trans prf1 Refl = prf1
trans prf1 (Step prf2) = Step (trans prf1 prf2)

export
append : (len : LengthOf xs) -> SuffixOf (toNat len == 0) ys (xs ++ ys)
append Z = Refl
append (S len) = Step (append len)

public export
record Irrelevant (a : Type) where
  constructor Squash
  0 unsquash : a

export
WellFounded (List a) (Irrelevant .: SuffixOf False) where
  wellFounded xs = Access (acc xs)
    where
    0 invert : forall x, xs, ys. SuffixOf False ys (x :: xs) -> (b ** SuffixOf b ys xs)
    invert (Step {b1} prf) = (b1 ** prf)

    acc :
      (xs, ys : List a) ->
      Irrelevant (SuffixOf False ys xs) ->
      Accessible (Irrelevant .: SuffixOf False) ys
    acc [] ys (Squash prf) = void $ absurd prf
    acc (x :: xs) ys (Squash prf) =
      let 0 inverted = invert prf in
      Access (\zs, prf' =>
        acc xs zs $ Squash $
        wkn (snd . soAnd {b = False}) $
        trans prf'.unsquash inverted.snd)
