module Flap.Data.SnocList.Elem

import public Data.SnocList.Elem

import Data.DPair
import Data.Nat
import Data.Singleton
import Flap.Decidable
import Flap.Decidable.Maybe
import Flap.Data.Assoc
import Flap.Data.List
import Flap.Data.SnocList

export
[HereThere] Uninhabited (Here {sx, x} ~=~ There {sx = sy, x = z, y} i) where
  uninhabited Refl impossible

export
[ThereHere] Uninhabited (There {sx = sy, x = z, y} i ~=~ Here {sx, x}) where
  uninhabited Refl impossible

export
thereCong :
  {0 i : Elem x sx} -> {0 j : Elem y sx} -> i = j ->
  There {y = z} i = There {y = z} j
thereCong Refl = Refl

export
toNatCong : {0 i : Elem x sx} -> {0 j : Elem y sx} -> i = j -> elemToNat i = elemToNat j
toNatCong Refl = Refl

export
thereInjective :
  {0 i : Elem x sx} -> {0 j : Elem y sx} -> There {y = z} i = There {y = z} j ->
  i = j
thereInjective Refl = Refl

export
toNatInjective : {i : Elem x sx} -> {j : Elem y sx} -> (0 _ : elemToNat i = elemToNat j) -> i = j
toNatInjective {i = Here} {j = Here} prf = Refl
toNatInjective {i = There i} {j = There j} prf with (toNatInjective {i} {j} $ injective prf)
  toNatInjective {i = There i} {j = There .(i)} prf | Refl = Refl

-- Decidable Equality -----------------------------------------------------------

public export
reflectEq : (i : Elem x sx) -> (j : Elem y sx) -> (i = j) `When` (elemToNat i == elemToNat j)
reflectEq Here Here = Refl
reflectEq Here (There j) = absurd @{HereThere}
reflectEq (There i) Here = absurd @{ThereHere}
reflectEq (There i) (There j) = mapWhen thereCong thereInjective $ reflectEq i j

public export
decEq : (i : Elem x sx) -> (j : Elem y sx) -> Dec' (i = j)
decEq i j = (elemToNat i == elemToNat j) `Because` reflectEq i j

-- Weakening -------------------------------------------------------------------

public export
wknL : Elem x sx -> LengthOf sy -> Elem x (sx ++ sy)
wknL pos Z = pos
wknL pos (S len) = There (wknL pos len)

public export
wknR : Elem x sx -> Elem x (sy ++ sx)
wknR Here = Here
wknR (There pos) = There (wknR pos)

public export
split : LengthOf sy -> Elem x (sx ++ sy) -> Either (Elem x sx) (Elem x sy)
split Z pos = Left pos
split (S len) Here = Right Here
split (S len) (There pos) = mapSnd There $ split len pos

public export
wknL' : Elem x sx -> LengthOf xs -> Elem x (sx <>< xs)
wknL' i Z = i
wknL' i (S len) = wknL' (There i) len

-- Lookup ----------------------------------------------------------------------

export
nameOf : {sx : SnocList a} -> Elem x sx -> Singleton x
nameOf Here = Val x
nameOf (There pos) = nameOf pos

-- Search ----------------------------------------------------------------------

export
lookup : DecEq' a => (x : a) -> (sx : SnocList a) -> Maybe (Elem x sx)
lookup x [<] = Nothing
lookup x (sx :< y) =
  case decEq x y of
    True `Because` Refl => Just Here
    False `Because` _ => There <$> lookup x sx

public export
decLookup : (n : String) -> (sx : SnocList (Assoc a)) -> DecWhen a (\x => Elem (n :- x) sx)
decLookup n [<] = Nothing `Because` (\_ => absurd)
decLookup n (sx :< (k :- x)) =
  map (maybe x id) leftToRight rightToLeft $
  first (decEq n k) (decLookup n sx)
  where
  leftToRight :
    forall n. (m : Maybe a) ->
    maybe (n = k) (\y => Elem (n :- y) sx) m ->
    Elem (n :- maybe x Basics.id m) (sx :< (k :- x))
  leftToRight Nothing Refl = Here
  leftToRight (Just _) prf = There prf

  rightToLeft :
    forall n.
    (Not (n = k), (y : a) -> Not (Elem (n :- y) sx)) ->
    (y : a) -> Not (Elem (n :- y) (sx :< (k :- x)))
  rightToLeft (neq, contra) _ Here = neq Refl
  rightToLeft (neq, contra) y (There i) = contra y i
