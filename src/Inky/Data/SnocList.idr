module Inky.Data.SnocList

import public Data.SnocList
import public Data.SnocList.Operations

import Inky.Decidable.Maybe

public export
data LengthOf : SnocList a -> Type where
  Z : LengthOf [<]
  S : LengthOf sx -> LengthOf (sx :< x)

%name LengthOf len

public export
toNat : LengthOf sx -> Nat
toNat Z = Z
toNat (S len) = S (toNat len)

public export
lengthOfAppend : LengthOf sx -> LengthOf sy -> LengthOf (sx ++ sy)
lengthOfAppend len1 Z = len1
lengthOfAppend len1 (S len2) = S (lengthOfAppend len1 len2)

public export
lengthOf : (sx : SnocList a) -> LengthOf sx
lengthOf [<] = Z
lengthOf (sx :< x) = S (lengthOf sx)

export
lengthUnique : (len1, len2 : LengthOf sx) -> len1 = len2
lengthUnique Z Z = Refl
lengthUnique (S len1) (S len2) = cong S $ lengthUnique len1 len2

export
isSnoc : (sx : SnocList a) -> Proof (SnocList a, a) (\syy => sx = fst syy :< snd syy) (sx = [<])
isSnoc [<] = Nothing `Because` Refl
isSnoc (sx :< x) = Just (sx, x) `Because` Refl

public export
replicate : Nat -> a -> SnocList a
replicate 0 x = [<]
replicate (S n) x = replicate n x :< x

public export
lengthOfReplicate : (n : Nat) -> (0 x : a) -> LengthOf (replicate n x)
lengthOfReplicate 0 x = Z
lengthOfReplicate (S k) x = S (lengthOfReplicate k x)
