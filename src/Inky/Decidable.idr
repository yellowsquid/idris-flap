module Inky.Decidable

import public Inky.Decidable.Either

import Data.Bool
import Data.Either
import Data.Maybe
import Data.List
import Data.List1
import Data.List1.Properties
import Data.Nat
import Data.SnocList
import Data.So
import Data.These
import Data.Vect

import Decidable.Equality

public export
When : Type -> Bool -> Type
When a = Union a (Not a)

public export
Dec' : (0 _ : Type) -> Type
Dec' a = LazyEither a (Not a)

-- Operations ------------------------------------------------------------------

-- Conversion to Dec

public export
fromDec : Dec a -> Dec' a
fromDec (Yes prf) = True `Because` prf
fromDec (No contra) = False `Because` contra

public export
toDec : Dec' a -> Dec a
toDec (True `Because` prf) = Yes prf
toDec (False `Because` contra) = No contra

-- Negation

public export
notWhen : {b : Bool} -> a `When` b -> Not a `When` not b
notWhen = Union.map id (\prf, contra => contra prf) . Union.not

public export
notDec : Dec' a -> Dec' (Not a)
notDec p = not p.does `Because` notWhen p.reason

-- Maps

public export
mapWhen : (a -> a') -> (0 _ : a' -> a) -> {b : Bool} -> a `When` b -> a' `When` b
mapWhen f g = Union.map f (\contra, prf => void $ contra $ g prf)

public export
mapDec : (a -> b) -> (0 _ : b -> a) -> Dec' a -> Dec' b
mapDec f g = map f (\contra, prf => void $ contra $ g prf)

-- Conjunction

public export
andWhen : {b1, b2 :  Bool} -> a1 `When` b1 -> Lazy (a2 `When` b2) -> (a1, a2) `When` (b1 && b2)
andWhen x y =
  Union.map {d = Not (a1, a2)} id (\x, (y, z) => either (\f => f y) (\g => g z) x) $
  Union.both x y

public export
andDec : Dec' a -> Dec' b -> Dec' (a, b)
andDec p q = (p.does && q.does) `Because` andWhen p.reason q.reason

-- Disjunction

public export
elseWhen : {b1, b2 : Bool} -> a1 `When` b1 -> Lazy (a2 `When` b2) -> Either a1 a2 `When` (b1 || b2)
elseWhen x y =
  Union.map {b = (Not a1, Not a2)} id (\(f, g) => either f g) $
  Union.first x y

public export
elseDec : Dec' a -> Dec' b -> Dec' (Either a b)
elseDec p q = (p.does || q.does) `Because` elseWhen p.reason q.reason

public export
orWhen : {b1, b2 : Bool} -> a1 `When` b1 -> a2 `When` b2 -> These a1 a2 `When` (b1 || b2)
orWhen x y =
  Union.map {b = (Not a1, Not a2)} id (\(f, g) => these f g (const g)) $
  Union.any x y

public export
orDec : Dec' a -> Dec' b -> Dec' (These a b)
orDec p q = (p.does || q.does) `Because` orWhen p.reason q.reason

-- Dependent Versions

public export
thenDec :
  (0 b : a -> Type) ->
  (0 unique : (x, y : a) -> b x -> b y) ->
  Dec' a -> ((x : a) -> Dec' (b x)) -> Dec' (x ** b x)
thenDec b unique p f =
  map id
    (\contra, (x ** prf) =>
      either
        (\contra => contra x)
        (\yContra => void $ snd yContra $ unique x (fst yContra) prf)
        contra) $
  andThen p f

-- Equality --------------------------------------------------------------------

public export
interface DecEq' (0 a : Type) where
  does : (x, y : a) -> Bool
  reason : (x, y : a) -> (x = y) `When` (does x y)

  decEq : (x, y : a) -> Dec' (x = y)
  decEq x y = does x y `Because` reason x y

public export
whenCong : (0 _ : Injective f) => {b : Bool} -> (x = y) `When` b -> (f x = f y) `When` b
whenCong = mapWhen (\prf => cong f prf) (\prf => inj f prf)

public export
whenCong2 :
  (0 _ : Biinjective f) =>
  {b1, b2 : Bool} ->
  (x = y) `When` b1 -> (z = w) `When` b2 ->
  (f x z = f y w) `When` (b1 && b2)
whenCong2 p q =
  mapWhen {a = (_, _)} (\prfs => cong2 f (fst prfs) (snd prfs)) (\prf => biinj f prf) $
  andWhen p q

[ToEq] DecEq' a => Eq a where
  x == y = does x y

-- Instances -------------------------------------------------------------------

public export
DecEq' () where
  does _ _ = True
  reason () () = Refl

public export
DecEq' Bool where
  does b1 b2 = b1 == b2

  reason False False = Refl
  reason False True = absurd
  reason True False = absurd
  reason True True = Refl

public export
DecEq' Nat where
  does k n = k == n

  reason 0 0 = Refl
  reason 0 (S n) = absurd
  reason (S k) 0 = absurd
  reason (S k) (S n) = whenCong (reason k n)

public export
(d : DecEq' a) => DecEq' (Maybe a) where
  does x y = let _ = ToEq @{d} in x == y

  reason Nothing Nothing = Refl
  reason Nothing (Just y) = absurd
  reason (Just x) Nothing = absurd
  reason (Just x) (Just y) = whenCong (reason x y)

public export
(d1 : DecEq' a) => (d2 : DecEq' b) => DecEq' (Either a b) where
  does x y = let _ = ToEq @{d1} in let _ = ToEq @{d2} in x == y

  reason (Left x) (Left y) = whenCong (reason x y)
  reason (Left x) (Right y) = absurd
  reason (Right x) (Left y) = absurd
  reason (Right x) (Right y) = whenCong (reason x y)


public export
(d1 : DecEq' a) => (d2 : DecEq' b) => DecEq' (These a b) where
  does x y = let _ = ToEq @{d1} in let _ = ToEq @{d2} in x == y

  reason (This x) (This y) = whenCong (reason x y)
  reason (That x) (That y) = whenCong (reason x y)
  reason (Both x z) (Both y w) = whenCong2 (reason x y) (reason z w)
  reason (This x) (That y) = \case Refl impossible
  reason (This x) (Both y z) = \case Refl impossible
  reason (That x) (This y) = \case Refl impossible
  reason (That x) (Both y z) = \case Refl impossible
  reason (Both x z) (This y) = \case Refl impossible
  reason (Both x z) (That y) = \case Refl impossible

public export
(d1 : DecEq' a) => (d2 : DecEq' b) => DecEq' (a, b) where
  does x y = let _ = ToEq @{d1} in let _ = ToEq @{d2} in x == y

  reason (x, y) (z, w) = whenCong2 (reason x z) (reason y w)

public export
(d : DecEq' a) => DecEq' (List a) where
  does x y = let _ = ToEq @{d} in x == y

  reason [] [] = Refl
  reason [] (y :: ys) = absurd
  reason (x :: xs) [] = absurd
  reason (x :: xs) (y :: ys) = whenCong2 (reason x y) (reason xs ys)

public export
(d : DecEq' a) => DecEq' (List1 a) where
  does x y = let _ = ToEq @{d} in x == y

  reason (x ::: xs) (y ::: ys) = whenCong2 (reason x y) (reason xs ys)

public export
(d : DecEq' a) => DecEq' (SnocList a) where
  does x y = let _ = ToEq @{d} in x == y

  reason [<] [<] = Refl
  reason [<] (sy :< y) = absurd
  reason (sx :< x) [<] = absurd
  reason (sx :< x) (sy :< y) =
    rewrite sym $ andCommutative (does sx sy) (does x y) in
    whenCong2 (reason sx sy) (reason x y)

-- Other Primitives

%unsafe
public export
primitiveEq : Eq a => (x, y : a) -> (x = y) `When` (x == y)
primitiveEq x y with (x == y)
  _ | True = believe_me (Refl {x})
  _ | False = \prf => believe_me {b = Void} ()

%unsafe
public export
[FromEq] Eq a => DecEq' a where
  does x y = x == y
  reason x y = primitiveEq x y

public export
DecEq' Int where
  does = does @{FromEq}
  reason = reason @{FromEq}

public export
DecEq' Char where
  does = does @{FromEq}
  reason = reason @{FromEq}

public export
DecEq' Integer where
  does = does @{FromEq}
  reason = reason @{FromEq}

public export
DecEq' String where
  does = does @{FromEq}
  reason = reason @{FromEq}
