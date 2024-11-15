module Inky.Decidable.Maybe

import Data.Maybe
import Data.These
import Inky.Decidable.Either

public export
WhenJust : (a -> Type) -> Type -> Maybe a -> Type
WhenJust p b (Just x) = p x
WhenJust p b Nothing = b

public export
record Proof (0 a : Type) (0 p : a -> Type) (0 b : Type) where
  constructor Because
  does : Maybe a
  reason : WhenJust p b does

%name Proof p, q

public export
DecWhen : (0 a : Type) -> (0 p : a -> Type) -> Type
DecWhen a p = Proof a p ((x : a) -> Not (p x))

-- Operations ------------------------------------------------------------------

public export
(.forget) : Proof a p b -> LazyEither (x ** p x) b
(Just x `Because` px).forget = True `Because` (x ** px)
(Nothing `Because` y).forget = False `Because` y

public export
map :
  (f : a -> a') ->
  ((x : a) -> p x -> q (f x)) ->
  (b -> b') ->
  Proof a p b -> Proof a' q b'
map f g h (Just x `Because` px) = Just (f x) `Because` g x px
map f g h (Nothing `Because` y) = Nothing `Because` h y

export autobind infixr 0 >=>

public export
andThen :
  {0 q : a -> a' -> Type} ->
  {0 b' : a -> Type} ->
  Proof a p b ->
  ((x : a) -> Proof a' (q x) (b' x)) ->
  Proof (a, a') (\xy => (p (fst xy), uncurry q xy)) (Either b (x ** (p x, b' x)))
andThen (Just x `Because` px) f = map (x,) (\_ => (px,)) (\y => Right (x ** (px, y))) $ f x
andThen (Nothing `Because` y) f = Nothing `Because` Left y

public export
(>=>) :
  {0 q : a -> a' -> Type} ->
  {0 b' : a -> Type} ->
  Proof a p b ->
  ((x : a) -> Proof a' (q x) (b' x)) ->
  Proof (a, a') (\xy => (p (fst xy), uncurry q xy)) (Either b (x ** (p x, b' x)))
(>=>) = andThen

public export
andThen' :
  {0 a' : a -> Type} ->
  {0 q : (x : a) -> a' x -> Type} ->
  {0 b' : a -> Type} ->
  Proof a p b ->
  ((x : a) -> Proof (a' x) (q x) (b' x)) ->
  Proof (x ** a' x) (\xy => (p (fst xy), q (fst xy) (snd xy))) (Either b (x ** (p x, b' x)))
andThen' (Just x `Because` px) f =
  map (\y => (x ** y)) (\_ => (px,)) (\y => Right (x ** (px, y))) $ f x
andThen' (Nothing `Because` y) f = Nothing `Because` Left y

public export
all :
  Proof a p b ->
  Proof a' q b' ->
  Proof (a, a') (\xy => (p (fst xy), q (snd xy))) (These b b')
all (Just x `Because` px) (Just y `Because` py) = Just (x, y) `Because` (px, py)
all (Just x `Because` px) (Nothing `Because` y) = Nothing `Because` That y
all (Nothing `Because` x) q =
  Nothing `Because`
    case q of
      (Just _ `Because` _) => This x
      (Nothing `Because` y) => Both x y

public export
first :
  Proof a p b ->
  Lazy (Proof c q d) ->
  Proof (Either a c) (either p q) (b, d)
first (Just x `Because` px) q = Just (Left x) `Because` px
first (Nothing `Because` x) (Just y `Because` py) = Just (Right y) `Because` py
first (Nothing `Because` x) (Nothing `Because` y) = Nothing `Because` (x, y)

namespace Either
  public export
  andThen :
    (0 c : a -> Type) ->
    (0 p : (x : a) -> c x -> Type) ->
    (0 d : a -> Type) ->
    LazyEither a b -> ((x : a) -> Proof (c x) (p x) (d x)) ->
    Proof (x ** c x) (\xy => p (fst xy) (snd xy)) (Either b (x ** d x))
  andThen _ _ _ (True `Because` x) f = map (\y => (x ** y)) (\_ => id) (\y => Right (x ** y)) (f x)
  andThen _ _ _ (False `Because` y) f = Nothing `Because` Left y

  public export
  first :
    LazyEither a b ->
    Lazy (Proof c p d) ->
    Proof (Maybe c) (maybe a p) (b, d)
  first (True `Because` x) q = Just Nothing `Because` x
  first (False `Because` x) (Just y `Because` py) = Just (Just y) `Because` py
  first (False `Because` x) (Nothing `Because` y) = Nothing `Because` (x, y)

  public export
  all : LazyEither a b -> Lazy (Proof c p d) -> Proof c (\x => (a, p x)) (These b d)
  all (True `Because` x) (Just y `Because` py) = Just y `Because` (x, py)
  all (True `Because` x) (Nothing `Because` y) = Nothing `Because` That y
  all (False `Because` x) q =
    Nothing `Because`
      case q of
        (Just y `Because` _) => This x
        (Nothing `Because` y) => Both x y

namespace Elim
  export autobind infixr 0 >=>

  public export
  andThen :
    {0 q, r : a -> Type} ->
    Proof a p b -> ((x : a) -> LazyEither (q x) (r x)) ->
    LazyEither (x ** (p x, q x)) (Either b (x ** (p x, r x)))
  andThen (Just x `Because` px) f = map (\qx => (x ** (px, qx))) (\rx => Right (x ** (px, rx))) (f x)
  andThen (Nothing `Because` y) f = False `Because` Left y

  public export
  (>=>) :
    {0 q, r : a -> Type} ->
    Proof a p b -> ((x : a) -> LazyEither (q x) (r x)) ->
    LazyEither (x ** (p x, q x)) (Either b (x ** (p x, r x)))
  (>=>) = andThen

public export
pure : (x : a) -> LazyEither (b x) c -> Proof a b c
pure x (True `Because` y) = Just x `Because` y
pure x (False `Because` y) = Nothing `Because` y
