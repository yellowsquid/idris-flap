module Inky.Decidable.Either

import Data.So
import Data.These

public export
Union : Type -> Type -> Bool -> Type
Union a b False = b
Union a b True = a

public export
record LazyEither (0 a, b : Type) where
  constructor Because
  does : Bool
  reason : Lazy (Union a b does)

%name LazyEither p, q

namespace Union
  public export
  map : {tag : Bool} -> (a -> c) -> (b -> d) -> Union a b tag -> Union c d tag
  map {tag = False} f g x = g x
  map {tag = True} f g x = f x

  public export
  not : {tag : Bool} -> Union a b tag -> Union b a (not tag)
  not {tag = False} x = x
  not {tag = True} x = x

  public export
  both :
    {tag1 : Bool} -> {tag2 : Lazy Bool} ->
    Union a b tag1 -> Lazy (Union c d tag2) ->
    Union (a, c) (Either b d) (tag1 && tag2)
  both {tag1 = True, tag2 = True} x y = (x, y)
  both {tag1 = True, tag2 = False} x y = Right y
  both {tag1 = False} x y = Left x

  public export
  first :
    {tag1 : Bool} -> {tag2 : Lazy Bool} ->
    Union a b tag1 -> Lazy (Union c d tag2) ->
    Union (Either a c) (b, d) (tag1 || tag2)
  first {tag1 = True} x y = Left x
  first {tag1 = False, tag2 = True} x y = Right y
  first {tag1 = False, tag2 = False} x y = (x, y)

  public export
  all :
    {tag1, tag2 : Bool} ->
    Union a b tag1 -> Union c d tag2 ->
    Union (a, c) (These b d) (tag1 && tag2)
  all {tag1 = True, tag2 = True} x y = (x, y)
  all {tag1 = True, tag2 = False} x y = That y
  all {tag1 = False, tag2 = True} x y = This x
  all {tag1 = False, tag2 = False} x y = Both x y

  public export
  any :
    {tag1, tag2 : Bool} ->
    Union a b tag1 -> Union c d tag2 ->
    Union (These a c) (b, d) (tag1 || tag2)
  any {tag1 = True, tag2 = True} x y = Both x y
  any {tag1 = True, tag2 = False} x y = This x
  any {tag1 = False, tag2 = True} x y = That y
  any {tag1 = False, tag2 = False} x y = (x, y)

public export
map : (a -> c) -> (b -> d) -> LazyEither a b -> LazyEither c d
map f g p = p.does `Because` Union.map f g p.reason

public export
not : LazyEither a b -> LazyEither b a
not p = not p.does `Because` Union.not p.reason

public export
both : LazyEither a b -> Lazy (LazyEither c d) -> LazyEither (a, c) (Either b d)
both p q = p.does && q.does `Because` Union.both p.reason q.reason

public export
first : LazyEither a b -> Lazy (LazyEither c d) -> LazyEither (Either a c) (b, d)
first p q = p.does || q.does `Because` Union.first p.reason q.reason

public export
all : LazyEither a b -> Lazy (LazyEither c d) -> LazyEither (a, c) (These b d)
all p q = p.does && q.does `Because` Union.all p.reason q.reason

public export
any : LazyEither a b -> Lazy (LazyEither c d) -> LazyEither (These a c) (b, d)
any p q = p.does || q.does `Because` Union.any p.reason q.reason

public export
so : (b : Bool) -> LazyEither (So b) (So $ not b)
so b = b `Because` if b then Oh else Oh

export autobind infixr 0 >=>

public export
andThen :
  {0 p, q : a -> Type} ->
  LazyEither a b -> ((x : a) -> LazyEither (p x) (q x)) ->
  LazyEither (x ** p x) (Either b (x ** q x))
andThen (True `Because` x) f = map (\px => (x ** px)) (\qx => Right (x ** qx)) (f x)
andThen (False `Because` y) f = False `Because` (Left y)

public export
(>=>) :
  {0 p, q : a -> Type} ->
  LazyEither a b -> ((x : a) -> LazyEither (p x) (q x)) ->
  LazyEither (x ** p x) (Either b (x ** q x))
(>=>) = andThen
