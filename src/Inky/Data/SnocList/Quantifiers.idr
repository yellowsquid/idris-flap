module Inky.Data.SnocList.Quantifiers

import public Data.SnocList.Quantifiers

import Data.List.Quantifiers
import Inky.Data.SnocList
import Inky.Data.SnocList.Elem
import Inky.Decidable

public export
(<><) : All p xs -> All p sx -> All p (xs <>< sx)
sxp <>< [] = sxp
sxp <>< (px :: pxs) = (sxp :< px) <>< pxs

public export
head : All p (sx :< x) -> p x
head (prfs :< px) = px

public export
tail : All p (sx :< x) -> All p sx
tail (prfs :< px) = prfs

public export
HSnocList : SnocList Type -> Type
HSnocList = All id

public export
all :
  ((x : a) -> LazyEither (p x) (q x)) ->
  (sx : SnocList a) -> LazyEither (All p sx) (Any q sx)
all f [<] = True `Because` [<]
all f (sx :< x) =
  map (\prfs => snd prfs :< fst prfs) (either Here There) $
  both (f x) (all f sx)

public export
tabulate : LengthOf sx -> (forall x. Elem x sx -> p x) -> All p sx
tabulate Z f = [<]
tabulate (S len) f = tabulate len (f . There) :< f Here

public export
data Pairwise : (a -> a -> Type) -> SnocList a -> Type where
  Lin : Pairwise r [<]
  (:<) : Pairwise r sx -> All (flip r x) sx -> Pairwise r (sx :< x)
