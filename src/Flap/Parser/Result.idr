module Flap.Parser.Result

import public Flap.Parser.Suffix
import public Data.List1
import Data.So

public export
data Result : (e : Type) -> (xs : List a) -> (equal : Bool) -> (t : Type) -> Type where
  Ok : (res : t) -> (ys : List a) -> (0 prf : SuffixOf equal ys xs) -> Result e xs equal t
  SoftErr : (errs : List1 e) -> (ys : List a) -> (0 prf : SuffixOf equal ys xs) -> Result e xs equal t
  Err : (errs : List1 e) -> Result e xs equal t

export
Functor (Result e xs equal) where
  map f (Ok res ys prf) = Ok (f res) ys prf
  map f (SoftErr errs ys prf) = SoftErr errs ys prf
  map f (Err errs) = Err errs

export
pure : {xs : List a} -> t -> Result e xs True t
pure res = Ok res xs Refl

export
(<*>) :
  Result e xs equal (t1 -> t2) ->
  ({ys : List a} -> {auto 0 prf : SuffixOf equal ys xs} -> Result e ys equal' t1) ->
  Result e xs (equal && equal') t2
Ok res ys prf <*> f =
  case f {ys} of
    Ok res' zs prf' => Ok (res res') zs (trans prf' prf)
    SoftErr errs zs prf' => SoftErr errs zs (trans prf' prf)
    Err errs => Err errs
SoftErr errs ys prf <*> f =
  case f {ys} of
    Ok _ zs prf' => SoftErr errs zs (trans prf' prf)
    SoftErr errs' zs prf' => SoftErr (errs ++ errs') zs (trans prf' prf)
    Err errs' => Err (errs ++ errs')
Err errs <*> f = Err errs

export infixl 3 <**>

export
(<**>) :
  Result e xs equal t1 ->
  ({ys : List a} -> {auto 0 prf : SuffixOf equal ys xs} -> Result e ys equal' t2) ->
  Result e xs (equal && equal') (t1, t2)
f <**> g = MkPair <$> f <*> g

export
(>>=) :
  Result e xs equal t1 ->
  (t1 -> {ys : List a} -> {auto 0 prf : SuffixOf equal ys xs} -> Result e ys equal' t2) ->
  Result e xs (equal && equal') t2
Ok res ys prf >>= f =
  case f res {prf} of
    Ok res' zs prf' => Ok res' zs (trans prf' prf)
    SoftErr errs zs prf' => SoftErr errs zs (trans prf' prf)
    Err errs => Err errs
SoftErr errs ys prf >>= f = Err errs
Err errs >>= f = Err errs

export
wkn : (0 f : So b1 -> So b2) -> Result e xs b1 t -> Result e xs b2 t
wkn f (Ok res ys prf) = Ok res ys (wkn f prf)
wkn f (SoftErr errs ys prf) = SoftErr errs ys (wkn f prf)
wkn f (Err e) = Err e

public export
record ParseT (state, error, tok : Type) (equal : Bool) (t : state -> Type) where
  constructor MkParseT
  runParser : (s : state) -> (xs : List tok) -> Result error xs equal (t s)
