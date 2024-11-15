module Inky.Data.Context.Var

import Data.DPair
import Data.Singleton
import Inky.Data.Context
import Inky.Data.SnocList.Elem
import Inky.Decidable
import Inky.Decidable.Maybe

export
prefix 2 %%, %%%

public export
record Var (ctx : Context a) (x : a) where
  constructor (%%)
  0 name : String
  {auto pos : Elem (name :- x) ctx}

%name Var i, j, k

public export
toVar : Elem (n :- x) ctx -> Var ctx x
toVar pos = (%%) n {pos}

public export
ThereVar : Var ctx x -> Var (ctx :< ny) x
ThereVar i = toVar (There i.pos)

export
Show (Var ctx x) where
  show i = show (elemToNat i.pos)

-- Basic Properties ---------------------------------------------------------

export
toVarCong :
  {0 n, k : String} -> {0 x, y : a} ->
  {0 i : Elem (n :- x) ctx} -> {0 j : Elem (k :- y) ctx} ->
  i ~=~ j -> toVar i ~=~ toVar j
toVarCong Refl = Refl

export
posCong : {0 i : Var ctx x} -> {0 j : Var ctx y} -> i = j -> i.pos ~=~ j.pos
posCong Refl = Refl

export
toVarInjective :
  {0 n, k : String} -> {0 x, y : a} ->
  {i : Elem (n :- x) ctx} -> {j : Elem (k :- y) ctx} ->
  (0 _ : toVar i ~=~ toVar j) -> i ~=~ j
toVarInjective prf = toNatInjective $ toNatCong $ posCong prf

export
posInjective : {i : Var ctx x} -> {j : Var ctx y} -> (0 _ : i.pos ~=~ j.pos) -> i ~=~ j
posInjective {i = %% x} {j = %% y} prf = irrelevantEq $ toVarCong prf

-- Decidable Equality ----------------------------------------------------------

public export
decEq : (i : Var ctx x) -> (j : Var ctx y) -> Dec' (i ~=~ j)
decEq i j =
  mapDec (\prf => irrelevantEq $ posInjective prf) posCong $
  decEq i.pos j.pos

-- Weakening -------------------------------------------------------------------

public export
wknL : (len : LengthOf ctx2) => Var ctx1 x -> Var (ctx1 ++ ctx2) x
wknL i = toVar $ wknL i.pos len

public export
wknR : Var ctx1 x -> Var (ctx2 ++ ctx1) x
wknR i = toVar $ wknR i.pos

public export
split : {auto len : LengthOf ctx2} -> Var (ctx1 ++ ctx2) x -> Either (Var ctx1 x) (Var ctx2 x)
split i = bimap toVar toVar $ split len i.pos

public export
lift :
  {auto len : LengthOf ctx3} ->
  (forall x. Var ctx1 x -> Var ctx2 x) ->
  Var (ctx1 ++ ctx3) x -> Var (ctx2 ++ ctx3) x
lift f = either (wknL {len} . f) wknR . split {len}

-- Names -----------------------------------------------------------------------

export
nameOf : {ctx : Context a} -> (i : Var ctx x) -> Singleton i.name
nameOf i = [| (nameOf i.pos).name |]

-- Search ----------------------------------------------------------------------

export
lookup : (n : String) -> (ctx : Context a) -> Maybe (x ** Var ctx x)
lookup n ctx =
  case decLookup n ctx of
    Just x `Because` pos => Just (x ** toVar pos)
    Nothing `Because` _ => Nothing

namespace Search
  public export
  data VarPos : String -> a -> (ctx : Context a) -> Type where
    [search ctx]
    Here : VarPos n x (ctx :< (n :- x))
    There : VarPos n x ctx -> VarPos n x (ctx :< ky)

  %name VarPos pos

  public export
  toElem : VarPos n x ctx -> Elem (n :- x) ctx
  toElem Here = Here
  toElem (There pos) = There (toElem pos)

  public export
  (%%%) : (0 n : String) -> {auto pos : VarPos n x ctx} -> Var ctx x
  (%%%) n {pos} = toVar $ toElem pos
