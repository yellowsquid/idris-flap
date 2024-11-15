module Inky.Data.SnocList.Var

import public Inky.Data.SnocList.Elem

import Data.Singleton
import Inky.Data.SnocList
import Inky.Decidable

export
prefix 2 %%

public export
record Var (sx : SnocList a) where
  constructor (%%)
  0 name : a
  {auto pos : Elem name sx}

%name Var i, j, k

public export
toVar : Elem x sx -> Var sx
toVar pos = (%%) x {pos}

public export
ThereVar : Var sx -> Var (sx :< x)
ThereVar i = toVar (There i.pos)

export
Show (Var sx) where
  show i = show (elemToNat i.pos)

-- Basic Properties ---------------------------------------------------------

export
toVarCong : {0 i : Elem x sx} -> {0 j : Elem y sx} -> i = j -> toVar i = toVar j
toVarCong Refl = Refl

export
posCong : {0 i, j : Var sx} -> i = j -> i.pos ~=~ j.pos
posCong Refl = Refl

export
toVarInjective : {i : Elem x sx} -> {j : Elem y sx} -> (0 _ : toVar i = toVar j) -> i = j
toVarInjective prf = toNatInjective $ toNatCong $ posCong prf

export
posInjective : {i : Var sx} -> {j : Var sx} -> (0 _ : i.pos ~=~ j.pos) -> i = j
posInjective {i = %% x} {j = %% y} prf = irrelevantEq $ toVarCong prf

-- Decidable Equality ----------------------------------------------------------

public export
DecEq' (Var {a} sx) where
  does i j = (decEq i.pos j.pos).does
  reason i j =
    mapWhen (\prf => irrelevantEq $ posInjective prf) posCong $
    (decEq i.pos j.pos).reason

-- Weakening -------------------------------------------------------------------

public export
wknL : (len : LengthOf sy) => Var sx -> Var (sx ++ sy)
wknL i = toVar $ wknL i.pos len

public export
wknR : Var sx -> Var (sy ++ sx)
wknR i = toVar $ wknR i.pos

public export
split : {auto len : LengthOf sy} -> Var (sx ++ sy) -> Either (Var sx) (Var sy)
split i = bimap toVar toVar $ split len i.pos

public export
lift1 :
  (Var sx -> Var sy) ->
  Var (sx :< x) -> Var (sy :< y)
lift1 f ((%%) x {pos = Here}) = %% y
lift1 f ((%%) name {pos = There i}) = ThereVar (f $ %% name)

-- Names -----------------------------------------------------------------------

export
nameOf : {sx : SnocList a} -> (i : Var sx) -> Singleton i.name
nameOf i = nameOf i.pos

-- Search ----------------------------------------------------------------------

export
lookup : DecEq' a => (x : a) -> (sx : SnocList a) -> Maybe (Var sx)
lookup x sx = toVar <$> lookup x sx
