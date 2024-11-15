module Flap.Data.SnocList.Thinning

import Data.DPair
import Data.Nat
import Flap.Data.List
import Flap.Data.SnocList
import Flap.Data.SnocList.Var
import Flap.Data.SnocList.Quantifiers
import Flap.Decidable.Maybe

--------------------------------------------------------------------------------
-- Thinnings -------------------------------------------------------------------
--------------------------------------------------------------------------------

public export
data Thins : SnocList a -> SnocList a -> Type where
  Id : sx `Thins` sx
  Drop : sx `Thins` sy -> sx `Thins` sy :< x
  Keep : sx `Thins` sy -> sx :< x `Thins` sy :< x

%name Thins f, g, h

-- Basics

public export
indexPos : (f : sx `Thins` sy) -> (pos : Elem x sx) -> Elem x sy
indexPos Id pos = pos
indexPos (Drop f) pos = There (indexPos f pos)
indexPos (Keep f) Here = Here
indexPos (Keep f) (There pos) = There (indexPos f pos)

public export
index : (f : sx `Thins` sy) -> Var sx -> Var sy
index f i = toVar (indexPos f i.pos)

public export
(.) : sy `Thins` sz -> sx `Thins` sy -> sx `Thins` sz
Id . g = g
Drop f . g = Drop (f . g)
Keep f . Id = Keep f
Keep f . Drop g = Drop (f . g)
Keep f . Keep g = Keep (f . g)

-- Basic properties

export
indexPosInjective :
  (f : sx `Thins` sy) -> {i : Elem x sx} -> {j : Elem y sx} ->
  (0 _ : elemToNat (indexPos f i) = elemToNat (indexPos f j)) -> i = j
indexPosInjective Id prf = toNatInjective prf
indexPosInjective (Drop f) prf = indexPosInjective f (injective prf)
indexPosInjective (Keep f) {i = Here} {j = Here} prf = Refl
indexPosInjective (Keep f) {i = There i} {j = There j} prf =
  thereCong (indexPosInjective f $ injective prf)

export
indexPosComp :
  (f : sy `Thins` sz) -> (g : sx `Thins` sy) -> (pos : Elem x sx) ->
  indexPos (f . g) pos = indexPos f (indexPos g pos)
indexPosComp Id g pos = Refl
indexPosComp (Drop f) g pos = cong There (indexPosComp f g pos)
indexPosComp (Keep f) Id pos = Refl
indexPosComp (Keep f) (Drop g) pos = cong There (indexPosComp f g pos)
indexPosComp (Keep f) (Keep g) Here = Refl
indexPosComp (Keep f) (Keep g) (There pos) = cong There (indexPosComp f g pos)

-- Congruence ------------------------------------------------------------------

export
infix 6 ~~~

public export
data (~~~) : sx `Thins` sy -> sx `Thins` sz -> Type where
  IdId : Id ~~~ Id
  IdKeep : Id ~~~ f -> Id ~~~ Keep f
  KeepId : f ~~~ Id -> Keep f ~~~ Id
  DropDrop : f ~~~ g -> Drop f ~~~ Drop g
  KeepKeep : f ~~~ g -> Keep f ~~~ Keep g

%name Thinning.(~~~) prf

export
Reflexive (sx `Thins` sy) (~~~) where
  reflexive {x = Id} = IdId
  reflexive {x = Drop f} = DropDrop reflexive
  reflexive {x = Keep f} = KeepKeep reflexive

export
sym : f ~~~ g -> g ~~~ f
sym IdId = IdId
sym (IdKeep prf) = KeepId (sym prf)
sym (KeepId prf) = IdKeep (sym prf)
sym (DropDrop prf) = DropDrop (sym prf)
sym (KeepKeep prf) = KeepKeep (sym prf)

export
compIdentityRight : (f : sx `Thins` sy) -> f . Id ~~~ f
compIdentityRight Id = IdId
compIdentityRight (Drop f) = DropDrop (compIdentityRight f)
compIdentityRight (Keep f) = KeepKeep reflexive

export
(.indexPos) : f ~~~ g -> (pos : Elem x sx) -> indexPos f pos = indexPos g pos
(IdId).indexPos pos = Refl
(IdKeep prf).indexPos Here = Refl
(IdKeep prf).indexPos (There pos) = cong There $ prf.indexPos pos
(KeepId prf).indexPos Here = Refl
(KeepId prf).indexPos (There pos) = cong There $ prf.indexPos pos
(DropDrop prf).indexPos pos = cong There $ prf.indexPos pos
(KeepKeep prf).indexPos Here = Refl
(KeepKeep prf).indexPos (There pos) = cong There $ prf.indexPos pos

export
(.index) :
  {0 f, g : sx `Thins` sy} -> f ~~~ g -> (i : Var sx) -> index f i = index g i
prf.index ((%%) n {pos}) = irrelevantEq $ toVarCong $ prf.indexPos pos

-- Useful for Parsers ----------------------------------------------------------

public export
(<><) : ctx1 `Thins` ctx2 -> LengthOf bound -> ctx1 <>< bound `Thins` ctx2 <>< bound
f <>< Z = f
f <>< S len = Keep f <>< len

public export
dropFish : ctx1 `Thins` ctx2 -> LengthOf bound -> ctx1 `Thins` ctx2 <>< bound
dropFish f Z = f
dropFish f (S len) = dropFish (Drop f) len

public export
dropPos : (pos : Elem x ctx) -> dropElem ctx pos `Thins` ctx
dropPos Here = Drop Id
dropPos (There pos) = Keep (dropPos pos)

public export
dropAll : LengthOf sy -> sx `Thins` sx ++ sy
dropAll Z = Id
dropAll (S len) = Drop (dropAll len)

public export
keepAll : LengthOf sz -> sx `Thins` sy -> sx ++ sz `Thins` sy ++ sz
keepAll Z f = f
keepAll (S len) f = Keep (keepAll len f)

public export
append :
  sx `Thins` sz -> sy `Thins` sw ->
  {auto len : LengthOf sw} ->
  sx ++ sy `Thins` sz ++ sw
append f Id = keepAll len f
append f (Drop g) {len = S len} = Drop (append f g)
append f (Keep g) {len = S len} = Keep (append f g)

public export
assoc : LengthOf sz -> sx ++ (sy ++ sz) `Thins` (sx ++ sy) ++ sz
assoc Z = Id
assoc (S len) = Keep (assoc len)

public export
growLengthOf : sx `Thins` sy -> LengthOf sx -> LengthOf sy
growLengthOf Id len = len
growLengthOf (Drop f) len = S (growLengthOf f len)
growLengthOf (Keep f) (S len) = S (growLengthOf f len)

public export
thinLengthOf : sx `Thins` sy -> LengthOf sy -> LengthOf sx
thinLengthOf Id len = len
thinLengthOf (Drop f) (S len) = thinLengthOf f len
thinLengthOf (Keep f) (S len) = S (thinLengthOf f len)

public export
thinAll : sx `Thins` sy -> All p sy -> All p sx
thinAll Id env = env
thinAll (Drop f) (env :< px) = thinAll f env
thinAll (Keep f) (env :< px) = thinAll f env :< px

public export
splitL :
  {0 sx, sy, sz : SnocList a} ->
  LengthOf sz ->
  sx `Thins` sy ++ sz ->
  Exists (\sxA => Exists (\sxB => (sx = sxA ++ sxB, sxA `Thins` sy, sxB `Thins` sz)))
splitL Z f = Evidence sx (Evidence [<] (Refl, f, Id))
splitL (S len) Id = Evidence sy (Evidence sz (Refl, Id, Id))
splitL (S len) (Drop f) =
  let Evidence sxA (Evidence sxB (Refl, g, h)) = splitL len f in
  Evidence sxA (Evidence sxB (Refl, g, Drop h))
splitL (S len) (Keep f) =
  let Evidence sxA (Evidence sxB (Refl, g, h)) = splitL len f in
  Evidence sxA (Evidence (sxB :< _) (Refl, g, Keep h))

public export
splitR :
  {0 sx, sy, sz : SnocList a} ->
  LengthOf sy ->
  sx ++ sy `Thins` sz ->
  Exists (\sxA => Exists (\sxB => (sz = sxA ++ sxB, sx `Thins` sxA, sy `Thins` sxB)))
splitR Z f = Evidence sz (Evidence [<] (Refl, f, Id))
splitR (S len) Id = Evidence sx (Evidence sy (Refl, Id, Id))
splitR (S len) (Drop f) =
  let Evidence sxA (Evidence sxB (Refl, g, h)) = splitR (S len) f in
  Evidence sxA (Evidence (sxB :< _) (Refl, g, Drop h))
splitR (S len) (Keep f) =
  let Evidence sxA (Evidence sxB (Refl, g, h)) = splitR len f in
  Evidence sxA (Evidence (sxB :< _) (Refl, g, Keep h))

-- Strengthening ---------------------------------------------------------------

public export
data Skips : sx `Thins` sy -> Elem y sy -> Type where
  Here : Drop f `Skips` Here
  Also : f `Skips` i -> Drop f `Skips` There i
  There : f `Skips` i -> Keep f `Skips` There i

%name Skips skips

export
skipsSplit :
  {0 f : sx `Thins` sy} -> {0 i : Elem y sy} ->
  f `Skips` i -> (j : Elem x sx) -> i ~=~ indexPos f j -> Void
skipsSplit Here j prf = absurd @{HereThere} prf
skipsSplit (Also skips) j prf = skipsSplit skips j (thereInjective prf)
skipsSplit (There skips) Here prf = absurd @{ThereHere} prf
skipsSplit (There skips) (There j) prf = skipsSplit skips j (thereInjective prf)

public export
strengthen :
  (f : sx `Thins` sy) -> (i : Elem y sy) ->
  Proof (Elem y sx) (\j => i = indexPos f j) (f `Skips` i)
strengthen Id i = Just i `Because` Refl
strengthen (Drop f) Here = Nothing `Because` Here
strengthen (Drop f) (There i) =
  map id (\_, prf => cong There prf) Also $
  strengthen f i
strengthen (Keep f) Here = Just Here `Because` Refl
strengthen (Keep f) (There i) =
  map There (\_, prf => cong There prf) There $
  strengthen f i

export
dropPosSkips : (i : Elem x sx) -> dropPos i `Skips` i
dropPosSkips Here = Here
dropPosSkips (There i) = There (dropPosSkips i)

export
skipsDropPos : (i : Elem x sx) -> dropPos i `Skips` j -> i ~=~ j
skipsDropPos Here Here = Refl
skipsDropPos (There i) (There skips) = thereCong (skipsDropPos i skips)

-- Removal ---------------------------------------------------------------------

public export
punchOut :
  (f : sx `Thins` sy) -> (i : Elem x sx) ->
  dropElem sx i `Thins` dropElem sy (indexPos f i)
punchOut Id i = Id
punchOut (Drop f) i = Drop (punchOut f i)
punchOut (Keep f) Here = f
punchOut (Keep f) (There i) = Keep (punchOut f i)

export
punchOutHomo :
  (f : sx `Thins` sy) -> (i : Elem x sx) ->
  dropPos (indexPos f i) . punchOut f i ~~~ f . dropPos i
punchOutHomo Id i = compIdentityRight (dropPos i)
punchOutHomo (Drop f) i = DropDrop (punchOutHomo f i)
punchOutHomo (Keep f) Here = DropDrop (sym $ compIdentityRight f)
punchOutHomo (Keep f) (There i) = KeepKeep (punchOutHomo f i)

------------------------ -------------------------------------------------------
-- Renaming Coalgebras ---------------------------------------------------------
--------------------------------------------------------------------------------

public export
interface Rename (0 a : Type) (0 t : SnocList a -> Type) where
  rename :
    {0 sx, sy : SnocList a} -> sx `Thins` sy ->
    t sx -> t sy
  0 renameCong :
    {0 sx, sy : SnocList a} -> {0 f, g : sx `Thins` sy} -> f ~~~ g ->
    (x : t sx) -> rename f x = rename g x
  0 renameId : {0 sx : SnocList a} -> (x : t sx) -> rename Id x = x
  0 renameHomo :
    {0 sx, sy, sz : SnocList a} ->
    (f : sy `Thins` sz) -> (g : sx `Thins` sy) -> (x : t sx) ->
    rename f (rename g x) = rename (f . g) x
