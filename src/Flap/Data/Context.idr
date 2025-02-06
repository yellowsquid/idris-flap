module Flap.Data.Context

import public Flap.Data.Assoc
import public Flap.Data.SnocList

import Flap.Data.SnocList.Quantifiers

-- Contexts --------------------------------------------------------------------

public export
Context : Type -> Type
Context a = SnocList (Assoc a)

public export
(.names) : Context a -> SnocList String
(.names) = map name

public export
(.values) : Context a -> SnocList a
(.values) = map value

export
mapNames : (0 f : a -> b) -> (ctx : Context a) -> (map (map f) ctx).names = ctx.names
mapNames f [<] = Refl
mapNames f (ctx :< nx) = cong (:< nx.name) $ mapNames f ctx

-- Construction ----------------------------------------------------------------

public export
fromAll : {sx : SnocList String} -> All (Assoc0 a) sx -> Context a
fromAll [<] = [<]
fromAll {sx = sx :< n} (ctx :< (_ :- x)) = fromAll ctx :< (n :- x)

export
fromAllNames : {sx : SnocList String} -> (ctx : All (Assoc0 a) sx) -> (fromAll ctx).names = sx
fromAllNames [<] = Refl
fromAllNames {sx = sx :< n} (ctx :< (k :- x)) = cong (:< n) $ fromAllNames ctx
