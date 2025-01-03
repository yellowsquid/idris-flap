module Flap.Parser.Types

-- import public Control.Algebra
import Data.So
import Flap.Parser.Core

public export
interface Monoid t => Set (0 i : Type) t where
  singleton : i -> t
  member : i -> t -> Bool
  intersect : t -> t -> t
  toList : t -> List i

public export
peek :
  Set i t =>
  (env : All (Assoc0 $ const t) free) ->
  Parser i nil locked free a -> t
public export
peekChain :
  Set i t =>
  (env : All (Assoc0 $ const t) free) ->
  ParserChain i nil locked free a -> t
public export
peekAll :
  Set i t =>
  (env : All (Assoc0 $ const t) free) ->
  {0 nils : List Bool} ->
  All (\nil => Parser i nil locked free a) nils ->
  All (const t) nils

peek env (Var x) = (indexAll x.pos env).value
peek env (Lit text) = singleton text
peek env (Seq ps) = peekChain env ps
peek env (OneOf ps) = foldMap id (forget $ peekAll env ps)
peek env (Fix x p) = peek env p
peek env (Map f p) = peek env p
peek env (WithBounds p) = peek env p

peekChain env [] = neutral
peekChain env ((::) {nil1 = False} p ps) = peek env p
peekChain env ((::) {nil1 = True} p ps) = peek env p <+> peekChain env ps

peekAll env [] = []
peekAll env (p :: ps) = peek env p :: peekAll env ps

public export
follow :
  Set i t =>
  (penv1 : All (Assoc0 $ const t) locked) ->
  (penv2 : All (Assoc0 $ const t) free) ->
  (fenv1 : All (Assoc0 $ const t) locked) ->
  (fenv2 : All (Assoc0 $ const t) free) ->
  Parser i nil locked free a -> t
public export
followChain :
  Set i t =>
  (penv1 : All (Assoc0 $ const t) locked) ->
  (penv2 : All (Assoc0 $ const t) free) ->
  (fenv1 : All (Assoc0 $ const t) locked) ->
  (fenv2 : All (Assoc0 $ const t) free) ->
  ParserChain i nil locked free a -> t
public export
followAll :
  Set i t =>
  (penv1 : All (Assoc0 $ const t) locked) ->
  (penv2 : All (Assoc0 $ const t) free) ->
  (fenv1 : All (Assoc0 $ const t) locked) ->
  (fenv2 : All (Assoc0 $ const t) free) ->
  {0 nils : List Bool} ->
  All (\nil => Parser i nil locked free a) nils ->
  t

follow penv1 penv2 fenv1 fenv2 (Var x) = (indexAll x.pos fenv2).value
follow penv1 penv2 fenv1 fenv2 (Lit text) = neutral
follow penv1 penv2 fenv1 fenv2 (Seq ps) = followChain penv1 penv2 fenv1 fenv2 ps
follow penv1 penv2 fenv1 fenv2 (OneOf ps) = followAll penv1 penv2 fenv1 fenv2 ps
follow penv1 penv2 fenv1 fenv2 (Fix x p) =
  -- Conjecture: The fix point converges after one step
  -- Proof:
  --   - we always add information
  --   - no step depends on existing information
  follow (penv1 :< (x :- peek penv2 p)) penv2 (fenv1 :< (x :- neutral)) fenv2 p
follow penv1 penv2 fenv1 fenv2 (Map f p) = follow penv1 penv2 fenv1 fenv2 p
follow penv1 penv2 fenv1 fenv2 (WithBounds p) = follow penv1 penv2 fenv1 fenv2 p

followChain penv1 penv2 fenv1 fenv2 [] = neutral
followChain penv1 penv2 fenv1 fenv2 ((::) {nil1 = False, nil2} p ps) =
  let xs = followChain [<] (penv2 ++ penv1) [<] (fenv2 ++ fenv1) ps in
  foldMap {t = List} id
    ( if nil2
      then [xs, peekChain (penv2 ++ penv1) ps, follow penv1 penv2 fenv1 fenv2 p]
      else [xs])
followChain penv1 penv2 fenv1 fenv2 ((::) {nil1 = True, nil2} p ps) =
  let xs = followChain penv1 penv2 fenv1 fenv2 ps in
  foldMap {t = List} id
    ( if nil2
      then [xs, peekChain penv2 ps, follow penv1 penv2 fenv1 fenv2 p]
      else [xs])

followAll penv1 penv2 fenv1 fenv2 [] = neutral
followAll penv1 penv2 fenv1 fenv2 (p :: ps) =
  follow penv1 penv2 fenv1 fenv2 p <+>
  followAll penv1 penv2 fenv1 fenv2 ps

public export
data Err : (i : Type) -> Type where
  AltAmbiguous : List (List i) -> Err i
  SeqAmbiguous : List (List i) -> Err i
  ChainPos : Nat -> Err i -> Err i
  Branch : Nat -> Err i -> Err i

public export
enumerate : List a -> List (Nat, a)
enumerate = reverse . fst . foldl (\(acc, n), x => ((n, x) :: acc, S n)) ([], 0)

public export
disjoint : (set : Set i t) => List t -> Bool
disjoint [] = True
disjoint (xs :: xss) =
  all (null . toList @{set} . intersect @{set} xs) xss && disjoint @{set} xss

public export
collectTypeErrs :
 (set : Set i t) =>
 (penv1 : All (Assoc0 $ const t) locked) ->
 (penv2 : All (Assoc0 $ const t) free) ->
 (fenv1 : All (Assoc0 $ const t) locked) ->
 (fenv2 : All (Assoc0 $ const t) free) ->
 Parser i nil locked free a ->
 List (Err i)

public export
collectChainTypeErrs:
 (set : Set i t) =>
 (penv1 : All (Assoc0 $ const t) locked) ->
 (penv2 : All (Assoc0 $ const t) free) ->
 (fenv1 : All (Assoc0 $ const t) locked) ->
 (fenv2 : All (Assoc0 $ const t) free) ->
 ParserChain i nil locked free a ->
 List (List (Err i))

public export
collectAllTypeErrs:
 Set i t =>
 (penv1 : All (Assoc0 $ const t) locked) ->
 (penv2 : All (Assoc0 $ const t) free) ->
 (fenv1 : All (Assoc0 $ const t) locked) ->
 (fenv2 : All (Assoc0 $ const t) free) ->
 {0 nils : List Bool} ->
 All (\nil => Parser i nil locked free a) nils ->
 List (List (Err i))

collectTypeErrs penv1 penv2 fenv1 fenv2 (Var j) = []
collectTypeErrs penv1 penv2 fenv1 fenv2 (Lit text) = []
collectTypeErrs penv1 penv2 fenv1 fenv2 (Seq ps) =
  let errs = collectChainTypeErrs penv1 penv2 fenv1 fenv2 ps in
  foldMap (\(n, es) => map (ChainPos n) es) $ enumerate errs
collectTypeErrs penv1 penv2 fenv1 fenv2 (OneOf ps) =
  let errs = collectAllTypeErrs penv1 penv2 fenv1 fenv2 ps in
  let peeked = forget $ peekAll penv2 ps in
  (if disjoint @{set} peeked then [] else [AltAmbiguous $ map toList peeked]) ++
  foldMap (\(n, es) => map (Branch n) es) (enumerate errs)
collectTypeErrs penv1 penv2 fenv1 fenv2 (Fix x p) =
  let peeked = peek penv2 (Fix x p) in
  let followed = follow penv1 penv2 fenv1 fenv2 (Fix x p) in
  collectTypeErrs
    (penv1 :< (x :- peeked))
    penv2
    (fenv1 :< (x :- followed))
    fenv2
    p
collectTypeErrs penv1 penv2 fenv1 fenv2 (Map f p) = collectTypeErrs
  penv1 penv2 fenv1 fenv2 p
collectTypeErrs penv1 penv2 fenv1 fenv2 (WithBounds p) =
  collectTypeErrs penv1 penv2 fenv1 fenv2 p

collectChainTypeErrs penv1 penv2 fenv1 fenv2 [] = []
collectChainTypeErrs penv1 penv2 fenv1 fenv2 ((::) {nil1 = False} p ps) =
  let sets = [follow penv1 penv2 fenv1 fenv2 p, peekChain (penv2 ++ penv1) ps] in
  (  (if disjoint @{set} sets then [] else [SeqAmbiguous $ map toList sets])
  ++ collectTypeErrs penv1 penv2 fenv1 fenv2 p
  )
  :: collectChainTypeErrs [<] (penv2 ++ penv1) [<] (fenv2 ++ fenv1) ps
collectChainTypeErrs penv1 penv2 fenv1 fenv2 ((::) {nil1 = True} p ps) =
  let sets = [follow penv1 penv2 fenv1 fenv2 p, peekChain penv2 ps] in
  (  (if disjoint @{set} sets then [] else [SeqAmbiguous $ map toList sets])
  ++ collectTypeErrs penv1 penv2 fenv1 fenv2 p
  )
  :: collectChainTypeErrs penv1 penv2 fenv1 fenv2 ps

collectAllTypeErrs penv1 penv2 fenv1 fenv2 [] = []
collectAllTypeErrs penv1 penv2 fenv1 fenv2 (p :: ps) =
  collectTypeErrs penv1 penv2 fenv1 fenv2 p :: collectAllTypeErrs penv1 penv2 fenv1 fenv2 ps
