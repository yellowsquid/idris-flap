module Flap.Parser.Types

import Data.So
import Flap.Parser.Core

public export
interface Monoid t => Set (0 tok : Type) t | t where
  singleton : tok -> t
  member    : tok -> t -> Bool
  intersect : t -> t -> t
  disjoint  : t -> t -> Bool
  toList    : t -> List tok

  disjoint x y = null $ toList $ intersect x y

public export
allDisjoint : Set tok t => List t -> Bool
allDisjoint []        = True
allDisjoint (x :: xs) = all (disjoint x) xs && allDisjoint xs

public export
peek :
  Set tok t =>
  (env : All (Assoc0 $ const t) free) ->
  Parser state error tok nil locked free a -> t
public export
peekChain :
  Set tok t =>
  (env : All (Assoc0 $ const t) free) ->
  ParserChain state error tok nil locked free a -> t
public export
peekAll :
  Set tok t =>
  (env : All (Assoc0 $ const t) free) ->
  {0 nils : List Bool} ->
  All (\nil => Parser state error tok nil locked free a) nils ->
  All (const t) nils

peek env (Var x) = (indexAll x.pos env).value
peek env (Lit text) = singleton text
peek env (Seq ps) = peekChain env ps
peek env (OneOf ps) = foldMap id (forget $ peekAll env ps)
peek env (Fix x p) = peek env p
peek env (Map f p) = peek env p
peek env (WithBounds p) = peek env p
peek env (Forget f p) = peek [<] p

peekChain env [] = neutral
peekChain env (Update {nil1 = False} p f ps) = peek env p
peekChain env (Update {nil1 = True} p f ps) = peek env p <+> peekChain env ps

peekAll env [] = []
peekAll env (p :: ps) = peek env p :: peekAll env ps

public export
follow :
  Set tok t =>
  (penv1 : All (Assoc0 $ const t) locked) ->
  (penv2 : All (Assoc0 $ const t) free) ->
  (fenv1 : All (Assoc0 $ const t) locked) ->
  (fenv2 : All (Assoc0 $ const t) free) ->
  Parser state error tok nil locked free a -> t
public export
followChain :
  Set tok t =>
  (penv1 : All (Assoc0 $ const t) locked) ->
  (penv2 : All (Assoc0 $ const t) free) ->
  (fenv1 : All (Assoc0 $ const t) locked) ->
  (fenv2 : All (Assoc0 $ const t) free) ->
  ParserChain state error tok nil locked free a -> t
public export
followAll :
  Set tok t =>
  (penv1 : All (Assoc0 $ const t) locked) ->
  (penv2 : All (Assoc0 $ const t) free) ->
  (fenv1 : All (Assoc0 $ const t) locked) ->
  (fenv2 : All (Assoc0 $ const t) free) ->
  {0 nils : List Bool} ->
  All (\nil => Parser state error tok nil locked free a) nils ->
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
follow penv1 penv2 fenv1 fenv2 (Forget f p) = follow [<] [<] [<] [<] p

followChain penv1 penv2 fenv1 fenv2 [] = neutral
followChain penv1 penv2 fenv1 fenv2 (Update {nil1 = False, nil2} p f ps) =
  let xs = followChain [<] (penv2 ++ penv1) [<] (fenv2 ++ fenv1) ps in
  foldMap {t = List} id
    ( if nil2
      then [xs, peekChain (penv2 ++ penv1) ps, follow penv1 penv2 fenv1 fenv2 p]
      else [xs])
followChain penv1 penv2 fenv1 fenv2 (Update {nil1 = True, nil2} p f ps) =
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
data Err : (tok : Type) -> Type where
  AltAmbiguous : List (List tok) -> Err tok
  SeqAmbiguous : List (List tok) -> Err tok
  ChainPos : Nat -> Err tok -> Err tok
  Branch : Nat -> Err tok -> Err tok

public export
enumerate : List a -> List (Nat, a)
enumerate = reverse . fst . foldl (\(acc, n), x => ((n, x) :: acc, S n)) ([], 0)

public export
collectTypeErrs :
 (set : Set tok t) =>
 (penv1 : All (Assoc0 $ const t) locked) ->
 (penv2 : All (Assoc0 $ const t) free) ->
 (fenv1 : All (Assoc0 $ const t) locked) ->
 (fenv2 : All (Assoc0 $ const t) free) ->
 Parser state error tok nil locked free a ->
 List (Err tok)

public export
collectChainTypeErrs:
 (set : Set tok t) =>
 (penv1 : All (Assoc0 $ const t) locked) ->
 (penv2 : All (Assoc0 $ const t) free) ->
 (fenv1 : All (Assoc0 $ const t) locked) ->
 (fenv2 : All (Assoc0 $ const t) free) ->
 ParserChain state error tok nil locked free a ->
 List (List (Err tok))

public export
collectAllTypeErrs:
 Set tok t =>
 (penv1 : All (Assoc0 $ const t) locked) ->
 (penv2 : All (Assoc0 $ const t) free) ->
 (fenv1 : All (Assoc0 $ const t) locked) ->
 (fenv2 : All (Assoc0 $ const t) free) ->
 {0 nils : List Bool} ->
 All (\nil => Parser state error tok nil locked free a) nils ->
 List (List (Err tok))

collectTypeErrs penv1 penv2 fenv1 fenv2 (Var j) = []
collectTypeErrs penv1 penv2 fenv1 fenv2 (Lit text) = []
collectTypeErrs penv1 penv2 fenv1 fenv2 (Seq ps) =
  let errs = collectChainTypeErrs penv1 penv2 fenv1 fenv2 ps in
  foldMap (\(n, es) => map (ChainPos n) es) $ enumerate errs
collectTypeErrs penv1 penv2 fenv1 fenv2 (OneOf ps) =
  let errs = collectAllTypeErrs penv1 penv2 fenv1 fenv2 ps in
  let peeked = forget $ peekAll penv2 ps in
  (if allDisjoint @{set} peeked then [] else [AltAmbiguous $ map toList peeked]) ++
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
collectTypeErrs penv1 penv2 fenv1 fenv2 (Map f p) =
  collectTypeErrs penv1 penv2 fenv1 fenv2 p
collectTypeErrs penv1 penv2 fenv1 fenv2 (WithBounds p) =
  collectTypeErrs penv1 penv2 fenv1 fenv2 p
collectTypeErrs penv1 penv2 fenv1 fenv2 (Forget f p) =
  collectTypeErrs @{set} [<] [<] [<] [<] p

collectChainTypeErrs penv1 penv2 fenv1 fenv2 [] = []
collectChainTypeErrs penv1 penv2 fenv1 fenv2 (Update {nil1 = False} p f ps) =
  let sets = [follow penv1 penv2 fenv1 fenv2 p, peekChain (penv2 ++ penv1) ps] in
  (  (if allDisjoint @{set} sets then [] else [SeqAmbiguous $ map toList sets])
  ++ collectTypeErrs penv1 penv2 fenv1 fenv2 p
  )
  :: collectChainTypeErrs [<] (penv2 ++ penv1) [<] (fenv2 ++ fenv1) ps
collectChainTypeErrs penv1 penv2 fenv1 fenv2 (Update {nil1 = True} p f ps) =
  let sets = [follow penv1 penv2 fenv1 fenv2 p, peekChain penv2 ps] in
  (  (if allDisjoint @{set} sets then [] else [SeqAmbiguous $ map toList sets])
  ++ collectTypeErrs penv1 penv2 fenv1 fenv2 p
  )
  :: collectChainTypeErrs penv1 penv2 fenv1 fenv2 ps

collectAllTypeErrs penv1 penv2 fenv1 fenv2 [] = []
collectAllTypeErrs penv1 penv2 fenv1 fenv2 (p :: ps) =
  collectTypeErrs penv1 penv2 fenv1 fenv2 p :: collectAllTypeErrs penv1 penv2 fenv1 fenv2 ps
