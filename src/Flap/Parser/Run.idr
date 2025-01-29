module Flap.Parser.Run

import public Flap.Parser.Core
import public Flap.Parser.Result
import public Flap.Parser.Types

import public Text.Lexer

import Control.WellFounded
import Data.Bool
import Data.So
import Flap.Data.List

public export
data ParseErr : Type -> Type where
  BadEOF : (expected : List tok) -> ParseErr tok
  Unexpected : (expected : List tok) -> (got : WithBounds $ Token tok) -> ParseErr tok
  MapFail : (msg : String) -> ParseErr tok

public export
ParseResult : {state, tok : Type} -> state -> List (WithBounds $ Token tok) -> Bool -> (state -> Type) -> Type
ParseResult s xs equal t = Result (ParseErr tok) xs equal (t s)

||| Searches `sets` for the first occurence of `x`.
||| On failure, returns the index for the nil element, if it exists.
|||
||| # Unsafe Invariants
||| * `nils` has at most one `True` element
||| * `sets` are disjoint
lookahead :
  Set tok t =>
  (x : Maybe tok) ->
  (nils : List Bool) ->
  (sets : Lazy (All (const t) nils)) ->
  Maybe (Any (const ()) nils)
lookahead x [] [] = Nothing
lookahead x (nil :: nils) (set :: sets) =
  (do
    x <- x
    if x `member` set then Just (Here ()) else Nothing)
  <|> There <$> lookahead x nils sets
  <|> (if nil then Just (Here ()) else Nothing)

parser :
  (set : Set tok t) =>
  (p : Parser state tok nil locked free a) ->
  (penv1 : All (Assoc0 $ const t) locked) ->
  (penv2 : All (Assoc0 $ const t) free) ->
  (xs : List (WithBounds (Token tok))) ->
  (s : state) ->
  All
    (Assoc0 (\x =>
      (ys : List (WithBounds (Token tok))) -> (0 _ : SuffixOf False ys xs) ->
      (s : state) ->
      uncurry (ParseResult s ys) x))
    locked ->
  All
    (Assoc0 (\x =>
      (ys : List (WithBounds (Token tok))) -> (0 _ : SuffixOf True ys xs) ->
      (s : state) ->
      uncurry (ParseResult s ys) x))
    free ->
  ParseResult s xs nil a
parserChain :
  (set : Set tok t) =>
  (ps : ParserChain state tok nil locked free as) ->
  (penv1 : All (Assoc0 $ const t) locked) ->
  (penv2 : All (Assoc0 $ const t) free) ->
  (xs : List (WithBounds (Token tok))) ->
  (s : state) ->
  All
    (Assoc0 (\x =>
      (ys : List (WithBounds (Token tok))) -> (0 _ : SuffixOf False ys xs) ->
      (s : state) ->
      uncurry (ParseResult s ys) x))
    locked ->
  All
    (Assoc0 (\x =>
      (ys : List (WithBounds (Token tok))) -> (0 _ : SuffixOf True ys xs) ->
      (s : state) ->
      uncurry (ParseResult s ys) x))
    free ->
  ParseResult s xs nil (\s => HList (map (\a => a s) as))
parserOneOf :
  (set : Set tok t) =>
  {nils : List Bool} ->
  (at : Any (const ()) nils) ->
  (ps : All (\nil => Parser state tok nil locked free a) nils) ->
  (penv1 : All (Assoc0 $ const t) locked) ->
  (penv2 : All (Assoc0 $ const t) free) ->
  (xs : List (WithBounds (Token tok))) ->
  (s : state) ->
  All
    (Assoc0 (\x =>
      (ys : List (WithBounds (Token tok))) -> (0 _ : SuffixOf False ys xs) ->
      (s : state) ->
      uncurry (ParseResult s ys) x))
    locked ->
  All
    (Assoc0 (\x =>
      (ys : List (WithBounds (Token tok))) -> (0 _ : SuffixOf True ys xs) ->
      (s : state) ->
      uncurry (ParseResult s ys) x))
    free ->
  ParseResult s xs (any Prelude.id nils) a

parser (Var x) penv1 penv2 xs s env1 env2 = (indexAll x.pos env2).value xs Refl s
parser (Lit text) penv1 penv2 xs s env1 env2 =
  let toks : t = singleton text in
  case xs of
    [] => Err (BadEOF [text])
    (x :: xs) =>
      if x.val.kind `member` toks
      then Ok x.val.text xs (Step Refl)
      else Err (Unexpected [text] x)
parser (Seq ps) penv1 penv2 xs s env1 env2 =
  parserChain ps penv1 penv2 xs s env1 env2
parser (OneOf {nils} ps) penv1 penv2 [] s env1 env2 =
  let sets = peekAll penv2 ps in
  case lookahead @{set} Nothing nils sets of
    Nothing => Err (BadEOF $ foldMap toList $ forget sets)
    Just at => parserOneOf at ps penv1 penv2 [] s env1 env2
parser (OneOf {nils} ps) penv1 penv2 (x :: xs) s env1 env2 =
  let sets = peekAll penv2 ps in
  case lookahead (Just x.val.kind) nils sets of
    Nothing => Err (Unexpected (foldMap toList $ forget sets) x)
    Just at => parserOneOf at ps penv1 penv2 (x :: xs) s env1 env2
parser (Fix {a, nil} x p) penv1 penv2 xs s env1 env2 =
  let f = parser p (penv1 :< (x :- peek penv2 (Fix x p))) penv2 in
  wfInd
    {rel = Irrelevant .: SuffixOf False}
    {P = \ys => (0 prf : SuffixOf True ys xs) -> (s : state) -> ParseResult s ys nil a}
    (\ys, rec, prf, s =>
      f ys s
        (  mapProperty (map $ \f, zs, 0 prf' => f zs $ trans prf' prf) env1
        :< (x :- (\zs, prf' => rec zs (Squash prf') (wkn (const Oh) $ trans prf' prf)))
        )
        (mapProperty (map $ \f, zs, 0 prf' => f zs $ trans prf' prf) env2))
    xs Refl s
parser (Map f p) penv1 penv2 xs s env1 env2 =
  case parser p penv1 penv2 xs s env1 env2 of
    Err e => Err e
    Ok res ys prf =>
      case f res of
        Left err => Err (MapFail err)
        Right res' => Ok res' ys prf
parser (WithState f p) penv1 penv2 xs s env1 env2 =
  parser p penv1 penv2 xs (f s) env1 env2
parser (WithBounds p) penv1 penv2 xs s env1 env2 =
  let (irrel, bnds) = bounds xs in
  (\x => MkBounded x irrel bnds) <$> parser p penv1 penv2 xs s env1 env2
  where
  bounds : (xs : List (WithBounds (Token tok))) -> (Bool, Bounds)
  bounds [] = (True, MkBounds 0 0 0 0)
  bounds (x :: xs) = (x.isIrrelevant, x.bounds)

parserChain [] penv1 penv2 xs s env1 env2 = Ok [] xs Refl
parserChain ((::) {nil1 = False, nil2} p ps) penv1 penv2 xs s env1 env2 = do
  x <- parser p penv1 penv2 xs s env1 env2
  xs <- parserChain ps [<] (penv2 ++ penv1) _ s
          [<]
          (  mapProperty (map (\f, zs, 0 prf, s => f zs (wkn (const Oh) $ trans {b2 = False} prf %search) s)) env2
          ++ mapProperty (map (\f, zs, 0 prf, s => f zs (trans {b2 = False} prf %search) s)) env1
          )
  pure (x :: xs)
parserChain ((::) {nil1 = True, nil2} p ps) penv1 penv2 xs s env1 env2 = do
  x <- parser p penv1 penv2 xs s env1 env2
  rewrite sym $ andTrueNeutral nil2
  xs <- parserChain ps penv1 penv2 _ s
          (mapProperty (map (\f, zs, prf => f zs $ trans {b2 = True} prf %search)) env1)
          (mapProperty (map (\f, zs, prf => f zs $ trans {b2 = True} prf %search)) env2)
  pure (x :: xs)

anyCons :
  (b : Bool) ->
  (0 f : a -> Bool) ->
  {0 xs : List a} -> LengthOf xs ->
  b || any f xs = foldl (\x, y => x || f y) b xs
anyCons b f Z = orFalseNeutral b
anyCons b f (S {x} {xs} len) =
  trans (sym $ cong (b ||) $ anyCons (f x) f len) $
  trans (orAssociative b (f x) _) $
  anyCons (b || f x) f len

parserOneOf {nils = nil :: nils} (Here ()) (p :: ps) penv1 penv2 xs s env1 env2 =
  wkn (rewrite sym $ anyCons nil id (lengthOf nils) in orSo . Left) $
  parser p penv1 penv2 xs s env1 env2
parserOneOf {nils = nil :: nils} (There at) (p :: ps) penv1 penv2 xs s env1 env2 =
  wkn (rewrite sym $ anyCons nil id (lengthOf nils) in orSo . Right) $
  parserOneOf at ps penv1 penv2 xs s env1 env2

export
parse :
  (set : Set tok t) =>
  (p : Parser state tok nil [<] [<] a) ->
  {auto 0 wf : collectTypeErrs @{set} [<] [<] [<] [<] p = []} ->
  ParseT state (ParseErr tok) (WithBounds $ Token tok) nil a
parse p = MkParseT (\s, xs => parser @{set} p [<] [<] xs s [<] [<])
