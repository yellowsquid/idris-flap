module Inky.Parser

import public Data.List.Quantifiers

import Control.WellFounded
import Data.Bool
import Data.DPair
import Data.List
import Data.List1
import Data.Nat
import Data.So
import Data.String.Extra
import Inky.Data.Context
import Inky.Data.Context.Var
import Inky.Data.SnocList.Quantifiers
import Inky.Data.SnocList.Thinning
import Text.Lexer

export
Interpolation Bounds where
  interpolate bounds = "\{show (1 + bounds.startLine)}:\{show bounds.startCol}--\{show (1 + bounds.endLine)}:\{show bounds.endCol}"

-- Parser Expressions ----------------------------------------------------------

export infixl 3 <**>, **>, <**
export infixr 2 <||>

public export
linUnless : Bool -> Context a -> Context a
linUnless False ctx = [<]
linUnless True ctx = ctx

public export
linUnlessLin : (0 a : Type) -> (b : Bool) -> linUnless {a} b [<] = [<]
linUnlessLin a False = Refl
linUnlessLin a True = Refl

public export
data Parser : (i : Type) -> (nil : Bool) -> (locked, free : Context (Bool, Type)) -> Type -> Type

public export
data ParserChain : (i : Type) -> (nil : Bool) -> (locked, free : Context (Bool, Type)) -> List Type -> Type

data Parser where
  Var : Var free (nil, a) -> Parser i nil locked free a
  Lit : (text : i) -> Parser i False locked free String
  Seq :
    ParserChain i nil locked free as ->
    Parser i nil locked free (HList as)
  OneOf :
    {nils : List Bool} ->
    All (\nil => Parser i nil locked free a) nils ->
    {auto 0 prf : length (filter Basics.id nils) `LTE` 1} ->
    Parser i (any Basics.id nils) locked free a
  Fix :
    (0 x : String) ->
    Parser i nil (locked :< (x :- (nil, a))) free a ->
    Parser i nil locked free a
  Map : (a -> b) -> Parser i nil locked free a -> Parser i nil locked free b
  WithBounds : Parser i nil locked free a -> Parser i nil locked free (WithBounds a)

data ParserChain where
  Nil : ParserChain i True locked free []
  (::) :
    {nil1, nil2 : Bool} ->
    Parser i nil1 locked free a ->
    ParserChain i nil2 (linUnless nil1 locked) (free ++ linUnless (not nil1) locked) as ->
    ParserChain i (nil1 && nil2) locked free (a :: as)

%name Parser p, q
%name ParserChain ps, qs

-- Weakening -------------------------------------------------------------------

public export
rename :
  locked1 `Thins` locked2 ->
  free1 `Thins` free2 ->
  {auto len : LengthOf locked2} ->
  Parser i nil locked1 free1 a -> Parser i nil locked2 free2 a
public export
renameChain :
  locked1 `Thins` locked2 ->
  free1 `Thins` free2 ->
  {auto len : LengthOf locked2} ->
  ParserChain i nil locked1 free1 a -> ParserChain i nil locked2 free2 a
public export
renameAll :
  locked1 `Thins` locked2 ->
  free1 `Thins` free2 ->
  {auto len : LengthOf locked2} ->
  {0 nils : List Bool} ->
  All (\nil => Parser i nil locked1 free1 a) nils ->
  All (\nil => Parser i nil locked2 free2 a) nils

rename f g (Var i) = Var (toVar $ indexPos g i.pos)
rename f g (Lit text) = Lit text
rename f g (Seq ps) = Seq (renameChain f g ps)
rename f g (OneOf ps) = OneOf (renameAll f g ps)
rename f g (Fix x p) = Fix x (rename (Keep f) g p)
rename f g (Map h p) = Map h (rename f g p)
rename f g (WithBounds p) = WithBounds (rename f g p)

renameChain f g [] = []
renameChain f g ((::) {nil1 = False} p ps) = rename f g p :: renameChain Id (append g f) ps
renameChain f g ((::) {nil1 = True} p ps) = rename f g p :: renameChain f g ps

renameAll f g [] = []
renameAll f g (p :: ps) = rename f g p :: renameAll f g ps

public export
weaken :
  (len1 : LengthOf free2) ->
  {auto len2 : LengthOf locked} ->
  Parser i nil (free2 ++ locked) free1 a -> Parser i nil locked (free1 ++ free2) a
public export
weakenChain :
  (len1 : LengthOf free2) ->
  {auto len2 : LengthOf locked} ->
  ParserChain i nil (free2 ++ locked) free1 a -> ParserChain i nil locked (free1 ++ free2) a
public export
weakenAll :
  (len1 : LengthOf free2) ->
  {auto len2 : LengthOf locked} ->
  {0 nils : List Bool} ->
  All (\nil => Parser i nil (free2 ++ locked) free1 a) nils ->
  All (\nil => Parser i nil locked (free1 ++ free2) a) nils

weaken len1 (Var x) = Var (wknL x)
weaken len1 (Lit text) = Lit text
weaken len1 (Seq ps) = Seq (weakenChain len1 ps)
weaken len1 (OneOf ps) = OneOf (weakenAll len1 ps)
weaken len1 (Fix x p) = Fix x (weaken len1 p)
weaken len1 (Map f p) = Map f (weaken len1 p)
weaken len1 (WithBounds p) = WithBounds (weaken len1 p)

weakenChain len1 [] = []
weakenChain len1 ((::) {nil1 = False} p ps) = weaken len1 p :: renameChain Id (assoc len2) ps
weakenChain len1 ((::) {nil1 = True} p ps) = weaken len1 p :: weakenChain len1 ps

weakenAll len1 [] = []
weakenAll len1 (p :: ps) = weaken len1 p :: weakenAll len1 ps

-- Substitution ----------------------------------------------------------------

public export
sub :
  {auto len : LengthOf locked2} ->
  (f : All (Assoc0 $ (\nilA => Parser i (fst nilA) [<] (free2 ++ locked2) (snd nilA))) locked1) ->
  (g : All (Assoc0 $ (\nilA => Parser i (fst nilA) locked2 free2 (snd nilA))) free1) ->
  Parser i nil locked1 free1 a -> Parser i nil locked2 free2 a
public export
subChain :
  {auto len : LengthOf locked2} ->
  (f : All (Assoc0 $ (\nilA => Parser i (fst nilA) [<] (free2 ++ locked2) (snd nilA))) locked1) ->
  (g : All (Assoc0 $ (\nilA => Parser i (fst nilA) locked2 free2 (snd nilA))) free1) ->
  ParserChain i nil locked1 free1 a -> ParserChain i nil locked2 free2 a
public export
subAll :
  {auto len : LengthOf locked2} ->
  (f : All (Assoc0 $ (\nilA => Parser i (fst nilA) [<] (free2 ++ locked2) (snd nilA))) locked1) ->
  (g : All (Assoc0 $ (\nilA => Parser i (fst nilA) locked2 free2 (snd nilA))) free1) ->
  {0 nils : List Bool} ->
  All (\nil => Parser i nil locked1 free1 a) nils -> All (\nil => Parser i nil locked2 free2 a) nils

sub f g (Var x) = (indexAll x.pos g).value
sub f g (Lit text) = Lit text
sub f g (Seq ps) = Seq (subChain f g ps)
sub f g (OneOf ps) = OneOf (subAll f g ps)
sub f g (Fix x p) =
  Fix x $
  sub
    (mapProperty (map $ rename Id (Drop Id)) f :< (x :- Var (%%% x)))
    (mapProperty (map $ rename (Drop Id) Id) g)
    p
sub f g (Map h p) = Map h (sub f g p)
sub f g (WithBounds p) = WithBounds (sub f g p)

subChain f g [] = []
subChain f g ((::) {nil1 = False} p ps) =
  sub f g p ::
  subChain [<] (mapProperty (map $ weaken len) g ++ f) ps
subChain f g ((::) {nil1 = True} p ps) = sub f g p :: subChain f g ps

subAll f g [] = []
subAll f g (p :: ps) = sub f g p :: subAll f g ps

-- Typing ----------------------------------------------------------------------

-- Lists are sufficient, as we assume each symbol appears once.
-- TODO: switch to some efficient tree?

public export
peek :
  (env : All (Assoc0 $ const $ List i) free) ->
  Parser i nil locked free a -> List i
public export
peekChain :
  (env : All (Assoc0 $ const $ List i) free) ->
  ParserChain i nil locked free a -> List i
public export
peekAll :
  (env : All (Assoc0 $ const $ List i) free) ->
  {0 nils : List Bool} ->
  All (\nil => Parser i nil locked free a) nils ->
  All (const $ List i) nils

peek env (Var x) = (indexAll x.pos env).value
peek env (Lit text) = [text]
peek env (Seq ps) = peekChain env ps
peek env (OneOf ps) = concat (forget $ peekAll env ps)
peek env (Fix x p) = peek env p
peek env (Map f p) = peek env p
peek env (WithBounds p) = peek env p

peekChain env [] = []
peekChain env ((::) {nil1 = False} p ps) = peek env p
peekChain env ((::) {nil1 = True} p ps) = peek env p ++ peekChain env ps

peekAll env [] = []
peekAll env (p :: ps) = peek env p :: peekAll env ps

public export
follow :
  (penv1 : All (Assoc0 $ const $ List i) locked) ->
  (penv2 : All (Assoc0 $ const $ List i) free) ->
  (fenv1 : All (Assoc0 $ const $ List i) locked) ->
  (fenv2 : All (Assoc0 $ const $ List i) free) ->
  Parser i nil locked free a -> List i
public export
followChain :
  (penv1 : All (Assoc0 $ const $ List i) locked) ->
  (penv2 : All (Assoc0 $ const $ List i) free) ->
  (fenv1 : All (Assoc0 $ const $ List i) locked) ->
  (fenv2 : All (Assoc0 $ const $ List i) free) ->
  ParserChain i nil locked free a -> List i
public export
followAll :
  (penv1 : All (Assoc0 $ const $ List i) locked) ->
  (penv2 : All (Assoc0 $ const $ List i) free) ->
  (fenv1 : All (Assoc0 $ const $ List i) locked) ->
  (fenv2 : All (Assoc0 $ const $ List i) free) ->
  {0 nils : List Bool} ->
  All (\nil => Parser i nil locked free a) nils ->
  List i

follow penv1 penv2 fenv1 fenv2 (Var x) = (indexAll x.pos fenv2).value
follow penv1 penv2 fenv1 fenv2 (Lit text) = []
follow penv1 penv2 fenv1 fenv2 (Seq ps) = followChain penv1 penv2 fenv1 fenv2 ps
follow penv1 penv2 fenv1 fenv2 (OneOf ps) = followAll penv1 penv2 fenv1 fenv2 ps
follow penv1 penv2 fenv1 fenv2 (Fix x p) =
  -- Conjecture: The fix point converges after one step
  -- Proof:
  --   - we always add information
  --   - no step depends on existing information
  follow (penv1 :< (x :- peek penv2 p)) penv2 (fenv1 :< (x :- empty)) fenv2 p
follow penv1 penv2 fenv1 fenv2 (Map f p) = follow penv1 penv2 fenv1 fenv2 p
follow penv1 penv2 fenv1 fenv2 (WithBounds p) = follow penv1 penv2 fenv1 fenv2 p

followChain penv1 penv2 fenv1 fenv2 [] = []
followChain penv1 penv2 fenv1 fenv2 ((::) {nil1 = False, nil2} p ps) =
  (if nil2
  then peekChain (penv2 ++ penv1) ps ++ follow penv1 penv2 fenv1 fenv2 p
  else []) ++
  followChain [<] (penv2 ++ penv1) [<] (fenv2 ++ fenv1) ps
followChain penv1 penv2 fenv1 fenv2 ((::) {nil1 = True, nil2} p ps) =
  (if nil2
  then peekChain penv2 ps ++ follow penv1 penv2 fenv1 fenv2 p
  else []) ++
  followChain penv1 penv2 fenv1 fenv2 ps

followAll penv1 penv2 fenv1 fenv2 [] = []
followAll penv1 penv2 fenv1 fenv2 (p :: ps) =
  follow penv1 penv2 fenv1 fenv2 p ++
  followAll penv1 penv2 fenv1 fenv2 ps

public export
all' : (a -> Bool) -> List a -> Bool
all' f [] = True
all' f (x :: xs) = f x && all' f xs

allTrue : (xs : List a) -> all' (const True) xs = True
allTrue [] = Refl
allTrue (x :: xs) = allTrue xs

public export
disjoint : Eq a => List (List a) -> Bool
disjoint [] = True
disjoint (xs :: xss) = all' (\ys => all' (\x => not (x `elem` ys)) xs) xss && disjoint xss

namespace WellTyped
  public export
  wellTyped :
    (e : Eq i) ->
    (penv1 : All (Assoc0 $ const $ List i) locked) ->
    (penv2 : All (Assoc0 $ const $ List i) free) ->
    (fenv1 : All (Assoc0 $ const $ List i) locked) ->
    (fenv2 : All (Assoc0 $ const $ List i) free) ->
    Parser i nil locked free a ->
    Bool
  public export
  wellTypedChain :
    (e : Eq i) ->
    (penv1 : All (Assoc0 $ const $ List i) locked) ->
    (penv2 : All (Assoc0 $ const $ List i) free) ->
    (fenv1 : All (Assoc0 $ const $ List i) locked) ->
    (fenv2 : All (Assoc0 $ const $ List i) free) ->
    ParserChain i nil locked free a ->
    Bool
  public export
  allWellTyped :
    (e : Eq i) ->
    (penv1 : All (Assoc0 $ const $ List i) locked) ->
    (penv2 : All (Assoc0 $ const $ List i) free) ->
    (fenv1 : All (Assoc0 $ const $ List i) locked) ->
    (fenv2 : All (Assoc0 $ const $ List i) free) ->
    {0 nils : List Bool} ->
    All (\nil => Parser i nil locked free a) nils ->
    Bool

  wellTyped e penv1 penv2 fenv1 fenv2 (Var i) = True
  wellTyped e penv1 penv2 fenv1 fenv2 (Lit txt) = True
  wellTyped e penv1 penv2 fenv1 fenv2 (Seq ps) = wellTypedChain e penv1 penv2 fenv1 fenv2 ps
  wellTyped e penv1 penv2 fenv1 fenv2 (OneOf {nils, prf} ps) =
    disjoint (forget $ peekAll penv2 ps) && allWellTyped e penv1 penv2 fenv1 fenv2 ps
  wellTyped e penv1 penv2 fenv1 fenv2 (Fix x p) =
    wellTyped e
      (penv1 :< (x :- peek penv2 p))
      penv2
      (fenv1 :< (x :- follow (penv1 :< (x :- peek penv2 p)) penv2 (fenv1 :< (x :- [])) fenv2 p))
      fenv2
      p
  wellTyped e penv1 penv2 fenv1 fenv2 (Map f p) = wellTyped e penv1 penv2 fenv1 fenv2 p
  wellTyped e penv1 penv2 fenv1 fenv2 (WithBounds p) = wellTyped e penv1 penv2 fenv1 fenv2 p

  wellTypedChain e penv1 penv2 fenv1 fenv2 [] = True
  wellTypedChain e penv1 penv2 fenv1 fenv2 ((::) {nil1 = False} p ps) =
    disjoint [follow penv1 penv2 fenv1 fenv2 p, peekChain (penv2 ++ penv1) ps] &&
    wellTyped e penv1 penv2 fenv1 fenv2 p &&
    wellTypedChain e [<] (penv2 ++ penv1) [<] (fenv2 ++ fenv1) ps
  wellTypedChain e penv1 penv2 fenv1 fenv2 ((::) {nil1 = True} p ps) =
    disjoint [follow penv1 penv2 fenv1 fenv2 p, peekChain penv2 ps] &&
    wellTyped e penv1 penv2 fenv1 fenv2 p &&
    wellTypedChain e penv1 penv2 fenv1 fenv2 ps

  allWellTyped e penv1 penv2 fenv1 fenv2 [] = True
  allWellTyped e penv1 penv2 fenv1 fenv2 (p :: ps) =
    wellTyped e penv1 penv2 fenv1 fenv2 p &&
    allWellTyped e penv1 penv2 fenv1 fenv2 ps

-- Parsing Function ------------------------------------------------------------

-- Utilty for recursion

public export
data SmallerX : Bool -> List a -> List a -> Type where
  Strict : {0 xs, ys : List a} -> xs `Smaller` ys -> SmallerX False xs ys
  Lax : {0 xs, ys : List a} -> size xs `LTE` size ys -> SmallerX True xs ys

transX :
  {xs, ys, zs : List a} ->
  SmallerX b1 xs ys -> SmallerX b2 ys zs -> SmallerX (b1 && b2) xs zs
transX (Strict prf1) (Strict prf2) = Strict (transitive prf1 (lteSuccLeft prf2))
transX (Strict prf1) (Lax prf2) = Strict (transitive prf1 prf2)
transX (Lax prf1) (Strict prf2) = Strict (transitive (LTESucc prf1) prf2)
transX (Lax prf1) (Lax prf2) = Lax (transitive prf1 prf2)

ofSmaller : {b : Bool} -> {0 xs, ys : List a} -> xs `Smaller` ys -> SmallerX b xs ys
ofSmaller {b = False} prf = Strict prf
ofSmaller {b = True} prf = Lax (lteSuccLeft prf)

wknSmallerL : SmallerX b1 xs ys -> (b2 : Bool) -> SmallerX (b1 || b2) xs ys
wknSmallerL (Strict prf) _ = ofSmaller prf
wknSmallerL (Lax prf) _ = Lax prf

wknSmallerR : (b1 : Bool) -> SmallerX b2 xs ys -> SmallerX (b1 || b2) xs ys
wknSmallerR b1 (Strict prf) =
  if b1 then ofSmaller prf else ofSmaller prf
wknSmallerR b1 (Lax prf) =
  if b1 then Lax prf else Lax prf

forget : SmallerX b xs ys -> SmallerX True xs ys
forget = wknSmallerR True

toSmaller : {xs, ys : List a} -> (0 _ : SmallerX False xs ys) -> xs `Smaller` ys
toSmaller {xs = []} {ys = []} (Strict prf) impossible
toSmaller {xs = []} {ys = (y :: ys)} (Strict prf) = LTESucc LTEZero
toSmaller {xs = (x :: xs)} {ys = []} (Strict prf) impossible
toSmaller {xs = (x :: xs)} {ys = (y :: ys)} (Strict (LTESucc prf)) = LTESucc (toSmaller (Strict prf))

anyCons : (b : Bool) -> (bs : List Bool) -> any Basics.id (b :: bs) = b || any Basics.id bs
anyCons b [] = sym (orFalseNeutral b)
anyCons b (b' :: bs) =
  trans (anyCons (b || b') bs) $
  trans (sym $ orAssociative b b' (any id bs))
        (cong (b ||) (sym $ anyCons b' bs))

anyTrue : (bs : List Bool) -> any Basics.id (True :: bs) = True
anyTrue = anyCons True

-- Return Type

namespace M
  public export
  data M : List a -> Bool -> Type -> Type where
    Err : String -> M xs nil b
    Ok : (res : b) -> (ys : List a) -> (0 prf : SmallerX nil ys xs) -> M xs nil b

  export
  Functor (M xs nil) where
    map f (Err msg) = Err msg
    map f (Ok res ys prf) = Ok (f res) ys prf

  export
  pure : {xs : List a} -> (x : b) -> M xs True b
  pure x = Ok x xs (Lax reflexive)

  export
  (>>=) :
    M xs nil b ->
    (b -> {ys : List a} -> {auto 0 prf : SmallerX nil ys xs} -> M ys nil' c) ->
    M xs (nil && nil') c
  Err str >>= f = Err str
  Ok res ys prf >>= f =
    case f {ys, prf} res of
      Err str => Err str
      Ok res' zs prf' => Ok res' zs (rewrite andCommutative nil nil' in transX prf' prf)

  export
  take :
    Eq a =>
    Interpolation a =>
    (toks : List a) ->
    (xs : List (WithBounds (Token a))) ->
    M xs False String
  take [tok] [] = Err "expected \{tok}; got end of input"
  take toks [] = Err "expected one of: \{join ", " $ map (\k => "\{k}") toks}; got end of input"
  take toks (x :: xs) =
    if x.val.kind `elem` toks
    then Ok x.val.text xs (Strict reflexive)
    else case toks of
      [tok] => Err "\{x.bounds}: expected \{tok}; got \{x.val.kind}"
      toks => Err "\{x.bounds}: expected one of: \{join ", " $ map (\k => "\{k}") toks}; got \{x.val.kind}"

  export
  bounds : (xs : List (WithBounds a)) -> M xs True (Bool, Bounds)
  bounds [] = Ok (True, MkBounds (-1) (-1) (-1) (-1)) [] (Lax reflexive)
  bounds (x :: xs) = Ok (x.isIrrelevant, x.bounds) (x :: xs) (Lax reflexive)

  export
  wknL : M xs b1 a -> (b2 : Bool) -> M xs (b1 || b2) a
  wknL (Err msg) b2 = Err msg
  wknL (Ok res ys prf) b2 = Ok res ys (wknSmallerL prf b2)

  export
  wknR : (b1 : Bool) -> M xs b2 a -> M xs (b1 || b2) a
  wknR b1 (Err msg) = Err msg
  wknR b1 (Ok res ys prf) = Ok res ys (wknSmallerR b1 prf)

  export
  anyL :
    (b : Bool) -> {0 bs : List Bool} ->
    M xs (any Basics.id bs) a -> M xs (any Basics.id (b :: bs)) a
  anyL b m = rewrite anyCons b bs in wknR b m

  export
  anyR : (bs : List Bool) -> M xs b a -> M xs (any Basics.id (b :: bs)) a
  anyR bs m = rewrite anyCons b bs in wknL m (any id bs)

-- The Big Function

||| Searches `sets` for the first occurence of `x`.
||| On failure, returns the index for the nil element, if it exists.
|||
||| # Unsafe Invariants
||| * `nils` has at most one `True` element
||| * `sets` are disjoint
lookahead :
  Eq a =>
  (x : Maybe a) ->
  (nils : List Bool) ->
  (sets : Lazy (All (const $ List a) nils)) ->
  Maybe (Any (const ()) nils)
lookahead x [] [] = Nothing
lookahead x (nil :: nils) (set :: sets) =
  (do
    x <- x
    if x `elem` set then Just (Here ()) else Nothing)
  <|> There <$> lookahead x nils sets
  <|> (if nil then Just (Here ()) else Nothing)

parser :
  (e : Eq i) => Interpolation i =>
  (p : Parser i nil locked free a) ->
  {penv1 : _} ->
  {penv2 : _} ->
  {0 fenv1 : _} ->
  {0 fenv2 : _} ->
  (0 wf : So (wellTyped e penv1 penv2 fenv1 fenv2 p)) ->
  (xs : List (WithBounds (Token i))) ->
  All (Assoc0 (\x => (ys : List (WithBounds (Token i))) -> (0 _ : SmallerX False ys xs) -> uncurry (M ys) x)) locked ->
  All (Assoc0 (\x => (ys : List (WithBounds (Token i))) -> (0 _ : SmallerX True ys xs) -> uncurry (M ys) x)) free ->
  M xs nil a
parserChain :
  (e : Eq i) => Interpolation i =>
  (ps : ParserChain i nil locked free as) ->
  {penv1 : _} ->
  {penv2 : _} ->
  {0 fenv1 : _} ->
  {0 fenv2 : _} ->
  (0 wf : So (wellTypedChain e penv1 penv2 fenv1 fenv2 ps)) ->
  (xs : List (WithBounds (Token i))) ->
  All (Assoc0 (\x => (ys : List (WithBounds (Token i))) -> (0 _ : SmallerX False ys xs) -> uncurry (M ys) x)) locked ->
  All (Assoc0 (\x => (ys : List (WithBounds (Token i))) -> (0 _ : SmallerX True ys xs) -> uncurry (M ys) x)) free ->
  M xs nil (HList as)
parserOneOf :
  (e : Eq i) => Interpolation i =>
  {nils : List Bool} ->
  (at : Any (const ()) nils) ->
  (ps : All (\nil => Parser i nil locked free a) nils) ->
  {penv1 : _} ->
  {penv2 : _} ->
  {0 fenv1 : _} ->
  {0 fenv2 : _} ->
  (0 wf : So (allWellTyped e penv1 penv2 fenv1 fenv2 ps)) ->
  (xs : List (WithBounds (Token i))) ->
  All (Assoc0 (\x => (ys : List (WithBounds (Token i))) -> (0 _ : SmallerX False ys xs) -> uncurry (M ys) x)) locked ->
  All (Assoc0 (\x => (ys : List (WithBounds (Token i))) -> (0 _ : SmallerX True ys xs) -> uncurry (M ys) x)) free ->
  M xs (any Basics.id nils) a

parser (Var x) wf xs env1 env2 = (indexAll x.pos env2).value xs (Lax reflexive)
parser (Lit text) wf xs env1 env2 = take [text] xs
parser (Seq ps) wf xs env1 env2 =
  parserChain ps wf xs env1 env2
parser (OneOf {nils} ps) wf [] env1 env2 =
  let 0 wfs = soAnd {a = disjoint (forget $ peekAll penv2 ps)} wf in
  let sets = peekAll penv2 ps in
  case lookahead Nothing nils sets of
    Nothing => Err "unexpected end of input"
    Just at => parserOneOf at ps (snd wfs) [] env1 env2
parser (OneOf {nils} ps) wf (x :: xs) env1 env2 =
  let 0 wfs = soAnd {a = disjoint (forget $ peekAll penv2 ps)} wf in
  let sets = peekAll penv2 ps in
  case lookahead (Just x.val.kind) nils sets of
    Nothing => Err "\{x.bounds}: expected one of: \{join ", " $ map (\k => "\{k}") $ concat $ forget sets}; got \{x.val.kind}"
    Just at => parserOneOf at ps (snd wfs) (x :: xs) env1 env2
parser (Fix {a, nil} x p) wf xs env1 env2 =
  let f = parser p wf in
  sizeInd {P = \ys => (0 prf : SmallerX True ys xs) -> M ys nil a}
    (\ys, rec, lte =>
      f ys
        (  mapProperty (map (\f, zs, 0 prf => f zs $ transX prf lte)) env1
        :< (x :- (\zs, prf => rec zs (toSmaller prf) (forget $ transX prf lte)))
        )
        (mapProperty (map (\f, zs, prf => f zs $ transX prf lte)) env2))
    xs (Lax reflexive)
parser (Map f p) wf xs env1 env2 =
  f <$> parser p wf xs env1 env2
parser (WithBounds p) wf xs env1 env2 = do
  (irrel, bounds) <- bounds xs
  rewrite sym $ andTrueNeutral nil
  x <- parser p wf _
         (mapProperty (map (\f, zs, 0 prf => f zs $ transX {b2 = True} prf %search)) env1)
         (mapProperty (map (\f, zs, 0 prf => f zs $ transX prf %search)) env2)
  pure (MkBounded x irrel bounds)

parserChain [] wf xs env1 env2 = Ok [] xs (Lax reflexive)
parserChain ((::) {nil1 = False, nil2} p ps) wf xs env1 env2 =
  let 0 wfs = soAnd wf in
  let 0 wfs' = soAnd (snd wfs) in do
    x <- parser p (fst wfs') xs env1 env2
    y <- parserChain ps (snd wfs')
          _
          [<]
          (  mapProperty (map (\f, zs, 0 prf => f zs $ forget $ transX {b2 = False} prf %search)) env2
          ++ mapProperty (map (\f, zs, 0 prf => f zs $ transX prf %search)) env1
          )
    pure (x :: y)
parserChain ((::) {nil1 = True, nil2} p ps) wf xs env1 env2 =
  let 0 wfs = soAnd wf in
  let 0 wfs' = soAnd (snd wfs) in do
    x <- parser p (fst wfs') xs env1 env2
    rewrite sym $ andTrueNeutral nil2
    y <- parserChain ps (snd wfs')
           _
           (mapProperty (map (\f, zs, prf => f zs $ transX {b2 = True} prf %search)) env1)
           (mapProperty (map (\f, zs, prf => f zs $ transX prf %search)) env2)
    pure (x :: y)

parserOneOf {nils = nil :: nils} (Here ()) (p :: ps) wf xs env1 env2 =
  let 0 wfs = soAnd wf in
  anyR nils (parser p (fst wfs) xs env1 env2)
parserOneOf {nils = nil :: nils} (There at) (p :: ps) wf xs env1 env2 =
  let 0 wfs = soAnd {a = wellTyped e penv1 penv2 fenv1 fenv2 p} wf in
  anyL nil (parserOneOf at ps (snd wfs) xs env1 env2)

export
parse :
  (e : Eq i) => Interpolation i =>
  (p : Parser i nil [<] [<] a) ->
  {auto 0 wf : So (wellTyped e [<] [<] [<] [<] p)} ->
  (xs : List (WithBounds (Token i))) -> M xs nil a
parse p xs = parser p wf xs [<] [<]

-- Functor ---------------------------------------------------------------------

public export
(++) :
  {nil2 : Bool} ->
  ParserChain i nil1 locked free as ->
  ParserChain i nil2 (linUnless nil1 locked) (free ++ linUnless (not nil1) locked) bs ->
  ParserChain i (nil1 && nil2) locked free (as ++ bs)
[] ++ qs = qs
((::) {nil1 = False, nil2} p ps) ++ qs =
  p ::
  (  ps
  ++ rewrite linUnlessLin (Bool, Type) nil2 in
     rewrite linUnlessLin (Bool, Type) (not nil2) in
     qs)
((::) {nil1 = True, nil2} p ps) ++ qs = p :: (ps ++ qs)

public export
(<**>) :
  {nil1, nil2 : Bool} ->
  Parser i nil1 locked free a ->
  Parser i nil2 (linUnless nil1 locked) (free ++ linUnless (not nil1) locked) b ->
  Parser i (nil1 && nil2) locked free (a, b)
p <**> Seq ps = Map (\(x :: xs) => (x, xs)) $ Seq (p :: ps)
-- HACK: andTrueNeutral isn't public, so do a full case split.
(<**>) {nil1 = True, nil2 = True} p q = Map (\[x, y] => (x, y)) $ Seq [p, q]
(<**>) {nil1 = True, nil2 = False} p q = Map (\[x, y] => (x, y)) $ Seq [p, q]
(<**>) {nil1 = False, nil2 = True} p q = Map (\[x, y] => (x, y)) $ Seq [p, q]
(<**>) {nil1 = False, nil2 = False} p q = Map (\[x, y] => (x, y)) $ Seq [p, q]

public export
Functor (Parser i nil locked free) where
  map f (Map g p) = Map (f . g) p
  map f p = Map f p

public export
Applicative (Parser i True locked free) where
  pure x = map (const x) (Seq [])
  p <*> q = map (\(f, x) => f x) (p <**> q)

-- Combinator ------------------------------------------------------------------

public export
(<|>) :
  {nil1, nil2 : Bool} ->
  Parser i nil1 locked free a ->
  Parser i nil2 locked free a ->
  {auto 0 prf : length (filter Basics.id [nil1, nil2]) `LTE` 1} ->
  Parser i (nil1 || nil2) locked free a
p <|> q = OneOf [p, q]

public export
(<||>) :
  {nil1, nil2 : Bool} ->
  Parser i nil1 locked free a ->
  Parser i nil2 locked free b ->
  {auto 0 prf : length (filter Basics.id [nil1, nil2]) `LTE` 1} ->
  Parser i (nil1 || nil2) locked free (Either a b)
p <||> q = Left <$> p <|> Right <$> q

public export
(**>) :
  {nil1, nil2 : Bool} ->
  Parser i nil1 locked free a ->
  Parser i nil2 (linUnless nil1 locked) (free ++ linUnless (not nil1) locked) b ->
  Parser i (nil1 && nil2) locked free b
p **> q = snd <$> (p <**> q)

public export
(<**) :
  {nil1, nil2 : Bool} ->
  Parser i nil1 locked free a ->
  Parser i nil2 (linUnless nil1 locked) (free ++ linUnless (not nil1) locked) b ->
  Parser i (nil1 && nil2) locked free a
p <** q = fst <$> (p <**> q)

public export
match : TokenKind i => (kind : i) -> Parser i False locked free (TokType kind)
match kind = Map (tokValue kind) $ Lit kind

public export
enclose :
  {b1, b2, b3 : Bool} ->
  (left : Parser i b1 locked free ()) ->
  (right :
    Parser i b3
      (linUnless b2 (linUnless b1 locked))
      ((free ++ linUnless (not b1) locked) ++ linUnless (not b2) (linUnless b1 locked))
      ()) ->
  Parser i b2 (linUnless b1 locked) (free ++ linUnless (not b1) locked) a ->
  Parser i (b1 && b2 && b3 && True) locked free a
enclose left right p = (\[_, x, _] => x) <$> Seq {as = [(), a, ()]} [left, p, right]

public export
option : Parser i False locked free a -> Parser i True locked free (Maybe a)
option p = (Just <$> p) <|> pure Nothing

public export
plus :
  {auto len : LengthOf locked} ->
  Parser i False locked free a ->
  Parser i False locked free (List1 a)
plus p =
  Fix "plus"
    (   uncurry (:::)
    <$> (rename (Drop Id) Id p <**> maybe [] forget <$> option (Var $ %%% "plus")))

public export
star :
  {auto len : LengthOf locked} ->
  Parser i False locked free a ->
  Parser i True locked free (List a)
star p = maybe [] forget <$> option (plus p)

public export
sepBy1 :
  {auto len : LengthOf locked} ->
  (sep : Parser i False locked free ()) ->
  Parser i False locked free a ->
  Parser i False locked free (List1 a)
sepBy1 sep p = uncurry (:::) <$> (p <**> star (weaken len sep **> weaken len p))

public export
sepBy :
  {auto len : LengthOf locked} ->
  (sep : Parser i False locked free ()) ->
  Parser i False locked free a ->
  Parser i True locked free (List a)
sepBy sep p = maybe [] forget <$> option (sepBy1 sep p)
