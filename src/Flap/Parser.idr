module Flap.Parser

import public Flap.Parser.Run

import Data.List1

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
