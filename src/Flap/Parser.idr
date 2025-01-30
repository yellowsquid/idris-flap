module Flap.Parser

import public Flap.Parser.Run

import Data.List1

-- Functor ---------------------------------------------------------------------

public export
(::) :
  {nil1, nil2 : Bool} ->
  Parser state error tok nil1 locked free a ->
  ParserChain state error tok nil2 (linUnless nil1 locked) (free ++ linUnless (not nil1) locked) as ->
  ParserChain state error tok (nil1 && nil2) locked free (MkStage a (\s, _ => s) :: as)
p :: ps = Update p (\s, _ => s) ps

%inline
public export
(<$>) :
  ({s : state} -> a s -> b s) ->
  Parser state error tok nil locked free a ->
  Parser state error tok nil locked free b
f <$> Map g p = Map (mapSnd f . g) p
f <$> p = Map (Right . f) p

%inline
public export
(<$) :
  ({s : state} -> b s) ->
  Parser state error tok nil locked free a ->
  Parser state error tok nil locked free b
x <$ p = const x <$> p

%inline
public export
($>) :
  Parser state error tok nil locked free a ->
  ({s : state} -> b s) ->
  Parser state error tok nil locked free b
p $> x = const x <$> p

%inline
public export
pure : ({s : state} -> a s) -> Parser state error tok True locked free a
pure x = x <$ Seq []

%inline
public export
(<**>) :
  {nil1, nil2 : Bool} ->
  Parser state error tok nil1 locked free a ->
  Parser state error tok nil2 (linUnless nil1 locked) (free ++ linUnless (not nil1) locked) b ->
  Parser state error tok (nil1 && nil2) locked free (\s => (a s, b s))
p <**> Seq ps = (\(x :: xs) => (x, xs)) <$> Seq (p :: ps)
-- HACK: andTrueNeutral isn't public, so do a full case split.
(<**>) {nil1 = True, nil2 = True} p q = (\[x, y] => (x, y)) <$> Seq [p, q]
(<**>) {nil1 = True, nil2 = False} p q = (\[x, y] => (x, y)) <$> Seq [p, q]
(<**>) {nil1 = False, nil2 = True} p q = (\[x, y] => (x, y)) <$> Seq [p, q]
(<**>) {nil1 = False, nil2 = False} p q = (\[x, y] => (x, y)) <$> Seq [p, q]

%inline
public export
(<*>) :
  {nil1, nil2 : Bool} ->
  Parser state error tok nil1 locked free (\s => a s -> b s) ->
  Parser state error tok nil2 (linUnless nil1 locked) (free ++ linUnless (not nil1) locked) a ->
  Parser state error tok (nil1 && nil2) locked free b
p <*> q = (\fx => fst fx $ snd fx) <$> (p <**> q)

%inline
public export
(<*) :
  {nil1, nil2 : Bool} ->
  Parser state error tok nil1 locked free a ->
  Parser state error tok nil2 (linUnless nil1 locked) (free ++ linUnless (not nil1) locked) b ->
  Parser state error tok (nil1 && nil2) locked free a
p <* q = fst <$> (p <**> q)

%inline
public export
(*>) :
  {nil1, nil2 : Bool} ->
  Parser state error tok nil1 locked free a ->
  Parser state error tok nil2 (linUnless nil1 locked) (free ++ linUnless (not nil1) locked) b ->
  Parser state error tok (nil1 && nil2) locked free b
p *> q = snd <$> (p <**> q)

-- -- Combinator ------------------------------------------------------------------

%inline
public export
(<|>) :
  {nil1, nil2 : Bool} ->
  Parser state error tok nil1 locked free a ->
  Parser state error tok nil2 locked free a ->
  {auto 0 prf : length (filter Basics.id [nil1, nil2]) `LTE` 1} ->
  Parser state error tok (nil1 || nil2) locked free a
p <|> q = OneOf [p, q]

%inline
public export
(<||>) :
  {nil1, nil2 : Bool} ->
  Parser state error tok nil1 locked free a ->
  Parser state error tok nil2 locked free b ->
  {auto 0 prf : length (filter Basics.id [nil1, nil2]) `LTE` 1} ->
  Parser state error tok (nil1 || nil2) locked free (\s => Either (a s) (b s))
p <||> q = Left <$> p <|> Right <$> q

%inline
public export
match : TokenKind tok => (kind : tok) -> Parser state error tok False locked free (const $ TokType kind)
match kind = tokValue kind <$> Lit kind

%inline
public export
enclose :
  {b1, b2, b3 : Bool} ->
  (left : Parser state error tok b1 locked free (const ())) ->
  (right :
    Parser state error tok b3
      (linUnless b2 (linUnless b1 locked))
      ((free ++ linUnless (not b1) locked) ++ linUnless (not b2) (linUnless b1 locked))
      (const ())) ->
  Parser state error tok b2 (linUnless b1 locked) (free ++ linUnless (not b1) locked) a ->
  Parser state error tok (b1 && b2 && b3 && True) locked free a
enclose left right p = (\[_, x, _] => x) <$> Seq [left, p, right]

%inline
public export
option : Parser state error tok False locked free a -> Parser state error tok True locked free (Maybe . a)
option p = (Just <$> p) <|> pure Nothing

%inline
public export
plus :
  {auto len : LengthOf locked} ->
  Parser state error tok False locked free a ->
  Parser state error tok False locked free (List1 . a)
plus p =
  Fix "plus"
    (   uncurry (:::)
    <$> (rename (Drop Id) Id p <**> maybe [] forget <$> option (Var $ %%% "plus")))

%inline
public export
star :
  {auto len : LengthOf locked} ->
  Parser state error tok False locked free a ->
  Parser state error tok True locked free (List . a)
star p = maybe [] forget <$> option (plus p)

public export
sepBy1 :
  {auto len : LengthOf locked} ->
  (sep : Parser state error tok False locked free (const ())) ->
  Parser state error tok False locked free a ->
  Parser state error tok False locked free (List1 . a)
sepBy1 sep p = uncurry (:::) <$> (p <**> star (weaken len sep *> weaken len p))

public export
sepBy :
  {auto len : LengthOf locked} ->
  (sep : Parser state error tok False locked free (const ())) ->
  Parser state error tok False locked free a ->
  Parser state error tok True locked free (List . a)
sepBy sep p = maybe [] forget <$> option (sepBy1 sep p)
