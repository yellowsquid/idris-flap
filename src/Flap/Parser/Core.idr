module Flap.Parser.Core

import public Data.List.Quantifiers
import public Data.Nat
import public Flap.Data.Context
import public Flap.Data.Context.Var
import public Flap.Data.SnocList.Quantifiers
import public Flap.Data.SnocList.Thinning
import public Flap.Parser.Sequence
import public Text.Bounded

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
data Parser :
  (state, error, tok : Type) ->
  (nil : Bool) ->
  (locked, free : Context (Bool, state -> Type)) ->
  (state -> Type) ->
  Type

public export
data ParserChain :
  (state, error, tok : Type) ->
  (nil : Bool) ->
  (locked, free : Context (Bool, state -> Type)) ->
  List (Stage state) ->
  Type

data Parser where
  Var : Var free (nil, a) -> Parser state error tok nil locked free a
  Lit : (text : tok) -> Parser state error tok False locked free (const String)
  Seq :
    ParserChain state error tok nil locked free stages ->
    Parser state error tok nil locked free (flip Sequence stages)
  OneOf :
    {nils : List Bool} ->
    All (\nil => Parser state error tok nil locked free a) nils ->
    {auto 0 prf : length (filter Basics.id nils) `LTE` 1} ->
    Parser state error tok (any Basics.id nils) locked free a
  Fix :
    (0 x : String) ->
    Parser state error tok nil (locked :< (x :- (nil, a))) free a ->
    Parser state error tok nil locked free a
  Map :
    ({s : state} -> a s -> Either error (b s)) ->
    Parser state error tok nil locked free a ->
    Parser state error tok nil locked free b
  WithBounds :
    Parser state error tok nil locked free a ->
    Parser state error tok nil locked free (WithBounds . a)

data ParserChain where
  Nil : ParserChain state error tok True locked free []
  Update :
    {nil1, nil2 : Bool} ->
    Parser state error tok nil1 locked free a ->
    (f : (s : state) -> a s -> state) ->
    ParserChain state error tok nil2 (linUnless nil1 locked) (free ++ linUnless (not nil1) locked) as ->
    ParserChain state error tok (nil1 && nil2) locked free (MkStage a f :: as)

%name Parser p, q
%name ParserChain ps, qs

-- Weakening -------------------------------------------------------------------

public export
rename :
  locked1 `Thins` locked2 ->
  free1 `Thins` free2 ->
  {auto len : LengthOf locked2} ->
  Parser state error tok nil locked1 free1 a ->
  Parser state error tok nil locked2 free2 a
public export
renameChain :
  locked1 `Thins` locked2 ->
  free1 `Thins` free2 ->
  {auto len : LengthOf locked2} ->
  ParserChain state error tok nil locked1 free1 a ->
  ParserChain state error tok nil locked2 free2 a
public export
renameAll :
  locked1 `Thins` locked2 ->
  free1 `Thins` free2 ->
  {auto len : LengthOf locked2} ->
  {0 nils : List Bool} ->
  All (\nil => Parser state error tok nil locked1 free1 a) nils ->
  All (\nil => Parser state error tok nil locked2 free2 a) nils

rename f g (Var tok) = Var (toVar $ indexPos g tok.pos)
rename f g (Lit text) = Lit text
rename f g (Seq ps) = Seq (renameChain f g ps)
rename f g (OneOf ps) = OneOf (renameAll f g ps)
rename f g (Fix x p) = Fix x (rename (Keep f) g p)
rename f g (Map h p) = Map h (rename f g p)
rename f g (WithBounds p) = WithBounds (rename f g p)

renameChain f g [] = []
renameChain f g (Update {nil1 = False} p h ps) =
  Update (rename f g p) h (renameChain Id (append g f) ps)
renameChain f g (Update {nil1 = True} p h ps) =
  Update (rename f g p) h (renameChain f g ps)

renameAll f g [] = []
renameAll f g (p :: ps) = rename f g p :: renameAll f g ps

public export
weaken :
  (len1 : LengthOf free2) ->
  {auto len2 : LengthOf locked} ->
  Parser state error tok nil (free2 ++ locked) free1 a ->
  Parser state error tok nil locked (free1 ++ free2) a
public export
weakenChain :
  (len1 : LengthOf free2) ->
  {auto len2 : LengthOf locked} ->
  ParserChain state error tok nil (free2 ++ locked) free1 a ->
  ParserChain state error tok nil locked (free1 ++ free2) a
public export
weakenAll :
  (len1 : LengthOf free2) ->
  {auto len2 : LengthOf locked} ->
  {0 nils : List Bool} ->
  All (\nil => Parser state error tok nil (free2 ++ locked) free1 a) nils ->
  All (\nil => Parser state error tok nil locked (free1 ++ free2) a) nils

weaken len1 (Var x) = Var (wknL x)
weaken len1 (Lit text) = Lit text
weaken len1 (Seq ps) = Seq (weakenChain len1 ps)
weaken len1 (OneOf ps) = OneOf (weakenAll len1 ps)
weaken len1 (Fix x p) = Fix x (weaken len1 p)
weaken len1 (Map f p) = Map f (weaken len1 p)
weaken len1 (WithBounds p) = WithBounds (weaken len1 p)

weakenChain len1 [] = []
weakenChain len1 (Update {nil1 = False} p f ps) = Update (weaken len1 p) f (renameChain Id (assoc len2) ps)
weakenChain len1 (Update {nil1 = True} p f ps) = Update (weaken len1 p) f (weakenChain len1 ps)

weakenAll len1 [] = []
weakenAll len1 (p :: ps) = weaken len1 p :: weakenAll len1 ps

-- Substitution ----------------------------------------------------------------

public export
sub :
  {auto len : LengthOf locked2} ->
  (f : All (Assoc0 $ (\nilA => Parser state error tok (fst nilA) [<] (free2 ++ locked2) (snd nilA))) locked1) ->
  (g : All (Assoc0 $ (\nilA => Parser state error tok (fst nilA) locked2 free2 (snd nilA))) free1) ->
  Parser state error tok nil locked1 free1 a ->
  Parser state error tok nil locked2 free2 a
public export
subChain :
  {auto len : LengthOf locked2} ->
  (f : All (Assoc0 $ (\nilA => Parser state error tok (fst nilA) [<] (free2 ++ locked2) (snd nilA))) locked1) ->
  (g : All (Assoc0 $ (\nilA => Parser state error tok (fst nilA) locked2 free2 (snd nilA))) free1) ->
  ParserChain state error tok nil locked1 free1 as ->
  ParserChain state error tok nil locked2 free2 as
public export
subAll :
  {auto len : LengthOf locked2} ->
  (f : All (Assoc0 $ (\nilA => Parser state error tok (fst nilA) [<] (free2 ++ locked2) (snd nilA))) locked1) ->
  (g : All (Assoc0 $ (\nilA => Parser state error tok (fst nilA) locked2 free2 (snd nilA))) free1) ->
  {0 nils : List Bool} ->
  All (\nil => Parser state error tok nil locked1 free1 a) nils ->
  All (\nil => Parser state error tok nil locked2 free2 a) nils

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
subChain f g (Update {nil1 = False} p h ps) =
  Update (sub f g p) h (subChain [<] (mapProperty (map $ weaken len) g ++ f) ps)
subChain f g (Update {nil1 = True} p h ps) = Update (sub f g p) h (subChain f g ps)

subAll f g [] = []
subAll f g (p :: ps) = sub f g p :: subAll f g ps
