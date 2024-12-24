module Flap.Parser.Core

import public Data.List.Quantifiers
import public Data.Nat
import public Flap.Data.Context
import public Flap.Data.Context.Var
import public Flap.Data.SnocList.Quantifiers
import public Flap.Data.SnocList.Thinning
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
