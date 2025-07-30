module DepType

import Data.List              -- for making a "set" out of lists
import Data.String            -- for stringToNatOrZ
import Data.SnocList          -- for map
import Flap.Data.SnocList.Var -- for representing variables in terms
import Flap.Decidable         -- for DecEq' String
import Flap.Parser

%hide Flap.Data.SnocList.Elem.lookup

-- We are trying to write a parser for the following term language.
-- Terms are intrisically well-scoped.
data Term : (0 ctx : SnocList String) -> Type where
  Var   : Var ctx -> Term ctx
  Lam   : (name : String) -> Term (ctx :< name) -> Term ctx
  App   : Term ctx -> Term ctx -> Term ctx
  Let   : (bound, ty : Term ctx) -> (name : String) -> (body : Term (ctx :< name)) -> Term ctx
  Univ  : Nat -> Term ctx
  Pi    : Term ctx -> (name : String) -> Term (ctx :< name) -> Term ctx
  Arrow : Term ctx -> Term ctx -> Term ctx

exampleTerm : String
exampleTerm = """
let Nat : U 1 = Π(N : U 0) → (N → N) → N → N in
let five : Nat = λ N, suc, zero →
  suc (suc (suc (suc (suc zero))))
in
let add : Nat → Nat → Nat = λ k, n, N, suc, zero →
  k N suc (n N suc zero)
in
let mul : Nat → Nat → Nat = λ k, n, N, suc, zero →
  k N (n N suc) zero
in
let ten      : Nat = add five five in
let hundred  : Nat = mul ten ten in
let thousand : Nat = mul ten hundred in
thousand
"""

---- Step 0: Define the Tokens -------------------------------------------------

-- We have the following parts of syntax:
data Kind =
  TLet | In | Eq | Id | Num | Colon | Arr | Comma | TPi | POpen | PClose | TU | TLam

-- Helper for equality. Must be injective.
toNat : Kind -> Nat
toNat TLet = 0
toNat In = 1
toNat Eq = 2
toNat Id = 3
toNat Num = 4
toNat Colon = 5
toNat Arr = 6
toNat Comma = 7
toNat TPi = 8
toNat POpen = 9
toNat PClose = 10
toNat TU = 11
toNat TLam = 12

-- We can do equality testing
Eq Kind where
  t == t' = toNat t == toNat t'

-- We can convert string to values
TokenKind Kind where
  TokType Id = String
  TokType Num = Nat
  TokType _ = ()

  tokValue TLet s = ()
  tokValue In s = ()
  tokValue Eq s = ()
  tokValue Id s = s
  tokValue Num s = stringToNatOrZ s
  tokValue Colon s = ()
  tokValue Arr s = ()
  tokValue Comma s = ()
  tokValue TPi s = ()
  tokValue POpen s = ()
  tokValue PClose s = ()
  tokValue TU s = ()
  tokValue TLam s = ()

---- Step 1: Decide an Order of Operations -------------------------------------

-- 1. Atomic         -- variables, parens
-- 2. Application-y  -- app, U
-- 3. Arrows         -- pi, arrow
-- 4. Open           -- lam, let

---- Step 2: Define Parsers for each Precedence --------------------------------

-- This makes our types look neater.
-- We:
--   - have `SnocList String` state (bound variables)
--   - have `String` errors (unbound variables)
--   - parse `Kind` tokens
--   - always consume input (`nil` is `False`)
--   - assume locked variables consume input and parse expressions
--   - have no free variables
--   - and parse a term
TermParser : (locked : SnocList String) -> Type
TermParser locked =
  Parser (SnocList String) String Kind False
    (map (\name => name :- (False, (\ctx => Term ctx))) locked)
    [<]
    (\ctx => Term ctx)

stringToVar : {ctx : SnocList String} -> String -> Either String (Term ctx)
stringToVar {ctx} str = case lookup str ctx of
  Just v => Right (Var v)
  Nothing => Left str

atomicTerm : TermParser [<"open"]
atomicTerm =
  OneOf
  [ -- A variable is a bound identifier.
    -- We use `Map` explicitly as the operation can fail.
    Map stringToVar (match Id)
  , -- Using parentheses makes open terms atomic.
    enclose (match POpen) (match PClose) (Var $ %%% "open")
  ]

appTerm : TermParser [<"open"]
appTerm = OneOf
  [ -- Universes are the symbol `U` applied to the universe level
    Univ <$ match TU <*> match Num
  , -- Application spines are made from lists of atomic terms
    foldl1 App <$> plus atomicTerm
  ]

arrowTerm : TermParser [<"open"]
arrowTerm = Fix "arrow" $ OneOf
  [ (\[(name, a), b] => Pi a name b) <$
    match TPi <*> Seq (
      -- We use `Update` so we can describe how the context changes.
      -- The first argument has to include the reference to `open`,
      -- as the new variable is not bound until after the arrow.
      -- The parser will never process the second-half of a stateful update
      -- if there is an error in the first half.
      -- We mitigate this by making the first half do as much work as possible.
      Update
        (  enclose (match POpen) (match PClose) (match Id <**> (match Colon *> Var (%%% "open")))
        <* match Arr)
        (Just (\ctx, (name, _) => ctx :< name))
        [Var $ %%% "arrow"])
  , -- Functions associate to the right
    Arrow <$> rename %search %search appTerm <*> (match Arr *> Var (%%% "arrow"))
  ]

bindAll : (names : List String) -> (body : Term (ctx <>< names)) -> Term ctx
bindAll [] body = body
bindAll (name :: names) body = Lam name (bindAll names body)

openTerm : TermParser [<"open"]
openTerm = OneOf
  [ (\[names, body] => bindAll (forget names) body) <$ match TLam <*> Seq (
      -- Lamdas bind a list of variables all at once.
      Update
        (sepBy1 (match Comma) (match Id) <* match Arr)
        (Just (\ctx, names => ctx <>< forget names))
      [Var $ %%% "open"])
  , (\[(name, ty, bound), body] => Let bound ty name body) <$ match TLet <*> Seq (
      -- Let expressions have both a type and a term
      -- before the bound variable can be used.
      Update
        (match Id <**> (match Colon *> Var (%%% "open") <**> (match Eq *> Var (%%% "open") <* match In)))
        (Just (\ctx, (name, _) => ctx :< name))
        [Var $ %%% "open"])
  , arrowTerm
  ]

-- Step 3: Tie the Recursive Knot with `Fix` -----------------------------------

-- We have no free variables in our top-level parser.
-- We use `Fix` to express our intent to do recursion.
-- We then give the name of the recursive variable ("open"),
-- and finally the expression we will recurse over.
parser : TermParser [<]
parser = Fix "open" openTerm

---- Step 4: Check for Parser Well-Formedness ----------------------------------

-- We need to have a way of collecting sets of token kinds.
-- For this toy language using lists is good enough.
-- The functions here _must_ compute within types.
[ListSet] Set Kind (List Kind) where
  toList    = id
  member    = elem
  singleton = List.singleton

  intersect xs ys = filter (flip elem xs) ys

-- Doing this explicitly isn't required if the definition of `parser`
-- is visible where you call `Flap.Parser.parse`.
-- Doing it seperately might make error messages easier to understand.
-- We use `%hint` so proof search can find it.

%hint
parserOk : WellFormed ListSet DepType.parser
parserOk = Refl

---- Step 5: Construct the Parse Function --------------------------------------

-- Construct the parser from an expression with `parse`.
-- Run the parser with `.runParser`, giving the initial state (in this case unit).
parseTerm :
  (xs : List (WithBounds $ Token Kind)) ->
  Result (ParseErr String Kind) xs False (Term [<])
parseTerm = (parse ListSet parser).runParser [<]
