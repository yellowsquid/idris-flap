module Arithmetic

import Data.List   -- for making a "set" out of lists
import Data.String -- for stringToNatOrZ
import Flap.Parser

-- We are trying to write a parser for the following expressions
data Expr : Type where
  Lit  : Nat -> Expr
  Add  : Expr -> Expr -> Expr
  Sub  : Expr -> Expr -> Expr
  Mult : Expr -> Expr -> Expr
  Div  : Expr -> Expr -> Expr

---- Step 0: Define the Tokens -------------------------------------------------

-- We have the following parts of syntax:
data Kind
  = Literal
  | Plus
  | Minus
  | Multiply
  | Divide
  | LeftParen
  | RightParen

-- Helper for equality. Must be injective.
toNat : Kind -> Nat
toNat Literal    = 0
toNat Plus       = 1
toNat Minus      = 2
toNat Multiply   = 3
toNat Divide     = 4
toNat LeftParen  = 5
toNat RightParen = 6

-- We can do equality testing
Eq Kind where
  k1 == k2 = toNat k1 == toNat k2

-- We can convert strings to values
TokenKind Kind where
  TokType Literal  = Nat
  TokType Plus     = Expr -> Expr -> Expr
  TokType Minus    = Expr -> Expr -> Expr
  TokType Multiply = Expr -> Expr -> Expr
  TokType Divide   = Expr -> Expr -> Expr
  TokType _        = ()

  tokValue Literal    = stringToNatOrZ
  tokValue Plus       = const Add
  tokValue Minus      = const Sub
  tokValue Multiply   = const Mult
  tokValue Divide     = const Div
  tokValue LeftParen  = const ()
  tokValue RightParen = const ()

---- Step 1: Decide an Order of Operations -------------------------------------

-- 1. Atomic         -- literals, parentheses
-- 3. Multiplicative -- multiply, divide
-- 2. Additive       -- plus, minus

---- Step 2: Define Parsers for each Precedence --------------------------------

-- This makes our types look neater.
-- We:
--   - have `Void` errors
--   - parse `Kind` tokens
--   - always consume input (`nil` is `False`)
--   - assume locked variables consume input and parse expressions
--   - have no free variables
--   - and parse an expression
ExprParser : SnocList String -> Type
ExprParser locked = Parser Void Kind False (map (:- (False, Expr)) locked) [<] Expr

-- By construction, our parsers grab data right associatively.
-- We use this function to apply operators left associatively.
reduceLeft : (Expr, List (Expr -> Expr -> Expr, Expr)) -> Expr
reduceLeft (hd, rest) = foldl (\acc, (op, arg) => op acc arg) hd rest

atomicExpr : ExprParser [<"open"]
atomicExpr =
  -- We will either
  OneOf
  [ -- ...wrap literal values in the `Lit` constructor...
    Lit <$> match Literal
  , -- ...or use `enclose` to surround expressions...
    enclose (match LeftParen) (match RightParen)
      -- ...and `Var` to recurse to the top level
      (Var $ %%%"open")
  ]

multiplicativeExpr : ExprParser [<"open"]
multiplicativeExpr =
  reduceLeft <$>
  (  -- We first match an atomic...
     atomicExpr <**>
     -- ...then we repeat zero or more times...
     star (
       -- ...matching an multiplicative operator...
       (match Multiply <|> match Divide) <**>
       -- ...and then matching another atomic.
       -- We need to `weaken` because atomic expects the variable `open` to be "locked".
       -- However, as earlier atomics and matching the operator consume some input stream,
       -- `open` has been "freed". We must weaken to forget that `open` is free.
       -- `S Z` is the length of the singleton list [<"open"]
       weaken (S Z) atomicExpr))

additiveExpr : ExprParser [<"open"]
additiveExpr  =
  reduceLeft <$> (
    multiplicativeExpr <**>
    star (
      (match Plus <|> match Minus) <**>
      weaken (S Z) multiplicativeExpr))

---- Step 3: Tie the Recursive Knot with `Fix` ---------------------------------

-- We have no free variables in our top-level parser.
-- We use `Fix` to express our intent to do recursion.
-- We then give the name of the recursive variable ("open"),
-- and finally the expression we will recurse over.
parser : ExprParser [<]
parser =
  Fix "open" additiveExpr

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
%hint
parserOk : WellFormed ListSet Arithmetic.parser
parserOk = Refl

---- Step 5: Construct the Parse Function --------------------------------------

-- Construct the parser from an expression with `parse`.
-- Run the parser with `.runParser`, giving the initial state (in this case unit).
parseExpr :
  (xs : List (WithBounds $ Token Kind)) ->
  Result (ParseErr Void Kind) xs False Expr
parseExpr = (parse ListSet parser).runParser ()
