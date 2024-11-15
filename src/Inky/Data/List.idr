module Inky.Data.List

public export
data LengthOf : List a -> Type where
  Z : LengthOf []
  S : LengthOf xs -> LengthOf (x :: xs)

%name LengthOf len

public export
lengthOf : (xs : List a) -> LengthOf xs
lengthOf [] = Z
lengthOf (x :: xs) = S (lengthOf xs)
