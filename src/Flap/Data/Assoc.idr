module Flap.Data.Assoc

export
infix 2 :-

public export
record Assoc (a : Type) where
  constructor (:-)
  name : String
  value : a

public export
Functor Assoc where
  map f x = x.name :- f x.value

namespace Irrelevant
  public export
  record Assoc0 (0 a : Type) (n : String) where
    constructor (:-)
    0 name : String
    {auto 0 prf : n = name}
    value : a

  public export
  map : (a -> b) -> Assoc0 a n -> Assoc0 b n
  map f nx = (:-) nx.name (f nx.value) @{nx.prf}

namespace Contexts
  public export
  record Assoc0 (0 p : a -> Type) (x : Assoc a) where
    constructor (:-)
    0 name : String
    {auto 0 prf : x.name = name}
    value : p x.value

  public export
  map : (forall x. p x -> q x) -> forall x. Assoc0 p x -> Assoc0 q x
  map f npx = (:-) npx.name (f npx.value) @{npx.prf}
