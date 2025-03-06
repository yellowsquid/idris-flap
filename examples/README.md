# Examples

Here are some examples of how to use `flap` of increasing complexity.

1. `Arithmetic` shows how to parse arithmetic expressions.

## General Strategy

Here is a general formula for constructing parsers:

- Define the tokens
- Decide an order of operations
- Define parsers for each precedence
- Tie the recursive knot with `Fix`
- Check for parser well-formedness
- Construct the parse function

### Define the Tokens

Start with a type of token kinds, say `Kind`. This data type should implement
`TokenKind`.

### Decide an Order of Operations

Some operations bind subterms more tightly than others. For example, addition
has a lower precedence than multiplication.

### Define Parsers for each Precedence

Starting with the highest precedence operations, define parsers. Use a "locked"
variable (e.g. `"open"`) to refer to arbitrary subterms. This is useful within
parentheses for example. For higher precedence subterms, use the names
explicitly. Depending on the structure of your grammar, you may have to use
`weaken` to coerce the types.

### Tie the Recursive Knot with `Fix`

Use the `Fix` constructor to bind the variable for open terms. The body of the
fixed point should be the lowest-precedence parser.

### Check for Parser Well-Formedness

Check that your parser is deterministic by proving that it is `WellFormed`. This
requires a definition of `Set`. The proof of well-formedness should be
`Refl`---if `Refl` doesn't work then either your parser isn't deterministic, or
you don't have visibility to compute with your choice of `Set`.

### Construct the Parse Function

Invoke `parse` with your choice of `Set` and your parser. Make sure that
auto-implicit search is able to find your proof of `WellFormed`. Invoke the
parser using `.runParser`, ensuring you provide an initial state.
