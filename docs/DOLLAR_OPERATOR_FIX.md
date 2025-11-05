# The `$` Operator Issue and Fix

## Summary

Cure's typeclass specifications use operators containing `$` (dollar sign), which were causing lexer errors. This document explains the issue, why we need these operators, and how we fixed it.

## The Problem

### Error Message
```
Error: Lexical Analysis failed: {{unexpected_character,36},82,9}
```
- Character 36 is ASCII for `$`
- Occurred when parsing typeclass specification files

### Root Cause
The lexer (`src/lexer/cure_lexer.erl`) only recognized characters in the `operators()` map. When it encountered `$`, it threw `{lexer_error, {unexpected_character, 36}, Line, Column}`.

This happened at two locations:
- **Line 448**: `scan_single_char/4` - handles single-character operators
- **Line 630**: `scan_one_token/3` - used during string interpolation

## Why We Need `$` Operators

These operators come from **Haskell's Functor and Applicative typeclasses** and are standard in functional programming languages.

### The Operators

#### Functor Operators

1. **`<$` (replace-left)** - Replace all values in a container with a constant
   ```cure
   def (<$)(value: A, fb: F(B)): F(A) =
     map(fn(_) -> value end, fb)
   ```
   
   Example usage:
   ```cure
   5 <$ Some(10)     # Result: Some(5)
   "x" <$ [1,2,3]    # Result: ["x", "x", "x"]
   ```

2. **`$>` (replace-right)** - Same as `<$` but with flipped arguments
   ```cure
   def ($>)(fa: F(A), value: B): F(B) =
     map(fn(_) -> value end, fa)
   ```
   
   Example usage:
   ```cure
   Some(10) $> 5     # Result: Some(5)
   [1,2,3] $> "x"    # Result: ["x", "x", "x"]
   ```

#### Applicative Operators

3. **`<*>` (apply)** - Apply a function in a context to a value in a context
   ```cure
   def (<*>)(ff: F(A -> B), fa: F(A)): F(B)
   ```

4. **`*>` (sequence-right)** - Sequence two actions, keeping only the second result
   ```cure
   def (*>)(fa: F(A), fb: F(B)): F(B)
   ```

5. **`<*` (sequence-left)** - Sequence two actions, keeping only the first result
   ```cure
   def (<*)(fa: F(A), fb: F(B)): F(A)
   ```

#### Monad Operators

6. **`>>=` (bind)** - Monadic bind operator
   ```cure
   def (>>=)(ma: M(A), f: A -> M(B)): M(B) = bind(ma, f)
   ```

7. **`>>` (then)** - Sequence two monadic actions, discarding the first result
   ```cure
   def (>>)(ma: M(A), mb: M(B)): M(B) =
     ma >>= fn(_) -> mb end
   ```

### Why Use `$` Specifically?

1. **Historical Convention**: Established by Haskell decades ago
   - `<$>` is the infix operator for `fmap` (our `map`)
   - `<$` and `$>` are natural variants

2. **Visual Distinction**: The `$` clearly indicates:
   - Function application
   - Value replacement
   - "Lifting" operations into contexts

3. **Ecosystem Compatibility**: Anyone familiar with Functor/Applicative expects these names
   - Haskell programmers
   - Scala programmers (similar operators)
   - PureScript programmers
   - Elm programmers (adapted versions)

4. **Semantic Clarity**: The operators form a visual pattern:
   - `<` points to what's kept
   - `$` indicates the operation
   - `>` shows direction

## The Fix

### What We Changed

Added the new operators to the `operators()` map in `src/lexer/cure_lexer.erl`:

```erlang
operators() ->
    #{
        % ... existing operators ...
        <<"|>">> => '|>',
        <<"#{">>=>>  'interpolation_start',
        % Functor/Applicative operators
        <<"<$">> => '<$',
        <<"$>">> => '$>',
        <<"<*>">> => '<*>',
        <<"*>">> => '*>',
        <<"<*">> => '<*',
        % Monad operators
        <<">>=">> => '>>=',
        <<">>">> => '>>'
    }.
```

### How It Works

The lexer now follows this process:

1. **Three-character check**: Tries `<*>` and `>>=` first (lines 412-421)
2. **Two-character check**: Tries `<$`, `$>`, `*>`, `<*`, `>>` (lines 429-441)
3. **Single-character check**: Only if no multi-char match (lines 444-454)

The order matters because:
- `<*>` must be checked before `<*` and `*>`
- `>>=` must be checked before `>>`
- Longer operators take precedence

### Testing

Verified the fix works:
```bash
$ erl -pa _build/ebin -noshell -eval \
  "case cure_lexer:tokenize_file(\"lib/typeclass_spec/typeclass.cure\") of \
     {ok, Tokens} -> io:format(\"Success! Tokenized ~p tokens~n\", [length(Tokens)]); \
     {error, E} -> io:format(\"Error: ~p~n\", [E]) \
   end, halt(0)."
   
Success! Tokenized 1026 tokens
```

## Alternative Approaches (Not Chosen)

### Option 2: Use Different Operator Names

We could have avoided `$` by using different names:

```cure
def replace_left(value: A, fb: F(B)): F(A)
def replace_right(fa: F(A), value: B): F(B)
```

**Rejected because**:
- Loses the elegant infix notation
- Breaks compatibility with functional programming conventions
- Makes code more verbose
- Reduces readability for experienced functional programmers

### Option 3: Use Unicode Operators

We could have used Unicode symbols:

```cure
def (⊳)(value: A, fb: F(B)): F(A)  # U+22B3 CONTAINS AS NORMAL SUBGROUP
def (⊲)(fa: F(A), value: B): F(B)  # U+22B2 NORMAL SUBGROUP OF
```

**Rejected because**:
- Harder to type on standard keyboards
- Not widely recognized in the functional programming community
- Adds unnecessary complexity
- Poor tool support

## Impact on Existing Code

### No Breaking Changes

Adding these operators is **backward compatible**:
- Existing code continues to work
- `$` was previously an error, so no code used it
- Parser needs updates to handle operator definitions

### What's Still Needed

1. **Parser Updates**: Add grammar rules for operator function definitions
   ```cure
   def (<$)(value: A, fb: F(B)): F(A) = ...
   ```

2. **Operator Precedence**: Define precedence and associativity
   - `<$` and `$>`: Same as `map` (high precedence)
   - `<*>`: Lower than `<$` (function application)
   - `*>` and `<*`: Same as `<*>`
   - `>>=` and `>>`: Lowest (sequencing)

3. **Type System**: Already supports these through typeclass definitions

## References

- **Haskell Functor**: https://hackage.haskell.org/package/base/docs/Data-Functor.html
- **Haskell Applicative**: https://hackage.haskell.org/package/base/docs/Control-Applicative.html
- **Haskell Monad**: https://hackage.haskell.org/package/base/docs/Control-Monad.html
- **Learn You a Haskell**: http://learnyouahaskell.com/functors-applicative-functors-and-monoids

## Summary of Changes

### Files Modified
- `src/lexer/cure_lexer.erl` - Added 7 new operators to `operators()` map

### Operators Added
- `<$` - Functor replace-left
- `$>` - Functor replace-right  
- `<*>` - Applicative apply
- `*>` - Applicative sequence-right
- `<*` - Applicative sequence-left
- `>>=` - Monad bind
- `>>` - Monad then

### Testing Status
- ✅ Lexer successfully tokenizes typeclass specifications
- ⏳ Parser grammar rules needed for operator definitions
- ⏳ Operator precedence rules needed
- ✅ Type system already supports typeclasses

## Next Steps

1. **Update Parser**: Add grammar rules for operator function definitions
2. **Define Precedence**: Establish operator precedence table
3. **Move Typeclass Files**: Once parser is ready, move from `lib/typeclass_spec/` to `lib/std/`
4. **Documentation**: Add operator documentation to language guide
5. **Examples**: Create example programs using these operators
