# Function Types in Cure

## Overview

Cure uses the `=>` operator to denote function types, distinct from the `->` operator used in pattern matching, lambdas, and FSM transitions.

## Syntax

### Function Type Arrow: `=>`
Used to specify function types in type annotations:

```cure
# Simple function type
def map(f: A => B, list: List(A)): List(B)

# Curried function type (right-associative)
def compose(f: A => B, g: B => C): A => C

# Function type nested in type constructor
def ap(ff: F(A => B), x: F(A)): F(B)

# Function returning function
def curry(f: (A, B) => C): A => B => C
```

### Match/Lambda Arrow: `->`
Used for pattern matching and lambda expressions:

```cure
# Match arms
match list do
  [] -> 0
  [x | xs] -> x + sum(xs)
end

# Lambda expressions
map(fn(x) -> x * 2 end, numbers)

# FSM transitions
state Ready do
  event(start) -> Running
end
```

## Rationale

The separation eliminates parsing ambiguity:

```cure
# Without separation, this is ambiguous:
def func(f: A -> B, x: A): B  # Is "A -> B" a type or part of a match?

# With =>, it's clear:
def func(f: A => B, x: A): B  # A => B is clearly a function type
```

## Type System Integration

### In Typeclasses

```cure
typeclass Functor(F) do
  def map(f: A => B, x: F(A)): F(B)
end

typeclass Monad(M) do
  def bind(m: M(A), f: A => M(B)): M(B)
end
```

### In Type Definitions

```cure
type Handler(A, B) = A => B
type Predicate(A) = A => Bool
type Callback(A) = A => Unit
```

### In Function Signatures

```cure
# Higher-order function
def filter(pred: A => Bool, list: List(A)): List(A)

# Function taking function returning function
def compose(f: B => C, g: A => B): A => C

# Multiple function parameters
def foldMap(f: A => B, op: B => B => B, init: B, list: List(A)): B
```

## Implementation Details

- **Lexer**: `=>` is tokenized as a two-character operator
- **Parser**: `parse_type_with_arrows` handles `=>` for function types
- **Operator Precedence**: `=>` is NOT an expression operator (not in `get_operator_info`)
- **Type Parameters**: `parse_type_parameter` calls `parse_type` to properly handle function types in contexts like `F(A => B)`

## Examples

### Simple Function Type
```cure
def apply(f: A => B, x: A): B = f(x)
```

### Nested Function Type
```cure
typeclass Applicative(F) do
  def ap(ff: F(A => B), x: F(A)): F(B)
end
```

### Curried Function Type
```cure
def add: Int => Int => Int = fn(x) -> fn(y) -> x + y end end
```

### Function Composition
```cure
def compose(f: B => C, g: A => B): A => C =
  fn(x) -> f(g(x)) end
```

## Migration Guide

If you have existing code using `->` for function types, replace with `=>`:

```cure
# Before
def map(f: A -> B, x: F(A)): F(B)

# After  
def map(f: A => B, x: F(A)): F(B)
```

Note: Do NOT change `->` in match arms, lambdas, or FSM transitions!

## See Also

- [Typeclass System](TYPECLASSES.md)
- [Pattern Matching](PATTERN_MATCHING.md)
- [Lambda Expressions](LAMBDAS.md)
