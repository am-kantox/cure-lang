## Typeclass Guide for Cure

**Version**: 1.0  
**Last Updated**: November 22, 2025

---

## Table of Contents

1. [Introduction](#introduction)
2. [Quick Start](#quick-start)
3. [Typeclass Definitions](#typeclass-definitions)
4. [Instance Definitions](#instance-definitions)
5. [Automatic Derivation](#automatic-derivation)
6. [Using Typeclasses](#using-typeclasses)
7. [Standard Library](#standard-library)
8. [Advanced Topics](#advanced-topics)
9. [Best Practices](#best-practices)
10. [Troubleshooting](#troubleshooting)

---

## Introduction

### What are Typeclasses?

Typeclasses are Cure's mechanism for **ad-hoc polymorphism** - allowing you to write generic code that works with any type that satisfies certain requirements. They're similar to:

- **Interfaces** in Java/C# (but more powerful)
- **Traits** in Rust
- **Protocols** in Elixir/Clojure
- **Type Classes** in Haskell (the inspiration)

### Why Use Typeclasses?

**1. Code Reuse**: Write generic functions once
```cure
def sort(list: List(T)): List(T) where Ord(T)
% Works with ANY orderable type
```

**2. Type Safety**: Compiler ensures constraints are met
```cure
% This won't compile - String doesn't have Num instance
def add_numbers(x: String, y: String) where Num(String) = x + y
```

**3. Zero Boilerplate**: Automatic derivation
```cure
record Point do x: Int, y: Int end
derive Show, Eq, Ord  % No manual implementation needed!
```

**4. Performance**: Monomorphization means zero runtime cost

---

## Quick Start

### 1. Define a Typeclass

```cure
typeclass Drawable(T) do
    def draw(x: T): String
    def size(x: T): {Int, Int}
end
```

### 2. Implement an Instance

```cure
record Circle do
    radius: Float
end

instance Drawable(Circle) do
    def draw(c: Circle): String = "⭕"
    def size(c: Circle): {Int, Int} = {c.radius * 2, c.radius * 2}
end
```

### 3. Use with Constraints

```cure
def render(obj: T): String where Drawable(T) =
    draw(obj)

% Works with any Drawable type
render(Circle { radius: 5.0 })  % "⭕"
```

---

## Typeclass Definitions

### Basic Syntax

```cure
typeclass TypeclassName(TypeParam) do
    def method_name(params): ReturnType
    % ... more methods
end
```

### Methods

**Required Methods** (must be implemented by instances):
```cure
typeclass Show(T) do
    def show(x: T): String
end
```

**Default Methods** (optional, can be overridden):
```cure
typeclass Eq(T) do
    def (==)(x: T, y: T): Bool
    def (!=)(x: T, y: T): Bool = not (x == y)  % Default
end
```

### Superclass Constraints

Typeclasses can require other typeclasses:

```cure
typeclass Ord(T) when Eq(T) do
    def compare(x: T, y: T): Ordering
    % Ord requires Eq
end
```

### Multiple Type Parameters

```cure
typeclass Convertible(From, To) do
    def convert(x: From): To
end
```

---

## Instance Definitions

### Basic Instance

```cure
instance Show(Int) do
    def show(x: Int): String = int_to_string(x)
end
```

### Parameterized Instances

For generic types, add constraints:

```cure
instance Show(List(T)) where Show(T) do
    def show(list: List(T)): String =
        "[" ++ join(", ", map(show, list)) ++ "]"
end
```

### Instance Rules

**1. Coherence**: Only one instance per typeclass/type pair
```cure
% ❌ ERROR: Duplicate instance
instance Show(Int) do ... end
instance Show(Int) do ... end  % Compiler error!
```

**2. Orphan Prevention**: Instances must be in same module as type or typeclass
```cure
% ✅ OK: In same module as Int definition (built-in)
instance Show(Int) do ... end

% ✅ OK: In same module as Circle definition
instance Show(Circle) do ... end

% ❌ ERROR: Orphan instance (neither Show nor String defined here)
instance Show(String) do ... end  % If not in Std module
```

---

## Automatic Derivation

### Syntax

```cure
record TypeName do
    % fields
end
derive TypeclassA, TypeclassB, TypeclassC
```

### Supported Typeclasses

#### Show - String Representation

```cure
record Point do
    x: Int
    y: Int
end
derive Show

% Generates:
% show(Point{x: 10, y: 20}) → "Point { x: 10, y: 20 }"
```

#### Eq - Equality Testing

```cure
record Person do
    name: String
    age: Int
end
derive Eq

% Generates structural equality:
% Person{name: "Alice", age: 30} == Person{name: "Alice", age: 30} → true
```

#### Ord - Ordering

```cure
record Book do
    title: String
    year: Int
end
derive Ord  % Automatically includes Eq

% Lexicographic ordering by fields (title, then year)
```

### Constraint Inference

For parameterized types, constraints are inferred automatically:

```cure
record Container(T) do
    value: T
end
derive Show

% Compiler generates:
% instance Show(Container(T)) where Show(T) do ... end
```

### When NOT to Derive

**Custom Behavior Needed**:
```cure
record Temperature do celsius: Float end

% Manual instance for custom formatting
instance Show(Temperature) do
    def show(t: Temperature): String =
        float_to_string(t.celsius) ++ "°C"
end
```

**Performance Optimization**:
```cure
record User do
    id: Int
    name: String
    metadata: Map(String, String)  % Large field
end

% Custom Eq that only compares ID (faster)
instance Eq(User) do
    def ==(u1: User, u2: User): Bool = u1.id == u2.id
end
```

---

## Using Typeclasses

### Function Constraints

Single constraint:
```cure
def print_value(x: T): Unit where Show(T) =
    println(show(x))
```

Multiple constraints:
```cure
def compare_and_show(x: T, y: T): String where Ord(T), Show(T) =
    match compare(x, y) do
        LT -> show(x) ++ " < " ++ show(y)
        EQ -> show(x) ++ " == " ++ show(y)
        GT -> show(x) ++ " > " ++ show(y)
    end
```

### Generic Algorithms

```cure
% Generic sort - works with ANY Ord type
def sort(list: List(T)): List(T) where Ord(T) =
    match list do
        [] -> []
        [pivot | rest] ->
            let smaller = [x | x <- rest, compare(x, pivot) == LT]
            let larger = [x | x <- rest, compare(x, pivot) != LT]
            sort(smaller) ++ [pivot] ++ sort(larger)
    end

% Use with different types
sort([3, 1, 4, 1, 5])              % Sort Ints
sort(["cat", "ant", "dog"])        % Sort Strings  
sort([Person{...}, Person{...}])   % Sort custom types
```

---

## Standard Library

### Core Typeclasses

#### Show
```cure
typeclass Show(T) do
    def show(x: T): String
end

% Instances: Int, Float, String, Bool, Atom, List(T), Option(T), Result(T,E)
% Helper: print, println, debug
```

#### Eq
```cure
typeclass Eq(T) do
    def (==)(x: T, y: T): Bool
    def (!=)(x: T, y: T): Bool  % Default
end

% Instances: All primitive types, List(T), Option(T), Result(T,E)
% Helper: elem, nub, same_elements
```

#### Ord
```cure
typeclass Ord(T) when Eq(T) do
    def compare(x: T, y: T): Ordering
    def (<)(x: T, y: T): Bool    % Default
    def (<=)(x: T, y: T): Bool   % Default
    def (>)(x: T, y: T): Bool    % Default
    def (>=)(x: T, y: T): Bool   % Default
end

% Instances: Int, Float, String, List(T)
% Helper: max, min, clamp
```

#### Functor
```cure
typeclass Functor(F) do
    def map(f: A -> B, fa: F(A)): F(B)
end

% Instances: List, Option, Result(*, E)
% Helper: map_nested, void, as
```

#### Applicative
```cure
typeclass Applicative(F) when Functor(F) do
    def pure(x: A): F(A)
    def (<*>)(ff: F(A -> B), fa: F(A)): F(B)
end

% Instances: List, Option, Result(*, E)
```

#### Monad
```cure
typeclass Monad(M) when Applicative(M) do
    def bind(ma: M(A), f: A -> M(B)): M(B)
    def (>>=)(ma: M(A), f: A -> M(B)): M(B)  % Alias
end

% Instances: List, Option, Result(*, E)
```

### Importing Typeclasses

```cure
% Import specific typeclasses and methods
import typeclass [Show, Eq, show, compare]

% Import all from standard library
import Std [*]
```

---

## Advanced Topics

### Higher-Kinded Types

Support for container types:

```cure
% Functor works with List, Option, Result, etc.
typeclass Functor(F) do
    def map(f: A -> B, fa: F(A)): F(B)
end

instance Functor(Option) do
    def map(f: A -> B, opt: Option(A)): Option(B) =
        match opt do
            Some(x) -> Some(f(x))
            None -> None
        end
end
```

### Associated Types

(Future feature - not yet implemented)

```cure
typeclass Collection(C) do
    type Element
    def empty(): C
    def insert(elem: Element, coll: C): C
end
```

### Overlapping Instances

Not allowed - ensures coherence:

```cure
% ❌ ERROR: Overlapping instances
instance Show(List(Int)) do ... end
instance Show(List(T)) where Show(T) do ... end
```

### Conditional Instances

Instances can have constraints:

```cure
instance Ord(Option(T)) where Ord(T) do
    def compare(opt1: Option(T), opt2: Option(T)): Ordering =
        match {opt1, opt2} do
            {None, None} -> EQ
            {None, Some(_)} -> LT
            {Some(_), None} -> GT
            {Some(x), Some(y)} -> compare(x, y)
        end
end
```

---

## Best Practices

### 1. Prefer Derivation

Start with derive, override only when needed:

```cure
% ✅ Good: Use derive for standard behavior
record Point do x: Int, y: Int end
derive Show, Eq, Ord

% ❌ Avoid: Manual implementation unless necessary
```

### 2. Name Methods Clearly

```cure
% ✅ Good: Clear method names
typeclass Serializable(T) do
    def serialize(x: T): String
    def deserialize(s: String): Option(T)
end

% ❌ Bad: Ambiguous names
typeclass Serializable(T) do
    def to(x: T): String
    def from(s: String): Option(T)
end
```

### 3. Use Superclass Constraints

```cure
% ✅ Good: Express dependencies
typeclass Ord(T) when Eq(T) do
    def compare(x: T, y: T): Ordering
end

% ❌ Bad: Duplicate Eq methods in Ord
```

### 4. Document Instances

```cure
% Custom instance with non-obvious behavior
% Orders products by price (ascending)
instance Ord(Product) do
    def compare(p1: Product, p2: Product): Ordering =
        compare(p1.price, p2.price)
end
```

### 5. Test Generic Code

```cure
% Test with multiple types
def test_sort() =
    assert sort([3,1,2]) == [1,2,3]
    assert sort(["c","a","b"]) == ["a","b","c"]
    assert sort([Point{x:2,y:1}, Point{x:1,y:1}]) == [Point{x:1,y:1}, Point{x:2,y:1}]
```

---

## Troubleshooting

### Common Errors

**1. No Instance Found**
```
Error: No instance of Show(MyType)
```
**Solution**: Add derive or manual instance
```cure
derive Show  % or
instance Show(MyType) do ... end
```

**2. Overlapping Instances**
```
Error: Overlapping instance for Show(List(Int))
```
**Solution**: Remove one instance, keep the more general one

**3. Missing Constraint**
```
Error: Cannot use '==' on type T
```
**Solution**: Add Eq constraint
```cure
def contains(x: T, list: List(T)) where Eq(T) = ...
```

**4. Orphan Instance**
```
Error: Orphan instance Show(ExternalType)
```
**Solution**: Define instance in same module as type or typeclass

### Debugging Tips

**1. Check Instance Resolution**
```cure
% Explicitly annotate types to see what instances are used
let result: Int = show(42)  % Uses Show(Int)
```

**2. Simplify Constraints**
```cure
% If complex constraints fail, break into simpler functions
def complex(x: T) where Show(T), Eq(T), Ord(T) = ...

% Becomes:
def simple_show(x: T) where Show(T) = ...
def simple_eq(x: T) where Eq(T) = ...
```

**3. Check Derivation**
```cure
% Verify generated instance exists
record Test do x: Int end
derive Show

% Test it
show(Test{x: 42})  % Should work
```

---

## Known Limitations

### Ord Typeclass Temporarily Disabled

**Status**: Compiler bug prevents Ord typeclass from compiling

**Issue**: Union type variants cannot be returned from typeclass instance methods due to a type unification bug:
```
Error: Type mismatch - unification failed between
  {primitive_type,'Ordering'} and {union_type,'Ordering',...}
```

**Impact**:
- The `Ord` typeclass and `Ordering` type are commented out in `lib/std/typeclasses.cure`
- You cannot use `compare()` method or derive `Ord` instances
- `Show`, `Eq`, and `Serializable` typeclasses work correctly

**Workaround**:
Use comparison operators (`<`, `>`, `<=`, `>=`) directly instead of the `compare()` method:
```cure
% ❌ Won't work until bug is fixed
def sort(list: List(T)) where Ord(T) = ...

% ✅ Use direct comparisons instead
def sort_int(list: List(Int)): List(Int) =
    % Use < and > operators directly
    ...
```

**Expected Fix**: The compiler's typeclass instance type checker needs to properly handle union type constructors.

---

## Examples

See these files for complete examples:
- `examples/08_typeclasses.cure` - Basic typeclass usage
- `examples/09_derive.cure` - Automatic derivation
- `examples/10_generic_algorithms.cure` - Real-world generic code

---

## Additional Resources

- [Derive Guide](./DERIVE_GUIDE.md) - Detailed derivation documentation
- [Implementation Status](./TYPECLASS_IMPLEMENTATION_STATUS.md) - Technical details
- [Type System](./TYPE_SYSTEM.md) - Cure's type system overview

---

*For questions or issues, see the project repository or documentation.*
