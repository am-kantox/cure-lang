# Automatic Typeclass Derivation in Cure

## Overview

Cure supports automatic derivation of typeclass instances for user-defined types using the `derive` clause. This feature eliminates boilerplate code and ensures consistency across your codebase.

## Syntax

### Basic Derivation

```cure
record Point do
    x: Int
    y: Int
end
derive Show, Eq, Ord
```

This automatically generates instances for `Show(Point)`, `Eq(Point)`, and `Ord(Point)`.

### Derivation with Type Parameters

```cure
record Container(T) do
    value: T
    name: String
end
derive Show, Eq
```

When deriving for parameterized types, the compiler automatically adds constraints:
```cure
% Generated instances:
instance Show(Container(T)) where Show(T) do
    def show(c: Container(T)): String = ...
end

instance Eq(Container(T)) where Eq(T) do
    def ==(c1: Container(T), c2: Container(T)): Bool = ...
end
```

## Supported Typeclasses

### Show

Derives a string representation of the type:

```cure
record Person do
    name: String
    age: Int
end
derive Show

% Usage:
let p = Person { name: "Alice", age: 30 }
show(p)  % "Person { name: \"Alice\", age: 30 }"
```

**Generated Implementation:**
- Records: `TypeName { field1: show(value1), field2: show(value2), ... }`
- Shows all fields in declaration order

### Eq

Derives structural equality checking:

```cure
record Point do
    x: Int
    y: Int
end
derive Eq

% Usage:
let p1 = Point { x: 10, y: 20 }
let p2 = Point { x: 10, y: 20 }
p1 == p2  % true
```

**Generated Implementation:**
- Implements `==` operator
- Default `!=` provided by typeclass
- Compares all fields for equality

### Ord

Derives lexicographic ordering:

```cure
record Person do
    name: String
    age: Int
end
derive Ord  % Requires Eq as superclass

% Usage:
let alice = Person { name: "Alice", age: 30 }
let bob = Person { name: "Bob", age: 25 }

match compare(alice, bob) do
    LT -> "Alice comes before Bob"
    EQ -> "Equal"
    GT -> "Alice comes after Bob"
end
```

**Generated Implementation:**
- Implements `compare` method returning `Ordering` (LT, EQ, or GT)
- Compares fields in declaration order (lexicographic)
- Automatically adds `Eq` constraint

## Constraint Inference

The derive mechanism automatically infers required constraints for parameterized types:

```cure
record Pair(A, B) do
    first: A
    second: B
end
derive Show, Eq

% Compiler generates:
% instance Show(Pair(A, B)) where Show(A), Show(B) do ... end
% instance Eq(Pair(A, B)) where Eq(A), Eq(B) do ... end
```

**Rules:**
1. For each type variable in fields, add corresponding constraint
2. Primitive types (Int, String, etc.) don't require constraints
3. Nested parameterized types require constraints for their parameters

## When to Use Manual Instances

While derivation is convenient, sometimes you need custom behavior:

### Custom Show Format

```cure
record Temperature do
    celsius: Float
end

% Manual instance for custom formatting
instance Show(Temperature) do
    def show(t: Temperature): String =
        float_to_string(t.celsius) ++ "°C"
end
```

### Custom Equality

```cure
record Person do
    id: Int
    name: String
    metadata: Map(String, String)
end

% Derive Show but manually implement Eq (compare only by ID)
derive Show

instance Eq(Person) do
    def ==(p1: Person, p2: Person): Bool =
        p1.id == p2.id  % Ignore name and metadata
end
```

### Custom Ordering

```cure
record Task do
    priority: Int
    name: String
    deadline: Timestamp
end

derive Show, Eq

% Custom ordering by priority, then deadline
instance Ord(Task) do
    def compare(t1: Task, t2: Task): Ordering =
        match compare(t1.priority, t2.priority) do
            EQ -> compare(t1.deadline, t2.deadline)
            result -> result
        end
end
```

## Limitations and Constraints

### What Can Be Derived

- ✅ Records with concrete field types
- ✅ Records with type parameters
- ✅ Nested records
- ✅ Empty records (unit types)

### What Cannot Be Derived

- ❌ Function types
- ❌ FSM types
- ❌ Recursive types (requires manual implementation)
- ❌ Types with existential quantification

### Typeclass Support

Currently supported:
- `Show` - String representation
- `Eq` - Equality testing
- `Ord` - Ordering/comparison

Not yet supported:
- `Functor` - Requires higher-kinded types
- `Monad` - Requires higher-kinded types
- `Semigroup` / `Monoid` - Requires domain knowledge

## Complete Examples

### Basic Usage

```cure
module geometry

record Point do
    x: Float
    y: Float
end
derive Show, Eq

def distance(p1: Point, p2: Point): Float =
    let dx = p1.x - p2.x
    let dy = p1.y - p2.y
    sqrt(dx * dx + dy * dy)

def main(): Unit =
    let origin = Point { x: 0.0, y: 0.0 }
    let p = Point { x: 3.0, y: 4.0 }
    
    println(show(origin))  % "Point { x: 0.0, y: 0.0 }"
    println(show(p))       % "Point { x: 3.0, y: 4.0 }"
    
    if origin == p then
        println("Points are equal")
    else
        let dist = distance(origin, p)
        println("Distance: " ++ show(dist))
    end
```

### Parameterized Types

```cure
module collections

record Box(T) do
    value: T
end
derive Show, Eq

def map_box(f: T -> U, box: Box(T)): Box(U) =
    Box { value: f(box.value) }

def main(): Unit where Show(Int), Show(String) =
    let int_box = Box { value: 42 }
    let str_box = map_box(int_to_string, int_box)
    
    println(show(int_box))  % "Box { value: 42 }"
    println(show(str_box))  % "Box { value: \"42\" }"
```

### Hierarchical Data

```cure
module organization

record Address do
    street: String
    city: String
    country: String
end
derive Show, Eq

record Person do
    name: String
    age: Int
    address: Address
end
derive Show, Eq, Ord

record Department do
    name: String
    manager: Person
    employees: List(Person)
end
derive Show, Eq

def main(): Unit =
    let addr = Address {
        street: "123 Main St",
        city: "Springfield",
        country: "USA"
    }
    
    let manager = Person {
        name: "Alice",
        age: 35,
        address: addr
    }
    
    let dept = Department {
        name: "Engineering",
        manager: manager,
        employees: []
    }
    
    println(show(dept))
```

## Best Practices

### 1. Derive by Default

Start with derivation for standard typeclasses:
```cure
record MyType do
    field1: T1
    field2: T2
end
derive Show, Eq
```

### 2. Custom When Needed

Override with manual instances only when necessary:
```cure
% Derive most instances
derive Show, Ord

% But custom Eq for special logic
instance Eq(MyType) do
    def ==(a: MyType, b: MyType): Bool = ...
end
```

### 3. Document Custom Instances

When manually implementing, explain why:
```cure
% Custom equality compares only the ID field
% because other fields are metadata that should be ignored
instance Eq(User) do
    def ==(u1: User, u2: User): Bool =
        u1.id == u2.id
end
```

### 4. Order Fields Intentionally

For derived `Ord`, field order matters:
```cure
% First name, then age for ordering
record Person do
    name: String    % Primary sort key
    age: Int        % Secondary sort key
    email: String   % Tertiary sort key
end
derive Ord
```

### 5. Consider Performance

Derived instances are straightforward but not always optimal:
```cure
% Many fields - derived Eq checks all
record LargeRecord do
    id: Int
    field1: String
    field2: String
    % ... 50 more fields
end

% Better: manual Eq that checks ID first
instance Eq(LargeRecord) do
    def ==(r1: LargeRecord, r2: LargeRecord): Bool =
        r1.id == r2.id  % Fast path
end
```

## Implementation Details

### Code Generation

Derived instances generate AST nodes equivalent to hand-written code:

```cure
record Point do x: Int, y: Int end
derive Show

% Equivalent to:
instance Show(Point) do
    def show(p: Point): String =
        "Point { x: " ++ show(p.x) ++ ", y: " ++ show(p.y) ++ " }"
end
```

### Compilation Phases

1. **Parse**: Recognize `derive` clause in AST
2. **Validate**: Check typeclass is derivable for type
3. **Generate**: Create instance definition AST
4. **Typecheck**: Verify generated instance is well-typed
5. **Codegen**: Compile instance to BEAM bytecode

### Performance Characteristics

- **Compile-time**: Zero runtime overhead
- **Generated code**: Equivalent to hand-written instances
- **Binary size**: No difference from manual implementations

## FAQ

**Q: Can I derive instances for existing types?**  
A: No, derive clauses must appear in the same module as the type definition.

**Q: Can I derive partial instances?**  
A: No, you either derive the complete instance or write it manually.

**Q: What if I derive and manually define the same instance?**  
A: Compiler error - instance coherence violation.

**Q: Can I derive instances conditionally?**  
A: Not directly, but you can use different type definitions in different modules.

**Q: How do I debug derived instances?**  
A: Use compiler flags to emit generated code for inspection.

## See Also

- [Typeclass Guide](./TYPECLASS_GUIDE.md) - Complete typeclass system documentation
- [Type System](./TYPE_SYSTEM.md) - Cure's type system overview
- [Standard Library](./STDLIB.md) - Built-in typeclass instances
