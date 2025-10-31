# Polymorphism in Cure

## Overview

Cure now supports parametric polymorphism (generics), allowing functions and types to be parameterized over types. This enables writing generic, reusable code while maintaining static type safety.

## Phase 1: Basic Parametric Polymorphism ✅ COMPLETED

### Features Implemented

#### 1. Polymorphic Function Definitions

Functions can now have type parameters using angle bracket syntax:

```cure
def identity<T>(x: T) -> T = x

def map<T, U>(f: T -> U, xs: List(T)) -> List(U) = ...

def compose<A, B, C>(g: B -> C, f: A -> B) -> (A -> C) = ...
```

#### 2. Type Parameter Syntax

- **Simple type parameters**: `<T>`, `<T, U>`, `<A, B, C>`
- **Bounded type parameters** (syntax support added): `<T: Eq>`, `<T: Eq + Ord>`
- Type parameters are single uppercase letters or follow patterns like `T`, `U`, `A`, `B`, `C`, etc.

#### 3. AST Extensions

**New Records** (`cure_ast.hrl`):
- `type_param_decl` - Represents type parameter declarations with optional bounds
- `poly_type` - Represents polymorphic types with forall quantification
- `type_var` - Represents type variables in type expressions

**Extended Records**:
- `function_def.type_params` - List of type parameter atoms for polymorphic functions
- `type_def.type_params` - List of type parameters for polymorphic type definitions

#### 4. Parser Support

**New Functions** (`cure_parser.erl`):
- `parse_type_parameter_list/2` - Parses `<T, U>` syntax
- `parse_type_bounds/2` - Parses type bounds like `Eq + Ord`

**Syntax Supported**:
```cure
def fn_name<T>(x: T) -> T = ...              % Simple type param
def fn_name<T, U>(x: T) -> U = ...           % Multiple type params
def fn_name<T: Eq>(x: T) -> Bool = ...       % Bounded type param (syntax only)
```

#### 5. Type System Support

**New Functions** (`cure_types.erl`):
- `instantiate_polymorphic_type/2` - Creates fresh type variables for type parameters
- `instantiate_poly_type/1` - Instantiates poly_type records with fresh variables
- `instantiate_poly_type/2` - Explicit type application with concrete types
- `fresh_type_vars_for_params/1` - Generates fresh type variables
- `extract_type_param_names/1` - Extracts names from type parameter list
- `apply_poly_substitution/2` - Applies type substitution to polymorphic types

**Type Instantiation**:
```erlang
% Given: forall T. T -> T
PolyType = {function_type, [{primitive_type, 'T'}], {primitive_type, 'T'}},
InstType = cure_types:instantiate_polymorphic_type(PolyType, ['T']).
% Result: {function_type, [TypeVar1], TypeVar1} where TypeVar1 is fresh
```

#### 6. Type Checker Integration

**New Functions** (`cure_typechecker.erl`):
- `check_polymorphic_function/8` - Type checks polymorphic function definitions
- `check_multiclause_polymorphic_function/4` - Handles multi-clause polymorphic functions

**Type Checking Process**:
1. Extract type parameter names from declaration
2. Add type parameters as type variables to environment
3. Process function parameters with type-parameter-enhanced environment
4. Check function body and infer types
5. Wrap result in `poly_type` record for storage

## Usage Examples

### Identity Function

```cure
def identity<T>(x: T) -> T = x

% Usage (implicit instantiation):
identity(42)        % Inferred as identity<Int>(42) -> Int
identity("hello")   % Inferred as identity<String>("hello") -> String
```

### List Map

```cure
def map<T, U>(f: T -> U, xs: List(T)) -> List(U) =
  match xs do
    [] -> []
    [h | t] -> [f(h) | map<T, U>(f, t)]
  end

% Usage:
map<Int, String>(int_to_string, [1, 2, 3])  % Explicit type args
map(int_to_string, [1, 2, 3])                % Implicit (to be implemented in Phase 2)
```

### Pair Projection

```cure
def first<T, U>(pair: {T, U}) -> T = 
  match pair do
    {x, _} -> x
  end

def second<T, U>(pair: {T, U}) -> U =
  match pair do
    {_, y} -> y
  end
```

### Function Composition

```cure
def compose<A, B, C>(g: B -> C, f: A -> B) -> (A -> C) =
  fn(x: A) -> g(f(x))

% Usage:
add_one = fn(x: Int) -> x + 1
double = fn(x: Int) -> x * 2
add_one_then_double = compose<Int, Int, Int>(double, add_one)
```

## Implementation Details

### Type Variable Generation

Fresh type variables are generated for each instantiation of a polymorphic function:

```erlang
% First call: identity<Int>
TVar1 = #type_var{id = 1, name = 'T'}
InstType1 = {function_type, [TVar1], TVar1}  % Specialized to Int

% Second call: identity<String>  
TVar2 = #type_var{id = 2, name = 'T'}
InstType2 = {function_type, [TVar2], TVar2}  % Specialized to String
```

### Environment Management

During type checking, type parameters are added to the environment as primitive types:

```erlang
% For function: def map<T, U>(f: T -> U, xs: List(T)) -> List(U)
Env1 = extend_env(Env, 'T', {primitive_type, 'T'}),
Env2 = extend_env(Env1, 'U', {primitive_type, 'U'}),
% Now T and U can be used in parameter and return types
```

### Poly Type Representation

Polymorphic functions are stored with `poly_type` wrapper:

```erlang
#poly_type{
    type_params = ['T', 'U'],
    constraints = [],  % For bounded polymorphism
    body_type = {function_type, [...], ...},
    location = Location
}
```

## Phase 2: Enhanced Type Inference ✅ COMPLETED

### Features Implemented

#### 1. Automatic Type Instantiation

**New Functions** (`cure_types.erl`):
- `instantiate_polymorphic_type_if_needed/1` - Automatically instantiates poly_type
- Enhanced `infer_expr` for identifier lookup with automatic instantiation

**Behavior**:
```cure
def identity<T>(x: T) -> T = x

% Now works without explicit type arguments!
identity(42)        % Automatically inferred as identity<Int>
identity("hello")   % Automatically inferred as identity<String>
```

#### 2. Poly_type Unification Support

Added unification clauses for `poly_type` records:
- Instantiates polymorphic types before unification
- Supports poly_type in both positions
- Maintains type safety through fresh variable generation

#### 3. Let-Polymorphism (Hindley-Milner)

**New Functions** (`cure_types.erl`):
- `generalize_type/2` - Generalizes types with free type variables
- `free_type_vars/1` - Finds free type variables in a type
- `free_type_vars_in_env/1` - Finds free type variables in environment

**Classic Example**:
```cure
def test() -> {Int, String} =
  let id = fn(x) -> x in
  % id is automatically generalized to: forall T. T -> T
  {id(42), id("hello")}  % Both uses are valid!
end
```

**Features**:
- Automatic generalization at let bindings
- Quantifies over type variables free in binding but not in environment
- Enables using same local function at multiple types
- Follows Hindley-Milner Algorithm W

#### 4. Enhanced Constraint Solving

Constraint solver now properly handles:
- Polymorphic type constraints
- Type variable quantification
- Fresh variable generation during instantiation

### Examples

See `examples/let_polymorphism_test.cure` for:
- Classic let-polymorphism
- Nested polymorphic bindings
- Polymorphic recursion in let
- Multiple uses of generalized functions

## Next Phases

### Phase 3: Monomorphization ✅ COMPLETED

**Completed Tasks**:
- ✅ **Phase 3.1**: Collect instantiation sites - `collect_call_sites/1` tracks all polymorphic calls
- ✅ **Phase 3.2**: Generate specialized function variants - `generate_specializations/3` creates monomorphic versions
- ✅ **Phase 3.3**: Transform calls to specialized versions - `transform_ast_with_specializations/2` rewrites calls
- ✅ **Phase 3.4**: Dead code elimination - `eliminate_unused_specializations/2` removes unused code

**Implementation** (`cure_type_optimizer.erl`):
- `monomorphize_ast/2` - Main entry point orchestrating all phases
- `create_monomorphic_function/3` - Generates specialized function from polymorphic definition
- `specialize_function_body/3` - Substitutes type parameters in function body
- `replace_poly_calls_in_expr/2` - Transforms all expressions to use specialized variants
- `find_reachable_functions/2` - Builds call graph to identify dead code

**Achieved Goals**:
✅ Zero-cost polymorphism through monomorphization
✅ Efficient BEAM bytecode generation
✅ Optimal performance for polymorphic code

**Example**:
```cure
% Original polymorphic function:
def identity<T>(x: T) -> T = x

% After monomorphization, generates:
identity_Int(x: Int) -> Int = x
identity_String(x: String) -> String = x

% Calls are transformed:
identity(42)       % becomes: identity_Int(42)
identity("hello")  % becomes: identity_String("hello")
```

### Phase 4: Trait System (Ad-hoc Polymorphism)

**Tasks**:
- **Phase 4.1**: Define trait system AST
- **Phase 4.2**: Parse trait definitions and implementations
- **Phase 4.3**: Trait-constrained type inference

**Goals**:
- Type classes / traits for bounded polymorphism
- Operator overloading
- Method resolution and dispatch

## Testing

Test file: `examples/polymorphic_test.cure`

Contains examples of:
- Simple polymorphic functions (identity)
- Multi-parameter type functions (map, first)
- Higher-order polymorphic functions (compose)
- Recursive polymorphic functions (filter)

## Technical Notes

### Type Parameter Naming Conventions

Type parameters follow Cure's naming conventions:
- Single uppercase letters: `T`, `U`, `V`, `A`, `B`, `C`
- Numbered variants: `T1`, `T2`, `U1`, `U2`
- Semantic names: `Elem`, `Key`, `Value` (future)

### Compatibility

- **Backward compatible**: Existing monomorphic code works unchanged
- **Gradual typing**: Can mix polymorphic and monomorphic code
- **Dependent types**: Polymorphism works alongside dependent types

### Performance Considerations

- **Type checking**: Polymorphic functions add minimal type checking overhead
- **Runtime**: Current implementation doesn't optimize yet (Phase 3)
- **Code size**: No specialization yet, so no code duplication
- **Future**: Monomorphization will provide zero-cost abstractions

## References

- **AST definitions**: `src/parser/cure_ast.hrl`
- **Parser**: `src/parser/cure_parser.erl`
- **Type system**: `src/types/cure_types.erl`
- **Type checker**: `src/types/cure_typechecker.erl`
- **Examples**: `examples/polymorphic_test.cure`

## Contribution Guidelines

When extending polymorphism support:

1. **Maintain backward compatibility** with existing code
2. **Follow Erlang conventions** for module organization
3. **Add comprehensive tests** for new features
4. **Document type inference rules** for complex cases
5. **Consider monomorphization impact** for Phase 3

## Known Limitations (Current Phase)

- Type arguments must be explicitly specified at call sites
- No type argument inference yet (coming in Phase 2)
- No bounded polymorphism implementation (syntax only)
- No trait system yet (Phase 4)
- Monomorphization not implemented (Phase 3)

## Contact & Support

For questions or issues with polymorphism:
- Review implementation in source files listed above
- Check examples in `examples/polymorphic_test.cure`
- Refer to Phase 2+ plans for upcoming features
