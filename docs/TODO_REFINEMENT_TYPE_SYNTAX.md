# Refinement Type Syntax Implementation Plan

**Status**: Planned  
**Priority**: High  
**Estimated Effort**: 2-3 days

## Goal

Implement full parser and typechecker support for refinement type syntax:

```cure
{var: Type | constraint}
```

### Examples

```cure
# Simple refinement
def divide(a: Int, b: {x: Int | x != 0}): Int = a / b

# Bounds with variables
def safe_access(arr: Vector(Int, n), idx: {i: Int | 0 <= i < n}): Int =
  arr[idx]

# Multiple constraints
def percentage(x: {p: Int | 0 <= p and p <= 100}): Int = p

# Nested constraints
def safe_list_access(lst: List(T), idx: {i: Int | i >= 0}): Option(T) =
  ...
```

## Current State

### Existing Infrastructure ✅

- **cure_refinement_types.erl** (609 lines) - Runtime refinement type checking
- **cure_refinement_types.hrl** - Record definitions for #refinement_type{}
- **cure_guard_refinement.erl** - Guard-based type refinement
- **cure_smt_translator.erl** - SMT translation support
- **cure_smt_solver.erl** - Z3 integration

### What's Missing ❌

1. **Parser Support**: `parse_primary_type` doesn't handle `{var: Type | constraint}`
2. **AST Integration**: Need to wire refinement_type records into type checking
3. **Constraint Verification**: SMT calls need to be integrated
4. **Error Messages**: User-friendly errors for constraint violations

## Implementation Steps

### Step 1: Parser Support (4-6 hours)

**File**: `src/parser/cure_parser.erl`

**Current**: `{` token starts tuple type parsing (line 2858)

**Change Needed**:

```erlang
% In parse_primary_type, when encountering '{'
'{' ->
    {_, State1} = expect(State, '{'),
    Location = get_token_location(current_token(State)),
    
    % Look ahead to distinguish {var: Type | constraint} from {T, U, V}
    case is_refinement_type_syntax(State1) of
        true ->
            % Parse refinement: {var: Type | constraint}
            parse_refinement_type(State1, Location);
        false ->
            % Parse tuple: {T, U, V}
            {ElementTypes, State2} = parse_tuple_type_elements(State1, []),
            {_, State3} = expect(State2, '}'),
            Type = #tuple_type{
                element_types = ElementTypes,
                location = Location
            },
            {Type, State3}
    end;
```

**New Functions Needed**:

```erlang
%% Check if '{' starts refinement type
is_refinement_type_syntax(State) ->
    % Look for pattern: identifier : Type |
    case current_token(State) of
        Token when is_identifier(Token) ->
            State1 = advance(State),
            case match_token(State1, ':') of
                true -> true;  % Looks like refinement
                false -> false % Looks like tuple
            end;
        _ ->
            false  % Tuple element
    end.

%% Parse {var: Type | constraint}
parse_refinement_type(State, Location) ->
    % Parse: identifier : Type | constraint }
    {VarToken, State1} = expect(State, identifier),
    Var = token_value_to_atom(get_token_value(VarToken)),
    
    {_, State2} = expect(State1, ':'),
    {BaseType, State3} = parse_type(State2),
    {_, State4} = expect(State3, '|'),
    {Constraint, State5} = parse_constraint_expression(State4),
    {_, State6} = expect(State5, '}'),
    
    RefinementType = #refinement_type{
        base_type = BaseType,
        variable = Var,
        predicate = Constraint,
        location = Location
    },
    {RefinementType, State6}.

%% Parse constraint expression (stops at '}')
parse_constraint_expression(State) ->
    % Parse binary expression but stop at '}'
    parse_constraint_binary_expression(State, 0).

parse_constraint_binary_expression(State, MinPrec) ->
    {Left, State1} = parse_primary_expression(State),
    parse_constraint_binary_rest(State1, Left, MinPrec).

parse_constraint_binary_rest(State, Left, MinPrec) ->
    case current_token(State) of
        eof ->
            {Left, State};
        Token ->
            TokenType = get_token_type(Token),
            % Stop at '}'
            case TokenType of
                '}' ->
                    {Left, State};
                _ ->
                    % Continue parsing operators
                    case get_operator_info(TokenType) of
                        {Prec, Assoc} when Prec >= MinPrec ->
                            {_, State1} = expect(State, TokenType),
                            NextMinPrec = case Assoc of
                                left -> Prec + 1;
                                right -> Prec
                            end,
                            {Right, State2} = parse_constraint_binary_expression(State1, NextMinPrec),
                            Location = get_token_location(Token),
                            BinOp = #binary_op_expr{
                                op = TokenType,
                                left = Left,
                                right = Right,
                                location = Location
                            },
                            parse_constraint_binary_rest(State2, BinOp, MinPrec);
                        _ ->
                            {Left, State}
                    end
            end
    end.
```

**Test Cases**:

```cure
# Simple
def f(x: {i: Int | i > 0}): Int = i

# With variable reference
def g(arr: Vector(T, n), idx: {i: Int | 0 <= i < n}): T = arr[i]

# Complex constraint
def h(x: {p: Int | p >= 0 and p <= 100}): Int = p

# Edge cases
def i(x: {a: Int | a != 0 and a != 1}): Int = a
```

### Step 2: AST Integration (2-3 hours)

**File**: `src/parser/cure_ast.hrl`

**Check**: Ensure `refinement_type` record is exported and available:

```erlang
-record(refinement_type, {
    base_type :: term(),
    variable :: atom(),
    predicate :: term(),
    location :: #location{}
}).
```

**File**: `src/types/cure_types.erl`

**Add** refinement type handling in key functions:

```erlang
%% In type_to_string
type_to_string(#refinement_type{base_type = Base, variable = Var, predicate = Pred}) ->
    BaseStr = type_to_string(Base),
    PredStr = expr_to_string(Pred),
    io_lib:format("{~s: ~s | ~s}", [Var, BaseStr, PredStr]);

%% In unify
unify(#refinement_type{base_type = Base1, predicate = Pred1},
      #refinement_type{base_type = Base2, predicate = Pred2}, Env) ->
    % Check if Pred1 => Pred2 using SMT
    case unify(Base1, Base2, Env) of
        {ok, UnifiedBase} ->
            case cure_refinement_types:check_subtype(
                #refinement_type{base_type = Base1, predicate = Pred1},
                #refinement_type{base_type = Base2, predicate = Pred2},
                Env
            ) of
                {ok, true} ->
                    {ok, #refinement_type{
                        base_type = UnifiedBase,
                        predicate = Pred2  % Use stronger constraint
                    }};
                _ ->
                    {error, refinement_mismatch}
            end;
        Error ->
            Error
    end;
```

### Step 3: Typechecker Integration (4-5 hours)

**File**: `src/types/cure_typechecker.erl`

**Add** constraint checking when values are assigned to refined types:

```erlang
%% When checking function application
check_function_application(FuncType, ArgTypes, ArgExprs, Location, Env) ->
    % ... existing code ...
    
    % For each parameter with refinement type
    lists:foreach(
        fun({ParamType, ArgExpr}) ->
            case ParamType of
                #refinement_type{variable = Var, predicate = Pred} ->
                    % Verify constraint holds for argument
                    case verify_refinement_constraint(ArgExpr, Var, Pred, Env) of
                        {ok, true} ->
                            ok;
                        {ok, false} ->
                            throw({refinement_violation, ArgExpr, Pred, Location});
                        {error, Reason} ->
                            % Conservative: warn but allow
                            add_warning({cannot_verify_refinement, Reason}, Location)
                    end;
                _ ->
                    ok
            end
        end,
        lists:zip(ParamTypes, ArgExprs)
    ).

%% Verify refinement constraint
verify_refinement_constraint(Expr, Var, Predicate, Env) ->
    % Substitute Expr for Var in Predicate
    SubstitutedPred = substitute_in_expr(Predicate, Var, Expr),
    
    % Try to evaluate or verify via SMT
    case try_static_eval(SubstitutedPred, Env) of
        {ok, true} ->
            {ok, true};
        {ok, false} ->
            {ok, false};
        {error, cannot_eval} ->
            % Use SMT to verify
            verify_with_smt(SubstitutedPred, Env)
    end.
```

### Step 4: SMT Verification (3-4 hours)

**File**: `src/types/cure_refinement_types.erl`

**Enhance** existing verification functions:

```erlang
%% Already exists, but needs integration
verify_subtype_smt(Refinement1, Refinement2, Env) ->
    % Generates SMT query: ∀x. Pred1(x) => Pred2(x)
    % Uses cure_smt_translator and Z3
    ...
```

**File**: `src/smt/cure_smt_translator.erl`

**Add** (if not exists):

```erlang
%% Generate SMT query for refinement constraint
generate_refinement_check_query(Var, BaseType, Predicate) ->
    TypeDecl = base_type_to_smt(BaseType),
    PredSMT = expr_to_smt(Predicate),
    
    [
        "(declare-const ", atom_to_list(Var), " ", TypeDecl, ")\n",
        "(assert (not ", PredSMT, "))\n",
        "(check-sat)\n"
    ].

%% Generate SMT query for subtype checking
generate_refinement_subtype_query(Pred1, Pred2, Var, BaseType) ->
    TypeDecl = base_type_to_smt(BaseType),
    Pred1SMT = expr_to_smt(Pred1),
    Pred2SMT = expr_to_smt(Pred2),
    
    [
        "(declare-const ", atom_to_list(Var), " ", TypeDecl, ")\n",
        "(assert ", Pred1SMT, ")\n",
        "(assert (not ", Pred2SMT, "))\n",
        "(check-sat)\n"  % unsat means implication holds
    ].
```

### Step 5: Error Messages (1-2 hours)

**File**: `src/parser/cure_error_reporter.erl`

**Add** user-friendly error formatting:

```erlang
format_error({refinement_violation, Expr, Predicate, Location}) ->
    ExprStr = expr_to_string(Expr),
    PredStr = expr_to_string(Predicate),
    #{{
        "message" => io_lib:format(
            "Refinement constraint violated: ~s does not satisfy ~s",
            [ExprStr, PredStr]
        ),
        "location" => format_location(Location),
        "severity" => "error"
    }};

format_error({cannot_verify_refinement, Reason}) ->
    #{{
        "message" => io_lib:format(
            "Cannot verify refinement constraint: ~p (using conservative approximation)",
            [Reason]
        ),
        "severity" => "warning"
    }}.
```

### Step 6: Testing (3-4 hours)

**Create**: `examples/07_refinement_types_demo.cure`

```cure
module RefinementDemo do
  export [main/0]
  
  import Std.Io [println]
  
  # Example 1: NonZero division
  def safe_divide(a: Int, b: {x: Int | x != 0}): Int =
    a / b
  
  # Example 2: Positive numbers
  def sqrt_positive(x: {n: Int | n > 0}): Float =
    # Implementation would go here
    0.0
  
  # Example 3: Bounded array access
  def get_element(arr: Vector(Int, n), idx: {i: Int | 0 <= i < n}): Int =
    arr[idx]
  
  # Example 4: Percentage validation
  def make_percentage(x: {p: Int | 0 <= p and p <= 100}): Int =
    p
  
  # Example 5: Compound constraints
  def process_year(year: {y: Int | y >= 1900 and y <= 2100}): Int =
    year
  
  def main(): Int =
    println("=== Refinement Types Demo ===")
    
    # These should work
    let result1 = safe_divide(10, 2)
    println("10 / 2 = " <> show(result1))
    
    # This should FAIL at compile time
    # let result2 = safe_divide(10, 0)  # ERROR: 0 does not satisfy {x: Int | x != 0}
    
    0
end
```

**Create**: `test/refinement_types_test.erl`

```erlang
-module(refinement_types_test).
-export([run/0]).

run() ->
    test_parser(),
    test_typechecker(),
    test_smt_verification(),
    io:format("All refinement type tests passed!~n").

test_parser() ->
    % Test parsing {var: Type | constraint}
    Source = "{x: Int | x > 0}",
    {ok, Tokens} = cure_lexer:tokenize(Source),
    {ok, AST} = cure_parser:parse_type_from_tokens(Tokens),
    
    % Verify AST structure
    #refinement_type{
        base_type = #primitive_type{name = 'Int'},
        variable = x,
        predicate = Pred
    } = AST,
    ok.

test_typechecker() ->
    % Test constraint verification
    ok.

test_smt_verification() ->
    % Test SMT-based subtype checking
    ok.
```

## Testing Strategy

### Unit Tests

1. **Parser tests**: Various refinement syntax forms
2. **Type unification**: Refinement type compatibility
3. **SMT queries**: Verify generated SMT-LIB is correct
4. **Error cases**: Invalid constraints, violated refinements

### Integration Tests

1. Compile `07_refinement_types_demo.cure`
2. Verify compile-time errors for violated constraints
3. Verify successful compilation for valid constraints
4. Test with Z3 installed and without (graceful degradation)

### Edge Cases

- Nested refinements: `{{i: Int | i > 0} | x > 5}`
- Multiple variable references: `{i: Int | 0 <= i < n}` where `n` is in scope
- Complex predicates: `{x: Int | x > 0 and x < 100 or x == -1}`
- Refinement in return types
- Refinement in record fields

## Success Criteria

- [ ] Parser handles `{var: Type | constraint}` syntax
- [ ] Typechecker verifies constraints at call sites
- [ ] SMT integration proves/disproves constraints
- [ ] `examples/07_refinement_types_demo.cure` compiles
- [ ] Error messages are clear and actionable
- [ ] Tests pass for all basic cases
- [ ] Documentation updated (TYPE_SYSTEM.md, FEATURE_REFERENCE.md)

## Estimated Timeline

- **Day 1**: Parser implementation and testing (Steps 1-2)
- **Day 2**: Typechecker and SMT integration (Steps 3-4)
- **Day 3**: Error messages, testing, documentation (Steps 5-6)

## Dependencies

- Z3 solver (optional, for SMT verification)
- Existing cure_refinement_types module
- cure_smt_translator for SMT-LIB generation

## Notes

- The infrastructure is already 70% there (cure_refinement_types.erl exists)
- Main work is parser support and wiring everything together
- SMT verification should gracefully degrade if Z3 not available
- Conservative approach: warn if can't verify, don't block compilation
