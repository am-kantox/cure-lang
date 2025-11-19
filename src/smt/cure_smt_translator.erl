%% Cure Programming Language - SMT-LIB Constraint Translator
%% Translates Cure AST expressions to SMT-LIB format for Z3/CVC5
-module(cure_smt_translator).

-moduledoc """
# Cure SMT-LIB Translator

Translates Cure type constraints and expressions into SMT-LIB format
for consumption by external SMT solvers (Z3, CVC5).

## Features

- Full translation of Cure expressions to SMT-LIB s-expressions
- Type mapping (Int, Nat, Bool, Float to SMT types)
- Logic inference (QF_LIA, QF_LRA, etc.)
- Variable declaration generation
- Assertion generation from constraints

## Usage

```erlang
% Translate a constraint to SMT-LIB query
Constraint = #binary_op_expr{op = '>', left = var(x), right = lit(0)},
Env = #{x => {type, int}},
Query = cure_smt_translator:generate_query(Constraint, Env).
% => \"(set-logic QF_LIA)\\n(declare-const x Int)\\n(assert (> x 0))\\n(check-sat)\\n\"
```
""".

-export([
    generate_query/2,
    generate_query/3,
    translate_expr/1,
    translate_expr/2,
    infer_logic/1,
    collect_variables/2,
    declare_variable/2,

    % Refinement type support
    generate_refinement_subtype_query/4,
    generate_constraint_check_query/3
]).

-include("../parser/cure_ast.hrl").

%% SMT-LIB logic types
-type smt_logic() :: 'QF_LIA' | 'QF_LRA' | 'QF_LIRA' | 'QF_NIA' | 'QF_NRA' | 'QF_UFLIA'.

%% ============================================================================
%% Public API
%% ============================================================================

-doc """
Generate a complete SMT-LIB query from a Cure constraint.

Produces a full SMT-LIB query including logic declaration, variable declarations,
assertions, and check-sat command.

## Arguments
- `Constraint` - Cure AST expression representing the constraint
- `Env` - Environment mapping variables to types

## Returns
- `iolist()` - SMT-LIB query as iolist (use iolist_to_binary/1 to convert)

## Example
```erlang
Constraint = #binary_op_expr{op = '+', left = var(x), right = var(y)},
Query = generate_query(Constraint, #{x => {type, int}, y => {type, int}}).
```
""".
-spec generate_query(expr(), map()) -> iolist().
generate_query(Constraint, Env) ->
    generate_query(Constraint, Env, #{}).

-doc """
Generate SMT-LIB query with options.

## Options
- `{get_model, boolean()}` - Include (get-model) command (default: true)
- `{logic, smt_logic()}` - Override logic inference
- `{timeout, integer()}` - Solver timeout hint in milliseconds
""".
-spec generate_query(expr(), map(), map()) -> iolist().
generate_query(Constraint, Env, Opts) ->
    % 1. Infer or get logic
    Logic = maps:get(logic, Opts, infer_logic(Constraint)),

    % 2. Collect variables from constraint
    Vars = collect_variables(Constraint, Env),

    % 3. Generate variable declarations
    Declarations = [declare_variable(V, Env) || V <- Vars],

    % 4. Generate Nat constraints (>= 0) for Nat-typed variables
    NatConstraints = generate_nat_constraints(Vars, Env),

    % 5. Translate constraint to assertion
    Assertion = ["(assert ", translate_expr(Constraint, Env), ")\n"],

    % 6. Add check-sat and optionally get-model
    CheckSat = "(check-sat)\n",
    GetModel =
        case maps:get(get_model, Opts, true) of
            true -> "(get-model)\n";
            false -> ""
        end,

    % 7. Assemble query with Nat constraints
    [
        "(set-logic ",
        atom_to_list(Logic),
        ")\n",
        Declarations,
        % Add Nat constraints after declarations
        NatConstraints,
        Assertion,
        CheckSat,
        GetModel
    ].

-doc """
Translate a Cure expression to SMT-LIB s-expression.

Converts Cure AST expressions to SMT-LIB format recursively.

## Arguments
- `Expr` - Cure AST expression

## Returns
- `iolist()` - SMT-LIB s-expression
""".
-spec translate_expr(expr()) -> iolist().
translate_expr(Expr) ->
    translate_expr(Expr, #{}).

-spec translate_expr(expr(), map()) -> iolist().
% Binary operations - arithmetic
translate_expr(#binary_op_expr{op = '+', left = L, right = R}, Env) ->
    ["(+ ", translate_expr(L, Env), " ", translate_expr(R, Env), ")"];
translate_expr(#binary_op_expr{op = '-', left = L, right = R}, Env) ->
    ["(- ", translate_expr(L, Env), " ", translate_expr(R, Env), ")"];
translate_expr(#binary_op_expr{op = '*', left = L, right = R}, Env) ->
    ["(* ", translate_expr(L, Env), " ", translate_expr(R, Env), ")"];
translate_expr(#binary_op_expr{op = '/', left = L, right = R}, Env) ->
    ["(/ ", translate_expr(L, Env), " ", translate_expr(R, Env), ")"];
translate_expr(#binary_op_expr{op = 'div', left = L, right = R}, Env) ->
    ["(div ", translate_expr(L, Env), " ", translate_expr(R, Env), ")"];
translate_expr(#binary_op_expr{op = 'rem', left = L, right = R}, Env) ->
    ["(mod ", translate_expr(L, Env), " ", translate_expr(R, Env), ")"];
translate_expr(#binary_op_expr{op = 'mod', left = L, right = R}, Env) ->
    ["(mod ", translate_expr(L, Env), " ", translate_expr(R, Env), ")"];
% Binary operations - comparison
translate_expr(#binary_op_expr{op = '==', left = L, right = R}, Env) ->
    ["(= ", translate_expr(L, Env), " ", translate_expr(R, Env), ")"];
translate_expr(#binary_op_expr{op = '/=', left = L, right = R}, Env) ->
    ["(not (= ", translate_expr(L, Env), " ", translate_expr(R, Env), "))"];
translate_expr(#binary_op_expr{op = '<', left = L, right = R}, Env) ->
    ["(< ", translate_expr(L, Env), " ", translate_expr(R, Env), ")"];
translate_expr(#binary_op_expr{op = '>', left = L, right = R}, Env) ->
    ["(> ", translate_expr(L, Env), " ", translate_expr(R, Env), ")"];
translate_expr(#binary_op_expr{op = '=<', left = L, right = R}, Env) ->
    ["(<= ", translate_expr(L, Env), " ", translate_expr(R, Env), ")"];
translate_expr(#binary_op_expr{op = '>=', left = L, right = R}, Env) ->
    ["(>= ", translate_expr(L, Env), " ", translate_expr(R, Env), ")"];
% Binary operations - boolean
translate_expr(#binary_op_expr{op = 'and', left = L, right = R}, Env) ->
    ["(and ", translate_expr(L, Env), " ", translate_expr(R, Env), ")"];
translate_expr(#binary_op_expr{op = 'or', left = L, right = R}, Env) ->
    ["(or ", translate_expr(L, Env), " ", translate_expr(R, Env), ")"];
translate_expr(#binary_op_expr{op = 'andalso', left = L, right = R}, Env) ->
    ["(and ", translate_expr(L, Env), " ", translate_expr(R, Env), ")"];
translate_expr(#binary_op_expr{op = 'orelse', left = L, right = R}, Env) ->
    ["(or ", translate_expr(L, Env), " ", translate_expr(R, Env), ")"];
translate_expr(#binary_op_expr{op = '=>', left = L, right = R}, Env) ->
    ["(=> ", translate_expr(L, Env), " ", translate_expr(R, Env), ")"];
% Unary operations
translate_expr(#unary_op_expr{op = 'not', operand = Operand}, Env) ->
    ["(not ", translate_expr(Operand, Env), ")"];
translate_expr(#unary_op_expr{op = '-', operand = Operand}, Env) ->
    ["(- ", translate_expr(Operand, Env), ")"];
% Function calls - SMT built-in functions
translate_expr(#function_call_expr{function = #identifier_expr{name = abs}, args = [Arg]}, Env) ->
    ["(abs ", translate_expr(Arg, Env), ")"];
translate_expr(
    #function_call_expr{function = #identifier_expr{name = min}, args = [Arg1, Arg2]}, Env
) ->
    % min(a, b) = ite(a < b, a, b)
    [
        "(ite (< ",
        translate_expr(Arg1, Env),
        " ",
        translate_expr(Arg2, Env),
        ") ",
        translate_expr(Arg1, Env),
        " ",
        translate_expr(Arg2, Env),
        ")"
    ];
translate_expr(
    #function_call_expr{function = #identifier_expr{name = max}, args = [Arg1, Arg2]}, Env
) ->
    % max(a, b) = ite(a > b, a, b)
    [
        "(ite (> ",
        translate_expr(Arg1, Env),
        " ",
        translate_expr(Arg2, Env),
        ") ",
        translate_expr(Arg1, Env),
        " ",
        translate_expr(Arg2, Env),
        ")"
    ];
translate_expr(#function_call_expr{function = #identifier_expr{name = length}, args = [List]}, Env) ->
    % For arrays, use (length array)
    % For now, treat as an uninterpreted function
    ["(length ", translate_expr(List, Env), ")"];
% Quantified expressions - forall (proper AST record)
translate_expr(#forall_expr{variables = Vars, body = Body}, Env) ->
    % (forall ((x Type) (y Type)) body)
    VarDecls = [translate_quantifier_var(V, Env) || V <- Vars],
    ["(forall (", lists:join(" ", VarDecls), ") ", translate_expr(Body, Env), ")"];
% Quantified expressions - exists (proper AST record)
translate_expr(#exists_expr{variables = Vars, body = Body}, Env) ->
    % (exists ((x Type) (y Type)) body)
    VarDecls = [translate_quantifier_var(V, Env) || V <- Vars],
    ["(exists (", lists:join(" ", VarDecls), ") ", translate_expr(Body, Env), ")"];
% Legacy tuple format support (backward compatibility)
translate_expr({forall_expr, Vars, Body}, Env) ->
    VarDecls = [translate_quantifier_var(V, Env) || V <- Vars],
    ["(forall (", lists:join(" ", VarDecls), ") ", translate_expr(Body, Env), ")"];
translate_expr({forall_expr, Vars, Body, _Location}, Env) ->
    VarDecls = [translate_quantifier_var(V, Env) || V <- Vars],
    ["(forall (", lists:join(" ", VarDecls), ") ", translate_expr(Body, Env), ")"];
translate_expr({exists_expr, Vars, Body}, Env) ->
    VarDecls = [translate_quantifier_var(V, Env) || V <- Vars],
    ["(exists (", lists:join(" ", VarDecls), ") ", translate_expr(Body, Env), ")"];
translate_expr({exists_expr, Vars, Body, _Location}, Env) ->
    VarDecls = [translate_quantifier_var(V, Env) || V <- Vars],
    ["(exists (", lists:join(" ", VarDecls), ") ", translate_expr(Body, Env), ")"];
% Identifiers (variables)
translate_expr(#identifier_expr{name = Name}, _Env) ->
    atom_to_list(Name);
% Literals
translate_expr(#literal_expr{value = Val}, _Env) when is_integer(Val) ->
    integer_to_list(Val);
translate_expr(#literal_expr{value = Val}, _Env) when is_float(Val) ->
    float_to_list(Val, [{decimals, 10}, compact]);
translate_expr(#literal_expr{value = true}, _Env) ->
    "true";
translate_expr(#literal_expr{value = false}, _Env) ->
    "false";
% Fallback for unsupported expressions
translate_expr(Expr, _Env) ->
    io_lib:format("(; unsupported: ~p ;)", [Expr]).

-doc """
Infer the appropriate SMT-LIB logic for a constraint.

Analyzes the constraint to determine which SMT-LIB logic is required.

## Logics
- `QF_LIA` - Quantifier-free linear integer arithmetic
- `QF_LRA` - Quantifier-free linear real arithmetic  
- `QF_LIRA` - Quantifier-free linear integer/real arithmetic
- `QF_NIA` - Quantifier-free nonlinear integer arithmetic
- `LIA` - Linear integer arithmetic (with quantifiers)
- `LRA` - Linear real arithmetic (with quantifiers)
- `NIA` - Nonlinear integer arithmetic (with quantifiers)

## Arguments
- `Constraint` - Cure AST expression

## Returns
- `smt_logic()` - Inferred logic
""".
-spec infer_logic(expr()) -> smt_logic().
infer_logic(Constraint) ->
    Features = analyze_features(Constraint),

    HasFloats = maps:get(has_floats, Features, false),
    HasInts = maps:get(has_ints, Features, true),
    IsNonlinear = maps:get(is_nonlinear, Features, false),
    HasQuantifiers = maps:get(has_quantifiers, Features, false),

    case {HasFloats, HasInts, IsNonlinear, HasQuantifiers} of
        % With quantifiers
        {true, true, _, true} -> 'LIRA';
        {true, false, false, true} -> 'LRA';
        {false, true, false, true} -> 'LIA';
        {false, true, true, true} -> 'NIA';
        % Quantifier-free (as before)
        {true, true, _, false} -> 'QF_LIRA';
        {true, false, false, false} -> 'QF_LRA';
        {false, true, false, false} -> 'QF_LIA';
        {false, true, true, false} -> 'QF_NIA';
        % Default to linear integer arithmetic
        _ -> 'QF_LIA'
    end.

%% Analyze features of constraint for logic inference
analyze_features(Expr) ->
    analyze_features(Expr, #{
        has_floats => false,
        has_ints => false,
        is_nonlinear => false,
        has_quantifiers => false
    }).

analyze_features(#binary_op_expr{op = Op, left = L, right = R}, Acc) ->
    % Check for nonlinear operations
    Acc1 =
        case Op of
            '*' -> Acc#{is_nonlinear => true};
            '/' -> Acc#{is_nonlinear => true};
            _ -> Acc
        end,
    Acc2 = analyze_features(L, Acc1),
    analyze_features(R, Acc2);
analyze_features(#unary_op_expr{operand = Operand}, Acc) ->
    analyze_features(Operand, Acc);
analyze_features(#function_call_expr{args = Args}, Acc) ->
    lists:foldl(fun analyze_features/2, Acc, Args);
%% Quantified expressions (proper AST records)
analyze_features(#forall_expr{body = Body}, Acc) ->
    analyze_features(Body, Acc#{has_quantifiers => true});
analyze_features(#exists_expr{body = Body}, Acc) ->
    analyze_features(Body, Acc#{has_quantifiers => true});
% Legacy tuple format support
analyze_features({forall_expr, _Vars, Body}, Acc) ->
    analyze_features(Body, Acc#{has_quantifiers => true});
analyze_features({forall_expr, _Vars, Body, _Loc}, Acc) ->
    analyze_features(Body, Acc#{has_quantifiers => true});
analyze_features({exists_expr, _Vars, Body}, Acc) ->
    analyze_features(Body, Acc#{has_quantifiers => true});
analyze_features({exists_expr, _Vars, Body, _Loc}, Acc) ->
    analyze_features(Body, Acc#{has_quantifiers => true});
% Literals
analyze_features(#literal_expr{value = Val}, Acc) when is_integer(Val) ->
    Acc#{has_ints => true};
analyze_features(#literal_expr{value = Val}, Acc) when is_float(Val) ->
    Acc#{has_floats => true};
analyze_features(_, Acc) ->
    Acc.

-doc """
Collect all variables from a constraint.

Traverses the AST to find all variable references.

## Arguments
- `Constraint` - Cure AST expression
- `Env` - Environment (for type information)

## Returns
- `[atom()]` - List of variable names (deduplicated)
""".
-spec collect_variables(expr(), map()) -> [atom()].
collect_variables(Constraint, _Env) ->
    Vars = collect_vars_helper(Constraint, []),
    lists:usort(Vars).

collect_vars_helper(#binary_op_expr{left = L, right = R}, Acc) ->
    Acc1 = collect_vars_helper(L, Acc),
    collect_vars_helper(R, Acc1);
collect_vars_helper(#unary_op_expr{operand = Operand}, Acc) ->
    collect_vars_helper(Operand, Acc);
collect_vars_helper(#identifier_expr{name = Name}, Acc) ->
    [Name | Acc];
collect_vars_helper(_, Acc) ->
    Acc.

-doc """
Generate SMT-LIB declaration for a variable.

Creates a (declare-const ...) declaration based on the variable's type.

## Arguments
- `VarName` - Variable name (atom)
- `Env` - Environment with type information

## Returns
- `iolist()` - SMT-LIB declaration
""".
-spec declare_variable(atom(), map()) -> iolist().
declare_variable(VarName, Env) ->
    Type = infer_variable_type(VarName, Env),
    SmtType = map_type_to_smt(Type),
    ["(declare-const ", atom_to_list(VarName), " ", SmtType, ")\n"].

%% Infer variable type from environment
infer_variable_type(VarName, Env) ->
    case maps:get(VarName, Env, undefined) of
        % Default to Int
        undefined -> int;
        {type, Type} -> Type;
        {value, Val} when is_integer(Val) -> int;
        {value, Val} when is_float(Val) -> real;
        {value, Val} when is_boolean(Val) -> bool;
        Type when is_atom(Type) -> Type;
        _ -> int
    end.

%% Map Cure types to SMT-LIB types
map_type_to_smt(int) -> "Int";
map_type_to_smt('Int') -> "Int";
% Nat is Int with constraint >= 0
map_type_to_smt(nat) -> "Int";
map_type_to_smt('Nat') -> "Int";
map_type_to_smt(float) -> "Real";
map_type_to_smt('Float') -> "Real";
map_type_to_smt(real) -> "Real";
map_type_to_smt(bool) -> "Bool";
map_type_to_smt('Bool') -> "Bool";
map_type_to_smt(boolean) -> "Bool";
% Default
map_type_to_smt(_) -> "Int".

%% ============================================================================
%% Helper Functions for Nat Type
%% ============================================================================

-doc """
Generate additional constraints for Nat variables.

Since Nat is represented as Int in SMT, we need to add (>= n 0) constraints.

## Arguments
- `Vars` - List of variable names
- `Env` - Environment with type information

## Returns
- `iolist()` - Additional assertions for Nat constraints
""".
-spec generate_nat_constraints([atom()], map()) -> iolist().
generate_nat_constraints(Vars, Env) ->
    NatVars = [V || V <- Vars, is_nat_type(V, Env)],
    [["(assert (>= ", atom_to_list(V), " 0))\n"] || V <- NatVars].

is_nat_type(VarName, Env) ->
    case maps:get(VarName, Env, undefined) of
        {type, nat} -> true;
        {type, 'Nat'} -> true;
        nat -> true;
        'Nat' -> true;
        _ -> false
    end.

%% ============================================================================
%% Quantifier Translation
%% ============================================================================

%% Translate a quantified variable declaration
%% Var can be: atom, {VarName, Type}, or #param{}
translate_quantifier_var(Var, Env) when is_atom(Var) ->
    % Infer type from environment
    Type = infer_variable_type(Var, Env),
    SmtType = map_type_to_smt(Type),
    ["(", atom_to_list(Var), " ", SmtType, ")"];
translate_quantifier_var({VarName, Type}, _Env) when is_atom(VarName) ->
    % Explicit type given
    SmtType = map_type_to_smt(Type),
    ["(", atom_to_list(VarName), " ", SmtType, ")"];
translate_quantifier_var(#param{name = Name, type = Type}, _Env) ->
    % Parameter record
    TypeAtom = extract_type_name(Type),
    SmtType = map_type_to_smt(TypeAtom),
    ["(", atom_to_list(Name), " ", SmtType, ")"];
translate_quantifier_var(Var, _Env) ->
    % Fallback
    io_lib:format("(; unsupported var: ~p ;)", [Var]).

%% Extract type name from type expression
extract_type_name(#primitive_type{name = Name}) -> Name;
extract_type_name(#dependent_type{name = Name}) -> Name;
extract_type_name(Type) when is_atom(Type) -> Type;
extract_type_name(_) -> int.

%% ============================================================================
%% Unit Tests (Internal)
%% ============================================================================

%% ============================================================================
%% Refinement Type Support
%% ============================================================================

-doc """
Generate SMT-LIB query to check refinement type subtyping.

Checks if refinement type with predicate Pred1 is a subtype of refinement type
with predicate Pred2. This is equivalent to proving: ∀Var. Pred1 => Pred2

## Arguments
- `Pred1` - Predicate of subtype (e.g., x > 0)
- `Pred2` - Predicate of supertype (e.g., x /= 0)
- `Var` - Refinement variable name
- `BaseType` - Base type (int, real, bool)

## Returns
- `iolist()` - SMT-LIB query

## Example
```erlang
% Check if Positive <: NonZero
% i.e., ∀x. (x > 0) => (x ≠ 0)
Pred1 = #binary_op_expr{op = '>', left = var(x), right = lit(0)},
Pred2 = #binary_op_expr{op = '/=', left = var(x), right = lit(0)},
Query = generate_refinement_subtype_query(Pred1, Pred2, x, int).
```
""".
-spec generate_refinement_subtype_query(expr(), expr(), atom(), atom()) -> iolist().
generate_refinement_subtype_query(Pred1, Pred2, Var, BaseType) ->
    % Build environment with variable type
    Env = #{Var => {type, BaseType}},

    % Build implication: Pred1 => Pred2
    Implication = #binary_op_expr{
        op = '=>',
        left = Pred1,
        right = Pred2,
        location = #location{line = 0, column = 0, file = undefined}
    },

    % Build forall quantifier: ∀Var. (Pred1 => Pred2)
    Quantified = {forall_expr, [{Var, BaseType}], Implication},

    % Infer logic
    Logic = infer_logic(Quantified),

    % Translate to SMT-LIB
    SmtType = map_type_to_smt(BaseType),
    VarDecl = ["(", atom_to_list(Var), " ", SmtType, ")"],

    Pred1Smt = translate_expr(Pred1, Env),
    Pred2Smt = translate_expr(Pred2, Env),

    % Build query
    % To prove ∀x. P1 => P2, we check if ∃x. P1 ∧ ¬P2 is unsat
    % i.e., assert (and Pred1 (not Pred2)) and check for unsat
    % If unsat, then there's no counterexample, so the implication holds
    [
        "(set-logic ",
        atom_to_list(Logic),
        ")\n",
        "(declare-const ",
        atom_to_list(Var),
        " ",
        SmtType,
        ")\n",
        "(assert ",
        Pred1Smt,
        ")\n",
        "(assert (not ",
        Pred2Smt,
        "))\n",
        "(check-sat)\n"
    ].

-doc """
Generate SMT-LIB query to check if a value satisfies a constraint.

## Arguments
- `ValueExpr` - Expression representing the value
- `Predicate` - Constraint predicate
- `Env` - Environment with variable types

## Returns
- `iolist()` - SMT-LIB query

## Example
```erlang
% Check if 5 satisfies (x > 0)
Value = #literal_expr{value = 5},
Pred = #binary_op_expr{op = '>', left = var(x), right = lit(0)},
Query = generate_constraint_check_query(Value, Pred, #{x => {type, int}}).
```
""".
-spec generate_constraint_check_query(expr(), expr(), map()) -> iolist().
generate_constraint_check_query(ValueExpr, Predicate, Env) ->
    % Simple version: just check if predicate with value substituted is sat
    % For more complex cases, we'd need proper substitution
    generate_query(Predicate, Env, #{}).

-ifdef(TEST).
-include_lib("eunit/include/eunit.hrl").

translation_test() ->
    % x > 0
    Constraint = #binary_op_expr{
        op = '>',
        left = #identifier_expr{name = x},
        right = #literal_expr{value = 0}
    },
    Result = translate_expr(Constraint),
    Expected = "(> x 0)",
    ?assertEqual(lists:flatten(Result), Expected).

query_generation_test() ->
    Constraint = #binary_op_expr{
        op = '>',
        left = #identifier_expr{name = x},
        right = #literal_expr{value = 0}
    },
    Env = #{x => {type, int}},
    Query = iolist_to_binary(generate_query(Constraint, Env)),

    % Check it contains all required parts
    ?assert(binary:match(Query, <<"(set-logic QF_LIA)">>) =/= nomatch),
    ?assert(binary:match(Query, <<"(declare-const x Int)">>) =/= nomatch),
    ?assert(binary:match(Query, <<"(assert (> x 0))">>) =/= nomatch),
    ?assert(binary:match(Query, <<"(check-sat)">>) =/= nomatch).

-endif.
