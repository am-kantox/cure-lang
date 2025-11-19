%% Cure LSP Code Actions - Phase 4.3
%% Quick fixes and suggestions for SMT constraint violations
-module(cure_lsp_code_actions).

-moduledoc """
# LSP Code Actions & Quick Fixes

This module provides automated fixes and suggestions for constraint violations:

## Quick Fix Categories

### 1. Add Runtime Checks
- Insert guard clauses: `when x > 0`
- Add assertions: `assert x > 0`
- Add conditional checks with error handling

### 2. Relax Constraints
- Suggest weaker constraints that would pass
- Example: `x > 0` → `x >= 0`
- Offer alternative type signatures

### 3. Add Type Annotations
- Suggest refinement types based on usage
- Auto-infer constraints from guards
- Propagate constraints from callers

### 4. Pattern Completion
- Add missing pattern match cases
- Generate exhaustive match arms

## Example Quick Fixes

**Add Guard:**
```cure
% Before
def divide(a: Int, b: Int): Int = a / b

% After
def divide(a: Int, b: Int) when b /= 0: Int = a / b
```

**Relax Constraint:**
```cure
% Error: Cannot prove Percentage <: Positive
type Percentage = Int when x >= 0 and x <= 100

% Suggested: Use NonNegative instead
type NonNegative = Int when x >= 0
def use_percentage(p: NonNegative): Int = ...
```

**Add Runtime Check:**
```cure
def process(n: Int): Result =
    if n > 0 then
        divide(100, n)
    else
        error(\"n must be positive\")
    end
```
""".

-export([
    % Code action generation
    generate_code_actions/3,
    generate_quick_fixes/2,

    % Specific fix types
    suggest_guard_clause/2,
    suggest_assertion/2,
    suggest_relaxed_constraint/2,
    suggest_type_annotation/2,
    suggest_pattern_completion/2,

    % Code edit generation
    create_text_edit/3,
    apply_code_action/2
]).

-include("../parser/cure_ast.hrl").

%%% ============================================================================
%%% Code Action Generation
%%% ============================================================================

%% @doc Generate code actions for a diagnostic at position
-spec generate_code_actions(binary(), map(), term()) -> [map()].
generate_code_actions(Uri, Diagnostic, AST) ->
    % Extract diagnostic information
    Code = maps:get(<<"code">>, Diagnostic, undefined),
    Range = maps:get(<<"range">>, Diagnostic),
    Message = maps:get(<<"message">>, Diagnostic),

    % Generate fixes based on diagnostic code
    case Code of
        <<"refinement-violation">> ->
            generate_refinement_fixes(Uri, Range, Message, AST);
        <<"non-exhaustive-pattern">> ->
            generate_pattern_fixes(Uri, Range, Message, AST);
        <<"type-mismatch">> ->
            generate_type_fixes(Uri, Range, Message, AST);
        <<"undefined-var">> ->
            generate_undefined_var_fixes(Uri, Range, Message, AST);
        _ ->
            []
    end.

%% @doc Generate quick fixes for common errors
-spec generate_quick_fixes(map(), term()) -> [map()].
generate_quick_fixes(Diagnostic, AST) ->
    Message = maps:get(<<"message">>, Diagnostic),
    Range = maps:get(<<"range">>, Diagnostic),

    % Parse diagnostic message to extract constraint information
    case extract_constraint_from_message(Message) of
        {ok, Constraint} ->
            [
                suggest_guard_clause(Range, Constraint),
                suggest_assertion(Range, Constraint),
                suggest_relaxed_constraint(Range, Constraint)
            ];
        undefined ->
            []
    end.

%%% ============================================================================
%%% Refinement Violation Fixes
%%% ============================================================================

%% Generate fixes for refinement type violations
generate_refinement_fixes(Uri, Range, Message, AST) ->
    Fixes = [],

    % Extract constraint from message
    case extract_constraint_from_message(Message) of
        {ok, Constraint} ->
            % Find the function containing this location
            case find_function_at_range(AST, Range) of
                {ok, FuncDef} ->
                    GuardFix = create_guard_clause_action(Uri, FuncDef, Constraint),
                    AssertionFix = create_assertion_action(Uri, Range, Constraint),
                    RelaxFix = create_relax_constraint_action(Uri, Range, Constraint),

                    Fixes ++ [GuardFix, AssertionFix, RelaxFix];
                _ ->
                    % Just offer assertion if we can't find function
                    [create_assertion_action(Uri, Range, Constraint)]
            end;
        _ ->
            Fixes
    end.

%% @doc Create guard clause quick fix
create_guard_clause_action(Uri, #function_def{name = Name, location = Loc} = FuncDef, Constraint) ->
    % Format constraint as guard clause
    GuardText = format_constraint_as_guard(Constraint),

    % Find insertion point (after parameters, before return type or =)
    Edit = create_guard_insertion_edit(FuncDef, GuardText),

    #{
        title => iolist_to_binary([<<"Add guard clause: when ">>, GuardText]),
        kind => <<"quickfix">>,
        diagnostics => [],
        edit => #{
            changes => #{
                Uri => [Edit]
            }
        }
    }.

%% @doc Create assertion insertion quick fix
create_assertion_action(Uri, Range, Constraint) ->
    AssertText = format_constraint_as_assertion(Constraint),

    % Insert at the beginning of the function body
    Edit = create_assertion_insertion_edit(Range, AssertText),

    #{
        title => iolist_to_binary([<<"Add assertion: ">>, AssertText]),
        kind => <<"quickfix">>,
        diagnostics => [],
        edit => #{
            changes => #{
                Uri => [Edit]
            }
        }
    }.

%% @doc Create relaxed constraint suggestion
create_relax_constraint_action(Uri, Range, Constraint) ->
    % Suggest weaker but passing constraint
    case suggest_weaker_constraint(Constraint) of
        {ok, WeakerConstraint} ->
            WeakerText = format_constraint_text(WeakerConstraint),

            #{
                title => iolist_to_binary([<<"Relax constraint to: ">>, WeakerText]),
                kind => <<"quickfix">>,
                diagnostics => [],
                edit => #{
                    changes => #{
                        Uri => [create_constraint_replacement_edit(Range, WeakerText)]
                    }
                }
            };
        undefined ->
            % Generic suggestion
            #{
                title => <<"Consider relaxing the constraint">>,
                kind => <<"refactor">>,
                diagnostics => []
            }
    end.

%%% ============================================================================
%%% Pattern Match Fixes
%%% ============================================================================

%% Generate fixes for non-exhaustive pattern matches
generate_pattern_fixes(Uri, Range, Message, AST) ->
    % Extract missing pattern from message
    case extract_missing_pattern(Message) of
        {ok, MissingPattern} ->
            [create_add_pattern_action(Uri, Range, MissingPattern, AST)];
        _ ->
            % Offer wildcard pattern as fallback
            [create_add_wildcard_pattern_action(Uri, Range)]
    end.

%% @doc Create action to add missing pattern
create_add_pattern_action(Uri, Range, MissingPattern, AST) ->
    % Find the match expression
    case find_match_at_range(AST, Range) of
        {ok, #match_expr{patterns = Patterns}} ->
            % Generate pattern clause
            PatternText = generate_pattern_clause(MissingPattern),

            % Insert after last existing pattern
            Edit = create_pattern_insertion_edit(Range, Patterns, PatternText),

            #{
                title => iolist_to_binary([
                    <<"Add missing case: ">>, format_pattern_brief(MissingPattern)
                ]),
                kind => <<"quickfix">>,
                diagnostics => [],
                edit => #{
                    changes => #{
                        Uri => [Edit]
                    }
                }
            };
        _ ->
            create_add_wildcard_pattern_action(Uri, Range)
    end.

%% @doc Create action to add wildcard pattern
create_add_wildcard_pattern_action(Uri, Range) ->
    PatternText = <<"    _ -> error(\"Unhandled case\")">>,

    #{
        title => <<"Add catch-all pattern">>,
        kind => <<"quickfix">>,
        diagnostics => [],
        edit => #{
            changes => #{
                Uri => [
                    #{
                        range => Range,
                        newText => PatternText
                    }
                ]
            }
        }
    }.

%%% ============================================================================
%%% Type Mismatch Fixes
%%% ============================================================================

%% Generate fixes for type mismatches
generate_type_fixes(Uri, Range, Message, AST) ->
    % Try to extract expected and actual types
    case extract_type_mismatch(Message) of
        {ok, Expected, Got} ->
            [
                create_type_annotation_action(Uri, Range, Expected),
                create_type_conversion_action(Uri, Range, Expected, Got)
            ];
        _ ->
            []
    end.

%% @doc Create action to add type annotation
create_type_annotation_action(Uri, Range, ExpectedType) ->
    TypeText = format_type_for_annotation(ExpectedType),

    #{
        title => iolist_to_binary([<<"Annotate type as: ">>, TypeText]),
        kind => <<"quickfix">>,
        diagnostics => [],
        edit => #{
            changes => #{
                Uri => [create_type_annotation_edit(Range, TypeText)]
            }
        }
    }.

%% @doc Create action to add type conversion
create_type_conversion_action(Uri, Range, Expected, Got) ->
    case suggest_conversion(Expected, Got) of
        {ok, ConversionFunc} ->
            #{
                title => iolist_to_binary([
                    <<"Convert using: ">>, atom_to_binary(ConversionFunc, utf8)
                ]),
                kind => <<"quickfix">>,
                diagnostics => [],
                edit => #{
                    changes => #{
                        Uri => [create_conversion_edit(Range, ConversionFunc)]
                    }
                }
            };
        undefined ->
            #{
                title => <<"Add explicit type conversion">>,
                kind => <<"refactor">>,
                diagnostics => []
            }
    end.

%%% ============================================================================
%%% Undefined Variable Fixes
%%% ============================================================================

generate_undefined_var_fixes(Uri, Range, Message, AST) ->
    case extract_variable_name(Message) of
        {ok, VarName} ->
            [
                create_add_parameter_action(Uri, Range, VarName, AST),
                create_define_variable_action(Uri, Range, VarName)
            ];
        _ ->
            []
    end.

create_add_parameter_action(Uri, Range, VarName, AST) ->
    case find_function_at_range(AST, Range) of
        {ok, FuncDef} ->
            #{
                title => iolist_to_binary([<<"Add parameter: ">>, atom_to_binary(VarName, utf8)]),
                kind => <<"quickfix">>,
                diagnostics => [],
                edit => #{
                    changes => #{
                        Uri => [create_parameter_insertion_edit(FuncDef, VarName)]
                    }
                }
            };
        _ ->
            create_define_variable_action(Uri, Range, VarName)
    end.

create_define_variable_action(Uri, Range, VarName) ->
    VarText = iolist_to_binary([atom_to_binary(VarName, utf8), <<" = ">>]),

    #{
        title => iolist_to_binary([<<"Define variable: ">>, atom_to_binary(VarName, utf8)]),
        kind => <<"quickfix">>,
        diagnostics => [],
        edit => #{
            changes => #{
                Uri => [
                    #{
                        range => Range,
                        newText => VarText
                    }
                ]
            }
        }
    }.

%%% ============================================================================
%%% Constraint Suggestion Helpers
%%% ============================================================================

%% @doc Suggest guard clause for a constraint
-spec suggest_guard_clause(term(), term()) -> map().
suggest_guard_clause(Range, Constraint) ->
    GuardText = format_constraint_as_guard(Constraint),
    #{
        title => iolist_to_binary([<<"Add guard: when ">>, GuardText]),
        kind => <<"quickfix">>,
        edit => #{
            range => Range,
            newText => iolist_to_binary([<<" when ">>, GuardText])
        }
    }.

%% @doc Suggest assertion for a constraint
-spec suggest_assertion(term(), term()) -> map().
suggest_assertion(Range, Constraint) ->
    AssertText = format_constraint_as_assertion(Constraint),
    #{
        title => iolist_to_binary([<<"Add assertion: ">>, AssertText]),
        kind => <<"quickfix">>,
        edit => #{
            range => Range,
            newText => iolist_to_binary([AssertText, <<"\n">>])
        }
    }.

%% @doc Suggest relaxed constraint
-spec suggest_relaxed_constraint(term(), term()) -> map().
suggest_relaxed_constraint(Range, Constraint) ->
    case suggest_weaker_constraint(Constraint) of
        {ok, WeakerConstraint} ->
            WeakerText = format_constraint_text(WeakerConstraint),
            #{
                title => iolist_to_binary([<<"Relax to: ">>, WeakerText]),
                kind => <<"refactor">>,
                edit => #{
                    range => Range,
                    newText => WeakerText
                }
            };
        undefined ->
            #{
                title => <<"Consider relaxing constraint">>,
                kind => <<"refactor">>
            }
    end.

%% @doc Suggest type annotation
-spec suggest_type_annotation(term(), term()) -> map().
suggest_type_annotation(Range, Type) ->
    TypeText = format_type_for_annotation(Type),
    #{
        title => iolist_to_binary([<<"Annotate as: ">>, TypeText]),
        kind => <<"quickfix">>,
        edit => #{
            range => Range,
            newText => iolist_to_binary([<<": ">>, TypeText])
        }
    }.

%% @doc Suggest pattern completion
-spec suggest_pattern_completion(term(), term()) -> map().
suggest_pattern_completion(Range, MissingPattern) ->
    PatternText = format_pattern_brief(MissingPattern),
    #{
        title => iolist_to_binary([<<"Add case: ">>, PatternText]),
        kind => <<"quickfix">>,
        edit => #{
            range => Range,
            newText => iolist_to_binary([PatternText, <<" -> ?">>])
        }
    }.

%%% ============================================================================
%%% Text Edit Creation
%%% ============================================================================

%% @doc Create text edit for code modification
-spec create_text_edit(term(), binary(), binary()) -> map().
create_text_edit(Range, NewText, _Description) ->
    #{
        range => normalize_range(Range),
        newText => NewText
    }.

%% @doc Apply code action (for testing)
-spec apply_code_action(map(), binary()) -> binary().
apply_code_action(#{edit := #{changes := Changes}}, Uri) ->
    case maps:get(Uri, Changes, []) of
        [] -> <<>>;
        [Edit | _] -> maps:get(newText, Edit, <<>>)
    end;
apply_code_action(_, _) ->
    <<>>.

%%% ============================================================================
%%% Formatting Helpers
%%% ============================================================================

%% Format constraint as guard clause
format_constraint_as_guard(#binary_op_expr{op = Op, left = Left, right = Right}) ->
    LeftStr = format_expr_for_guard(Left),
    RightStr = format_expr_for_guard(Right),
    OpStr = format_guard_op(Op),
    iolist_to_binary([LeftStr, <<" ">>, OpStr, <<" ">>, RightStr]);
format_constraint_as_guard(Expr) ->
    format_expr_for_guard(Expr).

format_expr_for_guard(#identifier_expr{name = Name}) ->
    atom_to_binary(Name, utf8);
format_expr_for_guard(#literal_expr{value = Val}) when is_integer(Val) ->
    integer_to_binary(Val);
format_expr_for_guard(#literal_expr{value = Val}) when is_atom(Val) ->
    atom_to_binary(Val, utf8);
format_expr_for_guard(_) ->
    <<"?">>.

format_guard_op('>') -> <<">">>;
format_guard_op('>=') -> <<">=">>;
format_guard_op('<') -> <<"<">>;
format_guard_op('<=') -> <<"<=">>;
format_guard_op('==') -> <<"==">>;
format_guard_op('/=') -> <<"/=">>;
format_guard_op('!=') -> <<"!=">>;
format_guard_op(Op) when is_atom(Op) -> atom_to_binary(Op, utf8);
format_guard_op(_) -> <<"?">>.

%% Format constraint as assertion
format_constraint_as_assertion(Constraint) ->
    ConstraintText = format_constraint_as_guard(Constraint),
    iolist_to_binary([<<"assert ">>, ConstraintText]).

%% Format constraint as text
format_constraint_text(Constraint) ->
    format_constraint_as_guard(Constraint).

%% Format type for annotation
format_type_for_annotation({primitive_type, Name}) ->
    atom_to_binary(Name, utf8);
format_type_for_annotation(Type) when is_atom(Type) ->
    atom_to_binary(Type, utf8);
format_type_for_annotation(Type) when is_binary(Type) ->
    Type;
format_type_for_annotation(_) ->
    <<"_">>.

%% Format pattern briefly
format_pattern_brief(Pattern) when is_atom(Pattern) ->
    atom_to_binary(Pattern, utf8);
format_pattern_brief(Pattern) when is_integer(Pattern) ->
    integer_to_binary(Pattern);
format_pattern_brief(Pattern) when is_binary(Pattern) ->
    Pattern;
format_pattern_brief(_) ->
    <<"_">>.

%%% ============================================================================
%%% Extraction Helpers
%%% ============================================================================

%% Extract constraint from diagnostic message
extract_constraint_from_message(Message) when is_binary(Message) ->
    % Try to parse "Required: <constraint>" pattern
    case binary:split(Message, <<"Required: ">>) of
        [_, ConstraintPart] ->
            % Extract first line
            case binary:split(ConstraintPart, <<"\n">>) of
                [ConstraintStr | _] ->
                    {ok, parse_constraint_string(ConstraintStr)};
                _ ->
                    undefined
            end;
        _ ->
            undefined
    end;
extract_constraint_from_message(_) ->
    undefined.

%% Parse constraint string to AST (simplified)
parse_constraint_string(Str) ->
    % For now, return as-is (would need full parser)
    Str.

%% Extract missing pattern from message
extract_missing_pattern(Message) when is_binary(Message) ->
    case binary:split(Message, <<"Missing case for: ">>) of
        [_, PatternPart] ->
            case binary:split(PatternPart, <<"\n">>) of
                [PatternStr | _] -> {ok, PatternStr};
                _ -> undefined
            end;
        _ ->
            undefined
    end;
extract_missing_pattern(_) ->
    undefined.

%% Extract type mismatch information
extract_type_mismatch(Message) when is_binary(Message) ->
    % Parse "Expected: X, but got Y" pattern
    case binary:split(Message, <<"expected ">>) of
        [_, Rest] ->
            case binary:split(Rest, <<", but got ">>) of
                [Expected, Got] -> {ok, Expected, Got};
                _ -> undefined
            end;
        _ ->
            undefined
    end;
extract_type_mismatch(_) ->
    undefined.

%% Extract variable name from message
extract_variable_name(Message) when is_binary(Message) ->
    case binary:split(Message, <<"Undefined variable: ">>) of
        [_, VarStr] ->
            {ok, binary_to_atom(VarStr, utf8)};
        _ ->
            undefined
    end;
extract_variable_name(_) ->
    undefined.

%%% ============================================================================
%%% Constraint Weakening
%%% ============================================================================

%% Suggest weaker constraint that might pass
suggest_weaker_constraint(#binary_op_expr{op = '>', left = L, right = R}) ->
    % x > 0 → x >= 0
    {ok, #binary_op_expr{op = '>=', left = L, right = R}};
suggest_weaker_constraint(#binary_op_expr{op = '<', left = L, right = R}) ->
    % x < 10 → x <= 10
    {ok, #binary_op_expr{op = '<=', left = L, right = R}};
suggest_weaker_constraint(_) ->
    undefined.

%% Suggest type conversion function
suggest_conversion(<<"Int">>, <<"Float">>) ->
    {ok, to_int};
suggest_conversion(<<"Float">>, <<"Int">>) ->
    {ok, to_float};
suggest_conversion(<<"String">>, <<"Int">>) ->
    {ok, parse_int};
suggest_conversion(<<"Int">>, <<"String">>) ->
    {ok, to_string};
suggest_conversion(_, _) ->
    undefined.

%%% ============================================================================
%%% AST Navigation
%%% ============================================================================

%% Find function definition at range
find_function_at_range(AST, _Range) when is_list(AST) ->
    % Would traverse AST to find function - simplified for now
    undefined;
find_function_at_range(#module_def{items = Items}, Range) ->
    find_function_in_items(Items, Range);
find_function_at_range(_, _) ->
    undefined.

find_function_in_items([], _Range) ->
    undefined;
find_function_in_items([#function_def{} = Func | _], _Range) ->
    {ok, Func};
find_function_in_items([_ | Rest], Range) ->
    find_function_in_items(Rest, Range).

%% Find match expression at range
find_match_at_range(_AST, _Range) ->
    % Would traverse AST to find match - simplified
    undefined.

%%% ============================================================================
%%% Edit Creation Helpers
%%% ============================================================================

create_guard_insertion_edit(_FuncDef, GuardText) ->
    % Would calculate precise insertion point - placeholder
    #{
        range => #{
            start => #{line => 0, character => 0},
            'end' => #{line => 0, character => 0}
        },
        newText => iolist_to_binary([<<" when ">>, GuardText])
    }.

create_assertion_insertion_edit(_Range, AssertText) ->
    #{
        range => #{
            start => #{line => 0, character => 0},
            'end' => #{line => 0, character => 0}
        },
        newText => iolist_to_binary([<<"    ">>, AssertText, <<"\n">>])
    }.

create_constraint_replacement_edit(_Range, NewText) ->
    #{
        range => #{
            start => #{line => 0, character => 0},
            'end' => #{line => 0, character => 0}
        },
        newText => NewText
    }.

create_pattern_insertion_edit(_Range, _Patterns, PatternText) ->
    #{
        range => #{
            start => #{line => 0, character => 0},
            'end' => #{line => 0, character => 0}
        },
        newText => iolist_to_binary([<<"    ">>, PatternText, <<"\n">>])
    }.

create_type_annotation_edit(_Range, TypeText) ->
    #{
        range => #{
            start => #{line => 0, character => 0},
            'end' => #{line => 0, character => 0}
        },
        newText => iolist_to_binary([<<": ">>, TypeText])
    }.

create_conversion_edit(_Range, ConvFunc) ->
    #{
        range => #{
            start => #{line => 0, character => 0},
            'end' => #{line => 0, character => 0}
        },
        newText => iolist_to_binary([atom_to_binary(ConvFunc, utf8), <<"(">>])
    }.

create_parameter_insertion_edit(_FuncDef, VarName) ->
    #{
        range => #{
            start => #{line => 0, character => 0},
            'end' => #{line => 0, character => 0}
        },
        newText => iolist_to_binary([atom_to_binary(VarName, utf8), <<": _">>])
    }.

generate_pattern_clause(Pattern) ->
    iolist_to_binary([format_pattern_brief(Pattern), <<" -> ?">>]).

normalize_range(#{start := _, 'end' := _} = Range) ->
    Range;
normalize_range(_) ->
    #{
        start => #{line => 0, character => 0},
        'end' => #{line => 0, character => 0}
    }.
