%% Cure LSP Rich Diagnostics - Phase 4.2
%% Enhanced error messages with SMT counterexamples and constraint context
-module(cure_lsp_diagnostics).

-moduledoc """
# LSP Rich Diagnostics with SMT Counterexamples

This module enhances LSP diagnostics with:
- Concrete counterexamples from SMT solver (e.g., \"x = -5 violates x > 0\")
- Constraint context (shows where constraint was defined)
- Related information links (jump to constraint definition)
- Human-readable formatting of SMT output

## Example Enhanced Diagnostic

```
Error: Refinement type constraint violated
  Type: Positive
  Required: x > 0
  Counterexample: x = -5 violates constraint
  
  Defined at: examples/test.cure:10:15
  
  Hint: Add a guard clause 'when x > 0' or use runtime assertion
```

## Features

### Counterexample Formatting
- Extract concrete values from SMT models
- Format in Cure syntax (not SMT-LIB)
- Show multiple variables if constraint involves them

### Constraint Context
- Track constraint definition locations
- Show original Cure code for constraint
- Link to definition via LSP relatedInformation

### Hover Information
- Show inferred refinement types on hover
- Display active constraints for variables
- Preview constraint satisfaction status
""".

-export([
    % Enhanced diagnostics
    create_refinement_diagnostic/4,
    create_pattern_diagnostic/3,
    create_type_mismatch_diagnostic/4,

    % Counterexample extraction
    extract_counterexample/2,
    format_counterexample_detailed/2,

    % Constraint context
    add_constraint_context/3,
    format_constraint_in_cure_syntax/1,

    % Hover information
    create_hover_info/3,
    format_refinement_type_hover/2
]).

-include("../parser/cure_ast.hrl").

%%% ============================================================================
%%% Enhanced Diagnostic Creation
%%% ============================================================================

%% @doc Create enhanced diagnostic for refinement type violation
%% Includes counterexample from SMT solver and constraint context
-spec create_refinement_diagnostic(atom(), term(), term(), term()) -> map().
create_refinement_diagnostic(TypeName, Constraint, Location, SmtResult) ->
    % Extract counterexample from SMT result
    CounterExample = extract_counterexample(Constraint, SmtResult),

    % Format main message
    MainMessage = format_refinement_violation_message(TypeName, Constraint, CounterExample),

    % Create base diagnostic
    BaseDiagnostic = #{
        range => location_to_range(Location),
        % Error
        severity => 1,
        source => <<"cure-smt">>,
        code => <<"refinement-violation">>,
        message => MainMessage
    },

    % Add counterexample details if available
    DiagWithCounter =
        case CounterExample of
            undefined ->
                BaseDiagnostic;
            _ ->
                BaseDiagnostic#{
                    message => iolist_to_binary([
                        MainMessage,
                        <<"\n\nCounterexample: ">>,
                        format_counterexample_detailed(CounterExample, Constraint)
                    ])
                }
        end,

    % Add constraint context
    add_constraint_context(DiagWithCounter, Constraint, Location).

%% @doc Create enhanced diagnostic for non-exhaustive patterns
-spec create_pattern_diagnostic(term(), term(), term()) -> map().
create_pattern_diagnostic(MatchExpr, CounterExample, Location) ->
    % Format the missing pattern from counterexample
    MissingPattern = format_missing_pattern(CounterExample),

    % Extract covered patterns for context
    CoveredPatterns = extract_covered_patterns(MatchExpr),

    Message = iolist_to_binary([
        <<"Pattern match is not exhaustive">>,
        <<"\n\nMissing case: ">>,
        MissingPattern,
        <<"\n\nCovered cases: ">>,
        format_pattern_list(CoveredPatterns)
    ]),

    #{
        range => location_to_range(Location),
        % Warning
        severity => 2,
        source => <<"cure-smt">>,
        code => <<"non-exhaustive-pattern">>,
        message => Message,
        codeDescription => #{
            href => <<"https://cure-lang.org/docs/pattern-matching#exhaustiveness">>
        },
        % Unnecessary code (if wildcard pattern suggested)
        tags => [1]
    }.

%% @doc Create enhanced diagnostic for type mismatch
-spec create_type_mismatch_diagnostic(term(), term(), term(), term()) -> map().
create_type_mismatch_diagnostic(Expected, Got, Reason, Location) ->
    % Format types in human-readable way
    ExpectedStr = format_type_for_display(Expected),
    GotStr = format_type_for_display(Got),

    % Build detailed message
    Message = iolist_to_binary([
        <<"Type mismatch">>,
        <<"\n\nExpected: ">>,
        ExpectedStr,
        <<"\nGot:      ">>,
        GotStr,
        case Reason of
            undefined -> <<>>;
            _ -> iolist_to_binary([<<"\n\nReason: ">>, format_reason(Reason)])
        end
    ]),

    #{
        range => location_to_range(Location),
        % Error
        severity => 1,
        source => <<"cure-typecheck">>,
        code => <<"type-mismatch">>,
        message => Message
    }.

%%% ============================================================================
%%% Counterexample Extraction and Formatting
%%% ============================================================================

%% @doc Extract counterexample from SMT solver result
-spec extract_counterexample(term(), term()) -> map() | undefined.
extract_counterexample(_Constraint, {unsat, _Model}) ->
    % Constraint is violated - extract model values
    % The SMT solver provides concrete values that violate the constraint

    % Placeholder - would extract from actual SMT model
    undefined;
extract_counterexample(Constraint, {sat, Model}) when is_map(Model) ->
    % Extract variable assignments from model
    Model;
extract_counterexample(_Constraint, _SmtResult) ->
    undefined.

%% @doc Format counterexample with detailed explanation
-spec format_counterexample_detailed(map(), term()) -> binary().
format_counterexample_detailed(CounterExample, Constraint) when is_map(CounterExample) ->
    % Format each variable assignment
    Assignments = maps:to_list(CounterExample),
    FormattedAssignments = lists:map(
        fun({Var, Val}) ->
            VarStr = format_variable(Var),
            ValStr = format_value_with_type(Val),
            iolist_to_binary([VarStr, <<" = ">>, ValStr])
        end,
        Assignments
    ),

    % Add constraint context
    ConstraintStr = format_constraint_in_cure_syntax(Constraint),

    iolist_to_binary([
        lists:join(<<", ">>, FormattedAssignments),
        <<" violates ">>,
        ConstraintStr
    ]);
format_counterexample_detailed(CounterExample, _Constraint) ->
    iolist_to_binary(io_lib:format("~p", [CounterExample])).

%% @doc Format value with inferred type information
format_value_with_type(Val) when is_integer(Val), Val < 0 ->
    iolist_to_binary([integer_to_binary(Val), <<" (negative integer)">>]);
format_value_with_type(Val) when is_integer(Val), Val == 0 ->
    <<"0 (zero)">>;
format_value_with_type(Val) when is_integer(Val), Val > 0 ->
    iolist_to_binary([integer_to_binary(Val), <<" (positive integer)">>]);
format_value_with_type(Val) when is_float(Val) ->
    float_to_binary(Val, [{decimals, 4}]);
format_value_with_type(Val) when is_atom(Val) ->
    atom_to_binary(Val, utf8);
format_value_with_type(Val) when is_binary(Val) ->
    iolist_to_binary([<<"\"">>, Val, <<"\"">>]);
format_value_with_type(Val) when is_list(Val) ->
    case io_lib:printable_list(Val) of
        true -> iolist_to_binary([<<"\"">>, Val, <<"\"">>]);
        false -> iolist_to_binary(io_lib:format("~p", [Val]))
    end;
format_value_with_type(Val) ->
    iolist_to_binary(io_lib:format("~p", [Val])).

format_variable(Var) when is_atom(Var) ->
    atom_to_binary(Var, utf8);
format_variable(Var) when is_binary(Var) ->
    Var;
format_variable(Var) ->
    iolist_to_binary(io_lib:format("~p", [Var])).

%%% ============================================================================
%%% Constraint Context
%%% ============================================================================

%% @doc Add constraint definition context to diagnostic
-spec add_constraint_context(map(), term(), term()) -> map().
add_constraint_context(Diagnostic, Constraint, DefinitionLoc) ->
    % Format constraint in Cure syntax
    ConstraintStr = format_constraint_in_cure_syntax(Constraint),

    % Create related information pointing to constraint definition
    RelatedInfo =
        case DefinitionLoc of
            #location{line = Line, column = Col, file = File} when File =/= undefined ->
                [
                    #{
                        location => #{
                            uri => file_path_to_uri(File),
                            range => #{
                                start => #{line => max(0, Line - 1), character => max(0, Col - 1)},
                                'end' => #{line => max(0, Line - 1), character => max(0, Col + 20)}
                            }
                        },
                        message => iolist_to_binary([
                            <<"Constraint defined here: ">>,
                            ConstraintStr
                        ])
                    }
                ];
            _ ->
                []
        end,

    % Add related information to diagnostic
    case RelatedInfo of
        [] -> Diagnostic;
        _ -> Diagnostic#{relatedInformation => RelatedInfo}
    end.

%% @doc Format constraint in Cure syntax (not SMT-LIB)
-spec format_constraint_in_cure_syntax(term()) -> binary().
format_constraint_in_cure_syntax(#binary_op_expr{op = Op, left = Left, right = Right}) ->
    LeftStr = format_expr_in_cure_syntax(Left),
    RightStr = format_expr_in_cure_syntax(Right),
    OpStr = format_operator(Op),
    iolist_to_binary([LeftStr, <<" ">>, OpStr, <<" ">>, RightStr]);
format_constraint_in_cure_syntax(#unary_op_expr{op = Op, operand = Operand}) ->
    OperandStr = format_expr_in_cure_syntax(Operand),
    OpStr = format_operator(Op),
    iolist_to_binary([OpStr, OperandStr]);
format_constraint_in_cure_syntax(Expr) ->
    format_expr_in_cure_syntax(Expr).

format_expr_in_cure_syntax(#identifier_expr{name = Name}) ->
    atom_to_binary(Name, utf8);
format_expr_in_cure_syntax(#literal_expr{value = Val}) ->
    format_value_with_type(Val);
format_expr_in_cure_syntax(#binary_op_expr{op = Op, left = Left, right = Right}) ->
    format_constraint_in_cure_syntax(#binary_op_expr{op = Op, left = Left, right = Right});
format_expr_in_cure_syntax(Expr) ->
    iolist_to_binary(io_lib:format("~p", [Expr])).

format_operator('>') -> <<">">>;
format_operator('>=') -> <<">=">>;
format_operator('<') -> <<"<">>;
format_operator('<=') -> <<"<=">>;
format_operator('==') -> <<"==">>;
format_operator('/=') -> <<"/=">>;
format_operator('!=') -> <<"!=">>;
format_operator('and') -> <<"and">>;
format_operator('or') -> <<"or">>;
format_operator('not') -> <<"not">>;
format_operator('+') -> <<"+">>;
format_operator('-') -> <<"-">>;
format_operator('*') -> <<"*">>;
format_operator('/') -> <<"/">>;
format_operator(Op) when is_atom(Op) -> atom_to_binary(Op, utf8);
format_operator(Op) -> iolist_to_binary(io_lib:format("~p", [Op])).

%%% ============================================================================
%%% Hover Information
%%% ============================================================================

%% @doc Create hover information for variable with refinement type
-spec create_hover_info(atom(), term(), term()) -> map().
create_hover_info(VarName, RefinementType, Location) ->
    Contents = format_refinement_type_hover(VarName, RefinementType),

    #{
        contents => #{
            kind => <<"markdown">>,
            value => Contents
        },
        range => location_to_range(Location)
    }.

%% @doc Format refinement type for hover display
-spec format_refinement_type_hover(atom(), term()) -> binary().
format_refinement_type_hover(VarName, {refined_type, BaseType, Constraint}) ->
    VarStr = atom_to_binary(VarName, utf8),
    BaseTypeStr = format_type_for_display(BaseType),
    ConstraintStr = format_constraint_in_cure_syntax(Constraint),

    iolist_to_binary([
        <<"```cure\n">>,
        VarStr,
        <<": ">>,
        BaseTypeStr,
        <<" when ">>,
        ConstraintStr,
        <<"\n```\n\n">>,
        <<"**Refinement Type**\n\n">>,
        <<"This variable has a refined type with the constraint:\n">>,
        <<"- `">>,
        ConstraintStr,
        <<"`\n\n">>,
        <<"The SMT solver will verify this constraint is satisfied.">>
    ]);
format_refinement_type_hover(VarName, Type) ->
    VarStr = atom_to_binary(VarName, utf8),
    TypeStr = format_type_for_display(Type),

    iolist_to_binary([
        <<"```cure\n">>,
        VarStr,
        <<": ">>,
        TypeStr,
        <<"\n```">>
    ]).

%%% ============================================================================
%%% Helper Functions
%%% ============================================================================

%% Format refinement violation message
format_refinement_violation_message(TypeName, Constraint, CounterExample) ->
    TypeStr = atom_to_binary(TypeName, utf8),
    ConstraintStr = format_constraint_in_cure_syntax(Constraint),

    BaseMsg = iolist_to_binary([
        <<"Refinement type constraint violated\n\n">>,
        <<"Type: ">>,
        TypeStr,
        <<"\n">>,
        <<"Required: ">>,
        ConstraintStr
    ]),

    case CounterExample of
        undefined -> BaseMsg;
        % Counterexample added separately
        _ -> BaseMsg
    end.

%% Format missing pattern from counterexample
format_missing_pattern(CounterExample) when is_map(CounterExample) ->
    case maps:to_list(CounterExample) of
        [] ->
            <<"_">>;
        [{_Var, Val}] ->
            format_pattern_value(Val);
        Multiple ->
            % Multiple bindings - format as tuple or record
            Values = [format_pattern_value(Val) || {_Var, Val} <- Multiple],
            iolist_to_binary([<<"{">>, lists:join(<<", ">>, Values), <<"}">>])
    end;
format_missing_pattern(Val) ->
    format_pattern_value(Val).

format_pattern_value(Val) when is_integer(Val) ->
    integer_to_binary(Val);
format_pattern_value(Val) when is_atom(Val) ->
    atom_to_binary(Val, utf8);
format_pattern_value(Val) when is_binary(Val) ->
    iolist_to_binary([<<"\"">>, Val, <<"\"">>]);
format_pattern_value(Val) when is_list(Val) ->
    case io_lib:printable_list(Val) of
        true -> iolist_to_binary([<<"\"">>, Val, <<"\"">>]);
        false -> <<"[...]">>
    end;
format_pattern_value(_) ->
    <<"_">>.

%% Extract covered patterns from match expression
extract_covered_patterns(#match_expr{patterns = Patterns}) ->
    lists:map(fun extract_pattern/1, Patterns);
extract_covered_patterns(_) ->
    [].

extract_pattern(#match_clause{pattern = Pattern}) ->
    Pattern;
extract_pattern(Pattern) ->
    Pattern.

%% Format list of patterns
format_pattern_list(Patterns) ->
    Formatted = lists:map(fun format_pattern_brief/1, Patterns),
    iolist_to_binary(lists:join(<<", ">>, Formatted)).

format_pattern_brief(#literal_pattern{value = Val}) ->
    format_pattern_value(Val);
format_pattern_brief(#constructor_pattern{name = Name, args = undefined}) ->
    atom_to_binary(Name, utf8);
format_pattern_brief(#constructor_pattern{name = Name, args = []}) ->
    atom_to_binary(Name, utf8);
format_pattern_brief(#constructor_pattern{name = Name}) ->
    iolist_to_binary([atom_to_binary(Name, utf8), <<"(...)">>]);
format_pattern_brief(#identifier_pattern{name = Name}) ->
    atom_to_binary(Name, utf8);
format_pattern_brief(#wildcard_pattern{}) ->
    <<"_">>;
format_pattern_brief(#list_pattern{elements = []}) ->
    <<"[]">>;
format_pattern_brief(#list_pattern{}) ->
    <<"[...]">>;
format_pattern_brief(_) ->
    <<"...">>.

%% Format type for display
format_type_for_display({primitive_type, Name}) ->
    atom_to_binary(Name, utf8);
format_type_for_display({refined_type, BaseType, Constraint}) ->
    BaseStr = format_type_for_display(BaseType),
    ConstraintStr = format_constraint_in_cure_syntax(Constraint),
    iolist_to_binary([BaseStr, <<" when ">>, ConstraintStr]);
format_type_for_display({function_type, Params, Return}) ->
    ParamStrs = [format_type_for_display(P) || P <- Params],
    ReturnStr = format_type_for_display(Return),
    iolist_to_binary([
        <<"(">>, lists:join(<<", ">>, ParamStrs), <<") -> ">>, ReturnStr
    ]);
format_type_for_display({list_type, ElemType}) ->
    ElemStr = format_type_for_display(ElemType),
    iolist_to_binary([<<"[">>, ElemStr, <<"]">>]);
format_type_for_display({tuple_type, ElemTypes}) ->
    ElemStrs = [format_type_for_display(T) || T <- ElemTypes],
    iolist_to_binary([<<"{">>, lists:join(<<", ">>, ElemStrs), <<"}">>]);
format_type_for_display(Type) when is_atom(Type) ->
    atom_to_binary(Type, utf8);
format_type_for_display(Type) when is_binary(Type) ->
    Type;
format_type_for_display(_) ->
    <<"<unknown>">>.

format_reason(Reason) when is_binary(Reason) ->
    Reason;
format_reason(Reason) when is_atom(Reason) ->
    atom_to_binary(Reason, utf8);
format_reason(Reason) ->
    iolist_to_binary(io_lib:format("~p", [Reason])).

%% Convert location to LSP range
location_to_range(#location{line = Line, column = Col}) ->
    #{
        start => #{line => max(0, Line - 1), character => max(0, Col - 1)},
        'end' => #{line => max(0, Line - 1), character => max(0, Col + 10)}
    };
location_to_range({Line, Col}) ->
    #{
        start => #{line => max(0, Line - 1), character => max(0, Col - 1)},
        'end' => #{line => max(0, Line - 1), character => max(0, Col + 10)}
    };
location_to_range(_) ->
    #{
        start => #{line => 0, character => 0},
        'end' => #{line => 0, character => 10}
    }.

%% Convert file path to LSP URI
file_path_to_uri(FilePath) when is_binary(FilePath) ->
    iolist_to_binary([<<"file://">>, FilePath]);
file_path_to_uri(FilePath) when is_list(FilePath) ->
    iolist_to_binary([<<"file://">>, list_to_binary(FilePath)]);
file_path_to_uri(_) ->
    <<"file:///unknown">>.
