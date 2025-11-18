-module(cure_pattern_checker).

%% Pattern exhaustiveness and redundancy checking
-export([
    check_match/2,
    check_exhaustiveness/2,
    check_redundancy/2,
    suggest_missing_patterns/2,
    format_diagnostic/1
]).

-include("../parser/cure_ast.hrl").

%% Type definitions for diagnostics
-type pattern_diagnostic() ::
    {exhaustive}
    | {incomplete, [ast_pattern()], string()}
    | {redundant, [integer()], string()}
    | {error, term()}.

% AST pattern node
-type ast_pattern() :: term().

%% ============================================================================
%% Main API
%% ============================================================================

%% @doc Check a match expression for exhaustiveness and redundancy
-spec check_match(MatchExpr :: term(), Env :: map()) -> pattern_diagnostic().
check_match(MatchExpr, Env) ->
    case MatchExpr of
        #match_expr{patterns = Clauses, location = _Loc} ->
            % Extract patterns from match clauses
            Patterns = [Pattern || #match_clause{pattern = Pattern} <- Clauses],

            % Infer the type being matched against
            % For now, use a simple heuristic: look at first pattern
            Type =
                case Patterns of
                    [FirstPattern | _] -> infer_pattern_type(FirstPattern, Env);
                    [] -> unknown
                end,

            % Check exhaustiveness first
            ExhaustivenessResult = check_exhaustiveness(Patterns, Type),

            % Then check for redundant patterns
            RedundancyResult = check_redundancy(Patterns, Type),

            % Combine results
            combine_diagnostics(ExhaustivenessResult, RedundancyResult);
        _ ->
            {error, not_a_match_expression}
    end.

%% @doc Check if patterns are exhaustive for a given type
-spec check_exhaustiveness([ast_pattern()], Type :: term()) -> pattern_diagnostic().
check_exhaustiveness(Patterns, Type) ->
    try
        case cure_pattern_encoder:check_exhaustiveness(Patterns, Type) of
            {complete} ->
                {exhaustive};
            {incomplete, MissingPatterns} ->
                Message = format_missing_patterns(MissingPatterns),
                {incomplete, MissingPatterns, Message};
            {error, Reason} ->
                {error, {z3_error, Reason}}
        end
    catch
        Error:CatchReason:_Stack ->
            {error, {exception, Error, CatchReason}}
    end.

%% @doc Check for redundant (unreachable) patterns
-spec check_redundancy([ast_pattern()], Type :: term()) -> pattern_diagnostic() | ok.
check_redundancy(Patterns, Type) ->
    % Check each pattern against all previous patterns
    % A pattern is redundant if it's subsumed by earlier patterns
    check_redundancy_impl(Patterns, Type, [], 1).

check_redundancy_impl([], _Type, _SeenPatterns, _Index) ->
    % No redundant patterns found
    ok;
check_redundancy_impl([Pattern | Rest], Type, SeenPatterns, Index) ->
    case is_redundant(Pattern, SeenPatterns, Type) of
        true ->
            % Found a redundant pattern
            Message = io_lib:format(
                "Pattern at position ~p is redundant (already covered by earlier patterns)", [Index]
            ),
            {redundant, [Index], lists:flatten(Message)};
        false ->
            % Pattern is not redundant, continue checking
            check_redundancy_impl(Rest, Type, [Pattern | SeenPatterns], Index + 1)
    end.

%% @doc Suggest missing patterns for incomplete matches
-spec suggest_missing_patterns([ast_pattern()], Type :: term()) ->
    [ast_pattern()] | {error, term()}.
suggest_missing_patterns(Patterns, Type) ->
    case check_exhaustiveness(Patterns, Type) of
        {incomplete, MissingPatterns, _Message} ->
            MissingPatterns;
        {exhaustive} ->
            [];
        {error, Reason} ->
            {error, Reason}
    end.

%% @doc Format a diagnostic message for display
-spec format_diagnostic(pattern_diagnostic()) -> string().
format_diagnostic({exhaustive}) ->
    "Pattern match is exhaustive";
format_diagnostic({incomplete, MissingPatterns, Message}) ->
    io_lib:format(
        "Pattern match is not exhaustive.~n~s~nMissing ~p pattern(s)",
        [Message, length(MissingPatterns)]
    );
format_diagnostic({redundant, Indices, Message}) ->
    io_lib:format("Redundant patterns at positions ~p:~n~s", [Indices, Message]);
format_diagnostic({error, Reason}) ->
    io_lib:format("Error checking patterns: ~p", [Reason]).

%% ============================================================================
%% Helper Functions
%% ============================================================================

%% Check if a pattern is redundant given previously seen patterns
-spec is_redundant(ast_pattern(), [ast_pattern()], Type :: term()) -> boolean().
is_redundant(_Pattern, [], _Type) ->
    % No previous patterns, can't be redundant
    false;
is_redundant(Pattern, SeenPatterns, Type) ->
    try
        % A pattern P is redundant if the union of all previous patterns covers P
        % i.e., P ∧ ¬(P1 ∨ P2 ∨ ... ∨ Pn) is unsatisfiable

        % Encode the current pattern
        PatternConstraint = cure_pattern_encoder:encode_pattern(Pattern, Type),

        % Encode all seen patterns as a disjunction
        SeenConstraint = cure_pattern_encoder:encode_patterns_disjunction(SeenPatterns, Type),

        % Check if (Pattern ∧ ¬SeenPatterns) is satisfiable
        % If unsatisfiable, Pattern is redundant
        TypeSort = cure_pattern_encoder:type_to_smt_sort(Type),
        Query = [
            "(declare-const val ",
            TypeSort,
            ")\n",
            "(assert ",
            PatternConstraint,
            ")\n",
            "(assert (not ",
            SeenConstraint,
            "))\n",
            "(check-sat)\n"
        ],

        case cure_z3:query(Query) of
            {ok, Result} ->
                % If unsat, the pattern is redundant
                string:trim(Result) =:= "unsat";
            {error, _} ->
                % On error, assume not redundant (conservative)
                false
        end
    catch
        _:_ ->
            % On exception, assume not redundant
            false
    end.

%% Infer the type of a pattern based on its structure
-spec infer_pattern_type(ast_pattern(), Env :: map()) -> term().
infer_pattern_type(Pattern, _Env) ->
    case Pattern of
        #literal_expr{value = Value} when is_integer(Value) ->
            #primitive_type{name = 'Int', location = undefined};
        #literal_expr{value = Value} when is_boolean(Value) ->
            #primitive_type{name = 'Bool', location = undefined};
        #literal_expr{value = Value} when is_float(Value) ->
            #primitive_type{name = 'Float', location = undefined};
        #literal_expr{value = Value} when is_binary(Value) ->
            #primitive_type{name = 'String', location = undefined};
        #constructor_pattern{name = Name, args = Args} ->
            % Infer ADT type from constructor
            % For now, return a simplified ADT type
            {adt, infer_adt_name(Name), [{Name, length(Args)}]};
        #list_pattern{} ->
            % Default to list of unknown element type
            {list, unknown};
        #tuple_pattern{elements = Elements} ->
            % Tuple with inferred element types
            {tuple, length(Elements)};
        _ ->
            unknown
    end.

%% Infer ADT name from constructor name
%% This is a heuristic - in a real implementation, we'd look this up in the environment
-spec infer_adt_name(atom()) -> atom().
infer_adt_name(ok) -> 'Result';
infer_adt_name(error) -> 'Result';
infer_adt_name(some) -> 'Maybe';
infer_adt_name(none) -> 'Maybe';
infer_adt_name(true) -> 'Bool';
infer_adt_name(false) -> 'Bool';
infer_adt_name(_) -> 'Unknown'.

%% Format missing patterns into a readable message
-spec format_missing_patterns([ast_pattern()]) -> string().
format_missing_patterns([]) ->
    "No specific patterns suggested";
format_missing_patterns(Patterns) ->
    PatternStrs = [format_pattern(P) || P <- Patterns],
    "Missing patterns:\n" ++ string:join(["  - " ++ S || S <- PatternStrs], "\n").

%% Format a single pattern for display
-spec format_pattern(ast_pattern()) -> string().
format_pattern(#literal_expr{value = Value}) ->
    io_lib:format("~p", [Value]);
format_pattern(#identifier_expr{name = '_'}) ->
    "_";
format_pattern(#identifier_expr{name = Name}) ->
    atom_to_list(Name);
format_pattern(#constructor_pattern{name = Name, args = []}) ->
    atom_to_list(Name);
format_pattern(#constructor_pattern{name = Name, args = Args}) ->
    ArgStrs = [format_pattern(A) || A <- Args],
    io_lib:format("~s(~s)", [Name, string:join(ArgStrs, ", ")]);
format_pattern(#list_pattern{elements = [], tail = undefined}) ->
    "[]";
format_pattern(#list_pattern{elements = Elements, tail = undefined}) ->
    ElemStrs = [format_pattern(E) || E <- Elements],
    io_lib:format("[~s]", [string:join(ElemStrs, ", ")]);
format_pattern(#list_pattern{elements = Elements, tail = Tail}) ->
    ElemStrs = [format_pattern(E) || E <- Elements],
    TailStr = format_pattern(Tail),
    io_lib:format("[~s | ~s]", [string:join(ElemStrs, ", "), TailStr]);
format_pattern(#tuple_pattern{elements = Elements}) ->
    ElemStrs = [format_pattern(E) || E <- Elements],
    io_lib:format("{~s}", [string:join(ElemStrs, ", ")]);
format_pattern(_) ->
    "?".

%% Combine exhaustiveness and redundancy diagnostics
-spec combine_diagnostics(pattern_diagnostic(), pattern_diagnostic() | ok) -> pattern_diagnostic().
combine_diagnostics({incomplete, Missing, Msg}, ok) ->
    {incomplete, Missing, Msg};
combine_diagnostics({exhaustive}, ok) ->
    {exhaustive};
combine_diagnostics({incomplete, Missing, Msg1}, {redundant, _Indices, Msg2}) ->
    % Both issues present - report incomplete first (more critical)
    CombinedMsg = Msg1 ++ "\n\nAlso: " ++ Msg2,
    {incomplete, Missing, CombinedMsg};
combine_diagnostics({exhaustive}, {redundant, Indices, Msg}) ->
    {redundant, Indices, Msg};
combine_diagnostics({error, _} = Error, _) ->
    Error;
combine_diagnostics(_, {error, _} = Error) ->
    Error.
