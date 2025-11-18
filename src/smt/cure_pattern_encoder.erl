-module(cure_pattern_encoder).

%% Pattern Exhaustiveness Synthesis using SMT
%% Encodes Cure patterns as SMT-LIB constraints for Z3 verification

-include("../parser/cure_ast.hrl").

-export([
    % Pattern encoding
    encode_pattern/2,
    encode_patterns_disjunction/2,

    % Exhaustiveness checking
    find_missing_pattern/2,
    check_exhaustiveness/2,

    % Model conversion
    model_to_pattern/2,

    % Utilities
    type_to_smt_sort/1
]).

%% ============================================================================
%% Pattern Encoding
%% ============================================================================

%% @doc Encode a single pattern as an SMT constraint
%% Returns an SMT-LIB expression that is true when value matches pattern
-spec encode_pattern(term(), term()) -> iolist().
encode_pattern(Pattern, Type) ->
    encode_pattern_impl(Pattern, Type, <<"val">>).

encode_pattern_impl(#literal_expr{value = Value}, _Type, VarName) when is_atom(Value) ->
    % Atom literal: (= val 'atom_name)
    io_lib:format("(= ~s ~s)", [VarName, atom_to_smt(Value)]);
encode_pattern_impl(#literal_expr{value = Value}, _Type, VarName) when is_integer(Value) ->
    % Integer literal: (= val 42)
    io_lib:format("(= ~s ~w)", [VarName, Value]);
encode_pattern_impl(#literal_expr{value = Value}, _Type, VarName) when is_boolean(Value) ->
    % Boolean literal: (= val true)
    io_lib:format("(= ~s ~s)", [VarName, atom_to_list(Value)]);
encode_pattern_impl(#identifier_expr{name = '_'}, _Type, _VarName) ->
    % Wildcard pattern: always matches
    "true";
encode_pattern_impl(#identifier_expr{name = Name}, _Type, VarName) ->
    % Variable pattern: binds to any value, always matches
    % We could track the binding: (let ((Name val)) true)
    % For now, just return true since it matches anything
    io_lib:format("(let ((~s ~s)) true)", [Name, VarName]);
encode_pattern_impl(#tuple_expr{elements = Elements}, {tuple, ElementTypes}, VarName) ->
    % Tuple pattern: (and (is-tuple val) (= (tuple-elem val 0) elem0) ...)
    ElementConstraints = lists:zipwith(
        fun(Elem, {Idx, ElemType}) ->
            ElemVarName = io_lib:format("(tuple-elem ~s ~w)", [VarName, Idx]),
            encode_pattern_impl(Elem, ElemType, ElemVarName)
        end,
        Elements,
        lists:zip(lists:seq(0, length(Elements) - 1), ElementTypes)
    ),
    io_lib:format("(and (is-tuple ~s) ~s)", [
        VarName,
        string:join([binary_to_list(iolist_to_binary(C)) || C <- ElementConstraints], " ")
    ]);
encode_pattern_impl(#list_pattern{elements = []}, _Type, VarName) ->
    % Empty list pattern: (= val nil)
    io_lib:format("(= ~s nil)", [VarName]);
encode_pattern_impl(
    #list_pattern{elements = Elements, tail = undefined}, {list, ElemType}, VarName
) ->
    % Fixed-length list pattern: [p1, p2, p3]
    Constraints = lists:zipwith(
        fun(Elem, Idx) ->
            ElemVarName = io_lib:format("(list-nth ~s ~w)", [VarName, Idx]),
            encode_pattern_impl(Elem, ElemType, ElemVarName)
        end,
        Elements,
        lists:seq(0, length(Elements) - 1)
    ),
    LengthConstraint = io_lib:format("(= (list-length ~s) ~w)", [VarName, length(Elements)]),
    io_lib:format("(and ~s ~s)", [
        LengthConstraint,
        string:join([binary_to_list(iolist_to_binary(C)) || C <- Constraints], " ")
    ]);
encode_pattern_impl(
    #constructor_pattern{name = Constructor, args = Args},
    {adt, _AdtName, Variants},
    VarName
) ->
    % ADT constructor pattern: Ok(x) or Error(msg)
    % (and (is-Ok val) (= (Ok-arg val) x-pattern))
    ConstructorAtom =
        case Constructor of
            #identifier_expr{name = N} -> N;
            N when is_atom(N) -> N
        end,

    % Find the variant type for this constructor
    VariantType = find_variant_type(ConstructorAtom, Variants),

    case Args of
        [] ->
            % Nullary constructor: Ok, Nothing
            io_lib:format("(is-~s ~s)", [ConstructorAtom, VarName]);
        _ ->
            % Constructor with arguments: Error(x), Just(v)
            ArgConstraints = lists:zipwith(
                fun(Arg, {Idx, ArgType}) ->
                    ArgVarName = io_lib:format("(~s-arg-~w ~s)", [ConstructorAtom, Idx, VarName]),
                    encode_pattern_impl(Arg, ArgType, ArgVarName)
                end,
                Args,
                lists:zip(lists:seq(0, length(Args) - 1), VariantType)
            ),
            io_lib:format("(and (is-~s ~s) ~s)", [
                ConstructorAtom,
                VarName,
                string:join([binary_to_list(iolist_to_binary(C)) || C <- ArgConstraints], " ")
            ])
    end;
encode_pattern_impl(Pattern, Type, VarName) ->
    % Fallback for unhandled patterns
    io_lib:format("true ; Unhandled pattern: ~p, type: ~p, var: ~s", [Pattern, Type, VarName]).

%% @doc Encode multiple patterns as a disjunction (OR)
%% Returns constraint that is true if ANY pattern matches
-spec encode_patterns_disjunction([term()], term()) -> iolist().
encode_patterns_disjunction([], _Type) ->
    % No patterns = nothing matches
    "false";
encode_patterns_disjunction([SinglePattern], Type) ->
    encode_pattern(SinglePattern, Type);
encode_patterns_disjunction(Patterns, Type) ->
    EncodedPatterns = [encode_pattern(P, Type) || P <- Patterns],
    io_lib:format("(or ~s)", [
        string:join([binary_to_list(iolist_to_binary(P)) || P <- EncodedPatterns], " ")
    ]).

%% ============================================================================
%% Exhaustiveness Checking
%% ============================================================================

%% @doc Find a missing pattern using SMT
%% Returns {ok, Pattern} if a missing pattern is found, or exhaustive if complete
-spec find_missing_pattern([term()], term()) ->
    {missing, term()} | exhaustive | {error, term()}.
find_missing_pattern(CoveredPatterns, Type) ->
    % Encode covered patterns as disjunction
    CoveredConstraint = encode_patterns_disjunction(CoveredPatterns, Type),

    % Query: Is there a value NOT covered by any pattern?
    % (not covered_constraint)
    Query = generate_exhaustiveness_query(CoveredConstraint, Type),

    % Send to Z3
    case execute_z3_query(Query) of
        {sat, Model} ->
            % Found uncovered value - convert to pattern
            Pattern = model_to_pattern(Model, Type),
            {missing, Pattern};
        {unsat, _} ->
            % No uncovered values - patterns are exhaustive
            exhaustive;
        {error, Reason} ->
            {error, Reason}
    end.

%% @doc Check if patterns are exhaustive
%% Returns {complete} or {incomplete, [MissingPatterns]}
-spec check_exhaustiveness([term()], term()) ->
    {complete} | {incomplete, [term()]} | {error, term()}.
check_exhaustiveness(Patterns, Type) ->
    % Max 5 missing patterns
    check_exhaustiveness_impl(Patterns, Type, [], 5).

check_exhaustiveness_impl(_Patterns, _Type, MissingPatterns, 0) ->
    % Reached max depth, return what we have
    {incomplete, lists:reverse(MissingPatterns)};
check_exhaustiveness_impl(Patterns, Type, MissingPatterns, Remaining) ->
    case find_missing_pattern(Patterns, Type) of
        exhaustive ->
            case MissingPatterns of
                [] -> {complete};
                _ -> {incomplete, lists:reverse(MissingPatterns)}
            end;
        {missing, Pattern} ->
            % Found missing pattern, add it to covered and continue
            NewPatterns = [Pattern | Patterns],
            check_exhaustiveness_impl(
                NewPatterns, Type, [Pattern | MissingPatterns], Remaining - 1
            );
        {error, Reason} ->
            {error, Reason}
    end.

%% ============================================================================
%% Model Conversion
%% ============================================================================

%% @doc Convert Z3 model to Cure pattern
-spec model_to_pattern(term(), term()) -> term().
model_to_pattern(Model, {adt, _AdtName, Variants}) ->
    % For ADT, check which constructor the model represents
    % Model format: [(val, ConstructorName), ...]
    case extract_constructor_from_model(Model) of
        {ok, Constructor} ->
            % Create constructor pattern
            #constructor_pattern{
                name = #identifier_expr{name = Constructor, location = dummy_loc()},
                % Simplified: no args for now
                args = [],
                location = dummy_loc()
            };
        error ->
            % Couldn't determine constructor, use wildcard
            #identifier_expr{name = '_', location = dummy_loc()}
    end;
model_to_pattern(Model, {tuple, _ElementTypes}) ->
    % Extract tuple elements from model
    % For now, create wildcard tuple
    #identifier_expr{name = '_', location = dummy_loc()};
model_to_pattern(Model, {list, _ElemType}) ->
    % Extract list from model
    % For now, create wildcard
    #identifier_expr{name = '_', location = dummy_loc()};
model_to_pattern(Model, _Type) ->
    % For primitive types, extract literal value
    case extract_value_from_model(Model) of
        {ok, Value} ->
            #literal_expr{value = Value, location = dummy_loc()};
        error ->
            #identifier_expr{name = '_', location = dummy_loc()}
    end.

%% ============================================================================
%% Utilities
%% ============================================================================

%% @doc Convert Cure type to SMT sort
-spec type_to_smt_sort(term()) -> iolist().
type_to_smt_sort(#primitive_type{name = 'Int'}) -> "Int";
type_to_smt_sort(#primitive_type{name = 'Bool'}) -> "Bool";
type_to_smt_sort(#primitive_type{name = 'String'}) -> "String";
type_to_smt_sort({tuple, _}) -> "Tuple";
type_to_smt_sort({list, _}) -> "List";
type_to_smt_sort({adt, Name, _}) -> atom_to_list(Name);
type_to_smt_sort(_) -> "Any".

%% ============================================================================
%% Internal Helpers
%% ============================================================================

%% Convert atom to SMT symbol
atom_to_smt(Atom) ->
    case Atom of
        true -> "true";
        false -> "false";
        nil -> "nil";
        _ -> io_lib:format("~s", [Atom])
    end.

%% Generate full exhaustiveness checking query
generate_exhaustiveness_query(CoveredConstraint, Type) ->
    Sort = type_to_smt_sort(Type),
    Declarations = generate_type_declarations(Type),
    iolist_to_binary([
        Declarations,
        io_lib:format("(declare-const val ~s)~n", [Sort]),
        io_lib:format("(assert (not ~s))~n", [CoveredConstraint]),
        "(check-sat)\n",
        "(get-model)\n"
    ]).

%% Generate SMT declarations for type
generate_type_declarations({adt, Name, Variants}) ->
    % Declare ADT with constructors
    ConstructorDecls = [
        io_lib:format("  (~s)", [VariantName])
     || {VariantName, _Args} <- Variants
    ],
    io_lib:format("(declare-datatype ~s (~n~s~n))~n", [
        Name,
        string:join([binary_to_list(iolist_to_binary(D)) || D <- ConstructorDecls], "\n")
    ]);
generate_type_declarations(_Type) ->
    % Primitive types don't need declarations
    "".

%% Find variant type for constructor
find_variant_type(Constructor, Variants) ->
    case lists:keyfind(Constructor, 1, Variants) of
        {Constructor, Args} -> Args;
        false -> []
    end.

%% Extract constructor name from Z3 model
extract_constructor_from_model(Model) when is_binary(Model) ->
    % Parse model output to find constructor
    % Simplified parsing - real implementation would parse S-expressions
    case binary:split(Model, [<<"val">>, <<"=">>], [global]) of
        [_, ConstructorBin | _] ->
            Constructor = binary_to_atom(string:trim(ConstructorBin), utf8),
            {ok, Constructor};
        _ ->
            error
    end;
extract_constructor_from_model(_) ->
    error.

%% Extract literal value from Z3 model
extract_value_from_model(Model) when is_binary(Model) ->
    % Simplified: try to parse as integer
    case string:to_integer(binary_to_list(Model)) of
        {Int, _} -> {ok, Int};
        _ -> error
    end;
extract_value_from_model(_) ->
    error.

%% Execute Z3 query
execute_z3_query(QueryBinary) ->
    case cure_smt_process:start_solver(z3, 5000) of
        {ok, Pid} ->
            try
                Result = cure_smt_process:execute_query(Pid, QueryBinary, 5000),
                cure_smt_process:stop_solver(Pid),
                Result
            catch
                _:Error ->
                    cure_smt_process:stop_solver(Pid),
                    {error, Error}
            end;
        {error, Reason} ->
            {error, Reason}
    end.

%% Create dummy location for generated patterns
dummy_loc() ->
    #location{line = 0, column = 0, file = undefined}.
