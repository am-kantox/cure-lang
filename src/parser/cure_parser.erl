%% Cure Programming Language - Parser
%% Recursive descent parser that converts tokens to AST
-module(cure_parser).

-export([parse/1, parse_file/1]).

-include("cure_ast_simple.hrl").

%% Parser state record
-record(parser_state, {
    tokens :: [term()],
    current :: term() | eof,
    position :: integer(),
    filename :: string() | undefined
}).

%% API Functions

%% @doc Parse a list of tokens into an AST
-spec parse([term()]) -> {ok, cure_ast:program()} | {error, term()}.
parse(Tokens) ->
    try
        State = init_parser(Tokens, undefined),
        {Program, _FinalState} = parse_program(State),
        {ok, Program}
    catch
        throw:{parse_error, Reason, Line, Column} ->
            {error, {parse_error, Reason, Line, Column}};
        Error:Reason:Stack ->
            {error, {Error, Reason, Stack}}
    end.

%% @doc Parse a file
-spec parse_file(string()) -> {ok, cure_ast:program()} | {error, term()}.
parse_file(Filename) ->
    case cure_lexer:tokenize_file(Filename) of
        {ok, Tokens} ->
            try
                State = init_parser(Tokens, Filename),
                {Program, _FinalState} = parse_program(State),
                {ok, Program}
            catch
                throw:{parse_error, Reason, Line, Column} ->
                    {error, {parse_error, Reason, Line, Column}};
                Error:Reason:Stack ->
                    {error, {Error, Reason, Stack}}
            end;
        {error, Reason} ->
            {error, Reason}
    end.

%% Internal Functions

%% Initialize parser state
init_parser([], Filename) ->
    #parser_state{
        tokens = [],
        current = eof,
        position = 0,
        filename = Filename
    };
init_parser([First | Rest], Filename) ->
    #parser_state{
        tokens = Rest,
        current = First,
        position = 1,
        filename = Filename
    }.

%% Get current token
current_token(#parser_state{current = Current}) ->
    Current.

%% Advance to next token
advance(#parser_state{tokens = [], filename = Filename}) ->
    #parser_state{
        tokens = [],
        current = eof,
        position = 0,
        filename = Filename
    };
advance(#parser_state{tokens = [Next | Rest], position = Pos, filename = Filename}) ->
    #parser_state{
        tokens = Rest,
        current = Next,
        position = Pos + 1,
        filename = Filename
    }.

%% Check if current token matches expected type
match_token(State, TokenType) ->
    case current_token(State) of
        eof -> false;
        Token ->
            get_token_type(Token) =:= TokenType
    end.

%% Get token type from token record
get_token_type(Token) when is_record(Token, token) ->
    Token#token.type;
get_token_type(_) ->
    unknown.

%% Get token value from token record
get_token_value(Token) when is_record(Token, token) ->
    Token#token.value;
get_token_value(Token) ->
    Token.

%% Get token location
get_token_location(Token) when is_record(Token, token) ->
    #location{
        line = Token#token.line,
        column = Token#token.column,
        file = undefined
    };
get_token_location(_) ->
    #location{line = 0, column = 0, file = undefined}.

%% Expect a specific token type and consume it
expect(State, TokenType) ->
    case match_token(State, TokenType) of
        true ->
            Token = current_token(State),
            {Token, advance(State)};
        false ->
            Current = current_token(State),
            throw({parse_error, {expected, TokenType, got, get_token_type(Current)}, 
                   0, 0}) % TODO: proper location
    end.

%% Parse the entire program
parse_program(State) ->
    parse_items(State, []).

%% Parse top-level items
parse_items(State, Acc) ->
    case current_token(State) of
        eof ->
            {lists:reverse(Acc), State};
        _ ->
            {Item, NewState} = parse_item(State),
            parse_items(NewState, [Item | Acc])
    end.

%% Parse a single top-level item
parse_item(State) ->
    case get_token_type(current_token(State)) of
        module ->
            parse_module(State);
        def ->
            parse_function(State);
        defp ->
            parse_function(State);
        fsm ->
            parse_fsm(State);
        type ->
            parse_type_def(State);
        import ->
            parse_import(State);
        _ ->
            Token = current_token(State),
            throw({parse_error, {unexpected_token, get_token_type(Token)}, 0, 0})
    end.

%% Parse module definition
parse_module(State) ->
    {_, State1} = expect(State, module),
    {NameToken, State2} = expect(State1, identifier),
    Name = binary_to_atom(get_token_value(NameToken), utf8),
    {_, State3} = expect(State2, do),
    
    {Exports, State4} = case match_token(State3, export) of
        true ->
            parse_export_list(State3);
        false ->
            {[], State3}
    end,
    
    {Items, State5} = parse_module_items(State4, []),
    {_, State6} = expect(State5, 'end'),
    
    % Collect all exports from items
    {AllExports, FilteredItems} = collect_exports(Exports, Items),
    
    Location = get_token_location(current_token(State)),
    Module = #module_def{
        name = Name,
        exports = AllExports,
        items = FilteredItems,
        location = Location
    },
    {Module, State6}.

%% Parse export list
parse_export_list(State) ->
    {_, State1} = expect(State, export),
    {_, State2} = expect(State1, '['),
    {Exports, State3} = parse_export_specs(State2, []),
    {_, State4} = expect(State3, ']'),
    {Exports, State4}.

%% Parse export specifications
parse_export_specs(State, Acc) ->
    case match_token(State, ']') of
        true ->
            {lists:reverse(Acc), State};
        false ->
            {Export, State1} = parse_export_spec(State),
            case match_token(State1, ',') of
                true ->
                    {_, State2} = expect(State1, ','),
                    parse_export_specs(State2, [Export | Acc]);
                false ->
                    {lists:reverse([Export | Acc]), State1}
            end
    end.

%% Parse single export spec (name/arity)
parse_export_spec(State) ->
    {NameToken, State1} = expect(State, identifier),
    Name = binary_to_atom(get_token_value(NameToken), utf8),
    {_, State2} = expect(State1, '/'),
    {ArityToken, State3} = expect(State2, number),
    Arity = get_token_value(ArityToken),
    
    Location = get_token_location(NameToken),
    Export = #export_spec{
        name = Name,
        arity = Arity,
        location = Location
    },
    {Export, State3}.

%% Parse export statement as module item
parse_export(State) ->
    {_, State1} = expect(State, export),
    {_, State2} = expect(State1, '['),
    {Exports, State3} = parse_export_specs(State2, []),
    {_, State4} = expect(State3, ']'),
    
    % Return as an export item
    {{export_list, Exports}, State4}.

%% Collect exports from module items and merge with header exports
collect_exports(HeaderExports, Items) ->
    collect_exports_helper(Items, HeaderExports, [], []).

collect_exports_helper([], ExportsAcc, ItemsAcc, _) ->
    {lists:reverse(ExportsAcc), lists:reverse(ItemsAcc)};
collect_exports_helper([{{export_list, Exports}} | Rest], ExportsAcc, ItemsAcc, _) ->
    collect_exports_helper(Rest, Exports ++ ExportsAcc, ItemsAcc, []);
collect_exports_helper([Item | Rest], ExportsAcc, ItemsAcc, _) ->
    collect_exports_helper(Rest, ExportsAcc, [Item | ItemsAcc], []).

%% Parse module items
parse_module_items(State, Acc) ->
    case get_token_type(current_token(State)) of
        'end' ->
            {lists:reverse(Acc), State};
        _ ->
            {Item, State1} = parse_module_item(State),
            parse_module_items(State1, [Item | Acc])
    end.

%% Parse single module item (similar to parse_item but includes export)
parse_module_item(State) ->
    case get_token_type(current_token(State)) of
        def ->
            parse_function(State);
        defp ->
            parse_function(State);
        fsm ->
            parse_fsm(State);
        type ->
            parse_type_def(State);
        import ->
            parse_import(State);
        export ->
            parse_export(State);
        _ ->
            Token = current_token(State),
            throw({parse_error, {unexpected_token, get_token_type(Token)}, 0, 0})
    end.

%% Parse function definition
parse_function(State) ->
    {DefToken, State1} = case get_token_type(current_token(State)) of
        def -> expect(State, def);
        defp -> expect(State, defp)
    end,
    
    {NameToken, State2} = expect(State1, identifier),
    Name = binary_to_atom(get_token_value(NameToken), utf8),
    
    {_, State3} = expect(State2, '('),
    {Params, State4} = parse_parameters(State3, []),
    {_, State5} = expect(State4, ')'),
    
    {ReturnType, State6} = case match_token(State5, ':') of
        true ->
            {_, State5a} = expect(State5, ':'),
            parse_type(State5a);
        false ->
            case match_token(State5, '->') of
                true ->
                    {_, State5b} = expect(State5, '->'),
                    parse_type(State5b);
                false ->
                    {undefined, State5}
            end
    end,
    
    {Constraint, State7} = case match_token(State6, 'when') of
        true ->
            {_, State6a} = expect(State6, 'when'),
            parse_expression(State6a);
        false ->
            {undefined, State6}
    end,
    
    {_, State8} = expect(State7, '='),
    {Body, State9} = parse_function_body(State8),
    
    Location = get_token_location(DefToken),
    Function = #function_def{
        name = Name,
        params = Params,
        return_type = ReturnType,
        constraint = Constraint,
        body = Body,
        location = Location
    },
    {Function, State9}.

%% Parse function parameters
parse_parameters(State, Acc) ->
    case match_token(State, ')') of
        true ->
            {lists:reverse(Acc), State};
        false ->
            {Param, State1} = parse_parameter(State),
            case match_token(State1, ',') of
                true ->
                    {_, State2} = expect(State1, ','),
                    parse_parameters(State2, [Param | Acc]);
                false ->
                    {lists:reverse([Param | Acc]), State1}
            end
    end.

%% Parse single parameter
parse_parameter(State) ->
    {NameToken, State1} = expect(State, identifier),
    Name = binary_to_atom(get_token_value(NameToken), utf8),
    Location = get_token_location(NameToken),
    
    {Type, State2} = case match_token(State1, ':') of
        true ->
            {_, State1a} = expect(State1, ':'),
            parse_type(State1a);
        false ->
            % No type annotation - use a generic type
            DefaultType = #primitive_type{
                name = 'Any',
                location = Location
            },
            {DefaultType, State1}
    end,
    
    Param = #param{
        name = Name,
        type = Type,
        location = Location
    },
    {Param, State2}.

%% Parse FSM definition
parse_fsm(State) ->
    {_, State1} = expect(State, fsm),
    {NameToken, State2} = expect(State1, identifier),
    Name = binary_to_atom(get_token_value(NameToken), utf8),
    {_, State3} = expect(State2, do),
    
    {States, State4} = parse_fsm_states_declaration(State3),
    {Initial, State5} = parse_fsm_initial(State4),
    {StateDefs, State6} = parse_fsm_state_definitions(State5, []),
    
    {_, State7} = expect(State6, 'end'),
    
    Location = get_token_location(NameToken),
    FSM = #fsm_def{
        name = Name,
        states = States,
        initial = Initial,
        state_defs = StateDefs,
        location = Location
    },
    {FSM, State7}.

%% Parse states declaration: states: [State1, State2, ...]
parse_fsm_states_declaration(State) ->
    {_, State1} = expect(State, states),
    {_, State2} = expect(State1, ':'),
    {_, State3} = expect(State2, '['),
    {States, State4} = parse_atom_list(State3, []),
    {_, State5} = expect(State4, ']'),
    {States, State5}.

%% Parse initial state: initial: StateName
parse_fsm_initial(State) ->
    {_, State1} = expect(State, initial),
    {_, State2} = expect(State1, ':'),
    {StateToken, State3} = expect(State2, identifier),
    Initial = binary_to_atom(get_token_value(StateToken), utf8),
    {Initial, State3}.

%% Parse FSM state definitions
parse_fsm_state_definitions(State, Acc) ->
    case get_token_type(current_token(State)) of
        'end' ->
            {lists:reverse(Acc), State};
        state ->
            {StateDef, State1} = parse_fsm_state_definition(State),
            parse_fsm_state_definitions(State1, [StateDef | Acc]);
        _ ->
            {lists:reverse(Acc), State}
    end.

%% Parse single FSM state definition
parse_fsm_state_definition(State) ->
    {_, State1} = expect(State, state),
    {NameToken, State2} = expect(State1, identifier),
    Name = binary_to_atom(get_token_value(NameToken), utf8),
    {_, State3} = expect(State2, do),
    
    {Transitions, State4} = parse_fsm_transitions(State3, []),
    {_, State5} = expect(State4, 'end'),
    
    Location = get_token_location(NameToken),
    StateDef = #state_def{
        name = Name,
        transitions = Transitions,
        location = Location
    },
    {StateDef, State5}.

%% Parse FSM transitions
parse_fsm_transitions(State, Acc) ->
    case get_token_type(current_token(State)) of
        'end' ->
            {lists:reverse(Acc), State};
        event ->
            {Transition, State1} = parse_fsm_transition(State),
            parse_fsm_transitions(State1, [Transition | Acc]);
        timeout ->
            {Transition, State1} = parse_fsm_transition(State),
            parse_fsm_transitions(State1, [Transition | Acc]);
        _ ->
            {lists:reverse(Acc), State}
    end.

%% Parse single FSM transition
parse_fsm_transition(State) ->
    case get_token_type(current_token(State)) of
        event ->
            {_, State1} = expect(State, event),
            {_, State2} = expect(State1, '('),
            {Event, State3} = parse_expression(State2),
            {_, State4} = expect(State3, ')'),
            
            % Optional guard condition with 'when'
            {Guard, State5} = case match_token(State4, 'when') of
                true ->
                    {_, State4a} = expect(State4, 'when'),
                    parse_expression(State4a);
                false ->
                    {undefined, State4}
            end,
            
            {_, State6} = expect(State5, '->'),
            {TargetToken, State7} = expect(State6, identifier),
            Target = binary_to_atom(get_token_value(TargetToken), utf8),
            
            % Optional action with 'do'
            {Action, State8} = case match_token(State7, 'do') of
                true ->
                    {_, State7a} = expect(State7, 'do'),
                    parse_action_expression(State7a);
                false ->
                    {undefined, State7}
            end,
            
            Location = get_token_location(current_token(State)),
            Transition = #transition{
                event = Event,
                guard = Guard,
                target = Target,
                action = Action,
                location = Location
            },
            {Transition, State8};
        timeout ->
            {_, State1} = expect(State, timeout),
            {_, State2} = expect(State1, '('),
            {TimeoutExpr, State3} = parse_expression(State2),
            {_, State4} = expect(State3, ')'),
            
            % Optional guard condition with 'when' for timeout as well
            {Guard, State5} = case match_token(State4, 'when') of
                true ->
                    {_, State4a} = expect(State4, 'when'),
                    parse_expression(State4a);
                false ->
                    {undefined, State4}
            end,
            
            {_, State6} = expect(State5, '->'),
            {TargetToken, State7} = expect(State6, identifier),
            Target = binary_to_atom(get_token_value(TargetToken), utf8),
            
            % Optional action with 'do'
            {Action, State8} = case match_token(State7, 'do') of
                true ->
                    {_, State7a} = expect(State7, 'do'),
                    parse_action_expression(State7a);
                false ->
                    {undefined, State7}
            end,
            
            Location = get_token_location(current_token(State)),
            Transition = #transition{
                event = TimeoutExpr,
                guard = Guard,
                target = Target,
                action = Action,
                location = Location
            },
            {Transition, State8}
    end.

%% Parse list of atoms/identifiers (backwards compatibility)
parse_atom_list(State, Acc) ->
    case match_token(State, ']') of
        true ->
            {lists:reverse(Acc), State};
        false ->
            {Token, State1} = expect(State, identifier),
            Atom = binary_to_atom(get_token_value(Token), utf8),
            case match_token(State1, ',') of
                true ->
                    {_, State2} = expect(State1, ','),
                    parse_atom_list(State2, [Atom | Acc]);
                false ->
                    {lists:reverse([Atom | Acc]), State1}
            end
    end.

%% Parse import items list (supports both plain identifiers and function/arity specs)
parse_import_items(State, Acc) ->
    case match_token(State, ']') of
        true ->
            {lists:reverse(Acc), State};
        false ->
            {Item, State1} = parse_import_item(State),
            case match_token(State1, ',') of
                true ->
                    {_, State2} = expect(State1, ','),
                    parse_import_items(State2, [Item | Acc]);
                false ->
                    {lists:reverse([Item | Acc]), State1}
            end
    end.

%% Parse single import item (identifier or function/arity spec)
parse_import_item(State) ->
    % Allow certain keywords to be used as identifiers in import lists
    {Token, State1} = case get_token_type(current_token(State)) of
        identifier -> expect(State, identifier);
        'Ok' -> expect(State, 'Ok');
        'Error' -> expect(State, 'Error');
        'Some' -> expect(State, 'Some');
        'None' -> expect(State, 'None');
        'ok' -> expect(State, 'ok');
        'error' -> expect(State, 'error');
        _ -> expect(State, identifier)
    end,
    Name = case get_token_type(Token) of
        identifier -> binary_to_atom(get_token_value(Token), utf8);
        'Ok' -> 'Ok';
        'Error' -> 'Error';
        'Some' -> 'Some';
        'None' -> 'None';
        'ok' -> ok;
        'error' -> error
    end,
    Location = get_token_location(Token),
    
    case match_token(State1, '/') of
        true ->
            % Function/arity specification
            {_, State2} = expect(State1, '/'),
            {ArityToken, State3} = expect(State2, number),
            Arity = get_token_value(ArityToken),
            
            FunctionImport = #function_import{
                name = Name,
                arity = Arity,
                location = Location
            },
            {FunctionImport, State3};
        false ->
            % Plain identifier (e.g., type constructor, constant)
            {Name, State1}
    end.

%% Parse import statement
parse_import(State) ->
    {_, State1} = expect(State, import),
    {ModuleName, State2} = parse_module_name(State1),
    
    {Items, State3} = case match_token(State2, '[') of
        true ->
            {_, State2a} = expect(State2, '['),
            {ItemList, State2b} = parse_import_items(State2a, []),
            {_, State2c} = expect(State2b, ']'),
            {ItemList, State2c};
        false ->
            {all, State2}
    end,
    
    Location = #location{line = 0, column = 0, file = undefined},  % TODO: proper location
    Import = #import_def{
        module = ModuleName,
        items = Items,
        location = Location
    },
    {Import, State3}.

%% Parse module name (supports dotted names like Std.Math)
parse_module_name(State) ->
    {FirstToken, State1} = expect(State, identifier),
    FirstPart = binary_to_atom(get_token_value(FirstToken), utf8),
    parse_module_name_parts(State1, [FirstPart]).

parse_module_name_parts(State, Acc) ->
    case match_token(State, '.') of
        true ->
            {_, State1} = expect(State, '.'),
            {PartToken, State2} = expect(State1, identifier),
            Part = binary_to_atom(get_token_value(PartToken), utf8),
            parse_module_name_parts(State2, [Part | Acc]);
        false ->
            % Combine parts into a dotted atom
            Parts = lists:reverse(Acc),
            ModuleName = list_to_atom(string:join([atom_to_list(P) || P <- Parts], ".")),
            {ModuleName, State}
    end.

%% Parse type definition
parse_type_def(State) ->
    {_, State1} = expect(State, type),
    {NameToken, State2} = expect(State1, identifier),
    Name = binary_to_atom(get_token_value(NameToken), utf8),
    
    % TODO: Parse type parameters
    {_, State3} = expect(State2, '='),
    {TypeExpr, State4} = parse_type(State3),
    
    Location = get_token_location(NameToken),
    TypeDef = #type_def{
        name = Name,
        params = [],
        definition = TypeExpr,
        location = Location
    },
    {TypeDef, State4}.

%% Parse type expressions (simplified for now)
parse_type(State) ->
    case get_token_type(current_token(State)) of
        identifier ->
            {Token, State1} = expect(State, identifier),
            Name = binary_to_atom(get_token_value(Token), utf8),
            Location = get_token_location(Token),
            
            % Check for parameterized type like List(T)
            case match_token(State1, '(') of
                true ->
                    {_, State2} = expect(State1, '('),
                    {Params, State3} = parse_type_parameters(State2, []),
                    {_, State4} = expect(State3, ')'),
                    
                    Type = #dependent_type{
                        name = Name,
                        params = Params,
                        location = Location
                    },
                    {Type, State4};
                false ->
                    Type = #primitive_type{
                        name = Name,
                        location = Location
                    },
                    {Type, State1}
            end;
        'Unit' ->
            {Token, State1} = expect(State, 'Unit'),
            Location = get_token_location(Token),
            Type = #primitive_type{
                name = 'Unit',
                location = Location
            },
            {Type, State1};
        _ ->
            throw({parse_error, expected_type, 0, 0})
    end.

%% Parse type parameters
parse_type_parameters(State, Acc) ->
    case match_token(State, ')') of
        true ->
            {lists:reverse(Acc), State};
        false ->
            {TypeParam, State1} = parse_type_parameter(State),
            case match_token(State1, ',') of
                true ->
                    {_, State2} = expect(State1, ','),
                    parse_type_parameters(State2, [TypeParam | Acc]);
                false ->
                    {lists:reverse([TypeParam | Acc]), State1}
            end
    end.

%% Parse single type parameter
parse_type_parameter(State) ->
    {Type, State1} = parse_type(State),
    Location = get_expr_location(Type),
    
    Param = #type_param{
        name = undefined,
        value = Type,
        location = Location
    },
    {Param, State1}.

%% Parse expressions with operator precedence
parse_expression(State) ->
    parse_expression_or_block(State).

%% Parse expression or block of expressions
parse_expression_or_block(State) ->
    % Try to parse as a block first (multiple expressions)
    {FirstExpr, State1} = parse_binary_expression(State, 0),
    
    % Check if there's a newline followed by more expressions
    case is_block_continuation(State1) of
        true ->
            % Parse as a block
            {RestExprs, State2} = parse_expression_sequence(State1, []),
            Location = get_expr_location(FirstExpr),
            BlockExpr = #block_expr{
                expressions = [FirstExpr | RestExprs],
                location = Location
            },
            {BlockExpr, State2};
        false ->
            % Single expression
            {FirstExpr, State1}
    end.

%% Check if we should continue parsing as a block
is_block_continuation(State) ->
    % Check if next token starts a new expression or statement
    case get_token_type(current_token(State)) of
        'let' -> true;
        identifier -> true;  % Could be function call
        _ -> false
    end.

%% Parse sequence of expressions in a block
parse_expression_sequence(State, Acc) ->
    case is_block_continuation(State) of
        true ->
            {Expr, State1} = parse_binary_expression(State, 0),
            parse_expression_sequence(State1, [Expr | Acc]);
        false ->
            {lists:reverse(Acc), State}
    end.

%% Get location from expression
get_expr_location(#literal_expr{location = Loc}) -> Loc;
get_expr_location(#identifier_expr{location = Loc}) -> Loc;
get_expr_location(#binary_op_expr{location = Loc}) -> Loc;
get_expr_location(#unary_op_expr{location = Loc}) -> Loc;
get_expr_location(#function_call_expr{location = Loc}) -> Loc;
get_expr_location(#if_expr{location = Loc}) -> Loc;
get_expr_location(#let_expr{location = Loc}) -> Loc;
get_expr_location(#block_expr{location = Loc}) -> Loc;
get_expr_location(#primitive_type{location = Loc}) -> Loc;
get_expr_location(#dependent_type{location = Loc}) -> Loc;
get_expr_location(_) -> #location{line = 0, column = 0, file = undefined}.

%% Parse binary expressions with precedence
parse_binary_expression(State, MinPrec) ->
    {Left, State1} = parse_primary_expression(State),
    parse_binary_rest(State1, Left, MinPrec).

parse_binary_rest(State, Left, MinPrec) ->
    case current_token(State) of
        eof ->
            {Left, State};
        Token ->
            case get_operator_info(get_token_type(Token)) of
                {Prec, Assoc} when Prec >= MinPrec ->
                    {_, State1} = expect(State, get_token_type(Token)),
                    NextMinPrec = case Assoc of
                        left -> Prec + 1;
                        right -> Prec
                    end,
                    {Right, State2} = parse_binary_expression(State1, NextMinPrec),
                    Location = get_token_location(Token),
                    BinOp = #binary_op_expr{
                        op = get_token_type(Token),
                        left = Left,
                        right = Right,
                        location = Location
                    },
                    parse_binary_rest(State2, BinOp, MinPrec);
                _ ->
                    {Left, State}
            end
    end.

%% Get operator precedence and associativity
get_operator_info('+') -> {10, left};
get_operator_info('-') -> {10, left};
get_operator_info('*') -> {20, left};
get_operator_info('/') -> {20, left};
get_operator_info('%') -> {20, left};
get_operator_info('++') -> {15, right};
get_operator_info('|>') -> {1, left};
get_operator_info('<') -> {5, left};
get_operator_info('>') -> {5, left};
get_operator_info('<=') -> {5, left};
get_operator_info('>=') -> {5, left};
get_operator_info('==') -> {5, left};
get_operator_info('!=') -> {5, left};
get_operator_info(_) -> undefined.

%% Parse primary expressions
parse_primary_expression(State) ->
    case get_token_type(current_token(State)) of
        identifier ->
            parse_identifier_or_call(State);
        '-' ->
            % Unary minus
            {_, State1} = expect(State, '-'),
            {Operand, State2} = parse_primary_expression(State1),
            Location = get_token_location(current_token(State)),
            UnaryExpr = #unary_op_expr{
                op = '-',
                operand = Operand,
                location = Location
            },
            {UnaryExpr, State2};
        '+' ->
            % Unary plus
            {_, State1} = expect(State, '+'),
            {Operand, State2} = parse_primary_expression(State1),
            Location = get_token_location(current_token(State)),
            UnaryExpr = #unary_op_expr{
                op = '+',
                operand = Operand,
                location = Location
            },
            {UnaryExpr, State2};
        'not' ->
            % Unary not
            {_, State1} = expect(State, 'not'),
            {Operand, State2} = parse_primary_expression(State1),
            Location = get_token_location(current_token(State)),
            UnaryExpr = #unary_op_expr{
                op = 'not',
                operand = Operand,
                location = Location
            },
            {UnaryExpr, State2};
        number ->
            {Token, State1} = expect(State, number),
            Value = get_token_value(Token),
            Location = get_token_location(Token),
            Expr = #literal_expr{
                value = Value,
                location = Location
            },
            {Expr, State1};
        string ->
            {Token, State1} = expect(State, string),
            Value = get_token_value(Token),
            Location = get_token_location(Token),
            Expr = #literal_expr{
                value = Value,
                location = Location
            },
            {Expr, State1};
        atom ->
            {Token, State1} = expect(State, atom),
            Value = get_token_value(Token),
            Location = get_token_location(Token),
            Expr = #literal_expr{
                value = Value,
                location = Location
            },
            {Expr, State1};
        true ->
            {Token, State1} = expect(State, true),
            Location = get_token_location(Token),
            Expr = #literal_expr{
                value = true,
                location = Location
            },
            {Expr, State1};
        false ->
            {Token, State1} = expect(State, false),
            Location = get_token_location(Token),
            Expr = #literal_expr{
                value = false,
                location = Location
            },
            {Expr, State1};
        'Ok' ->
            parse_constructor_expression(State);
        'Error' ->
            parse_constructor_expression(State);
        'Some' ->
            parse_constructor_expression(State);
        'None' ->
            parse_constructor_expression(State);
        'ok' ->
            parse_constructor_expression(State);
        'error' ->
            parse_constructor_expression(State);
        'if' ->
            parse_if_expression(State);
        'let' ->
            parse_let_expression(State);
        '[' ->
            parse_list_literal(State);
        'fn' ->
            parse_lambda_expression(State);
        'match' ->
            parse_match_expression(State);
        '(' ->
            {_, State1} = expect(State, '('),
            {Expr, State2} = parse_expression(State1),
            {_, State3} = expect(State2, ')'),
            {Expr, State3};
        _ ->
            Token = current_token(State),
            throw({parse_error, {unexpected_token_in_expression, get_token_type(Token)}, 0, 0})
    end.

%% Parse identifier or function call
parse_identifier_or_call(State) ->
    % Allow certain keywords to be used as identifiers in function calls
    {Token, State1} = case get_token_type(current_token(State)) of
        identifier -> expect(State, identifier);
        'ok' -> expect(State, 'ok');
        'error' -> expect(State, 'error');
        _ -> expect(State, identifier)
    end,
    Name = case get_token_type(Token) of
        identifier -> binary_to_atom(get_token_value(Token), utf8);
        'ok' -> ok;
        'error' -> error
    end,
    Location = get_token_location(Token),
    
    % Check for function call (identifier followed by '.')
    case match_token(State1, '.') of
        true ->
            {_, State2} = expect(State1, '.'),
            {FuncToken, State3} = expect(State2, identifier),
            FuncName = binary_to_atom(get_token_value(FuncToken), utf8),
            case match_token(State3, '(') of
                true ->
                    {_, State4} = expect(State3, '('),
                    {Args, State5} = parse_argument_list(State4, []),
                    {_, State6} = expect(State5, ')'),
                    
                    % Create qualified function call
                    ModuleExpr = #identifier_expr{name = Name, location = Location},
                    FuncExpr = #identifier_expr{name = FuncName, location = get_token_location(FuncToken)},
                    QualifiedFunc = #binary_op_expr{
                        op = '.',
                        left = ModuleExpr,
                        right = FuncExpr,
                        location = Location
                    },
                    CallExpr = #function_call_expr{
                        function = QualifiedFunc,
                        args = Args,
                        location = Location
                    },
                    {CallExpr, State6};
                false ->
                    % Module.function without call
                    ModuleExpr = #identifier_expr{name = Name, location = Location},
                    FuncExpr = #identifier_expr{name = FuncName, location = get_token_location(FuncToken)},
                    QualifiedExpr = #binary_op_expr{
                        op = '.',
                        left = ModuleExpr,
                        right = FuncExpr,
                        location = Location
                    },
                    {QualifiedExpr, State3}
            end;
        false ->
            % Simple identifier or function call
            case match_token(State1, '(') of
                true ->
                    {_, State2} = expect(State1, '('),
                    {Args, State3} = parse_argument_list(State2, []),
                    {_, State4} = expect(State3, ')'),
                    FuncExpr = #identifier_expr{name = Name, location = Location},
                    CallExpr = #function_call_expr{
                        function = FuncExpr,
                        args = Args,
                        location = Location
                    },
                    {CallExpr, State4};
                false ->
                    Expr = #identifier_expr{
                        name = Name,
                        location = Location
                    },
                    {Expr, State1}
            end
    end.

%% Parse argument list for function calls
parse_argument_list(State, Acc) ->
    case match_token(State, ')') of
        true ->
            {lists:reverse(Acc), State};
        false ->
            {Arg, State1} = parse_expression(State),
            case match_token(State1, ',') of
                true ->
                    {_, State2} = expect(State1, ','),
                    parse_argument_list(State2, [Arg | Acc]);
                false ->
                    {lists:reverse([Arg | Acc]), State1}
            end
    end.

%% Parse if expression
parse_if_expression(State) ->
    {_, State1} = expect(State, 'if'),
    {Condition, State2} = parse_binary_expression(State1, 0),  % Use binary_expression to avoid blocks
    {_, State3} = expect(State2, then),
    {ThenBranch, State4} = parse_binary_expression(State3, 0),  % Use binary_expression to avoid blocks
    {_, State5} = expect(State4, 'else'),
    {ElseBranch, State6} = parse_binary_expression(State5, 0),  % Use binary_expression to avoid blocks
    {_, State7} = expect(State6, 'end'),  % Expect end token
    
    Location = get_token_location(current_token(State)),
    IfExpr = #if_expr{
        condition = Condition,
        then_branch = ThenBranch,
        else_branch = ElseBranch,
        location = Location
    },
    {IfExpr, State7}.

%% Parse let expression
parse_let_expression(State) ->
    {_, State1} = expect(State, 'let'),
    {BindingVar, State2} = expect(State1, identifier),
    {_, State3} = expect(State2, '='),
    {Value, State4} = parse_binary_expression(State3, 0),  % Parse only single expression, not block
    
    % For now, let expressions without 'in' - just return the binding and continue
    VarName = binary_to_atom(get_token_value(BindingVar), utf8),
    Location = get_token_location(BindingVar),
    
    % Create a simple identifier pattern for the binding
    Pattern = #identifier_pattern{
        name = VarName,
        location = Location
    },
    
    Binding = #binding{
        pattern = Pattern,
        value = Value,
        location = Location
    },
    
    % Simple let without body for now - return as identifier
    LetExpr = #let_expr{
        bindings = [Binding],
        body = #identifier_expr{name = VarName, location = Location},
        location = Location
    },
    {LetExpr, State4}.

%% Parse list literal [1, 2, 3]
parse_list_literal(State) ->
    {_, State1} = expect(State, '['),
    Location = get_token_location(current_token(State)),
    
    {Elements, State2} = parse_expression_list(State1, []),
    {_, State3} = expect(State2, ']'),
    
    ListExpr = #list_expr{
        elements = Elements,
        location = Location
    },
    {ListExpr, State3}.

%% Parse comma-separated expression list
parse_expression_list(State, Acc) ->
    case match_token(State, ']') of
        true ->
            {lists:reverse(Acc), State};
        false ->
            {Expr, State1} = parse_expression(State),
            case match_token(State1, ',') of
                true ->
                    {_, State2} = expect(State1, ','),
                    parse_expression_list(State2, [Expr | Acc]);
                false ->
                    {lists:reverse([Expr | Acc]), State1}
            end
    end.

%% Parse lambda expression: fn(x, y) -> x + y end
parse_lambda_expression(State) ->
    {_, State1} = expect(State, 'fn'),
    {_, State2} = expect(State1, '('),
    {Params, State3} = parse_lambda_parameters(State2, []),
    {_, State4} = expect(State3, ')'),
    {_, State5} = expect(State4, '->'),
    {Body, State6} = parse_expression(State5),
    {_, State7} = expect(State6, 'end'),
    
    Location = get_token_location(current_token(State)),
    LambdaExpr = #lambda_expr{
        params = Params,
        body = Body,
        location = Location
    },
    {LambdaExpr, State7}.

%% Parse lambda parameters
parse_lambda_parameters(State, Acc) ->
    case match_token(State, ')') of
        true ->
            {lists:reverse(Acc), State};
        false ->
            {Token, State1} = expect(State, identifier),
            ParamName = binary_to_atom(get_token_value(Token), utf8),
            Location = get_token_location(Token),
            
            % Create parameter without type for now
            Param = #param{
                name = ParamName,
                type = undefined,
                location = Location
            },
            
            case match_token(State1, ',') of
                true ->
                    {_, State2} = expect(State1, ','),
                    parse_lambda_parameters(State2, [Param | Acc]);
                false ->
                    {lists:reverse([Param | Acc]), State1}
            end
    end.


%% Parse match expression: match expr do pattern -> body end
parse_match_expression(State) ->
    {_, State1} = expect(State, 'match'),
    {Expr, State2} = parse_expression(State1),
    {_, State3} = expect(State2, 'do'),
    {Clauses, State4} = parse_match_clauses(State3, []),
    {_, State5} = expect(State4, 'end'),
    
    Location = get_token_location(current_token(State)),
    MatchExpr = #match_expr{
        expr = Expr,
        patterns = Clauses,
        location = Location
    },
    {MatchExpr, State5}.

%% Parse match clauses
parse_match_clauses(State, Acc) ->
    case match_token(State, 'end') of
        true ->
            {lists:reverse(Acc), State};
        false ->
            {Clause, State1} = parse_match_clause(State),
            parse_match_clauses(State1, [Clause | Acc])
    end.

%% Parse single match clause: pattern -> body
parse_match_clause(State) ->
    {Pattern, State1} = parse_pattern(State),
    {_, State2} = expect(State1, '->'),
    {Body, State3} = parse_expression(State2),
    
    Location = get_pattern_location(Pattern),
    Clause = #match_clause{
        pattern = Pattern,
        guard = undefined,  % Guards not implemented yet
        body = Body,
        location = Location
    },
    {Clause, State3}.

%% Parse patterns
parse_pattern(State) ->
    case get_token_type(current_token(State)) of
        identifier ->
            {Token, State1} = expect(State, identifier),
            Name = binary_to_atom(get_token_value(Token), utf8),
            Location = get_token_location(Token),
            
            % Check for wildcard pattern
            case Name of
                '_' ->
                    Pattern = #wildcard_pattern{
                        location = Location
                    },
                    {Pattern, State1};
                _ ->
                    % Check if it's a constructor pattern like Ok(value)
                    case match_token(State1, '(') of
                        true when Name =:= 'Ok'; Name =:= 'Error'; Name =:= 'Some' ->
                            {_, State2} = expect(State1, '('),
                            {InnerPattern, State3} = parse_pattern(State2),
                            {_, State4} = expect(State3, ')'),
                            
                            % For now, represent as a record pattern
                            Pattern = #record_pattern{
                                name = Name,
                                fields = [#field_pattern{
                                    name = value,
                                    pattern = InnerPattern,
                                    location = Location
                                }],
                                location = Location
                            },
                            {Pattern, State4};
                        false ->
                            % Simple identifier pattern
                            Pattern = #identifier_pattern{
                                name = Name,
                                location = Location
                            },
                            {Pattern, State1}
                    end
            end;
        '[' ->
            parse_list_pattern(State);
        number ->
            {Token, State1} = expect(State, number),
            Value = get_token_value(Token),
            Location = get_token_location(Token),
            Pattern = #literal_pattern{
                value = Value,
                location = Location
            },
            {Pattern, State1};
        string ->
            {Token, State1} = expect(State, string),
            Value = get_token_value(Token),
            Location = get_token_location(Token),
            Pattern = #literal_pattern{
                value = Value,
                location = Location
            },
            {Pattern, State1};
        atom ->
            {Token, State1} = expect(State, atom),
            Value = get_token_value(Token),
            Location = get_token_location(Token),
            Pattern = #literal_pattern{
                value = Value,
                location = Location
            },
            {Pattern, State1};
        'Ok' ->
            {Token, State1} = expect(State, 'Ok'),
            Location = get_token_location(Token),
            case match_token(State1, '(') of
                true ->
                    {_, State2} = expect(State1, '('),
                    {InnerPattern, State3} = parse_pattern(State2),
                    {_, State4} = expect(State3, ')'),
                    Pattern = #record_pattern{
                        name = 'Ok',
                        fields = [#field_pattern{
                            name = value,
                            pattern = InnerPattern,
                            location = Location
                        }],
                        location = Location
                    },
                    {Pattern, State4};
                false ->
                    Pattern = #identifier_pattern{
                        name = 'Ok',
                        location = Location
                    },
                    {Pattern, State1}
            end;
        'Error' ->
            {Token, State1} = expect(State, 'Error'),
            Location = get_token_location(Token),
            case match_token(State1, '(') of
                true ->
                    {_, State2} = expect(State1, '('),
                    {InnerPattern, State3} = parse_pattern(State2),
                    {_, State4} = expect(State3, ')'),
                    Pattern = #record_pattern{
                        name = 'Error',
                        fields = [#field_pattern{
                            name = value,
                            pattern = InnerPattern,
                            location = Location
                        }],
                        location = Location
                    },
                    {Pattern, State4};
                false ->
                    Pattern = #identifier_pattern{
                        name = 'Error',
                        location = Location
                    },
                    {Pattern, State1}
            end;
        'Some' ->
            {Token, State1} = expect(State, 'Some'),
            Location = get_token_location(Token),
            case match_token(State1, '(') of
                true ->
                    {_, State2} = expect(State1, '('),
                    {InnerPattern, State3} = parse_pattern(State2),
                    {_, State4} = expect(State3, ')'),
                    Pattern = #record_pattern{
                        name = 'Some',
                        fields = [#field_pattern{
                            name = value,
                            pattern = InnerPattern,
                            location = Location
                        }],
                        location = Location
                    },
                    {Pattern, State4};
                false ->
                    Pattern = #identifier_pattern{
                        name = 'Some',
                        location = Location
                    },
                    {Pattern, State1}
            end;
        'None' ->
            {Token, State1} = expect(State, 'None'),
            Location = get_token_location(Token),
            case match_token(State1, '(') of
                true ->
                    {_, State2} = expect(State1, '('),
                    {InnerPattern, State3} = parse_pattern(State2),
                    {_, State4} = expect(State3, ')'),
                    Pattern = #record_pattern{
                        name = 'None',
                        fields = [#field_pattern{
                            name = value,
                            pattern = InnerPattern,
                            location = Location
                        }],
                        location = Location
                    },
                    {Pattern, State4};
                false ->
                    Pattern = #identifier_pattern{
                        name = 'None',
                        location = Location
                    },
                    {Pattern, State1}
            end;
        _ ->
            Token = current_token(State),
            throw({parse_error, {unexpected_token_in_pattern, get_token_type(Token)}, 0, 0})
    end.

%% Parse list pattern [head | tail] or [a, b, c]
parse_list_pattern(State) ->
    {_, State1} = expect(State, '['),
    Location = get_token_location(current_token(State)),
    
    case match_token(State1, ']') of
        true ->
            % Empty list []
            {_, State2} = expect(State1, ']'),
            Pattern = #list_pattern{
                elements = [],
                tail = undefined,
                location = Location
            },
            {Pattern, State2};
        false ->
            {FirstPattern, State2} = parse_pattern(State1),
            case match_token(State2, '|') of
                true ->
                    % [head | tail] pattern
                    {_, State3} = expect(State2, '|'),
                    {TailPattern, State4} = parse_pattern(State3),
                    {_, State5} = expect(State4, ']'),
                    Pattern = #list_pattern{
                        elements = [FirstPattern],
                        tail = TailPattern,
                        location = Location
                    },
                    {Pattern, State5};
                false ->
                    % [a, b, c] pattern - parse rest of elements
                    {RestElements, State3} = parse_pattern_list(State2, []),
                    {_, State4} = expect(State3, ']'),
                    Pattern = #list_pattern{
                        elements = [FirstPattern | RestElements],
                        tail = undefined,
                        location = Location
                    },
                    {Pattern, State4}
            end
    end.

%% Parse comma-separated pattern list
parse_pattern_list(State, Acc) ->
    case match_token(State, ']') of
        true ->
            {lists:reverse(Acc), State};
        false ->
            case match_token(State, ',') of
                true ->
                    {_, State1} = expect(State, ','),
                    {Pattern, State2} = parse_pattern(State1),
                    parse_pattern_list(State2, [Pattern | Acc]);
                false ->
                    {lists:reverse(Acc), State}
            end
    end.

%% Get pattern location
get_pattern_location(#identifier_pattern{location = Loc}) -> Loc;
get_pattern_location(#literal_pattern{location = Loc}) -> Loc;
get_pattern_location(#list_pattern{location = Loc}) -> Loc;
get_pattern_location(#record_pattern{location = Loc}) -> Loc;
get_pattern_location(#wildcard_pattern{location = Loc}) -> Loc;
get_pattern_location(_) -> #location{line = 0, column = 0, file = undefined}.

%% Parse constructor expressions like Ok(value), Error("msg")
parse_constructor_expression(State) ->
    {Token, State1} = case get_token_type(current_token(State)) of
        'Ok' -> expect(State, 'Ok');
        'Error' -> expect(State, 'Error');
        'Some' -> expect(State, 'Some');
        'None' -> expect(State, 'None');
        'ok' -> expect(State, 'ok');
        'error' -> expect(State, 'error')
    end,
    
    Name = case get_token_type(Token) of
        'Ok' -> 'Ok';
        'Error' -> 'Error';
        'Some' -> 'Some';
        'None' -> 'None';
        'ok' -> ok;
        'error' -> error;
        _ -> get_token_value(Token)
    end,
    Location = get_token_location(Token),
    
    case match_token(State1, '(') of
        true ->
            % Constructor with argument: Ok(value)
            {_, State2} = expect(State1, '('),
            {Arg, State3} = parse_expression(State2),
            {_, State4} = expect(State3, ')'),
            
            % Represent as a function call
            ConstructorExpr = #identifier_expr{name = Name, location = Location},
            CallExpr = #function_call_expr{
                function = ConstructorExpr,
                args = [Arg],
                location = Location
            },
            {CallExpr, State4};
        false ->
            % Constructor without argument: None
            Expr = #identifier_expr{
                name = Name,
                location = Location
            },
            {Expr, State1}
    end.

%% Parse function body (can be a sequence of statements)
parse_function_body(State) ->
    parse_statement_sequence(State, []).

%% Parse sequence of statements in function body
parse_statement_sequence(State, Acc) ->
    {Stmt, State1} = parse_expression(State),
    
    % Check if this is the last statement or if there are more
    case is_end_of_body(State1) of
        true ->
            % This is the last statement - return it or wrap in block
            case Acc of
                [] -> {Stmt, State1};
                _ -> 
                    Location = get_expr_location(Stmt),
                    Block = #block_expr{
                        expressions = lists:reverse([Stmt | Acc]),
                        location = Location
                    },
                    {Block, State1}
            end;
        false ->
            % More statements follow
            parse_statement_sequence(State1, [Stmt | Acc])
    end.

%% Check if we're at the end of a function body
is_end_of_body(State) ->
    case get_token_type(current_token(State)) of
        eof -> true;
        'end' -> true;
        'else' -> true;
        'def' -> true;
        'defp' -> true;
        _ -> false
    end.

%% ============================================================================
%% Action Expression Parsing
%% ============================================================================

%% Parse action expressions for FSM transitions
parse_action_expression(State) ->
    case get_token_type(current_token(State)) of
        '{' ->
            % Action sequence: do { action1; action2; ... }
            {_, State1} = expect(State, '{'),
            {Actions, State2} = parse_action_sequence(State1, []),
            {_, State3} = expect(State2, '}'),
            Location = get_token_location(current_token(State)),
            {{sequence, Actions, Location}, State3};
        
        identifier ->
            % Single action or assignment
            parse_single_action(State);
        
        'if' ->
            % Conditional action
            parse_conditional_action(State);
        
        'log' ->
            % Logging action
            parse_log_action(State);
        
        'emit' ->
            % Event emission action
            parse_emit_action(State);
        
        _ ->
            {error, {unexpected_token_in_action, get_token_type(current_token(State))}}
    end.

%% Parse a sequence of actions separated by semicolons
parse_action_sequence(State, Acc) ->
    case get_token_type(current_token(State)) of
        '}' ->
            {lists:reverse(Acc), State};
        _ ->
            {Action, State1} = parse_single_action(State),
            case match_token(State1, ';') of
                true ->
                    {_, State2} = expect(State1, ';'),
                    parse_action_sequence(State2, [Action | Acc]);
                false ->
                    {lists:reverse([Action | Acc]), State1}
            end
    end.

%% Parse a single action
parse_single_action(State) ->
    {NameToken, State1} = expect(State, identifier),
    Name = binary_to_atom(get_token_value(NameToken), utf8),
    Location = get_token_location(NameToken),
    
    case get_token_type(current_token(State1)) of
        '=' ->
            % Assignment: variable = value
            {_, State2} = expect(State1, '='),
            {Value, State3} = parse_action_value(State2),
            {{assign, Name, Value, Location}, State3};
        
        '+=' ->
            % Increment: variable += amount
            {_, State2} = expect(State1, '+='),
            {Amount, State3} = parse_action_value(State2),
            {{increment, Name, Amount, Location}, State3};
        
        '-=' ->
            % Decrement: variable -= amount
            {_, State2} = expect(State1, '-='),
            {Amount, State3} = parse_action_value(State2),
            {{decrement, Name, Amount, Location}, State3};
        
        '(' ->
            % Function call: function(args)
            {_, State2} = expect(State1, '('),
            {Args, State3} = parse_action_arguments(State2, []),
            {_, State4} = expect(State3, ')'),
            {{call, Name, Args, Location}, State4};
        
        _ ->
            % Just a variable reference or field access
            case match_token(State1, '.') of
                true ->
                    {_, State2} = expect(State1, '.'),
                    {FieldToken, State3} = expect(State2, identifier),
                    Field = binary_to_atom(get_token_value(FieldToken), utf8),
                    
                    case match_token(State3, '=') of
                        true ->
                            {_, State4} = expect(State3, '='),
                            {Value, State5} = parse_action_value(State4),
                            {{update, Field, Value, Location}, State5};
                        false ->
                            {{state_field, Field, Location}, State3}
                    end;
                false ->
                    {{state_var, Name, Location}, State1}
            end
    end.

%% Parse conditional actions: if condition then action else action end
parse_conditional_action(State) ->
    {_, State1} = expect(State, 'if'),
    {Condition, State2} = parse_action_condition(State1),
    {_, State3} = expect(State2, 'then'),
    {ThenAction, State4} = parse_action_expression(State3),
    
    {ElseAction, State5} = case match_token(State4, 'else') of
        true ->
            {_, State4a} = expect(State4, 'else'),
            parse_action_expression(State4a);
        false ->
            {undefined, State4}
    end,
    
    {_, State6} = expect(State5, 'end'),
    Location = get_token_location(current_token(State)),
    {{if_then, Condition, ThenAction, ElseAction, Location}, State6}.

%% Parse log actions: log(level, message)
parse_log_action(State) ->
    {_, State1} = expect(State, 'log'),
    {_, State2} = expect(State1, '('),
    {LevelToken, State3} = expect(State2, identifier),
    Level = binary_to_atom(get_token_value(LevelToken), utf8),
    {_, State4} = expect(State3, ','),
    {Message, State5} = parse_action_value(State4),
    {_, State6} = expect(State5, ')'),
    Location = get_token_location(current_token(State)),
    {{log, Level, Message, Location}, State6}.

%% Parse emit actions: emit(event) or emit(event, data)
parse_emit_action(State) ->
    {_, State1} = expect(State, 'emit'),
    {_, State2} = expect(State1, '('),
    {Event, State3} = parse_action_value(State2),
    
    {Data, State4} = case match_token(State3, ',') of
        true ->
            {_, State3a} = expect(State3, ','),
            parse_action_value(State3a);
        false ->
            {undefined, State3}
    end,
    
    {_, State5} = expect(State4, ')'),
    Location = get_token_location(current_token(State)),
    {{emit, Event, Data, Location}, State5}.

%% Parse action conditions (similar to expressions)
parse_action_condition(State) ->
    parse_expression(State).

%% Parse action values (expressions that produce values)
parse_action_value(State) ->
    case get_token_type(current_token(State)) of
        number ->
            {Token, State1} = expect(State, number),
            Value = get_token_value(Token),
            Location = get_token_location(Token),
            {{literal, Value, Location}, State1};
        
        string ->
            {Token, State1} = expect(State, string),
            Value = get_token_value(Token),
            Location = get_token_location(Token),
            {{literal, Value, Location}, State1};
        
        atom ->
            {Token, State1} = expect(State, atom),
            Value = get_token_value(Token),
            Location = get_token_location(Token),
            {{literal, Value, Location}, State1};
        
        identifier ->
            {NameToken, State1} = expect(State, identifier),
            Name = binary_to_atom(get_token_value(NameToken), utf8),
            Location = get_token_location(NameToken),
            
            case Name of
                event_data -> {{event_data, Location}, State1};
                current_state -> {{current_state, Location}, State1};
                _ ->
                    case match_token(State1, '.') of
                        true ->
                            {_, State2} = expect(State1, '.'),
                            {FieldToken, State3} = expect(State2, identifier),
                            Field = binary_to_atom(get_token_value(FieldToken), utf8),
                            {{state_field, Field, Location}, State3};
                        false ->
                            case match_token(State1, '(') of
                                true ->
                                    % Function call
                                    {_, State2} = expect(State1, '('),
                                    {Args, State3} = parse_action_arguments(State2, []),
                                    {_, State4} = expect(State3, ')'),
                                    {{function_call, Name, Args, Location}, State4};
                                false ->
                                    {{state_var, Name, Location}, State1}
                            end
                    end
            end;
        
        '(' ->
            % Parenthesized expression or binary operation
            {_, State1} = expect(State, '('),
            {Value, State2} = parse_action_binary_expr(State1),
            {_, State3} = expect(State2, ')'),
            {Value, State3};
        
        _ ->
            {error, {unexpected_token_in_action_value, get_token_type(current_token(State))}}
    end.

%% Parse binary expressions in actions
parse_action_binary_expr(State) ->
    {Left, State1} = parse_action_value(State),
    case get_token_type(current_token(State1)) of
        '+' ->
            {_, State2} = expect(State1, '+'),
            {Right, State3} = parse_action_value(State2),
            Location = get_token_location(current_token(State)),
            {{binary_op, '+', Left, Right, Location}, State3};
        '-' ->
            {_, State2} = expect(State1, '-'),
            {Right, State3} = parse_action_value(State2),
            Location = get_token_location(current_token(State)),
            {{binary_op, '-', Left, Right, Location}, State3};
        '*' ->
            {_, State2} = expect(State1, '*'),
            {Right, State3} = parse_action_value(State2),
            Location = get_token_location(current_token(State)),
            {{binary_op, '*', Left, Right, Location}, State3};
        '/' ->
            {_, State2} = expect(State1, '/'),
            {Right, State3} = parse_action_value(State2),
            Location = get_token_location(current_token(State)),
            {{binary_op, '/', Left, Right, Location}, State3};
        _ ->
            {Left, State1}
    end.

%% Parse action function arguments
parse_action_arguments(State, Acc) ->
    case get_token_type(current_token(State)) of
        ')' ->
            {lists:reverse(Acc), State};
        _ ->
            {Arg, State1} = parse_action_value(State),
            case match_token(State1, ',') of
                true ->
                    {_, State2} = expect(State1, ','),
                    parse_action_arguments(State2, [Arg | Acc]);
                false ->
                    {lists:reverse([Arg | Acc]), State1}
            end
    end.
