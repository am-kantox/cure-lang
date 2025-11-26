%% Melquíades Operator Tests
%% Tests for the |-> operator (message sending to GenServers)
-module(melquiades_test).

-include_lib("eunit/eunit.hrl").
-include("../src/parser/cure_ast.hrl").

%% ============================================================================
%% Lexer Tests
%% ============================================================================

lexer_recognizes_melquiades_operator_test() ->
    Source = <<"message |-> :server">>,
    {ok, Tokens} = cure_lexer:tokenize(Source),

    % Extract token types
    TokenTypes = [cure_lexer:token_type(T) || T <- Tokens],

    % Should contain melquiades_send token
    ?assert(lists:member(melquiades_send, TokenTypes)),
    ok.

lexer_distinguishes_pipe_from_melquiades_test() ->
    Source1 = <<"x |> f">>,
    Source2 = <<"x |-> f">>,

    {ok, Tokens1} = cure_lexer:tokenize(Source1),
    {ok, Tokens2} = cure_lexer:tokenize(Source2),

    Types1 = [cure_lexer:token_type(T) || T <- Tokens1],
    Types2 = [cure_lexer:token_type(T) || T <- Tokens2],

    % Source1 should have |> but not melquiades_send
    ?assert(lists:member('|>', Types1)),
    ?assertNot(lists:member(melquiades_send, Types1)),

    % Source2 should have melquiades_send but not |>
    ?assert(lists:member(melquiades_send, Types2)),
    ?assertNot(lists:member('|>', Types2)),
    ok.

lexer_handles_melquiades_in_expression_test() ->
    Source = <<"def send(msg, srv) do msg |-> srv end">>,
    {ok, Tokens} = cure_lexer:tokenize(Source),

    Types = [cure_lexer:token_type(T) || T <- Tokens],

    % Should contain def, identifiers, do, melquiades_send, and end
    ?assert(lists:member(def, Types)),
    ?assert(lists:member(melquiades_send, Types)),
    ?assert(lists:member('end', Types)),
    ok.

%% ============================================================================
%% Parser Tests
%% ============================================================================

parser_creates_melquiades_send_expr_test() ->
    Source = <<"message |-> :server">>,
    {ok, Tokens} = cure_lexer:scan(Source),

    % Parse as an expression
    case cure_parser:parse(Tokens) of
        {ok, _AST} ->
            % Parser should succeed
            ok;
        {error, Reason} ->
            ?debugFmt("Parser error: ~p", [Reason]),
            ?assert(false)
    end.

parser_handles_record_message_test() ->
    Source =
        <<"\n"
        "        record Msg do\n"
        "            content: String\n"
        "        end\n"
        "        \n"
        "        def send() do\n"
        "            let m = Msg{content: \"hello\"}\n"
        "            m |-> :server\n"
        "        end\n"
        "    ">>,
    {ok, Tokens} = cure_lexer:scan(Source),

    case cure_parser:parse(Tokens) of
        {ok, _AST} ->
            ok;
        {error, Reason} ->
            ?debugFmt("Parser error: ~p", [Reason]),
            ?assert(false)
    end.

parser_respects_operator_precedence_test() ->
    % |-> should have same precedence as |> (1, left associative)
    Source = <<"a |> f |-> s">>,
    {ok, Tokens} = cure_lexer:scan(Source),

    % Should parse without errors
    case cure_parser:parse(Tokens) of
        {ok, _AST} ->
            ok;
        {error, Reason} ->
            ?debugFmt("Parser error: ~p", [Reason]),
            ?assert(false)
    end.

parser_handles_tuple_target_test() ->
    Source = <<"message |-> {:global, :name}">>,
    {ok, Tokens} = cure_lexer:scan(Source),

    case cure_parser:parse(Tokens) of
        {ok, _AST} ->
            ok;
        {error, Reason} ->
            ?debugFmt("Parser error: ~p", [Reason]),
            ?assert(false)
    end.

%% ============================================================================
%% AST Structure Tests
%% ============================================================================

ast_structure_test() ->
    % Create a melquiades_send_expr manually
    Message = #literal_expr{
        value = <<"Hello">>,
        location = {location, 1, 1, undefined}
    },
    Target = #identifier_expr{
        name = server,
        location = {location, 1, 10, undefined}
    },

    MelquiadesExpr = #melquiades_send_expr{
        message = Message,
        target = Target,
        location = {location, 1, 1, undefined}
    },

    % Verify structure
    ?assertEqual(Message, MelquiadesExpr#melquiades_send_expr.message),
    ?assertEqual(Target, MelquiadesExpr#melquiades_send_expr.target),
    ok.

%% ============================================================================
%% Code Generation Tests
%% ============================================================================

codegen_compiles_melquiades_expr_test() ->
    Message = #literal_expr{
        value = <<"test">>,
        location = {location, 1, 1, undefined}
    },
    Target = #identifier_expr{
        name = my_server,
        location = {location, 1, 10, undefined}
    },

    MelquiadesExpr = #melquiades_send_expr{
        message = Message,
        target = Target,
        location = {location, 1, 1, undefined}
    },

    State = cure_codegen:new_state(),
    StateWithModule = State#codegen_state{module_name = test_module},

    % Compile the expression
    case cure_codegen:compile_expression(MelquiadesExpr, StateWithModule) of
        {Instructions, _NewState} when is_list(Instructions) ->
            % Should generate instructions
            ?assert(length(Instructions) > 0),

            % Should contain melquiades_transform_message instruction
            HasTransform = lists:any(
                fun
                    (#beam_instr{op = Op}) -> Op =:= melquiades_transform_message;
                    (_) -> false
                end,
                Instructions
            ),
            ?assert(HasTransform),

            % Should contain genserver_cast instruction
            HasCast = lists:any(
                fun
                    (#beam_instr{op = Op}) -> Op =:= genserver_cast;
                    (_) -> false
                end,
                Instructions
            ),
            ?assert(HasCast),
            ok;
        {error, Reason} ->
            ?debugFmt("Codegen error: ~p", [Reason]),
            ?assert(false)
    end.

codegen_injects_module_name_test() ->
    Message = #literal_expr{value = <<"msg">>, location = {location, 1, 1, undefined}},
    Target = #identifier_expr{name = srv, location = {location, 1, 5, undefined}},

    MelquiadesExpr = #melquiades_send_expr{
        message = Message,
        target = Target,
        location = {location, 1, 1, undefined}
    },

    State = cure_codegen:new_state(),
    StateWithModule = State#codegen_state{module_name = 'TestModule'},

    {Instructions, _} = cure_codegen:compile_expression(MelquiadesExpr, StateWithModule),

    % Find the transform instruction and verify it has the module name
    TransformInstr = lists:filter(
        fun
            (#beam_instr{op = Op}) -> Op =:= melquiades_transform_message;
            (_) -> false
        end,
        Instructions
    ),

    ?assertEqual(1, length(TransformInstr)),
    [#beam_instr{args = [ModuleName]}] = TransformInstr,
    ?assertEqual('TestModule', ModuleName),
    ok.

%% ============================================================================
%% Integration Tests
%% ============================================================================

full_pipeline_simple_message_test() ->
    Source =
        <<"\n"
        "        module TestSend do\n"
        "            export [send_msg/0]\n"
        "            \n"
        "            def send_msg() -> None do\n"
        "                \"hello\" |-> :my_server\n"
        "            end\n"
        "        end\n"
        "    ">>,

    % Full pipeline: tokenize -> parse -> compile
    case cure_lexer:tokenize(Source) of
        {ok, Tokens} ->
            case cure_parser:parse(Tokens) of
                {ok, [Module]} ->
                    case cure_codegen:compile_module(Module) of
                        {ok, _CompiledModule} ->
                            ok;
                        {error, CompileError} ->
                            ?debugFmt("Compile error: ~p", [CompileError]),
                            ?assert(false)
                    end;
                {error, ParseError} ->
                    ?debugFmt("Parse error: ~p", [ParseError]),
                    ?assert(false)
            end;
        {error, LexError} ->
            ?debugFmt("Lex error: ~p", [LexError]),
            ?assert(false)
    end.

full_pipeline_record_message_test() ->
    Source =
        <<"\n"
        "        module RecordSend do\n"
        "            export [send_event/0]\n"
        "            \n"
        "            record Event do\n"
        "                name: String,\n"
        "                value: Int\n"
        "            end\n"
        "            \n"
        "            def send_event() -> None do\n"
        "                let evt = Event{name: \"test\", value: 42}\n"
        "                evt |-> :event_server\n"
        "            end\n"
        "        end\n"
        "    ">>,

    case cure_lexer:tokenize(Source) of
        {ok, Tokens} ->
            case cure_parser:parse(Tokens) of
                {ok, [Module]} ->
                    case cure_codegen:compile_module(Module) of
                        {ok, _CompiledModule} ->
                            ok;
                        {error, CompileError} ->
                            ?debugFmt("Compile error: ~p", [CompileError]),
                            ?assert(false)
                    end;
                {error, ParseError} ->
                    ?debugFmt("Parse error: ~p", [ParseError]),
                    ?assert(false)
            end;
        {error, LexError} ->
            ?debugFmt("Lex error: ~p", [LexError]),
            ?assert(false)
    end.

%% ============================================================================
%% Edge Cases
%% ============================================================================

handles_complex_message_expression_test() ->
    Source = <<"(x + y) |-> :calc_server">>,
    {ok, Tokens} = cure_lexer:scan(Source),

    case cure_parser:parse(Tokens) of
        {ok, _AST} ->
            ok;
        {error, Reason} ->
            ?debugFmt("Parser error: ~p", [Reason]),
            ?assert(false)
    end.

handles_complex_target_expression_test() ->
    Source = <<"msg |-> compute_server_name()">>,
    {ok, Tokens} = cure_lexer:scan(Source),

    case cure_parser:parse(Tokens) of
        {ok, _AST} ->
            ok;
        {error, Reason} ->
            ?debugFmt("Parser error: ~p", [Reason]),
            ?assert(false)
    end.

handles_chained_operations_test() ->
    Source =
        <<"\n"
        "        def process() do\n"
        "            data\n"
        "                |> transform()\n"
        "                |> validate()\n"
        "                |-> :processor\n"
        "        end\n"
        "    ">>,
    {ok, Tokens} = cure_lexer:scan(Source),

    case cure_parser:parse(Tokens) of
        {ok, _AST} ->
            ok;
        {error, Reason} ->
            ?debugFmt("Parser error: ~p", [Reason]),
            ?assert(false)
    end.

%% ============================================================================
%% Type System Tests (placeholders for future implementation)
%% ============================================================================

% These tests would verify GenServerRef type checking once implemented
% genserver_ref_type_local_test() -> ...
% genserver_ref_type_global_test() -> ...
% genserver_ref_type_via_test() -> ...

%% ============================================================================
%% Helper Functions
%% ============================================================================

run_all_tests() ->
    eunit:test(?MODULE, [verbose]).
