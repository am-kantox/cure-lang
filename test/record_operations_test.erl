-module(record_operations_test).

%% Test module for record field access and update operations
%% Tests the implementation of:
%%   - Direct field access: record.field
%%   - Chained field access: record.field1.field2
%%   - Record update syntax: Record{base | field: value}
%%   - Multiple field updates

-export([run/0]).

-include("../src/parser/cure_ast.hrl").

run() ->
    io:format("~n=== Record Operations Tests ===~n"),
    Results = [
        {"Parse field access", test_parse_field_access()},
        {"Parse chained field access", test_parse_chained_field_access()},
        {"Parse record update single field", test_parse_record_update_single()},
        {"Parse record update multiple fields", test_parse_record_update_multiple()},
        {"Field access in expression context", test_field_access_in_expression()},
        {"Compile field access", test_compile_field_access()},
        {"Compile record update", test_compile_record_update()},
        {"Record update with computation", test_update_with_computation()}
    ],

    Passed = length([ok || {_, ok} <- Results]),
    Total = length(Results),

    io:format("~nResults: ~p/~p tests passed~n", [Passed, Total]),

    case Passed =:= Total of
        true ->
            io:format("✓ All record operations tests passed!~n"),
            ok;
        false ->
            io:format("✗ Some tests failed~n"),
            lists:foreach(
                fun
                    ({Name, ok}) ->
                        io:format("  ✓ ~s~n", [Name]);
                    ({Name, {error, Reason}}) ->
                        io:format("  ✗ ~s: ~p~n", [Name, Reason])
                end,
                Results
            ),
            error
    end.

%% ============================================================================
%% Test Cases
%% ============================================================================

test_parse_field_access() ->
    Code =
        "\n"
        "        module Test do\n"
        "          record Person do\n"
        "            name: String\n"
        "            age: Int\n"
        "          end\n"
        "          \n"
        "          def get_name(p: Person): String =\n"
        "            p.name\n"
        "          \n"
        "          def main(): Int = 0\n"
        "        end\n"
        "    ",
    try
        Tokens = cure_lexer:tokenize(Code),
        case cure_parser:parse(Tokens) of
            {ok, [Module | _]} when is_record(Module, module_def) ->
                % Find the get_name function
                case find_function(Module, get_name, 1) of
                    {ok, #function_def{body = Body}} ->
                        case Body of
                            #field_access_expr{
                                record = #identifier_expr{name = p},
                                field = name
                            } ->
                                ok;
                            Other ->
                                {error, {unexpected_body, Other}}
                        end;
                    not_found ->
                        {error, function_not_found}
                end;
            {error, Reason} ->
                {error, {parse_error, Reason}}
        end
    catch
        _:Err -> {error, Err}
    end.

test_parse_chained_field_access() ->
    Code =
        "\n"
        "        module Test do\n"
        "          record Address do\n"
        "            city: String\n"
        "          end\n"
        "          \n"
        "          record Person do\n"
        "            address: Address\n"
        "          end\n"
        "          \n"
        "          def get_city(p: Person): String =\n"
        "            p.address.city\n"
        "          \n"
        "          def main(): Int = 0\n"
        "        end\n"
        "    ",
    try
        Tokens = cure_lexer:tokenize(Code),
        case cure_parser:parse(Tokens) of
            {ok, [Module | _]} when is_record(Module, module_def) ->
                case find_function(Module, get_city, 1) of
                    {ok, #function_def{body = Body}} ->
                        % Check for nested field access
                        case Body of
                            #field_access_expr{
                                record = #field_access_expr{
                                    record = #identifier_expr{name = p},
                                    field = address
                                },
                                field = city
                            } ->
                                ok;
                            Other ->
                                {error, {unexpected_chained_access, Other}}
                        end;
                    not_found ->
                        {error, function_not_found}
                end;
            {error, Reason} ->
                {error, {parse_error, Reason}}
        end
    catch
        _:Err -> {error, Err}
    end.

test_parse_record_update_single() ->
    Code =
        "\n"
        "        module Test do\n"
        "          record Person do\n"
        "            name: String\n"
        "            age: Int\n"
        "          end\n"
        "          \n"
        "          def birthday(p: Person): Person =\n"
        "            Person{p | age: p.age + 1}\n"
        "          \n"
        "          def main(): Int = 0\n"
        "        end\n"
        "    ",
    try
        Tokens = cure_lexer:tokenize(Code),
        case cure_parser:parse(Tokens) of
            {ok, [Module | _]} when is_record(Module, module_def) ->
                case find_function(Module, birthday, 1) of
                    {ok, #function_def{body = Body}} ->
                        case Body of
                            #record_update_expr{
                                name = 'Person',
                                base = #identifier_expr{name = p},
                                fields = [#field_expr{name = age}]
                            } ->
                                ok;
                            Other ->
                                {error, {unexpected_update_expr, Other}}
                        end;
                    not_found ->
                        {error, function_not_found}
                end;
            {error, Reason} ->
                {error, {parse_error, Reason}}
        end
    catch
        _:Err -> {error, Err}
    end.

test_parse_record_update_multiple() ->
    Code =
        "\n"
        "        module Test do\n"
        "          record Point do\n"
        "            x: Float\n"
        "            y: Float\n"
        "          end\n"
        "          \n"
        "          def move(pt: Point, dx: Float, dy: Float): Point =\n"
        "            Point{pt | x: pt.x + dx, y: pt.y + dy}\n"
        "          \n"
        "          def main(): Int = 0\n"
        "        end\n"
        "    ",
    try
        Tokens = cure_lexer:tokenize(Code),
        case cure_parser:parse(Tokens) of
            {ok, [Module | _]} when is_record(Module, module_def) ->
                case find_function(Module, move, 3) of
                    {ok, #function_def{body = Body}} ->
                        case Body of
                            #record_update_expr{
                                name = 'Point',
                                base = #identifier_expr{name = pt},
                                fields = [#field_expr{name = x}, #field_expr{name = y}]
                            } ->
                                ok;
                            #record_update_expr{fields = Fields} when length(Fields) =:= 2 ->
                                ok;
                            Other ->
                                {error, {unexpected_multiple_update, Other}}
                        end;
                    not_found ->
                        {error, function_not_found}
                end;
            {error, Reason} ->
                {error, {parse_error, Reason}}
        end
    catch
        _:Err -> {error, Err}
    end.

test_field_access_in_expression() ->
    Code =
        "\n"
        "        module Test do\n"
        "          record Point do\n"
        "            x: Float\n"
        "            y: Float\n"
        "          end\n"
        "          \n"
        "          def distance_squared(p: Point): Float =\n"
        "            p.x * p.x + p.y * p.y\n"
        "          \n"
        "          def main(): Int = 0\n"
        "        end\n"
        "    ",
    try
        Tokens = cure_lexer:tokenize(Code),
        case cure_parser:parse(Tokens) of
            {ok, [Module | _]} when is_record(Module, module_def) ->
                case find_function(Module, distance_squared, 1) of
                    {ok, #function_def{body = Body}} ->
                        % Check that field access appears in binary operations
                        case has_field_access(Body) of
                            true -> ok;
                            false -> {error, no_field_access_found}
                        end;
                    not_found ->
                        {error, function_not_found}
                end;
            {error, Reason} ->
                {error, {parse_error, Reason}}
        end
    catch
        _:Err -> {error, Err}
    end.

test_compile_field_access() ->
    Code =
        "\n"
        "        module Test do\n"
        "          record Person do\n"
        "            name: String\n"
        "          end\n"
        "          \n"
        "          def get_name(p: Person): String =\n"
        "            p.name\n"
        "          \n"
        "          def main(): Int = 0\n"
        "        end\n"
        "    ",
    try
        Tokens = cure_lexer:tokenize(Code),
        case cure_parser:parse(Tokens) of
            {ok, [Module | _]} when is_record(Module, module_def) ->
                % Try to compile to BEAM instructions
                case cure_codegen:compile_module(Module) of
                    {ok, _Instructions} ->
                        ok;
                    {error, Reason} ->
                        {error, {compile_error, Reason}}
                end;
            {error, Reason} ->
                {error, {parse_error, Reason}}
        end
    catch
        _:Err -> {error, Err}
    end.

test_compile_record_update() ->
    Code =
        "\n"
        "        module Test do\n"
        "          record Person do\n"
        "            age: Int\n"
        "          end\n"
        "          \n"
        "          def birthday(p: Person): Person =\n"
        "            Person{p | age: p.age + 1}\n"
        "          \n"
        "          def main(): Int = 0\n"
        "        end\n"
        "    ",
    try
        Tokens = cure_lexer:tokenize(Code),
        case cure_parser:parse(Tokens) of
            {ok, [Module | _]} when is_record(Module, module_def) ->
                % Try to compile to BEAM instructions
                case cure_codegen:compile_module(Module) of
                    {ok, _Instructions} ->
                        ok;
                    {error, Reason} ->
                        {error, {compile_error, Reason}}
                end;
            {error, Reason} ->
                {error, {parse_error, Reason}}
        end
    catch
        _:Err -> {error, Err}
    end.

test_update_with_computation() ->
    Code =
        "\n"
        "        module Test do\n"
        "          record Counter do\n"
        "            value: Int\n"
        "          end\n"
        "          \n"
        "          def increment_by(c: Counter, n: Int): Counter =\n"
        "            Counter{c | value: c.value + n}\n"
        "          \n"
        "          def main(): Int = 0\n"
        "        end\n"
        "    ",
    try
        Tokens = cure_lexer:tokenize(Code),
        case cure_parser:parse(Tokens) of
            {ok, [Module | _]} when is_record(Module, module_def) ->
                case find_function(Module, increment_by, 2) of
                    {ok, #function_def{body = #record_update_expr{fields = [Field]}}} ->
                        % Check that the field value contains computation
                        case Field of
                            #field_expr{
                                name = value,
                                value = #binary_op_expr{op = '+'}
                            } ->
                                ok;
                            Other ->
                                {error, {unexpected_field_value, Other}}
                        end;
                    not_found ->
                        {error, function_not_found};
                    Other ->
                        {error, {unexpected_function_body, Other}}
                end;
            {error, Reason} ->
                {error, {parse_error, Reason}}
        end
    catch
        _:Err -> {error, Err}
    end.

%% ============================================================================
%% Helper Functions
%% ============================================================================

find_function(#module_def{items = Items}, Name, Arity) ->
    case
        lists:filter(
            fun
                (#function_def{name = N, params = Params}) ->
                    N =:= Name andalso length(Params) =:= Arity;
                (_) ->
                    false
            end,
            Items
        )
    of
        [Func] -> {ok, Func};
        [] -> not_found;
        Multiple -> {error, {multiple_matches, length(Multiple)}}
    end.

has_field_access(#field_access_expr{}) ->
    true;
has_field_access(#binary_op_expr{left = Left, right = Right}) ->
    has_field_access(Left) orelse has_field_access(Right);
has_field_access(#unary_op_expr{operand = Operand}) ->
    has_field_access(Operand);
has_field_access(#function_call_expr{args = Args}) ->
    lists:any(fun has_field_access/1, Args);
has_field_access(#let_expr{body = Body}) ->
    has_field_access(Body);
has_field_access(#block_expr{expressions = Exprs}) ->
    lists:any(fun has_field_access/1, Exprs);
has_field_access(_) ->
    false.
