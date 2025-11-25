-module(cure_mcp_server).
-export([start/0, start/1, loop/1]).

%% Model Context Protocol (MCP) Server for Cure Language
%% Implements JSON-RPC 2.0 over stdio for AI assistant integration

-record(server_state, {
    capabilities = #{
        tools => #{},
        resources => #{},
        prompts => #{}
    },
    tool_handlers = #{}
}).

%% Start the MCP server
start() ->
    start([]).

start(Options) ->
    State = init_state(Options),
    %% Start stdin reader process
    register(?MODULE, self()),
    spawn_link(fun() -> stdin_reader() end),
    %% Don't log on startup to avoid interfering with JSON-RPC protocol
    loop(State).

%% Initialize server state with tool handlers
init_state(_Options) ->
    #server_state{
        capabilities = #{
            tools => #{
                listChanged => false
            },
            resources => #{
                subscribe => false,
                listChanged => false
            }
        },
        tool_handlers = #{
            <<"compile_cure">> => fun handle_compile/1,
            <<"parse_cure">> => fun handle_parse/1,
            <<"type_check_cure">> => fun handle_type_check/1,
            <<"get_ast">> => fun handle_get_ast/1,
            <<"analyze_fsm">> => fun handle_analyze_fsm/1,
            <<"format_cure">> => fun handle_format/1,
            <<"get_syntax_help">> => fun handle_syntax_help/1,
            <<"get_examples">> => fun handle_get_examples/1,
            <<"get_stdlib_docs">> => fun handle_stdlib_docs/1,
            <<"validate_syntax">> => fun handle_validate_syntax/1
        }
    }.

%% Main server loop - receive messages from stdin reader
loop(State) ->
    loop(State, <<>>).

loop(State, Buffer) ->
    receive
        {stdin, eof} ->
            % Gracefully exit on EOF from stdin so non-interactive usage doesn't hang
            ok;
        {stdin, Data} ->
            NewBuffer = <<Buffer/binary, Data/binary>>,
            case parse_jsonrpc_messages(NewBuffer) of
                {ok, Requests, Remaining} ->
                    NewState = lists:foldl(
                        fun(Request, St) ->
                            Response = handle_request(Request, St),
                            send_jsonrpc_response(Response),
                            St
                        end,
                        State,
                        Requests
                    ),
                    loop(NewState, Remaining);
                {incomplete, _} ->
                    loop(State, NewBuffer)
            end;
        Other ->
            log_error("Unexpected message: ~p", [Other]),
            loop(State, Buffer)
    end.

%% Parse JSON-RPC messages from buffer (can be multiple messages)
parse_jsonrpc_messages(Buffer) ->
    parse_jsonrpc_messages(Buffer, []).

parse_jsonrpc_messages(<<>>, Acc) ->
    {ok, lists:reverse(Acc), <<>>};
parse_jsonrpc_messages(Buffer, Acc) ->
    % Try to find a complete JSON message (newline-delimited)
    case binary:split(Buffer, <<"\n">>) of
        [Line, Rest] when Line =/= <<>> ->
            try
                Request = json:decode(Line),
                parse_jsonrpc_messages(Rest, [Request | Acc])
            catch
                _:_ ->
                    % Skip invalid JSON and continue
                    parse_jsonrpc_messages(Rest, Acc)
            end;
        [Line, Rest] ->
            % Empty line, skip it
            parse_jsonrpc_messages(Rest, Acc);
        [Incomplete] ->
            % No newline found, need more data
            {incomplete, <<Incomplete/binary>>}
    end.

%% Send a JSON-RPC response to stdout
send_jsonrpc_response(Response) ->
    Json = json:encode(Response),
    io:format("~s~n", [Json]).

%% Stdin reader process using port to avoid terminal crashes
stdin_reader() ->
    % Open stdin as a port to read binary data (fd 0 for input, fd 0 for output to avoid conflicts)
    Port = open_port({fd, 0, 0}, [stream, binary, eof, {line, 8192}]),
    stdin_reader_loop(Port).

stdin_reader_loop(Port) ->
    receive
        {Port, {data, {eol, Data}}} ->
            % Line-based read, add newline back
            ?MODULE ! {stdin, <<Data/binary, "\n">>},
            stdin_reader_loop(Port);
        {Port, {data, {noeol, Data}}} ->
            % Partial line without newline
            ?MODULE ! {stdin, Data},
            stdin_reader_loop(Port);
        {Port, {data, Data}} ->
            % Raw binary data
            ?MODULE ! {stdin, Data},
            stdin_reader_loop(Port);
        {Port, eof} ->
            % Signal EOF to main loop to terminate gracefully
            ?MODULE ! {stdin, eof},
            ok;
        _Other ->
            stdin_reader_loop(Port)
    end.

%% Handle incoming JSON-RPC request
handle_request(Request, State) ->
    Method = maps:get(<<"method">>, Request, undefined),
    Id = maps:get(<<"id">>, Request, null),
    Params = maps:get(<<"params">>, Request, #{}),
    
    case Method of
        <<"initialize">> ->
            handle_initialize(Id, Params, State);
        <<"tools/list">> ->
            handle_tools_list(Id, State);
        <<"tools/call">> ->
            handle_tools_call(Id, Params, State);
        <<"resources/list">> ->
            handle_resources_list(Id, State);
        <<"resources/read">> ->
            handle_resources_read(Id, Params, State);
        <<"prompts/list">> ->
            handle_prompts_list(Id, State);
        _ ->
            error_response(Id, -32601, <<"Method not found">>)
    end.

%% Handle initialize request
handle_initialize(Id, _Params, State) ->
    #{
        <<"jsonrpc">> => <<"2.0">>,
        <<"id">> => Id,
        <<"result">> => #{
            <<"protocolVersion">> => <<"2024-11-05">>,
            <<"serverInfo">> => #{
                <<"name">> => <<"cure-mcp-server">>,
                <<"version">> => <<"0.1.0">>
            },
            <<"capabilities">> => State#server_state.capabilities
        }
    }.

%% Handle tools/list request
handle_tools_list(Id, _State) ->
    Tools = [
        #{
            <<"name">> => <<"compile_cure">>,
            <<"description">> => <<"Compile a Cure source file and return compilation results">>,
            <<"inputSchema">> => #{
                <<"type">> => <<"object">>,
                <<"properties">> => #{
                    <<"file_path">> => #{
                        <<"type">> => <<"string">>,
                        <<"description">> => <<"Path to the .cure source file to compile">>
                    },
                    <<"output_dir">> => #{
                        <<"type">> => <<"string">>,
                        <<"description">> => <<"Optional output directory for compiled .beam files">>
                    }
                },
                <<"required">> => [<<"file_path">>]
            }
        },
        #{
            <<"name">> => <<"parse_cure">>,
            <<"description">> => <<"Parse Cure source code and return the AST">>,
            <<"inputSchema">> => #{
                <<"type">> => <<"object">>,
                <<"properties">> => #{
                    <<"code">> => #{
                        <<"type">> => <<"string">>,
                        <<"description">> => <<"Cure source code to parse">>
                    }
                },
                <<"required">> => [<<"code">>]
            }
        },
        #{
            <<"name">> => <<"type_check_cure">>,
            <<"description">> => <<"Type-check Cure code and report type errors">>,
            <<"inputSchema">> => #{
                <<"type">> => <<"object">>,
                <<"properties">> => #{
                    <<"code">> => #{
                        <<"type">> => <<"string">>,
                        <<"description">> => <<"Cure source code to type-check">>
                    }
                },
                <<"required">> => [<<"code">>]
            }
        },
        #{
            <<"name">> => <<"get_ast">>,
            <<"description">> => <<"Get the Abstract Syntax Tree representation of Cure code">>,
            <<"inputSchema">> => #{
                <<"type">> => <<"object">>,
                <<"properties">> => #{
                    <<"code">> => #{
                        <<"type">> => <<"string">>,
                        <<"description">> => <<"Cure source code to analyze">>
                    },
                    <<"pretty_print">> => #{
                        <<"type">> => <<"boolean">>,
                        <<"description">> => <<"Whether to pretty-print the AST (default: true)">>
                    }
                },
                <<"required">> => [<<"code">>]
            }
        },
        #{
            <<"name">> => <<"analyze_fsm">>,
            <<"description">> => <<"Analyze FSM definitions in Cure code and report state machine structure">>,
            <<"inputSchema">> => #{
                <<"type">> => <<"object">>,
                <<"properties">> => #{
                    <<"code">> => #{
                        <<"type">> => <<"string">>,
                        <<"description">> => <<"Cure source code containing FSM definitions">>
                    }
                },
                <<"required">> => [<<"code">>]
            }
        },
        #{
            <<"name">> => <<"validate_syntax">>,
            <<"description">> => <<"Validate Cure code syntax without full compilation">>,
            <<"inputSchema">> => #{
                <<"type">> => <<"object">>,
                <<"properties">> => #{
                    <<"code">> => #{
                        <<"type">> => <<"string">>,
                        <<"description">> => <<"Cure source code to validate">>
                    }
                },
                <<"required">> => [<<"code">>]
            }
        },
        #{
            <<"name">> => <<"get_syntax_help">>,
            <<"description">> => <<"Get syntax help and examples for Cure language features">>,
            <<"inputSchema">> => #{
                <<"type">> => <<"object">>,
                <<"properties">> => #{
                    <<"topic">> => #{
                        <<"type">> => <<"string">>,
                        <<"description">> => <<"Topic to get help for: 'functions', 'types', 'fsm', 'typeclasses', 'pattern_matching', 'modules', 'records'">>,
                        <<"enum">> => [<<"functions">>, <<"types">>, <<"fsm">>, <<"typeclasses">>, 
                                       <<"pattern_matching">>, <<"modules">>, <<"records">>, <<"all">>]
                    }
                },
                <<"required">> => [<<"topic">>]
            }
        },
        #{
            <<"name">> => <<"get_examples">>,
            <<"description">> => <<"Get Cure code examples from the examples directory">>,
            <<"inputSchema">> => #{
                <<"type">> => <<"object">>,
                <<"properties">> => #{
                    <<"category">> => #{
                        <<"type">> => <<"string">>,
                        <<"description">> => <<"Example category: 'basics', 'fsm', 'typeclasses', 'advanced', 'all'">>,
                        <<"enum">> => [<<"basics">>, <<"fsm">>, <<"typeclasses">>, <<"advanced">>, <<"all">>]
                    }
                },
                <<"required">> => [<<"category">>]
            }
        },
        #{
            <<"name">> => <<"get_stdlib_docs">>,
            <<"description">> => <<"Get documentation for Cure standard library modules">>,
            <<"inputSchema">> => #{
                <<"type">> => <<"object">>,
                <<"properties">> => #{
                    <<"module">> => #{
                        <<"type">> => <<"string">>,
                        <<"description">> => <<"Standard library module: 'Std.List', 'Std.Io', 'Std.Fsm', 'Std.Option', 'Std.Result', 'all'">>
                    }
                },
                <<"required">> => [<<"module">>]
            }
        }
    ],
    #{
        <<"jsonrpc">> => <<"2.0">>,
        <<"id">> => Id,
        <<"result">> => #{
            <<"tools">> => Tools
        }
    }.

%% Handle tools/call request
handle_tools_call(Id, Params, State) ->
    ToolName = maps:get(<<"name">>, Params, undefined),
    Arguments = maps:get(<<"arguments">>, Params, #{}),
    Handlers = State#server_state.tool_handlers,
    
    case maps:get(ToolName, Handlers, undefined) of
        undefined ->
            error_response(Id, -32602, <<"Unknown tool">>);
        Handler ->
            try
                Result = Handler(Arguments),
                #{
                    <<"jsonrpc">> => <<"2.0">>,
                    <<"id">> => Id,
                    <<"result">> => #{
                        <<"content">> => [
                            #{
                                <<"type">> => <<"text">>,
                                <<"text">> => Result
                            }
                        ]
                    }
                }
            catch
                Type:Error:Stacktrace ->
                    ErrorMsg = io_lib:format("Tool execution failed: ~p:~p~n~p", 
                                           [Type, Error, Stacktrace]),
                    error_response(Id, -32603, list_to_binary(ErrorMsg))
            end
    end.

%% Handle resources/list request
handle_resources_list(Id, _State) ->
    #{
        <<"jsonrpc">> => <<"2.0">>,
        <<"id">> => Id,
        <<"result">> => #{
            <<"resources">> => [
                #{
                    <<"uri">> => <<"cure://project/todo">>,
                    <<"name">> => <<"Project TODO & Status">>,
                    <<"description">> => <<"Comprehensive project status, audit results, and production readiness assessment (90% complete)">>,
                    <<"mimeType">> => <<"text/markdown">>
                }
            ]
        }
    }.

%% Handle resources/read request
handle_resources_read(Id, Params, _State) ->
    Uri = maps:get(<<"uri">>, Params, undefined),
    
    case Uri of
        <<"cure://project/todo">> ->
            TodoPath = "../TODO-2025-11-24.md",
            case file:read_file(TodoPath) of
                {ok, Content} ->
                    #{
                        <<"jsonrpc">> => <<"2.0">>,
                        <<"id">> => Id,
                        <<"result">> => #{
                            <<"contents">> => [
                                #{
                                    <<"uri">> => <<"cure://project/todo">>,
                                    <<"mimeType">> => <<"text/markdown">>,
                                    <<"text">> => Content
                                }
                            ]
                        }
                    };
                {error, Reason} ->
                    error_response(Id, -32603, 
                        list_to_binary(io_lib:format("Cannot read TODO file: ~p", [Reason])))
            end;
        _ ->
            error_response(Id, -32602, <<"Unknown resource URI">>)
    end.

%% Handle prompts/list request
handle_prompts_list(Id, _State) ->
    #{
        <<"jsonrpc">> => <<"2.0">>,
        <<"id">> => Id,
        <<"result">> => #{
            <<"prompts">> => []
        }
    }.

%% Tool handlers
handle_compile(Args) ->
    FilePath = maps:get(<<"file_path">>, Args),
    OutputDir = maps:get(<<"output_dir">>, Args, <<"_build/mcp">>),
    
    case file:read_file(FilePath) of
        {ok, Code} ->
            compile_cure_code(binary_to_list(Code), binary_to_list(FilePath), binary_to_list(OutputDir));
        {error, Reason} ->
            format_error(<<"Cannot read file">>, Reason)
    end.

handle_parse(Args) ->
    Code = binary_to_list(maps:get(<<"code">>, Args)),
    parse_cure_code(Code).

handle_type_check(Args) ->
    Code = binary_to_list(maps:get(<<"code">>, Args)),
    type_check_cure_code(Code).

handle_get_ast(Args) ->
    Code = binary_to_list(maps:get(<<"code">>, Args)),
    PrettyPrint = maps:get(<<"pretty_print">>, Args, true),
    get_ast_representation(Code, PrettyPrint).

handle_analyze_fsm(Args) ->
    Code = binary_to_list(maps:get(<<"code">>, Args)),
    analyze_fsm_code(Code).

handle_format(_Args) ->
    <<"Code formatting not yet implemented">>.

handle_validate_syntax(Args) ->
    Code = binary_to_list(maps:get(<<"code">>, Args)),
    validate_syntax(Code).

handle_syntax_help(Args) ->
    Topic = maps:get(<<"topic">>, Args, <<"all">>),
    get_syntax_help(Topic).

handle_get_examples(Args) ->
    Category = maps:get(<<"category">>, Args, <<"all">>),
    get_examples(Category).

handle_stdlib_docs(Args) ->
    Module = maps:get(<<"module">>, Args, <<"all">>),
    get_stdlib_documentation(Module).

%% Helper: compile Cure code
compile_cure_code(Code, FilePath, OutputDir) ->
    try
        %% Ensure output directory exists
        filelib:ensure_dir(OutputDir ++ "/"),
        
        %% Tokenize
        case cure_lexer:tokenize(Code) of
            {ok, Tokens} ->
                %% Parse
                case cure_parser:parse(Tokens) of
                    {ok, AST} ->
                        %% Type check
                        case cure_typechecker:typecheck(AST) of
                            {ok, TypedAST} ->
                                %% Generate code
                                case cure_codegen:generate(TypedAST, OutputDir) of
                                    {ok, BeamFiles} ->
                                        format_success(<<"Compilation successful">>, #{
                                            <<"beam_files">> => BeamFiles,
                                            <<"output_dir">> => list_to_binary(OutputDir)
                                        });
                                    {error, CodegenError} ->
                                        format_error(<<"Code generation failed">>, CodegenError)
                                end;
                            {error, TypeError} ->
                                format_error(<<"Type checking failed">>, TypeError)
                        end;
                    {error, ParseError} ->
                        format_error(<<"Parse error">>, ParseError)
                end;
            {error, LexError} ->
                format_error(<<"Lexical error">>, LexError)
        end
    catch
        Type:Error:Stacktrace ->
            ErrorMsg = io_lib:format("Compilation exception: ~p:~p~n~p", [Type, Error, Stacktrace]),
            list_to_binary(ErrorMsg)
    end.

%% Helper: parse Cure code
parse_cure_code(Code) ->
    try
        case cure_lexer:tokenize(Code) of
            {ok, Tokens} ->
                case cure_parser:parse(Tokens) of
                    {ok, AST} ->
                        format_success(<<"Parse successful">>, #{
                            <<"ast_summary">> => summarize_ast(AST)
                        });
                    {error, ParseError} ->
                        format_error(<<"Parse error">>, ParseError)
                end;
            {error, LexError} ->
                format_error(<<"Lexical error">>, LexError)
        end
    catch
        Type:Error:Stacktrace ->
            ErrorMsg = io_lib:format("Parse exception: ~p:~p~n~p", [Type, Error, Stacktrace]),
            list_to_binary(ErrorMsg)
    end.

%% Helper: type-check Cure code
type_check_cure_code(Code) ->
    try
        case cure_lexer:tokenize(Code) of
            {ok, Tokens} ->
                case cure_parser:parse(Tokens) of
                    {ok, AST} ->
                        case cure_typechecker:typecheck(AST) of
                            {ok, _TypedAST} ->
                                format_success(<<"Type checking passed">>, #{});
                            {error, TypeError} ->
                                format_error(<<"Type error">>, TypeError)
                        end;
                    {error, ParseError} ->
                        format_error(<<"Parse error (cannot type-check)">>, ParseError)
                end;
            {error, LexError} ->
                format_error(<<"Lexical error (cannot type-check)">>, LexError)
        end
    catch
        Type:Error:Stacktrace ->
            ErrorMsg = io_lib:format("Type-check exception: ~p:~p~n~p", [Type, Error, Stacktrace]),
            list_to_binary(ErrorMsg)
    end.

%% Helper: get AST representation
get_ast_representation(Code, PrettyPrint) ->
    try
        case cure_lexer:tokenize(Code) of
            {ok, Tokens} ->
                case cure_parser:parse(Tokens) of
                    {ok, AST} ->
                        AstStr = if
                            PrettyPrint ->
                                io_lib:format("~p", [AST]);
                            true ->
                                io_lib:format("~w", [AST])
                        end,
                        list_to_binary(io_lib:format("AST:~n~s", [AstStr]));
                    {error, ParseError} ->
                        format_error(<<"Parse error">>, ParseError)
                end;
            {error, LexError} ->
                format_error(<<"Lexical error">>, LexError)
        end
    catch
        Type:Error:Stacktrace ->
            ErrorMsg = io_lib:format("AST extraction exception: ~p:~p~n~p", [Type, Error, Stacktrace]),
            list_to_binary(ErrorMsg)
    end.

%% Helper: analyze FSM definitions
analyze_fsm_code(Code) ->
    try
        case cure_lexer:tokenize(Code) of
            {ok, Tokens} ->
                case cure_parser:parse(Tokens) of
                    {ok, AST} ->
                        FSMs = extract_fsms(AST),
                        format_fsm_analysis(FSMs);
                    {error, ParseError} ->
                        format_error(<<"Parse error">>, ParseError)
                end;
            {error, LexError} ->
                format_error(<<"Lexical error">>, LexError)
        end
    catch
        Type:Error:Stacktrace ->
            ErrorMsg = io_lib:format("FSM analysis exception: ~p:~p~n~p", [Type, Error, Stacktrace]),
            list_to_binary(ErrorMsg)
    end.

%% Helper: validate syntax
validate_syntax(Code) ->
    try
        case cure_lexer:tokenize(Code) of
            {ok, Tokens} ->
                case cure_parser:parse(Tokens) of
                    {ok, _AST} ->
                        <<"✓ Syntax is valid">>;
                    {error, ParseError} ->
                        format_error(<<"Syntax error">>, ParseError)
                end;
            {error, LexError} ->
                format_error(<<"Lexical error">>, LexError)
        end
    catch
        Type:Error:Stacktrace ->
            ErrorMsg = io_lib:format("Validation exception: ~p:~p~n~p", [Type, Error, Stacktrace]),
            list_to_binary(ErrorMsg)
    end.

%% Helper: get syntax help
get_syntax_help(<<"all">>) ->
    <<"Cure Language Syntax Reference:\n\n", 
      (get_syntax_help(<<"modules">>))/binary, "\n\n",
      (get_syntax_help(<<"functions">>))/binary, "\n\n",
      (get_syntax_help(<<"types">>))/binary, "\n\n",
      (get_syntax_help(<<"records">>))/binary, "\n\n",
      (get_syntax_help(<<"fsm">>))/binary, "\n\n",
      (get_syntax_help(<<"typeclasses">>))/binary, "\n\n",
      (get_syntax_help(<<"pattern_matching">>))/binary>>;

get_syntax_help(<<"modules">>) ->
    <<"=== Modules ===
module ModuleName do
  export [function_name/arity, ...]
  import OtherModule [imported_fn/arity]
  
  # Module contents
end">>;

get_syntax_help(<<"functions">>) ->
    <<"=== Functions ===
# Simple function
def function_name(param: Type): ReturnType =
  expression

# Multi-clause function
def function_name
  | (x: Int): Int when x > 0 = x * 2
  | (x: Int): Int when x <= 0 = 0
  
# Generic function with type parameters
def map(list: List(T), f: T -> U): List(U) where Show(T) =
  # Implementation
">>;

get_syntax_help(<<"types">>) ->
    <<"=== Types ===
# Primitive types: Int, String, Bool, Atom

# Dependent types
type Vector(T, n: Nat) = ...

# Union types
type Option(T) = Some(T) | None

# Function types
type Transform(T) = T -> T
">>;

get_syntax_help(<<"records">>) ->
    <<"=== Records ===
record Person do
  name: String
  age: Int
end

# Generic record
record Box(T) do
  value: T
end

# Creating records
let person = Person{name: \"Alice\", age: 30}
">>;

get_syntax_help(<<"fsm">>) ->
    <<"=== Finite State Machines ===
record FSMData do
  counter: Int
end

fsm FSMData{counter: 0} do
  StateA --> |event1| StateB
  StateB --> |event2| StateC
  StateC --> |reset| StateA
end

# Using FSMs
import Std.Fsm [fsm_spawn/2, fsm_cast/2, fsm_state/1]

let pid = fsm_spawn(:FSMData, FSMData{counter: 0})
fsm_cast(pid, pair(:event1, []))
">>;

get_syntax_help(<<"typeclasses">>) ->
    <<"=== Typeclasses ===
# Define typeclass
typeclass Show(T) do
  def show(x: T): String
end

# Implement instance
instance Show(Int) do
  def show(x: Int): String = \"Int: \" <> to_string(x)
end

# Use with constraints
def debug(x: T): T where Show(T) =
  println(show(x))
  x
">>;

get_syntax_help(<<"pattern_matching">>) ->
    <<"=== Pattern Matching ===
match value do
  Some(x) -> x
  None -> default_value
end

# With guards
match x do
  n when n > 0 -> \"positive\"
  n when n < 0 -> \"negative\"
  _ -> \"zero\"
end
">>;

get_syntax_help(_) ->
    <<"Unknown topic. Available topics: functions, types, fsm, typeclasses, pattern_matching, modules, records, all">>.

%% Helper: get examples
get_examples(Category) ->
    ExamplesDir = "../examples",
    
    Files = case Category of
        <<"basics">> ->
            ["01_list_basics.cure", "01_vector_basics.cure", "02_result_handling.cure",
             "03_option_type.cure", "04_pattern_guards.cure", "05_recursion.cure"];
        <<"fsm">> ->
            ["06_fsm_traffic_light.cure", "06_fsm_traffic_light_enhanced.cure", "07_fsm_verification.cure"];
        <<"typeclasses">> ->
            ["08_typeclasses.cure", "09_derive.cure", "10_generic_algorithms.cure",
             "11_advanced_typeclasses.cure", "12_show_typeclass.cure"];
        <<"advanced">> ->
            ["13_show.cure", "14_pipe.cure", "refinement_types_advanced.cure"];
        <<"all">> ->
            case file:list_dir(ExamplesDir) of
                {ok, AllFiles} ->
                    lists:filter(fun(F) -> lists:suffix(".cure", F) end, AllFiles);
                _ ->
                    []
            end;
        _ ->
            []
    end,
    
    read_example_files(ExamplesDir, Files).

read_example_files(Dir, Files) ->
    Results = lists:map(fun(File) ->
        Path = filename:join(Dir, File),
        case file:read_file(Path) of
            {ok, Content} ->
                io_lib:format("=== ~s ===~n~s~n~n", [File, Content]);
            {error, _} ->
                io_lib:format("% Could not read ~s~n", [File])
        end
    end, Files),
    list_to_binary(lists:flatten(Results)).

%% Helper: get stdlib documentation
get_stdlib_documentation(<<"all">>) ->
    <<(get_stdlib_documentation(<<"Std.List">>))/binary, "\n\n",
      (get_stdlib_documentation(<<"Std.Io">>))/binary, "\n\n",
      (get_stdlib_documentation(<<"Std.Fsm">>))/binary, "\n\n",
      (get_stdlib_documentation(<<"Std.Option">>))/binary, "\n\n",
      (get_stdlib_documentation(<<"Std.Result">>))/binary>>;

get_stdlib_documentation(<<"Std.List">>) ->
    <<"=== Std.List Module ===
Functions for working with lists:
- map/2: Apply function to each element
- filter/2: Keep elements matching predicate
- fold/3: Reduce list to single value
- length/1: Get list length
- reverse/1: Reverse list order
- append/2: Concatenate two lists

Example:
import Std.List [map/2, filter/2]
let doubled = map([1,2,3], fn(x) -> x * 2 end)
">>;

get_stdlib_documentation(<<"Std.Io">>) ->
    <<"=== Std.Io Module ===
Input/output functions:
- println/1: Print line to stdout
- print/1: Print without newline
- read_line/0: Read line from stdin

Example:
import Std.Io [println/1]
println(\"Hello, Cure!\")
">>;

get_stdlib_documentation(<<"Std.Fsm">>) ->
    <<"=== Std.Fsm Module ===
Finite State Machine runtime functions:
- fsm_spawn/2: Create new FSM instance
- fsm_cast/2: Send async event to FSM
- fsm_call/2: Send sync request to FSM
- fsm_state/1: Get current FSM state
- fsm_advertise/2: Register FSM with name

Example:
import Std.Fsm [fsm_spawn/2, fsm_cast/2]
let pid = fsm_spawn(:MyFSM, initial_data)
fsm_cast(pid, pair(:event, []))
">>;

get_stdlib_documentation(<<"Std.Option">>) ->
    <<"=== Std.Option Module ===
Option type for representing optional values:
type Option(T) = Some(T) | None

Functions:
- map/2: Transform Some value
- flat_map/2: Chain optional operations
- unwrap/1: Extract value or error
- unwrap_or/2: Extract with default

Example:
match find_user(id) do
  Some(user) -> user.name
  None -> \"Unknown\"
end
">>;

get_stdlib_documentation(<<"Std.Result">>) ->
    <<"=== Std.Result Module ===
Result type for operations that may fail:
type Result(T, E) = Ok(T) | Err(E)

Functions:
- map/2: Transform Ok value
- map_err/2: Transform Err value
- flat_map/2: Chain fallible operations
- unwrap/1: Extract Ok or panic

Example:
match parse_int(\"42\") do
  Ok(n) -> n * 2
  Err(e) -> 0
end
">>;

get_stdlib_documentation(_) ->
    <<"Unknown module. Available modules: Std.List, Std.Io, Std.Fsm, Std.Option, Std.Result, all">>.

%% Helper: extract FSMs from AST
extract_fsms({module_def, _Name, _Exports, Items, _Loc}) ->
    lists:filtermap(fun(Item) ->
        case Item of
            {fsm_def, Name, States, Initial, StateDefs, _} ->
                {true, #{name => Name, states => States, initial => Initial, 
                        state_defs => StateDefs}};
            _ ->
                false
        end
    end, Items);
extract_fsms(_) ->
    [].

%% Helper: format FSM analysis
format_fsm_analysis([]) ->
    <<"No FSM definitions found in the code.">>;
format_fsm_analysis(FSMs) ->
    Header = io_lib:format("Found ~p FSM definition(s):~n~n", [length(FSMs)]),
    Details = lists:map(fun(FSM) ->
        Name = maps:get(name, FSM),
        States = maps:get(states, FSM),
        Initial = maps:get(initial, FSM),
        io_lib:format("FSM: ~p~n  Initial State: ~p~n  States: ~p~n", 
                     [Name, Initial, States])
    end, FSMs),
    list_to_binary([Header | Details]).

%% Helper: summarize AST
summarize_ast({module_def, Name, Exports, Items, _}) ->
    io_lib:format("Module: ~p~nExports: ~p~nItems: ~p definitions", 
                 [Name, length(Exports), length(Items)]);
summarize_ast(_) ->
    "Unknown AST structure".

%% Helper: format success response
format_success(Message, Data) ->
    DataStr = io_lib:format("~p", [Data]),
    list_to_binary(io_lib:format("✓ ~s~n~s", [Message, DataStr])).

%% Helper: format error response
format_error(Message, Reason) ->
    list_to_binary(io_lib:format("✗ ~s~nReason: ~p", [Message, Reason])).

%% Error response helper
error_response(Id, Code, Message) ->
    #{
        <<"jsonrpc">> => <<"2.0">>,
        <<"id">> => Id,
        <<"error">> => #{
            <<"code">> => Code,
            <<"message">> => Message
        }
    }.

%% Logging helpers - disabled to avoid terminal issues in MCP mode
log_info(_Msg) ->
    ok.

log_info(_Fmt, _Args) ->
    ok.

log_error(_Fmt, _Args) ->
    ok.
