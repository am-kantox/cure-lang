%% Cure Programming Language - Code Generation Header
%% Record definitions for code generation

%% BEAM instruction record
-record(beam_instr, {
    op :: atom(),
    args :: [term()],
    location :: term() | undefined
}).

%% Code generation state
-record(codegen_state, {
    module_name :: atom(),
    functions = [] :: [term()],
    exports = [] :: [term()],
    local_vars = #{} :: map(),
    temp_counter = 0 :: integer(),
    label_counter = 0 :: integer(),
    constants = #{} :: map(),
    type_info = #{} :: map(),
    optimization_level = 0 :: integer()
}).

%% Function compilation result
-record(compiled_function, {
    name :: atom(),
    arity :: integer(),
    instructions :: [term()],
    locals :: map(),
    location :: term()
}).

%% Module compilation result
-record(compiled_module, {
    name :: atom(),
    functions :: [term()],
    exports :: [term()],
    constants :: map(),
    location :: term()
}).

%% Pattern compilation state
-record(pattern_state, {
    variables :: map(),
    bindings :: [term()],
    fail_label :: term(),
    location :: term()
}).

%% Guard compilation context
-record(guard_context, {
    variables :: map(),
    fail_label :: term(),
    parameters :: [atom()],
    location :: term()
}).
