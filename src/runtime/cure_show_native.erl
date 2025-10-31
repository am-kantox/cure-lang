-module(cure_show_native).

-moduledoc """
Native Erlang implementations of Show trait functions for Cure.

Provides efficient primitive-to-string conversions for the Show trait system.
""".

-export([
    % Primitive type conversions
    int_to_string/1,
    float_to_string/1,
    bool_to_string/1,
    atom_to_string/1,
    escape_string/1,

    % Collection conversions
    show_tuple/1,
    show_list/1,
    show_list_elements/1,

    % Type guards for runtime dispatch
    is_integer_value/1,
    is_float_value/1,
    is_bool_value/1,
    is_atom_value/1,
    is_string_value/1,
    is_tuple_value/1,
    is_list_value/1
]).

%% ============================================================================
%% Primitive Type Conversions
%% ============================================================================

-doc """
Convert an integer to its string representation.
""".
-spec int_to_string(integer()) -> binary().
int_to_string(Int) when is_integer(Int) ->
    integer_to_binary(Int).

-doc """
Convert a float to its string representation.
""".
-spec float_to_string(float()) -> binary().
float_to_string(Float) when is_float(Float) ->
    % Use shortest representation that preserves the value
    float_to_binary(Float, [{decimals, 10}, compact]).

-doc """
Convert a boolean to its string representation.
""".
-spec bool_to_string(boolean()) -> binary().
bool_to_string(true) -> <<"true">>;
bool_to_string(false) -> <<"false">>.

-doc """
Convert an atom to its string representation.
""".
-spec atom_to_string(atom()) -> binary().
atom_to_string(Atom) when is_atom(Atom) ->
    <<":", (atom_to_binary(Atom, utf8))/binary>>.

-doc """
Escape special characters in a string and wrap in quotes.
""".
-spec escape_string(binary()) -> binary().
escape_string(Str) when is_binary(Str) ->
    Escaped = escape_string_chars(Str, <<>>),
    <<"\"", Escaped/binary, "\"">>.

% Helper to escape string characters
escape_string_chars(<<>>, Acc) ->
    Acc;
escape_string_chars(<<$\n, Rest/binary>>, Acc) ->
    escape_string_chars(Rest, <<Acc/binary, "\\n">>);
escape_string_chars(<<$\t, Rest/binary>>, Acc) ->
    escape_string_chars(Rest, <<Acc/binary, "\\t">>);
escape_string_chars(<<$\r, Rest/binary>>, Acc) ->
    escape_string_chars(Rest, <<Acc/binary, "\\r">>);
escape_string_chars(<<$\\, Rest/binary>>, Acc) ->
    escape_string_chars(Rest, <<Acc/binary, "\\\\">>);
escape_string_chars(<<$\", Rest/binary>>, Acc) ->
    escape_string_chars(Rest, <<Acc/binary, "\\\"">>);
escape_string_chars(<<C, Rest/binary>>, Acc) ->
    escape_string_chars(Rest, <<Acc/binary, C>>).

%% ============================================================================
%% Collection Conversions
%% ============================================================================

-doc """
Convert a tuple to its string representation.
Only handles tuples up to size 5 for now.
""".
-spec show_tuple(tuple()) -> binary().
show_tuple({}) ->
    <<"{}">>;
show_tuple({A}) ->
    iolist_to_binary([<<"{">>, show_value(A), <<"}">>]);
show_tuple({A, B}) ->
    iolist_to_binary([<<"{">>, show_value(A), <<", ">>, show_value(B), <<"}">>]);
show_tuple({A, B, C}) ->
    iolist_to_binary([
        <<"{">>,
        show_value(A),
        <<", ">>,
        show_value(B),
        <<", ">>,
        show_value(C),
        <<"}">>
    ]);
show_tuple({A, B, C, D}) ->
    iolist_to_binary([
        <<"{">>,
        show_value(A),
        <<", ">>,
        show_value(B),
        <<", ">>,
        show_value(C),
        <<", ">>,
        show_value(D),
        <<"}">>
    ]);
show_tuple({A, B, C, D, E}) ->
    iolist_to_binary([
        <<"{">>,
        show_value(A),
        <<", ">>,
        show_value(B),
        <<", ">>,
        show_value(C),
        <<", ">>,
        show_value(D),
        <<", ">>,
        show_value(E),
        <<"}">>
    ]);
show_tuple(Tuple) when is_tuple(Tuple) ->
    % For larger tuples, show a placeholder
    Size = tuple_size(Tuple),
    iolist_to_binary([<<"{...">>, integer_to_binary(Size), <<" elements...}">>]).

-doc """
Convert a list to its string representation.
""".
-spec show_list(list()) -> binary().
show_list([]) ->
    <<"[]">>;
show_list(List) when is_list(List) ->
    Elements = show_list_elements(List),
    <<"[", Elements/binary, "]">>.

-doc """
Convert list elements to comma-separated string representations.
""".
-spec show_list_elements(list()) -> binary().
show_list_elements([]) ->
    <<>>;
show_list_elements([H]) ->
    show_value(H);
show_list_elements([H | T]) ->
    Head = show_value(H),
    Tail = show_list_elements(T),
    <<Head/binary, ", ", Tail/binary>>.

%% ============================================================================
%% Generic Value Conversion (for nested structures)
%% ============================================================================

% Convert any Erlang term to a string representation
show_value(Val) when is_integer(Val) ->
    int_to_string(Val);
show_value(Val) when is_float(Val) ->
    float_to_string(Val);
show_value(Val) when is_boolean(Val) ->
    bool_to_string(Val);
show_value(Val) when is_atom(Val) ->
    atom_to_string(Val);
show_value(Val) when is_binary(Val) ->
    escape_string(Val);
show_value(Val) when is_tuple(Val) ->
    show_tuple(Val);
show_value(Val) when is_list(Val) ->
    show_list(Val);
show_value(_Val) ->
    <<"<opaque>">>.

%% ============================================================================
%% Type Guard Functions (for Cure pattern matching)
%% ============================================================================

-doc """
Check if value is an integer (for Cure pattern guards).
""".
-spec is_integer_value(term()) -> boolean().
is_integer_value(Val) -> is_integer(Val).

-doc """
Check if value is a float (for Cure pattern guards).
""".
-spec is_float_value(term()) -> boolean().
is_float_value(Val) -> is_float(Val).

-doc """
Check if value is a boolean (for Cure pattern guards).
""".
-spec is_bool_value(term()) -> boolean().
is_bool_value(true) -> true;
is_bool_value(false) -> true;
is_bool_value(_) -> false.

-doc """
Check if value is an atom (for Cure pattern guards).
""".
-spec is_atom_value(term()) -> boolean().
is_atom_value(Val) -> is_atom(Val).

-doc """
Check if value is a string/binary (for Cure pattern guards).
""".
-spec is_string_value(term()) -> boolean().
is_string_value(Val) -> is_binary(Val).

-doc """
Check if value is a tuple (for Cure pattern guards).
""".
-spec is_tuple_value(term()) -> boolean().
is_tuple_value(Val) -> is_tuple(Val).

-doc """
Check if value is a list (for Cure pattern guards).
""".
-spec is_list_value(term()) -> boolean().
is_list_value(Val) -> is_list(Val).
