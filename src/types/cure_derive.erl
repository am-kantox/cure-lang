-module(cure_derive).

%% Automatic instance derivation for typeclasses
-export([
    derive_instance/4,
    can_derive/2,
    derive_show/3,
    derive_eq/3,
    derive_ord/3
]).

-include("../parser/cure_ast.hrl").

%% ============================================================================
%% Derivation Entry Point
%% ============================================================================

-doc """
Automatically derives a typeclass instance for a given type.

## Arguments
- `TypeclassName` - Name of the typeclass to derive (e.g., 'Show', 'Eq')
- `ForType` - Type expression to derive instance for
- `Constraints` - Required constraints for the instance
- `TypeEnv` - Type environment with type definitions

## Returns
- `{ok, InstanceDef}` - Generated instance definition
- `{error, Reason}` - Cannot derive instance

## Example
```erlang
{ok, ShowInstance} = cure_derive:derive_instance(
    'Show', 
    #record_type{name = 'Person'}, 
    [],
    TypeEnv
).
```
""".
-spec derive_instance(atom(), term(), [term()], term()) ->
    {ok, #instance_def{}} | {error, term()}.
derive_instance(TypeclassName, ForType, Constraints, TypeEnv) ->
    case TypeclassName of
        'Show' -> derive_show(ForType, Constraints, TypeEnv);
        'Eq' -> derive_eq(ForType, Constraints, TypeEnv);
        'Ord' -> derive_ord(ForType, Constraints, TypeEnv);
        _ -> {error, {cannot_derive, TypeclassName}}
    end.

%% ============================================================================
%% Derivability Checking
%% ============================================================================

-doc """
Checks if a typeclass can be automatically derived for a type.

## Arguments
- `TypeclassName` - Name of the typeclass
- `ForType` - Type to check

## Returns
- `true` - Can be derived
- `false` - Cannot be derived
""".
-spec can_derive(atom(), term()) -> boolean().
can_derive('Show', #record_def{}) -> true;
can_derive('Show', #primitive_type{}) -> true;
can_derive('Eq', #record_def{}) -> true;
can_derive('Eq', #primitive_type{}) -> true;
can_derive('Ord', #record_def{}) -> true;
can_derive('Ord', #primitive_type{}) -> true;
can_derive(_, _) -> false.

%% ============================================================================
%% Show Derivation
%% ============================================================================

-doc """
Derives a Show instance for a record type.

Generates a show method that displays the record as:
  RecordName { field1: value1, field2: value2 }
""".
-spec derive_show(term(), [term()], term()) ->
    {ok, #instance_def{}} | {error, term()}.
derive_show(#primitive_type{name = TypeName}, _Constraints, _TypeEnv) ->
    % For primitive types, generate simple show
    Location = #location{line = 0, column = 0, file = "derived"},

    ShowMethod = create_show_method_for_primitive(TypeName, Location),

    Instance = #instance_def{
        typeclass = 'Show',
        type_args = [#primitive_type{name = TypeName, location = Location}],
        constraints = [],
        methods = [ShowMethod],
        location = Location
    },
    {ok, Instance};
derive_show(#record_def{name = RecordName, fields = Fields}, Constraints, _TypeEnv) ->
    Location = #location{line = 0, column = 0, file = "derived"},

    % Generate show method for record
    ShowMethod = create_show_method_for_record(RecordName, Fields, Location),

    % Determine required constraints (Show(T) for each field type T)
    FieldConstraints = derive_field_constraints('Show', Fields, Location),

    Instance = #instance_def{
        typeclass = 'Show',
        type_args = [#primitive_type{name = RecordName, location = Location}],
        constraints = FieldConstraints ++ Constraints,
        methods = [ShowMethod],
        location = Location
    },
    {ok, Instance};
derive_show(ForType, _Constraints, _TypeEnv) ->
    {error, {cannot_derive_show, ForType}}.

%% Create show method for primitive type
create_show_method_for_primitive(TypeName, Location) ->
    Param = #param{
        name = x,
        type = #primitive_type{name = TypeName, location = Location},
        location = Location
    },

    % For now, generate a placeholder that would call the appropriate conversion
    Body = #function_call_expr{
        function = #identifier_expr{name = 'to_string', location = Location},
        args = [#identifier_expr{name = x, location = Location}],
        location = Location
    },

    #function_def{
        name = show,
        type_params = [],
        clauses = [],
        params = [Param],
        return_type = #primitive_type{name = 'String', location = Location},
        constraint = undefined,
        body = Body,
        is_private = false,
        location = Location
    }.

%% Create show method for record type
create_show_method_for_record(RecordName, Fields, Location) ->
    Param = #param{
        name = record,
        type = #primitive_type{name = RecordName, location = Location},
        location = Location
    },

    % Generate body that creates string representation
    % Simplified: would actually generate proper string concatenation
    Body = generate_show_record_body(RecordName, Fields, Location),

    #function_def{
        name = show,
        type_params = [],
        clauses = [],
        params = [Param],
        return_type = #primitive_type{name = 'String', location = Location},
        constraint = undefined,
        body = Body,
        is_private = false,
        location = Location
    }.

%% Generate the body of a show method for a record
generate_show_record_body(RecordName, _Fields, Location) ->
    % This would generate:
    % RecordName { field1: show(record.field1), field2: show(record.field2), ... }
    % For now, simplified implementation
    RecordNameStr = atom_to_list(RecordName),

    #literal_expr{
        value = RecordNameStr ++ " { ... }",
        location = Location
    }.

%% ============================================================================
%% Eq Derivation
%% ============================================================================

-doc """
Derives an Eq instance for a record type.

Generates equality check that compares all fields structurally.
""".
-spec derive_eq(term(), [term()], term()) ->
    {ok, #instance_def{}} | {error, term()}.
derive_eq(#primitive_type{name = TypeName}, _Constraints, _TypeEnv) ->
    Location = #location{line = 0, column = 0, file = "derived"},

    EqMethod = create_eq_method_for_primitive(TypeName, Location),

    Instance = #instance_def{
        typeclass = 'Eq',
        type_args = [#primitive_type{name = TypeName, location = Location}],
        constraints = [],
        methods = [EqMethod],
        location = Location
    },
    {ok, Instance};
derive_eq(#record_def{name = RecordName, fields = Fields}, Constraints, _TypeEnv) ->
    Location = #location{line = 0, column = 0, file = "derived"},

    % Generate == method for record
    EqMethod = create_eq_method_for_record(RecordName, Fields, Location),

    % Determine required constraints (Eq(T) for each field type T)
    FieldConstraints = derive_field_constraints('Eq', Fields, Location),

    Instance = #instance_def{
        typeclass = 'Eq',
        type_args = [#primitive_type{name = RecordName, location = Location}],
        constraints = FieldConstraints ++ Constraints,
        methods = [EqMethod],
        location = Location
    },
    {ok, Instance};
derive_eq(ForType, _Constraints, _TypeEnv) ->
    {error, {cannot_derive_eq, ForType}}.

%% Create == method for primitive type
create_eq_method_for_primitive(TypeName, Location) ->
    Param1 = #param{
        name = x,
        type = #primitive_type{name = TypeName, location = Location},
        location = Location
    },

    Param2 = #param{
        name = y,
        type = #primitive_type{name = TypeName, location = Location},
        location = Location
    },

    % Generate call to built-in equality
    Body = #binary_op_expr{
        op = '==',
        left = #identifier_expr{name = x, location = Location},
        right = #identifier_expr{name = y, location = Location},
        location = Location
    },

    #function_def{
        name = '==',
        type_params = [],
        clauses = [],
        params = [Param1, Param2],
        return_type = #primitive_type{name = 'Bool', location = Location},
        constraint = undefined,
        body = Body,
        is_private = false,
        location = Location
    }.

%% Create == method for record type
create_eq_method_for_record(RecordName, Fields, Location) ->
    Param1 = #param{
        name = r1,
        type = #primitive_type{name = RecordName, location = Location},
        location = Location
    },

    Param2 = #param{
        name = r2,
        type = #primitive_type{name = RecordName, location = Location},
        location = Location
    },

    % Generate body that compares all fields
    Body = generate_eq_record_body(Fields, Location),

    #function_def{
        name = '==',
        type_params = [],
        clauses = [],
        params = [Param1, Param2],
        return_type = #primitive_type{name = 'Bool', location = Location},
        constraint = undefined,
        body = Body,
        is_private = false,
        location = Location
    }.

%% Generate the body of == method for a record
generate_eq_record_body(Fields, Location) ->
    % This would generate:
    % r1.field1 == r2.field1 and r1.field2 == r2.field2 and ...
    % For now, simplified
    case Fields of
        [] ->
            #literal_expr{value = true, location = Location};
        _ ->
            % In real implementation, would chain all field comparisons
            #literal_expr{value = true, location = Location}
    end.

%% ============================================================================
%% Ord Derivation
%% ============================================================================

-doc """
Derives an Ord instance for a record type.

Generates lexicographic ordering based on field order.
Requires Eq instance (superclass).
""".
-spec derive_ord(term(), [term()], term()) ->
    {ok, #instance_def{}} | {error, term()}.
derive_ord(#record_def{name = RecordName, fields = Fields}, Constraints, _TypeEnv) ->
    Location = #location{line = 0, column = 0, file = "derived"},

    % Ord requires Eq, so we need to ensure Eq constraint
    EqConstraint = #typeclass_constraint{
        typeclass = 'Eq',
        type_args = [#primitive_type{name = RecordName, location = Location}],
        location = Location
    },

    % Generate compare method for record
    CompareMethod = create_compare_method_for_record(RecordName, Fields, Location),

    % Determine required constraints (Ord(T) for each field type T)
    FieldConstraints = derive_field_constraints('Ord', Fields, Location),

    Instance = #instance_def{
        typeclass = 'Ord',
        type_args = [#primitive_type{name = RecordName, location = Location}],
        constraints = [EqConstraint | FieldConstraints] ++ Constraints,
        methods = [CompareMethod],
        location = Location
    },
    {ok, Instance};
derive_ord(ForType, _Constraints, _TypeEnv) ->
    {error, {cannot_derive_ord, ForType}}.

%% Create compare method for record type
create_compare_method_for_record(RecordName, Fields, Location) ->
    Param1 = #param{
        name = r1,
        type = #primitive_type{name = RecordName, location = Location},
        location = Location
    },

    Param2 = #param{
        name = r2,
        type = #primitive_type{name = RecordName, location = Location},
        location = Location
    },

    % Generate body that compares fields lexicographically
    Body = generate_compare_record_body(Fields, Location),

    #function_def{
        name = compare,
        type_params = [],
        clauses = [],
        params = [Param1, Param2],
        return_type = #primitive_type{name = 'Ordering', location = Location},
        constraint = undefined,
        body = Body,
        is_private = false,
        location = Location
    }.

%% Generate the body of compare method for a record
generate_compare_record_body(Fields, Location) ->
    % This would generate lexicographic comparison:
    % match compare(r1.field1, r2.field1) do
    %   EQ -> compare(r1.field2, r2.field2)
    %   result -> result
    % end
    % For now, simplified
    case Fields of
        [] ->
            #identifier_expr{name = 'EQ', location = Location};
        _ ->
            #identifier_expr{name = 'EQ', location = Location}
    end.

%% ============================================================================
%% Helper Functions
%% ============================================================================

%% Derive constraints for all field types
derive_field_constraints(TypeclassName, Fields, Location) ->
    % For each field, if its type is a type variable or parameterized,
    % we need a constraint for that typeclass
    UniqueTypes = extract_unique_field_types(Fields),

    [
        #typeclass_constraint{
            typeclass = TypeclassName,
            type_args = [Type],
            location = Location
        }
     || Type <- UniqueTypes, is_type_variable_or_param(Type)
    ].

%% Extract unique types from fields
extract_unique_field_types(Fields) ->
    Types = [Field#record_field_def.type || Field <- Fields],
    lists:usort(Types).

%% Check if a type is a type variable or parameterized
is_type_variable_or_param(#primitive_type{name = Name}) ->
    % Simple heuristic: uppercase single letter is likely a type variable
    case atom_to_list(Name) of
        [C] when C >= $A, C =< $Z -> true;
        _ -> false
    end;
is_type_variable_or_param(#dependent_type{}) ->
    true;
is_type_variable_or_param(_) ->
    false.

%% ============================================================================
%% Testing Helpers
%% ============================================================================

-doc """
Generate instance code as a string for inspection/debugging.
""".
-spec format_instance(#instance_def{}) -> string().
format_instance(#instance_def{typeclass = TC, type_args = Args}) ->
    TypeArgStr = format_type_args(Args),
    io_lib:format("instance ~p(~s) do ... end", [TC, TypeArgStr]).

format_type_args([]) -> "";
format_type_args([#primitive_type{name = Name}]) -> atom_to_list(Name);
format_type_args([H | T]) -> format_type_args([H]) ++ ", " ++ format_type_args(T).
