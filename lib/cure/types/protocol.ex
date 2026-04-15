defmodule Cure.Types.Protocol do
  @moduledoc """
  Tracks protocol definitions and their implementations within a module.

  Used during codegen to collect `proto` and `impl` containers, then
  generate type-dispatched functions.

  ## Dispatch Strategy

  For each protocol method, the codegen generates:
  - One private function per implementation: `method__for__type(args)`
  - One exported dispatch function with guard clauses that route to
    the correct implementation based on the runtime type of the first
    argument (the protocol's type parameter).
  """

  defstruct protocols: %{}, implementations: []

  @type method_sig :: %{name: String.t(), params: list(), return_type: term()}

  @type protocol_def :: %{
          name: String.t(),
          type_params: [String.t()],
          methods: [method_sig()]
        }

  @type impl_def :: %{
          protocol: String.t(),
          for_type: String.t(),
          methods: list()
        }

  @type t :: %__MODULE__{
          protocols: %{String.t() => protocol_def()},
          implementations: [impl_def()]
        }

  # -- Construction ------------------------------------------------------------

  @doc "Create an empty protocol context."
  @spec new() :: t()
  def new, do: %__MODULE__{}

  # -- Protocol Registration ---------------------------------------------------

  @doc "Register a protocol definition from a `:protocol` container."
  @spec register_protocol(t(), keyword(), list()) :: t()
  def register_protocol(%__MODULE__{} = ctx, meta, body) do
    name = Keyword.get(meta, :name, "Unknown")
    type_params = Keyword.get(meta, :type_params, [])

    methods =
      Enum.flat_map(body, fn
        {:function_def, m, _body} ->
          [
            %{
              name: Keyword.get(m, :name, "unknown"),
              params: Keyword.get(m, :params, []),
              return_type: Keyword.get(m, :return_type)
            }
          ]

        _ ->
          []
      end)

    proto_def = %{name: name, type_params: type_params, methods: methods}
    %{ctx | protocols: Map.put(ctx.protocols, name, proto_def)}
  end

  # -- Implementation Registration ---------------------------------------------

  @doc "Register an implementation from a `:trait` container."
  @spec register_impl(t(), keyword(), list()) :: t()
  def register_impl(%__MODULE__{} = ctx, meta, body) do
    proto_name = Keyword.get(meta, :protocol, "Unknown")
    for_type = Keyword.get(meta, :for, "Unknown")

    impl = %{protocol: proto_name, for_type: for_type, methods: body}
    %{ctx | implementations: [impl | ctx.implementations]}
  end

  # -- Queries -----------------------------------------------------------------

  @doc "Get all implementations for a given protocol."
  @spec impls_for(t(), String.t()) :: [impl_def()]
  def impls_for(%__MODULE__{implementations: impls}, proto_name) do
    Enum.filter(impls, &(&1.protocol == proto_name))
  end

  @doc "Get the protocol definition by name, or nil."
  @spec get_protocol(t(), String.t()) :: protocol_def() | nil
  def get_protocol(%__MODULE__{protocols: protos}, name) do
    Map.get(protos, name)
  end

  @doc "Get method names declared by a protocol."
  @spec method_names(t(), String.t()) :: [String.t()]
  def method_names(%__MODULE__{} = ctx, proto_name) do
    case get_protocol(ctx, proto_name) do
      nil -> []
      proto -> Enum.map(proto.methods, & &1.name)
    end
  end

  # -- Guard Generation --------------------------------------------------------

  @doc """
  Return the Erlang abstract-form guard test for a Cure type name.

  Given a variable form (e.g., `{:var, line, :V_x}`) and a Cure type
  name string, returns a guard expression for use in function clauses.
  """
  @spec type_guard(tuple(), String.t(), non_neg_integer()) :: tuple() | nil
  def type_guard(var_form, type_name, line) do
    case type_name do
      "Int" ->
        {:call, line, {:atom, line, :is_integer}, [var_form]}

      "Float" ->
        {:call, line, {:atom, line, :is_float}, [var_form]}

      "String" ->
        {:call, line, {:atom, line, :is_binary}, [var_form]}

      "Bool" ->
        {:call, line, {:atom, line, :is_boolean}, [var_form]}

      "Atom" ->
        {:call, line, {:atom, line, :is_atom}, [var_form]}

      "List" ->
        {:call, line, {:atom, line, :is_list}, [var_form]}

      "Tuple" ->
        {:call, line, {:atom, line, :is_tuple}, [var_form]}

      "Map" ->
        {:call, line, {:atom, line, :is_map}, [var_form]}

      "Pid" ->
        {:call, line, {:atom, line, :is_pid}, [var_form]}

      "Ref" ->
        {:call, line, {:atom, line, :is_reference}, [var_form]}

      _ ->
        # User-defined type: generate is_map(V) andalso maps:get(__struct__, V, nil) == type_atom
        type_atom = type_name |> Macro.underscore() |> String.to_atom()

        is_map_guard = {:call, line, {:atom, line, :is_map}, [var_form]}

        struct_check =
          {:op, line, :==,
           {:call, line, {:remote, line, {:atom, line, :maps}, {:atom, line, :get}},
            [{:atom, line, :__struct__}, var_form, {:atom, line, nil}]}, {:atom, line, type_atom}}

        {:op, line, :andalso, is_map_guard, struct_check}
    end
  end

  @doc """
  Return a sort priority for type dispatch.
  Lower numbers are more specific and should be checked first.
  """
  @spec type_specificity(String.t()) :: integer()
  def type_specificity("Bool"), do: 0
  def type_specificity("Int"), do: 1
  def type_specificity("Float"), do: 1
  def type_specificity("String"), do: 1
  def type_specificity("List"), do: 1
  def type_specificity("Tuple"), do: 1
  def type_specificity("Map"), do: 1
  def type_specificity("Pid"), do: 1
  def type_specificity("Ref"), do: 1
  def type_specificity("Atom"), do: 10
  def type_specificity(_), do: 100

  @doc """
  Mangle an impl method name: `show` for type `Int` -> `show__for__int`.
  """
  @spec mangle_impl_name(String.t(), String.t()) :: atom()
  def mangle_impl_name(method_name, for_type) do
    "#{String.downcase(method_name)}__for__#{String.downcase(for_type)}"
    |> String.to_atom()
  end
end
