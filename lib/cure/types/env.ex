defmodule Cure.Types.Env do
  @moduledoc """
  Scoped typing environment for the Cure type checker.

  Maintains variable bindings, named type definitions, and function
  signatures in a stack of scopes. The outermost scope contains
  built-in types and operators.
  """

  defstruct scopes: [%{}],
            types: %{},
            used: MapSet.new(),
            refinement_assumptions: [],
            refinement_var_types: %{}

  @type t :: %__MODULE__{
          scopes: [map()],
          types: map(),
          used: MapSet.t(String.t()),
          refinement_assumptions: [tuple()],
          refinement_var_types: %{String.t() => atom()}
        }

  # -- Construction ------------------------------------------------------------

  @doc "Create a new environment pre-loaded with built-in bindings and types."
  @spec new() :: t()
  def new do
    builtins = %{
      # Arithmetic operators are inferred contextually, not via env lookup.
      # But we register common stdlib-like names for completeness.
      "abs" => {:fun, [:int], :int},
      "length" => {:fun, [{:list, :any}], :int},
      "to_string" => {:fun, [:any], :string}
    }

    builtin_types = %{
      "Int" => :int,
      "Float" => :float,
      "String" => :string,
      "Bool" => :bool,
      "Atom" => :atom,
      "Unit" => :unit,
      "Any" => :any,
      "Never" => :never,
      "Char" => :char
    }

    %__MODULE__{scopes: [builtins], types: builtin_types}
  end

  # -- Variable Bindings -------------------------------------------------------

  @doc "Look up a variable name in the environment. Returns `{:ok, type}` or `:error`."
  @spec lookup(t(), String.t()) :: {:ok, term()} | :error
  def lookup(%__MODULE__{scopes: scopes} = env, name) do
    result =
      Enum.find_value(scopes, :error, fn scope ->
        case Map.fetch(scope, name) do
          {:ok, _} = ok -> ok
          :error -> nil
        end
      end)

    # Track usage (side-effect free -- caller must use the returned env if tracking)
    case result do
      {:ok, _} -> mark_used(env, name)
      _ -> env
    end

    result
  end

  @doc "Mark a variable as used."
  @spec mark_used(t(), String.t()) :: t()
  def mark_used(%__MODULE__{} = env, name) do
    # Access `env.used` through the accessor rather than destructuring so
    # dialyzer preserves MapSet's opaqueness through this function.
    %{env | used: MapSet.put(env.used, name)}
  end

  @doc "Get unused variables (those extended but never looked up, excluding _-prefixed)."
  @spec unused_variables(t()) :: [String.t()]
  def unused_variables(%__MODULE__{} = env) do
    all_vars =
      env.scopes
      |> Enum.flat_map(fn scope -> Map.keys(scope) end)
      |> MapSet.new()

    all_vars
    |> MapSet.difference(env.used)
    |> Enum.reject(&String.starts_with?(&1, "_"))
    |> Enum.reject(&(&1 in ["abs", "length", "to_string"]))
    |> Enum.sort()
  end

  @doc "Extend the current scope with a new variable binding."
  @spec extend(t(), String.t(), term()) :: t()
  def extend(%__MODULE__{scopes: [top | rest]} = env, name, type) do
    %{env | scopes: [Map.put(top, name, type) | rest]}
  end

  @doc "Push a new empty scope (for blocks, lambdas, function bodies)."
  @spec push_scope(t()) :: t()
  def push_scope(%__MODULE__{scopes: scopes} = env) do
    %{env | scopes: [%{} | scopes]}
  end

  @doc "Pop the innermost scope."
  @spec pop_scope(t()) :: t()
  def pop_scope(%__MODULE__{scopes: [_ | rest]} = env) when rest != [] do
    %{env | scopes: rest}
  end

  def pop_scope(env), do: env

  # -- Named Types -------------------------------------------------------------

  @doc "Register a named type (ADT, record, alias)."
  @spec extend_type(t(), String.t(), term()) :: t()
  def extend_type(%__MODULE__{types: types} = env, name, type) do
    %{env | types: Map.put(types, name, type)}
  end

  @doc "Look up a named type. Returns `{:ok, type}` or `:error`."
  @spec lookup_type(t(), String.t()) :: {:ok, term()} | :error
  def lookup_type(%__MODULE__{types: types}, name) do
    Map.fetch(types, name)
  end

  @doc """
  Recursively resolve `{:named, name}` references through the type
  namespace, returning the underlying canonical type when an alias is
  registered (e.g. a stdlib refinement type or ADT) and the input
  unchanged otherwise.

  Cycle-safe: an unresolved nominal name encountered for a second time
  is returned as-is rather than recursed into.

  Records are deliberately *not* unwrapped: callers that need record
  field schemas continue to look the record up by name through
  `lookup_type/2`. Anything else found in `env.types` (refinements,
  ADTs, primitive aliases, function types) is followed.
  """
  @spec deref(t(), term()) :: term()
  def deref(%__MODULE__{} = env, type), do: do_deref(env, type, MapSet.new())

  defp do_deref(env, {:named, name} = orig, seen) when is_binary(name) do
    if MapSet.member?(seen, name) do
      orig
    else
      case lookup_type(env, name) do
        {:ok, {:record, _, _}} -> orig
        {:ok, resolved} -> do_deref(env, resolved, MapSet.put(seen, name))
        :error -> orig
      end
    end
  end

  defp do_deref(_env, type, _seen), do: type
end
