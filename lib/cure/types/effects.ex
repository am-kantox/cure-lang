defmodule Cure.Types.Effects do
  @moduledoc """
  Effect system for the Cure programming language.

  Tracks side effects (IO, mutable state, exceptions, spawning, extern calls)
  through the type system. Pure functions can be aggressively optimized;
  effectful functions are clearly marked.

  ## Effect Kinds

  - `:io` -- I/O operations (print, file access)
  - `:state` -- mutable state (send, receive, process dictionary)
  - `:exception` -- exception throwing
  - `:spawn` -- process spawning
  - `:extern` -- unclassified extern calls (conservative default)

  ## Usage

      effects = Cure.Types.Effects.infer_effects(ast, env)
      # => MapSet<[:io, :exception]>
  """

  alias Cure.Types.{Type, Env}
  alias Cure.Pipeline.Events

  # Erlang modules classified by effect kind
  @io_modules [:io, :file, :io_lib]
  @state_modules [:gen_server, :gen_statem, :ets, :persistent_term, :erlang]
  @spawn_modules [:proc_lib]

  # Known stdlib module effects
  @stdlib_effects %{
    "Std.Io" => MapSet.new([:io]),
    "Std.System" => MapSet.new([:io, :state]),
    "Std.Fsm" => MapSet.new([:state])
  }

  # Function names known to be effectful
  @io_functions ["print", "println", "put_chars", "print_int", "print_float"]
  @state_functions ["send"]

  @doc """
  Infer the effects of a function body AST node.

  Walks the AST, collecting effects from:
  - Direct calls to functions with known effect types (env lookup)
  - `@extern` decorators (classified by target module)
  - Keywords: send -> :state, spawn -> :spawn, throw -> :exception, receive -> :state
  - Transitive: calling a function with effects E adds E to the caller

  Returns a `MapSet` of effect atoms.
  """
  @spec infer_effects(term(), Env.t()) :: MapSet.t()
  def infer_effects(ast, env) do
    do_infer(ast, env, MapSet.new())
  end

  @doc """
  Check declared effects against inferred effects.

  If the function has an explicit `!` annotation, verifies the inferred effects
  are a subset of the declared effects.

  Returns:
  - `:ok` if effects match
  - `{:warning, message}` if body is purer than declared (over-annotation)
  - `{:error, message}` if body has undeclared effects
  """
  @spec check_effects(list(), MapSet.t(), String.t()) :: :ok | {:warning, String.t()} | {:error, String.t()}
  def check_effects(declared_effects, inferred_effects, fn_name) do
    declared_set = MapSet.new(declared_effects)

    cond do
      MapSet.equal?(declared_set, inferred_effects) ->
        :ok

      MapSet.subset?(inferred_effects, declared_set) ->
        extra = MapSet.difference(declared_set, inferred_effects)
        effs = extra |> Enum.sort() |> Enum.map_join(", ", &Type.display_effect/1)
        {:warning, "function '#{fn_name}' declares effects #{effs} but does not use them"}

      true ->
        missing = MapSet.difference(inferred_effects, declared_set)
        effs = missing |> Enum.sort() |> Enum.map_join(", ", &Type.display_effect/1)
        {:error, "function '#{fn_name}' has undeclared effects: #{effs}"}
    end
  end

  @doc """
  Classify effects of an @extern declaration by its target module.
  """
  @spec classify_extern({atom(), atom(), integer()} | term()) :: MapSet.t()
  def classify_extern({module, _fun, _arity}) when is_atom(module) do
    cond do
      module in @io_modules -> MapSet.new([:io])
      module in @state_modules -> MapSet.new([:state])
      module in @spawn_modules -> MapSet.new([:spawn])
      true -> MapSet.new([:extern])
    end
  end

  def classify_extern(_), do: MapSet.new([:extern])

  @doc """
  Emit effect-related pipeline events.
  """
  @spec emit_effects(String.t(), MapSet.t(), String.t(), pos_integer()) :: :ok
  def emit_effects(fn_name, effects, file, line) do
    Events.emit(:type_checker, :effects_inferred, {fn_name, effects}, Events.meta(file, line))
  end

  # -- Effect Inference (AST Walk) ---------------------------------------------

  defp do_infer({:function_call, meta, args}, env, acc) do
    name = Keyword.get(meta, :name, "")

    # Infer effects from arguments first
    acc = Enum.reduce(args, acc, fn arg, a -> do_infer(arg, env, a) end)

    # Check if the called function has known effects
    call_effects = infer_call_effects(name, env)
    MapSet.union(acc, call_effects)
  end

  defp do_infer({:async_operation, _meta, children}, env, acc) do
    # receive -> :state
    acc = MapSet.put(acc, :state)
    Enum.reduce(children, acc, fn child, a -> do_infer(child, env, a) end)
  end

  defp do_infer({:throw, _meta, [expr]}, env, acc) do
    acc = MapSet.put(acc, :exception)
    do_infer(expr, env, acc)
  end

  defp do_infer({:early_return, _meta, [expr]}, env, acc) do
    do_infer(expr, env, acc)
  end

  defp do_infer({:binary_op, _meta, [left, right]}, env, acc) do
    acc = do_infer(left, env, acc)
    do_infer(right, env, acc)
  end

  defp do_infer({:unary_op, _meta, [operand]}, env, acc) do
    do_infer(operand, env, acc)
  end

  defp do_infer({:conditional, _meta, [cond_ast, then_ast, else_ast]}, env, acc) do
    acc = do_infer(cond_ast, env, acc)
    acc = do_infer(then_ast, env, acc)
    do_infer(else_ast, env, acc)
  end

  defp do_infer({:assignment, _meta, [_pattern, value]}, env, acc) do
    do_infer(value, env, acc)
  end

  defp do_infer({:block, _meta, children}, env, acc) do
    Enum.reduce(children, acc, fn child, a -> do_infer(child, env, a) end)
  end

  defp do_infer({:pattern_match, _meta, [scrutinee | arms]}, env, acc) do
    acc = do_infer(scrutinee, env, acc)
    Enum.reduce(arms, acc, fn arm, a -> do_infer(arm, env, a) end)
  end

  defp do_infer({:match_arm, _meta, [body]}, env, acc) do
    do_infer(body, env, acc)
  end

  defp do_infer({:lambda, _meta, [body]}, env, acc) do
    do_infer(body, env, acc)
  end

  defp do_infer({:exception_handling, _meta, children}, env, acc) do
    Enum.reduce(children, acc, fn child, a -> do_infer(child, env, a) end)
  end

  defp do_infer({:string_interpolation, _meta, parts}, env, acc) do
    Enum.reduce(parts, acc, fn part, a -> do_infer(part, env, a) end)
  end

  defp do_infer({:list, _meta, elements}, env, acc) do
    Enum.reduce(elements, acc, fn elem, a -> do_infer(elem, env, a) end)
  end

  defp do_infer({:tuple, _meta, elements}, env, acc) do
    Enum.reduce(elements, acc, fn elem, a -> do_infer(elem, env, a) end)
  end

  defp do_infer({:map, _meta, pairs}, env, acc) do
    Enum.reduce(pairs, acc, fn pair, a -> do_infer(pair, env, a) end)
  end

  defp do_infer({:pair, _meta, [key, value]}, env, acc) do
    acc = do_infer(key, env, acc)
    do_infer(value, env, acc)
  end

  # Leaf nodes: literals, variables -- no effects
  defp do_infer(_, _env, acc), do: acc

  # -- Call Effect Classification -----------------------------------------------

  defp infer_call_effects(name, env) do
    cond do
      # Known IO functions from stdlib
      name in @io_functions ->
        MapSet.new([:io])

      # send keyword-like function
      name in @state_functions ->
        MapSet.new([:state])

      # Check if we know the function's type from the environment
      true ->
        case Env.lookup(env, name) do
          {:ok, {:effun, _, _, effects}} -> effects
          {:ok, {:fun, _, _}} -> MapSet.new()
          {:ok, {:constrained_fun, _, _, _, _}} -> MapSet.new()
          _ -> check_stdlib_effects(name)
        end
    end
  end

  defp check_stdlib_effects(name) do
    # Check if the function name suggests it comes from a known stdlib module
    Enum.find_value(@stdlib_effects, MapSet.new(), fn {mod_prefix, effects} ->
      if String.starts_with?(name, mod_prefix <> ".") do
        effects
      end
    end)
  end
end
