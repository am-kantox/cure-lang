defmodule Cure.Types.Unify do
  @moduledoc """
  First-order unification for the Cure type system.

  Used to solve **implicit arguments** at call sites of dependent
  functions:

      fn id({T}, x: T) -> T = x
      id(42)          # T solved to Int
      id("hello")     # T solved to String

  And to elaborate dependent return types whose value parameters are
  inferred from the explicit-argument types:

      fn append({T}, {m: Nat}, {n: Nat},
                xs: Vector(T, m), ys: Vector(T, n)) -> Vector(T, m + n)
      append(va, vb)  # m, n, T solved from va, vb

  ## Algorithm

  Standard syntactic unification with an occurs check:

  1. A *flex* type variable matches anything; we record the binding.
  2. Two atoms unify only if equal.
  3. Composites unify pairwise after the head matches.
  4. The occurs check rejects `t = f(t)` cycles.

  ## Trace

  Every step records a tuple `{lhs, rhs, action}` in the trace, which
  is published as the `:unification_trace` pipeline event when
  unification fails. The LSP renders the trace in hover; the CLI
  prints it.

  ## Output

  - `unify/2` returns `{:ok, %{var => type}, trace}` or
    `{:error, reason, trace}`.
  - `apply_subst/2` substitutes solved variables through a type.
  """

  alias Cure.Pipeline.Events

  @type subst :: %{optional(String.t()) => term()}
  @type trace_step :: {term(), term(), atom()}
  @type result :: {:ok, subst(), [trace_step()]} | {:error, String.t(), [trace_step()]}

  # -- Public API --------------------------------------------------------------

  @doc """
  Unify two types. Variable types `{:type_var, name}` are flex.
  """
  @spec unify(term(), term()) :: result()
  def unify(t1, t2) do
    do_unify(t1, t2, %{}, [])
  end

  @doc """
  Unify two types under a starting substitution.
  """
  @spec unify(term(), term(), subst()) :: result()
  def unify(t1, t2, subst) do
    do_unify(t1, t2, subst, [])
  end

  @doc """
  Unify a list of `{lhs, rhs}` constraints in order.
  """
  @spec unify_many([{term(), term()}]) :: result()
  def unify_many(constraints) do
    Enum.reduce_while(constraints, {:ok, %{}, []}, fn {l, r}, {:ok, subst, trace} ->
      case do_unify(l, r, subst, trace) do
        {:ok, _s, _t} = ok -> {:cont, ok}
        {:error, _, _} = err -> {:halt, err}
      end
    end)
  end

  @doc """
  Substitute every solved variable through a type.
  """
  @spec apply_subst(term(), subst()) :: term()
  def apply_subst(type, subst), do: do_apply(type, subst)

  @doc """
  Emit a `:unification_trace` pipeline event.
  """
  @spec emit_trace(String.t(), [trace_step()], String.t(), pos_integer()) :: :ok
  def emit_trace(reason, trace, file, line) do
    Events.emit(:type_checker, :unification_trace, {reason, trace}, Events.meta(file, line))
  end

  # -- Core unification --------------------------------------------------------

  defp do_unify(t, t, subst, trace), do: {:ok, subst, [{t, t, :reflex} | trace]}

  # Refinements are transparent to unification: the predicate narrows a
  # base type with no structural contribution, so unifying through
  # `{:refinement, base, ...}` on either side is just unifying `base`.
  # Strip them eagerly -- before the `{:type_var, _}` clauses -- so a
  # type variable binds to the cleaner base type rather than carrying
  # an inapplicable predicate into downstream substitution.
  defp do_unify({:refinement, base, _, _}, t, subst, trace) do
    do_unify(base, t, subst, [{:refinement, :lhs, :strip} | trace])
  end

  defp do_unify(t, {:refinement, base, _, _}, subst, trace) do
    do_unify(t, base, subst, [{:refinement, :rhs, :strip} | trace])
  end

  defp do_unify({:type_var, name}, t, subst, trace) when is_binary(name) do
    bind(name, t, subst, [{:type_var_l, name, t} | trace])
  end

  defp do_unify(t, {:type_var, name}, subst, trace) when is_binary(name) do
    bind(name, t, subst, [{:type_var_r, name, t} | trace])
  end

  defp do_unify(:any, _, subst, trace), do: {:ok, subst, [{:any, :match, :widened} | trace]}
  defp do_unify(_, :any, subst, trace), do: {:ok, subst, [{:any, :match, :widened} | trace]}

  defp do_unify({:list, a}, {:list, b}, subst, trace) do
    do_unify(a, b, subst, [{:list, :enter, :recurse} | trace])
  end

  defp do_unify({:tuple, as}, {:tuple, bs}, subst, trace) when length(as) == length(bs) do
    Enum.zip(as, bs)
    |> Enum.reduce_while({:ok, subst, [{:tuple, :enter, :recurse} | trace]}, fn {a, b}, {:ok, s, tr} ->
      case do_unify(a, b, s, tr) do
        {:ok, _, _} = ok -> {:cont, ok}
        {:error, _, _} = err -> {:halt, err}
      end
    end)
  end

  defp do_unify({:fun, ps1, r1}, {:fun, ps2, r2}, subst, trace) when length(ps1) == length(ps2) do
    constraints = Enum.zip(ps1, ps2) ++ [{r1, r2}]

    Enum.reduce_while(constraints, {:ok, subst, [{:fun, :enter, :recurse} | trace]}, fn {a, b}, {:ok, s, tr} ->
      case do_unify(a, b, s, tr) do
        {:ok, _, _} = ok -> {:cont, ok}
        {:error, _, _} = err -> {:halt, err}
      end
    end)
  end

  defp do_unify({:adt, name, ps1}, {:adt, name, ps2}, subst, trace) when length(ps1) == length(ps2) do
    Enum.zip(ps1, ps2)
    |> Enum.reduce_while({:ok, subst, [{:adt, name, :recurse} | trace]}, fn {a, b}, {:ok, s, tr} ->
      case do_unify(a, b, s, tr) do
        {:ok, _, _} = ok -> {:cont, ok}
        {:error, _, _} = err -> {:halt, err}
      end
    end)
  end

  defp do_unify({:map, k1, v1}, {:map, k2, v2}, subst, trace) do
    with {:ok, subst, trace} <- do_unify(k1, k2, subst, [{:map, :key, :recurse} | trace]) do
      do_unify(v1, v2, subst, [{:map, :value, :recurse} | trace])
    end
  end

  # A nominal record/ADT reference and a resolved record/ADT line up when
  # their lowercased names match; the parameter lists carry no unifiable
  # information at the named level.
  defp do_unify({:named, a}, {:named, b}, subst, trace) do
    if a == b do
      {:ok, subst, [{:named, a, :match} | trace]}
    else
      {:error, "cannot unify named type #{a} with #{b}", trace}
    end
  end

  defp do_unify({:named, a}, {:record, key, _fields} = rec, subst, trace) do
    if String.downcase(a) == Atom.to_string(key) do
      {:ok, subst, [{:named, a, :record_match} | trace]}
    else
      {:error, "cannot unify #{a} with #{display(rec)}", trace}
    end
  end

  defp do_unify({:record, _, _} = rec, {:named, _} = named, subst, trace) do
    do_unify(named, rec, subst, trace)
  end

  defp do_unify({:named, a}, {:adt, key, _} = adt, subst, trace) do
    if String.downcase(a) == Atom.to_string(key) do
      {:ok, subst, [{:named, a, :adt_match} | trace]}
    else
      {:error, "cannot unify #{a} with #{display(adt)}", trace}
    end
  end

  defp do_unify({:adt, _, _} = adt, {:named, _} = named, subst, trace) do
    do_unify(named, adt, subst, trace)
  end

  defp do_unify(:int, :float, subst, trace),
    do: {:ok, subst, [{:int, :float, :widening} | trace]}

  defp do_unify(t1, t2, _subst, trace) do
    {:error, "cannot unify #{display(t1)} with #{display(t2)}", trace}
  end

  defp bind(name, type, subst, trace) do
    case Map.get(subst, name) do
      nil ->
        if occurs?(name, type, subst) do
          {:error, "occurs check failed for ?#{name}", trace}
        else
          {:ok, Map.put(subst, name, type), trace}
        end

      existing ->
        # Already bound -- unify with existing binding
        do_unify(existing, type, subst, trace)
    end
  end

  defp occurs?(name, {:type_var, n}, _subst) when n == name, do: true

  defp occurs?(name, {:type_var, n}, subst) do
    case Map.get(subst, n) do
      nil -> false
      t -> occurs?(name, t, subst)
    end
  end

  defp occurs?(name, {:list, a}, subst), do: occurs?(name, a, subst)
  defp occurs?(name, {:tuple, ts}, subst), do: Enum.any?(ts, &occurs?(name, &1, subst))

  defp occurs?(name, {:fun, ps, r}, subst),
    do: Enum.any?(ps, &occurs?(name, &1, subst)) or occurs?(name, r, subst)

  defp occurs?(name, {:adt, _n, ps}, subst), do: Enum.any?(ps, &occurs?(name, &1, subst))
  defp occurs?(name, {:map, k, v}, subst), do: occurs?(name, k, subst) or occurs?(name, v, subst)
  defp occurs?(name, {:refinement, base, _, _}, subst), do: occurs?(name, base, subst)
  defp occurs?(_name, _type, _subst), do: false

  # -- Substitution ------------------------------------------------------------

  defp do_apply({:type_var, name} = tv, subst) do
    case Map.get(subst, name) do
      nil -> tv
      t -> do_apply(t, subst)
    end
  end

  defp do_apply({:list, a}, s), do: {:list, do_apply(a, s)}
  defp do_apply({:tuple, ts}, s), do: {:tuple, Enum.map(ts, &do_apply(&1, s))}

  defp do_apply({:fun, ps, r}, s),
    do: {:fun, Enum.map(ps, &do_apply(&1, s)), do_apply(r, s)}

  defp do_apply({:effun, ps, r, effs}, s),
    do: {:effun, Enum.map(ps, &do_apply(&1, s)), do_apply(r, s), effs}

  defp do_apply({:adt, n, ps}, s), do: {:adt, n, Enum.map(ps, &do_apply(&1, s))}
  defp do_apply({:map, k, v}, s), do: {:map, do_apply(k, s), do_apply(v, s)}

  defp do_apply({:refinement, base, var, pred}, s),
    do: {:refinement, do_apply(base, s), var, pred}

  defp do_apply(other, _s), do: other

  # -- Display -----------------------------------------------------------------

  defp display(t) do
    case Cure.Types.Type.display(t) do
      result when is_binary(result) -> result
      _ -> inspect(t)
    end
  rescue
    _ -> inspect(t)
  end
end
