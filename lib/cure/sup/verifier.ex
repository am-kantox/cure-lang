defmodule Cure.Sup.Verifier do
  @moduledoc """
  Verification pass for `sup` containers.

  Enforced invariants (see docs/SUPERVISION.md):

    * `strategy` is one of `:one_for_one`, `:one_for_all`,
      `:rest_for_one`, `:simple_one_for_one`.
    * `intensity` is a non-negative integer.
    * `period` is a positive integer.
    * Every child spec has a unique `id` within the supervisor.
    * Every child spec's `restart` value (if provided) is one of
      `:permanent`, `:transient`, `:temporary`.
    * Every child spec's `shutdown` value (if provided) is
      `:brutal_kill`, `:infinity`, or a positive integer.
    * The supervisor does not list itself as a child (trivial cycle).

  Emits errors via `Cure.Pipeline.Events` under the `:sup_verifier`
  stage so IDE/LSP consumers can react. The return value mirrors
  `Cure.FSM.Verifier`: `{:ok, ast}` when verification passes,
  `{:error, errors}` when it fails.
  """

  alias Cure.Pipeline.Events

  @valid_strategies [:one_for_one, :one_for_all, :rest_for_one, :simple_one_for_one]
  @valid_restarts [:permanent, :transient, :temporary]

  @type error ::
          {:invalid_strategy, term(), keyword()}
          | {:invalid_intensity, term(), keyword()}
          | {:invalid_period, term(), keyword()}
          | {:duplicate_child_id, String.t(), keyword()}
          | {:invalid_restart, term(), keyword()}
          | {:invalid_shutdown, term(), keyword()}
          | {:supervisor_self_reference, String.t(), keyword()}

  @spec verify(tuple(), keyword()) :: {:ok, tuple()} | {:error, [error()]}
  def verify({:container, meta, children} = ast, opts \\ []) do
    emit? = Keyword.get(opts, :emit_events, true)
    file = Keyword.get(opts, :file, "nofile")
    line = Keyword.get(meta, :line, 1)

    errors =
      []
      |> check_strategy(meta)
      |> check_intensity(meta)
      |> check_period(meta)
      |> check_child_specs(meta, children)

    case errors do
      [] ->
        if emit? do
          Events.emit(:sup_verifier, :verified, ast, Events.meta(file, line))
        end

        {:ok, ast}

      errs ->
        errs = Enum.reverse(errs)

        if emit? do
          Events.emit(:sup_verifier, :error, errs, Events.meta(file, line))
        end

        {:error, errs}
    end
  end

  # -- Container-level checks -------------------------------------------------

  defp check_strategy(errors, meta) do
    case Keyword.get(meta, :strategy) do
      nil ->
        errors

      ast ->
        case literal_atom(ast) do
          {:ok, atom} when atom in @valid_strategies ->
            errors

          {:ok, other} ->
            [{:invalid_strategy, other, meta_for(ast, meta)} | errors]

          :error ->
            [{:invalid_strategy, ast, meta_for(ast, meta)} | errors]
        end
    end
  end

  defp check_intensity(errors, meta) do
    case Keyword.get(meta, :intensity) do
      nil ->
        errors

      ast ->
        case literal_integer(ast) do
          {:ok, n} when is_integer(n) and n >= 0 ->
            errors

          _ ->
            [{:invalid_intensity, ast, meta_for(ast, meta)} | errors]
        end
    end
  end

  defp check_period(errors, meta) do
    case Keyword.get(meta, :period) do
      nil ->
        errors

      ast ->
        case literal_integer(ast) do
          {:ok, n} when is_integer(n) and n > 0 ->
            errors

          _ ->
            [{:invalid_period, ast, meta_for(ast, meta)} | errors]
        end
    end
  end

  # -- Child-spec checks ------------------------------------------------------

  defp check_child_specs(errors, container_meta, children) do
    own_name = Keyword.get(container_meta, :name)

    {errors, _ids} =
      Enum.reduce(children, {errors, MapSet.new()}, fn spec, {errs, ids} ->
        case spec do
          {:child_spec, spec_meta, _} ->
            id = Keyword.get(spec_meta, :id)
            module_path = Keyword.get(spec_meta, :module)

            errs =
              errs
              |> check_child_self_ref(own_name, module_path, spec_meta)
              |> check_child_restart(spec_meta)
              |> check_child_shutdown(spec_meta)

            if id != nil and MapSet.member?(ids, id) do
              {[{:duplicate_child_id, id, spec_meta} | errs], ids}
            else
              {errs, MapSet.put(ids, id)}
            end

          _ ->
            {errs, ids}
        end
      end)

    errors
  end

  defp check_child_self_ref(errors, nil, _module, _meta), do: errors
  defp check_child_self_ref(errors, _own_name, nil, _meta), do: errors

  defp check_child_self_ref(errors, own_name, module_path, meta) do
    if module_path == own_name do
      [{:supervisor_self_reference, own_name, meta} | errors]
    else
      errors
    end
  end

  defp check_child_restart(errors, meta) do
    case Keyword.get(meta, :restart) do
      nil ->
        errors

      ast ->
        case literal_atom(ast) do
          {:ok, atom} when atom in @valid_restarts ->
            errors

          {:ok, other} ->
            [{:invalid_restart, other, meta} | errors]

          :error ->
            [{:invalid_restart, ast, meta} | errors]
        end
    end
  end

  defp check_child_shutdown(errors, meta) do
    case Keyword.get(meta, :shutdown) do
      nil ->
        errors

      ast ->
        case literal_shutdown(ast) do
          {:ok, :brutal_kill} ->
            errors

          {:ok, :infinity} ->
            errors

          {:ok, n} when is_integer(n) and n > 0 ->
            errors

          _ ->
            [{:invalid_shutdown, ast, meta} | errors]
        end
    end
  end

  # -- Small AST helpers ------------------------------------------------------

  @doc false
  def literal_atom({:literal, _, atom}) when is_atom(atom), do: {:ok, atom}
  def literal_atom({:variable, _, name}) when is_binary(name), do: {:ok, String.to_atom(name)}
  def literal_atom(_), do: :error

  @doc false
  def literal_integer({:literal, _, n}) when is_integer(n), do: {:ok, n}

  def literal_integer({:unary_op, meta, [{:literal, _, n}]}) when is_integer(n) do
    case Keyword.get(meta, :op) do
      :minus -> {:ok, -n}
      _ -> {:ok, n}
    end
  end

  def literal_integer(_), do: :error

  @doc false
  def literal_shutdown(ast) do
    case literal_atom(ast) do
      {:ok, atom} when atom in [:brutal_kill, :infinity] -> {:ok, atom}
      _ -> literal_integer(ast)
    end
  end

  defp meta_for({_, m, _}, _outer) when is_list(m), do: m
  defp meta_for(_, outer), do: outer
end
