defmodule Cure.App.Verifier do
  @moduledoc """
  Verification pass for `app` containers.

  Enforced invariants:

    * Container name is a non-empty dotted path.
    * `applications` (if present) is a list literal whose elements are
      atom literals.
    * `included_applications` (if present) follows the same rule.
    * `env` (if present) is a map literal whose keys are atom literals.
    * `root` (if present) is either a bare PascalCase identifier, a
      dotted path, or a `sup Name` soft-keyword form. Anything else is
      an `E054 Unresolved Root Supervisor`.
    * When `:declared_phases` is passed via `opts`, every phase atom
      must have a matching `on_phase :name` clause and every declared
      `on_phase` must appear in the list (bidirectional). Mismatches
      surface as `E053 Start Phase Mismatch`.

  Emits errors via `Cure.Pipeline.Events` under the `:app_verifier`
  stage so IDE/LSP consumers can react. The return value mirrors
  `Cure.Sup.Verifier`: `{:ok, ast}` when verification passes,
  `{:error, errors}` when it fails.
  """

  alias Cure.Pipeline.Events

  @type error ::
          {:invalid_root, term(), keyword()}
          | {:invalid_applications, term(), keyword()}
          | {:invalid_included_applications, term(), keyword()}
          | {:invalid_env, term(), keyword()}
          | {:start_phase_missing, atom(), keyword()}
          | {:start_phase_unexpected, atom(), keyword()}
          | {:invalid_app_name, term(), keyword()}

  @spec verify(tuple(), keyword()) :: {:ok, tuple()} | {:error, [error()]}
  def verify({:container, meta, _body} = ast, opts \\ []) do
    emit? = Keyword.get(opts, :emit_events, true)
    file = Keyword.get(opts, :file, "nofile")
    line = Keyword.get(meta, :line, 1)
    declared_phases = Keyword.get(opts, :declared_phases, nil)

    errors =
      []
      |> check_name(meta)
      |> check_root(meta)
      |> check_applications(meta, :applications)
      |> check_applications(meta, :included_applications)
      |> check_env(meta)
      |> check_phases(meta, declared_phases)

    case errors do
      [] ->
        if emit? do
          Events.emit(:app_verifier, :verified, ast, Events.meta(file, line))
        end

        {:ok, ast}

      errs ->
        errs = Enum.reverse(errs)

        if emit? do
          Events.emit(:app_verifier, :error, errs, Events.meta(file, line))
        end

        {:error, errs}
    end
  end

  # -- Container-level checks ------------------------------------------------

  defp check_name(errors, meta) do
    case Keyword.get(meta, :name) do
      name when is_binary(name) and name != "" ->
        errors

      other ->
        [{:invalid_app_name, other, meta} | errors]
    end
  end

  defp check_root(errors, meta) do
    case Keyword.get(meta, :root) do
      nil ->
        errors

      ast ->
        case classify_root(ast) do
          :ok -> errors
          :error -> [{:invalid_root, ast, meta_for(ast, meta)} | errors]
        end
    end
  end

  @doc false
  def classify_root({:variable, _, name}) when is_binary(name) and name != "", do: :ok
  def classify_root({:function_call, _, _}), do: :ok
  def classify_root({:attribute_access, _, _}), do: :ok

  # `root = sup Name` parses as a call to a local variable `sup` followed
  # by an identifier, but under the Cure pratt parser `sup Name` inside
  # an expression becomes the supervisor container AST. Accept it too.
  def classify_root({:container, m, _}) do
    case Keyword.get(m, :container_type) do
      :supervisor -> :ok
      _ -> :error
    end
  end

  def classify_root({:literal, m, _}) do
    case Keyword.get(m, :subtype) do
      :symbol -> :ok
      _ -> :error
    end
  end

  def classify_root(_), do: :error

  defp check_applications(errors, meta, key) do
    case Keyword.get(meta, key) do
      nil ->
        errors

      {:list, _, items} when is_list(items) ->
        if Enum.all?(items, &literal_atom?/1) do
          errors
        else
          invalid_key_error(key, errors, Keyword.get(meta, key), meta)
        end

      other ->
        invalid_key_error(key, errors, other, meta)
    end
  end

  defp invalid_key_error(:applications, errors, value, meta),
    do: [{:invalid_applications, value, meta} | errors]

  defp invalid_key_error(:included_applications, errors, value, meta),
    do: [{:invalid_included_applications, value, meta} | errors]

  defp check_env(errors, meta) do
    case Keyword.get(meta, :env) do
      nil ->
        errors

      {:map, _, pairs} when is_list(pairs) ->
        if Enum.all?(pairs, &env_pair_atom_keyed?/1) do
          errors
        else
          [{:invalid_env, Keyword.get(meta, :env), meta} | errors]
        end

      other ->
        [{:invalid_env, other, meta} | errors]
    end
  end

  defp env_pair_atom_keyed?({:pair, _, [key, _]}), do: literal_atom?(key)
  defp env_pair_atom_keyed?(_), do: false

  defp check_phases(errors, _meta, nil), do: errors

  defp check_phases(errors, meta, declared_phases) when is_list(declared_phases) do
    # The parser emits one `on_phase: [{phase, clauses}]` entry per
    # `on_phase :name` block, so a container with three blocks puts
    # three separate `:on_phase` keys into the keyword list. Gather
    # them all with `Keyword.get_values/2`.
    on_phase_entries =
      meta
      |> Keyword.get_values(:on_phase)
      |> List.flatten()

    implemented = for {phase, _clauses} <- on_phase_entries, do: phase
    declared = Enum.map(declared_phases, &to_atom_safe/1)

    missing = declared -- implemented
    extra = implemented -- declared

    errors =
      Enum.reduce(missing, errors, fn phase, acc ->
        [{:start_phase_missing, phase, meta} | acc]
      end)

    Enum.reduce(extra, errors, fn phase, acc ->
      [{:start_phase_unexpected, phase, meta} | acc]
    end)
  end

  # -- Literal helpers -------------------------------------------------------

  @doc false
  def literal_atom?({:literal, m, _}) do
    Keyword.get(m, :subtype) == :symbol
  end

  def literal_atom?(_), do: false

  @doc false
  def literal_atom_value({:literal, _, value}) when is_atom(value), do: value
  def literal_atom_value({:literal, _, value}) when is_binary(value), do: String.to_atom(value)
  def literal_atom_value(_), do: nil

  defp to_atom_safe(a) when is_atom(a), do: a
  defp to_atom_safe(b) when is_binary(b), do: String.to_atom(b)
  defp to_atom_safe(_), do: :__invalid__

  defp meta_for({_, m, _}, _outer) when is_list(m), do: m
  defp meta_for(_, outer), do: outer
end
