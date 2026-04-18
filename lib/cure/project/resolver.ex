defmodule Cure.Project.Resolver do
  @moduledoc """
  Deterministic dependency resolver (v0.19.0).

  This is the first half of the registry work outlined in
  `docs/PACKAGE_REGISTRY.md`: a plain backtracking resolver over a
  local/git workspace. The fancy Pubgrub-based variant with conflict
  narrowing is scheduled for v0.20.0 alongside the index service.

  The resolver is pure: given a "registry" shaped like

      %{
        "http" => [
          %{version: {1, 0, 0, nil}, deps: [{"json", \"~> 2.0\"}]},
          %{version: {2, 0, 0, nil}, deps: []}
        ],
        "json" => [%{version: {2, 0, 0, nil}, deps: []}]
      }

  and top-level constraints `%{\"http\" => [...parsed constraint...]}`,
  `resolve/2` returns `{:ok, %{\"http\" => version, ...}}` or
  `{:error, {:version_conflict, name, constraints}}`.
  """

  alias Cure.Project.Version

  @type pkg_name :: String.t()
  @type registry_entry :: %{version: Version.version(), deps: [{pkg_name(), String.t()}]}
  @type registry :: %{pkg_name() => [registry_entry()]}
  @type resolution :: %{pkg_name() => Version.version()}

  @doc """
  Resolve top-level constraints against a registry.

  Returns `{:ok, resolution}` on success, or
  `{:error, {:version_conflict, pkg, constraints}}` when no single set
  of versions satisfies every active constraint.

  The algorithm is deterministic backtracking: at each step we pick the
  package with the fewest satisfying candidates and prefer the *newest*
  compatible version.
  """
  @spec resolve(%{pkg_name() => String.t()}, registry()) ::
          {:ok, resolution()} | {:error, {atom(), pkg_name(), any()}}
  def resolve(top_constraints, registry) do
    parsed =
      Enum.reduce_while(top_constraints, {:ok, %{}}, fn {name, cstr}, {:ok, acc} ->
        case Version.parse_constraint(cstr) do
          {:ok, parsed} -> {:cont, {:ok, Map.put(acc, name, parsed)}}
          {:error, reason} -> {:halt, {:error, {:invalid_constraint, name, reason}}}
        end
      end)

    with {:ok, active} <- parsed do
      solve(active, %{}, registry)
    end
  end

  # -- Core DFS solver --------------------------------------------------------

  defp solve(active, resolved, _registry) when map_size(active) == 0 do
    {:ok, resolved}
  end

  defp solve(active, resolved, registry) do
    {name, constraints, rest_active} = pick_next(active)

    candidates =
      registry
      |> Map.get(name, [])
      |> Enum.filter(fn %{version: v} -> Version.satisfies?(v, constraints) end)
      |> Enum.sort(fn a, b -> Version.compare(a.version, b.version) != :lt end)

    try_candidates(name, candidates, constraints, rest_active, resolved, registry)
  end

  defp try_candidates(name, [], constraints, _rest_active, _resolved, _registry) do
    {:error, {:version_conflict, name, constraints}}
  end

  defp try_candidates(name, [cand | rest], constraints, active, resolved, registry) do
    resolved_next = Map.put(resolved, name, cand.version)

    # Fold this candidate's deps into the active constraint map.
    case extend_active(active, cand.deps, resolved_next, registry) do
      {:ok, next_active} ->
        case solve(next_active, resolved_next, registry) do
          {:ok, _} = ok -> ok
          _ -> try_candidates(name, rest, constraints, active, resolved, registry)
        end

      :conflict ->
        try_candidates(name, rest, constraints, active, resolved, registry)
    end
  end

  defp extend_active(active, deps, resolved, registry) do
    Enum.reduce_while(deps, {:ok, active}, fn {dep_name, cstr}, {:ok, acc} ->
      case Version.parse_constraint(cstr) do
        {:ok, parsed} ->
          # If the dependency is already resolved, it must still satisfy
          # the new constraint; otherwise we conflict.
          case Map.get(resolved, dep_name) do
            nil ->
              merged = Map.update(acc, dep_name, parsed, fn existing -> existing ++ parsed end)
              {:cont, {:ok, merged}}

            version ->
              if Version.satisfies?(version, parsed) do
                {:cont, {:ok, acc}}
              else
                _ = registry
                {:halt, :conflict}
              end
          end

        _ ->
          {:halt, :conflict}
      end
    end)
  end

  # Pick the package with the fewest active-constraint entries first --
  # a rough heuristic that keeps the search tree shallow.
  defp pick_next(active) do
    {name, constraints} =
      Enum.min_by(active, fn {_n, c} -> length(c) end)

    {name, constraints, Map.delete(active, name)}
  end
end
