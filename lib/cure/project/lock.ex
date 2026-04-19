defmodule Cure.Project.Lock do
  @moduledoc """
  Cure.lock file reader and writer (v0.23.0).

  Shipped alongside the remote registry, the lockfile captures the
  concrete `{name, version, sha256}` triples that were resolved on
  the last successful run of `cure deps`. Subsequent invocations of
  `cure deps` reuse the lockfile whenever every top-level constraint
  still accepts the locked version, skipping the backtracking resolver
  and the network round trip entirely.

  ## Format

  One TOML table per locked package. Example:

      [lock.http]
      version = "1.2.3"
      hash = "sha256:1a2b3c..."
      dependencies = ["json ~> 2.0", "uri >= 0.1.0"]

      [lock.json]
      version = "2.1.0"
      hash = "sha256:deadbeef..."
      dependencies = []

  Path / git dependencies have no `hash` or `dependencies` rows because
  their content is not content-addressable; they persist only a
  `version = "<commit-or-path>"` row for the tree renderer.

  The TOML parser used here is intentionally a minimal hand-rolled
  subset: the lockfile is the only TOML we write, and we want zero
  dependencies beyond OTP.
  """

  alias Cure.Project.Version

  @filename "Cure.lock"

  @type lock_entry :: %{
          name: String.t(),
          version: String.t(),
          hash: String.t() | nil,
          dependencies: [{String.t(), String.t()}]
        }
  @type t :: %{String.t() => lock_entry()}

  # -- Public API -------------------------------------------------------------

  @doc """
  Return the path to the lockfile inside `root`.
  """
  @spec path(String.t()) :: String.t()
  def path(root \\ "."), do: Path.join(root, @filename)

  @doc """
  Read the lockfile inside `root`. Returns `{:ok, lock_map}` or
  `{:error, :no_lock}` when the file does not exist.
  """
  @spec read(String.t()) :: {:ok, t()} | {:error, :no_lock | {:parse, term()}}
  def read(root \\ ".") do
    case File.read(path(root)) do
      {:ok, content} ->
        {:ok, parse(content)}

      {:error, :enoent} ->
        {:error, :no_lock}

      {:error, reason} ->
        {:error, {:parse, reason}}
    end
  end

  @doc """
  Write `lock` to disk at `root`.

  Entries are sorted alphabetically for a stable diff.
  """
  @spec write(String.t(), t()) :: :ok
  def write(root, lock) when is_binary(root) and is_map(lock) do
    body =
      lock
      |> Map.to_list()
      |> Enum.sort_by(fn {n, _} -> n end)
      |> Enum.map_join("\n\n", fn {name, entry} -> render_entry(name, entry) end)

    File.write!(path(root), body <> "\n")
  end

  @doc """
  Given the top-level constraint map, the current lockfile, and the
  registry data, return `{:ok, resolution}` when every constraint is
  already satisfied by the lockfile, or `:stale` when the lockfile is
  missing an entry or a locked version no longer fits a constraint.
  """
  @spec resolve_with_lock(%{String.t() => String.t()}, t()) :: {:ok, map()} | :stale
  def resolve_with_lock(top_constraints, lock) when is_map(top_constraints) and is_map(lock) do
    Enum.reduce_while(top_constraints, {:ok, %{}}, fn {name, cstr}, {:ok, acc} ->
      with %{version: v_string} <- Map.get(lock, name, :missing),
           {:ok, parsed} <- Version.parse(v_string),
           {:ok, constraint} <- Version.parse_constraint(cstr),
           true <- Version.satisfies?(parsed, constraint) do
        {:cont, {:ok, Map.put(acc, name, parsed)}}
      else
        _ -> {:halt, :stale}
      end
    end)
  end

  @doc """
  Convert the resolver's output (map of `name -> version_tuple`) plus
  a registry snapshot into a lockfile structure ready for `write/2`.
  """
  @spec build(map(), map()) :: t()
  def build(resolution, registry_snapshot) when is_map(resolution) and is_map(registry_snapshot) do
    resolution
    |> Enum.map(fn {name, version} ->
      meta = find_meta(registry_snapshot, name, version) || %{}

      {
        name,
        %{
          name: name,
          version: Version.to_string(version),
          hash: Map.get(meta, :hash, nil),
          dependencies: Map.get(meta, :deps, [])
        }
      }
    end)
    |> Map.new()
  end

  # -- Internals: rendering ---------------------------------------------------

  defp render_entry(name, %{version: v} = entry) do
    hash_row =
      case Map.get(entry, :hash) do
        nil -> ""
        "" -> ""
        h -> "\nhash = \"#{h}\""
      end

    deps_row =
      case Map.get(entry, :dependencies, []) do
        [] ->
          "\ndependencies = []"

        deps ->
          rendered =
            deps
            |> Enum.map(fn
              {n, c} -> ~s("#{n} #{c}")
              other -> ~s("#{other}")
            end)
            |> Enum.join(", ")

          "\ndependencies = [#{rendered}]"
      end

    "[lock.#{name}]\nversion = \"#{v}\"#{hash_row}#{deps_row}"
  end

  # -- Internals: parsing -----------------------------------------------------

  defp parse(content) do
    lines = String.split(content, "\n")
    do_parse(lines, nil, %{}, %{})
  end

  defp do_parse([], _section, current, acc) do
    commit_section(current, acc)
  end

  defp do_parse([line | rest], section, current, acc) do
    trimmed = String.trim(line)

    cond do
      trimmed == "" or String.starts_with?(trimmed, "#") ->
        do_parse(rest, section, current, acc)

      section_name = section_header(trimmed) ->
        acc2 = commit_section(current, acc)
        do_parse(rest, section_name, %{name: section_name}, acc2)

      section != nil ->
        {key, value} = parse_kv(trimmed)
        do_parse(rest, section, Map.put(current, String.to_atom(key), parse_value(value)), acc)

      true ->
        do_parse(rest, section, current, acc)
    end
  end

  defp section_header(line) do
    case Regex.run(~r/^\[lock\.([^\]]+)\]$/, line) do
      [_, name] -> name
      _ -> nil
    end
  end

  defp parse_kv(line) do
    [k, v] = String.split(line, "=", parts: 2) |> Enum.map(&String.trim/1)
    {k, v}
  end

  defp parse_value("[]"), do: []

  defp parse_value(<<"[", _::binary>> = list_text) do
    list_text
    |> String.trim_leading("[")
    |> String.trim_trailing("]")
    |> String.split(",")
    |> Enum.map(&String.trim/1)
    |> Enum.map(fn s -> String.trim(s, "\"") end)
    |> Enum.reject(&(&1 == ""))
    |> Enum.map(fn s ->
      case String.split(s, " ", parts: 2) do
        [name, constraint] -> {name, constraint}
        [single] -> single
      end
    end)
  end

  defp parse_value(s), do: String.trim(s, "\"")

  defp commit_section(current, acc) do
    case current do
      %{name: name} ->
        entry = %{
          name: name,
          version: Map.get(current, :version, "0.0.0"),
          hash: Map.get(current, :hash, nil),
          dependencies: Map.get(current, :dependencies, [])
        }

        Map.put(acc, name, entry)

      _ ->
        acc
    end
  end

  defp find_meta(registry_snapshot, name, version) do
    registry_snapshot
    |> Map.get(name, [])
    |> Enum.find(fn %{version: v} -> v == version end)
  end
end
