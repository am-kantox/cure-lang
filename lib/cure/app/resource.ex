defmodule Cure.App.Resource do
  @moduledoc """
  Emits OTP `.app` resource files.

  Given a project's `app` container (the `%{name, meta, ...}` shape
  returned by `Cure.Project.detect_app/2`), the compiled module list,
  and the project metadata, this module produces a classic
  `{application, Name, [Keys]}` tuple and writes it to
  `<output_dir>/<name>.app` in the canonical Erlang format.

  ## Keys written

    * `:description`  -- `[application].description` or `""`.
    * `:vsn`          -- `[application].vsn`, `vsn = ` from the
      container, or `[project].version` (in that order).
    * `:modules`      -- every non-erlang atom in the compiled module
      list.
    * `:registered`   -- `[application].registered` (empty by default).
    * `:applications` -- union of `[application].applications` and any
      atoms listed under `applications = [...]` in the container.
      Always includes `:kernel` and `:stdlib` as the OTP convention
      requires.
    * `:included_applications` -- `[application].included_applications`.
    * `:env`          -- merge of `[application.env]` and the
      container's `env = %{...}` literal. TOML values win on conflict.
    * `:mod`          -- `{:"Cure.App.<Name>", []}`.
    * `:start_phases` -- when `[application].start_phases` is set, emit
      `[{phase, []}, ...]` in declared order.

  The file is written using `:io.format(fh, ~c\"~p.~n\", [term])` so the
  output is re-readable by `:file.consult/1`, `:application.load/1`,
  and all standard OTP release tooling.
  """

  @spec write(map() | nil, [module()], Cure.Project.t(), keyword()) :: :ok | {:error, term()}
  def write(nil, _modules, _project, _opts), do: :ok

  def write(%{name: name, meta: meta}, modules, project, opts) when is_binary(name) do
    output_dir = Keyword.fetch!(opts, :output_dir)
    File.mkdir_p!(output_dir)

    app_atom = app_resource_atom(project, name)
    props = build_props(name, meta, modules, project)

    path = Path.join(output_dir, "#{app_atom}.app")
    contents = :io_lib.format(~c"~p.~n", [{:application, app_atom, props}])

    case File.write(path, IO.iodata_to_binary(contents)) do
      :ok -> :ok
      {:error, reason} -> {:error, {:app_resource_write_failed, path, reason}}
    end
  end

  def write(_app_info, _modules, _project, _opts), do: :ok

  @doc false
  def build_props(container_name, meta, modules, project) do
    app = project.application || %{}

    description = Map.get(app, :description, "") |> to_string()
    vsn = pick_vsn(app, meta, project)
    mod_atom = String.to_atom("Cure.App." <> container_name)

    extra_apps = normalize_atoms(Map.get(app, :applications, []))
    container_apps = extract_atom_list(meta, :applications)
    included_apps = normalize_atoms(Map.get(app, :included_applications, []))
    registered = normalize_atoms(Map.get(app, :registered, []))

    applications =
      (extra_apps ++ container_apps ++ [:kernel, :stdlib])
      |> Enum.uniq()

    env_atoms =
      [extract_env_pairs(meta), atomize_env(Map.get(app, :env, %{}))]
      |> Enum.reduce(%{}, fn kv, acc -> Map.merge(acc, Enum.into(kv, %{})) end)

    modules_atoms = filter_app_modules(modules)

    base = [
      {:description, to_charlist_safe(description)},
      {:vsn, to_charlist_safe(vsn)},
      {:modules, modules_atoms},
      {:registered, registered},
      {:applications, applications},
      {:included_applications, included_apps},
      {:env, Enum.into(env_atoms, [])},
      {:mod, {mod_atom, []}}
    ]

    phases = normalize_atoms(Map.get(app, :start_phases, []))

    if phases == [] do
      base
    else
      base ++ [{:start_phases, Enum.map(phases, fn p -> {p, []} end)}]
    end
  end

  # -- Naming / vsn ---------------------------------------------------------

  defp app_resource_atom(project, container_name) do
    case Cure.Project.app_name_for(project) do
      "" -> String.to_atom(Macro.underscore(container_name))
      normalized -> String.to_atom(normalized)
    end
  end

  defp pick_vsn(app, meta, project) do
    case Map.get(app, :vsn) do
      vsn when is_binary(vsn) and vsn != "" ->
        vsn

      _ ->
        case extract_string(meta, :vsn) do
          vsn when is_binary(vsn) and vsn != "" -> vsn
          _ -> project.version || "0.1.0"
        end
    end
  end

  defp extract_string(meta, key) do
    case Keyword.get(meta, key) do
      {:literal, _, value} when is_binary(value) -> value
      _ -> nil
    end
  end

  # -- AST extraction helpers -----------------------------------------------

  defp extract_atom_list(meta, key) do
    case Keyword.get(meta, key) do
      {:list, _, items} -> Enum.flat_map(items, &extract_atom/1)
      _ -> []
    end
  end

  defp extract_atom({:literal, _, value}) when is_atom(value), do: [value]
  defp extract_atom({:literal, _, value}) when is_binary(value), do: [String.to_atom(value)]
  defp extract_atom(_), do: []

  defp extract_env_pairs(meta) do
    case Keyword.get(meta, :env) do
      {:map, _, pairs} -> Enum.flat_map(pairs, &extract_env_pair/1)
      _ -> []
    end
  end

  defp extract_env_pair({:pair, _, [key_ast, value_ast]}) do
    case extract_atom(key_ast) do
      [key] -> [{key, extract_value(value_ast)}]
      _ -> []
    end
  end

  defp extract_env_pair(_), do: []

  defp extract_value({:literal, _, value}), do: value
  defp extract_value({:list, _, items}), do: Enum.map(items, &extract_value/1)
  defp extract_value({:tuple, _, items}), do: List.to_tuple(Enum.map(items, &extract_value/1))
  defp extract_value({:map, _, pairs}), do: pairs |> Enum.flat_map(&extract_env_pair/1) |> Enum.into(%{})
  defp extract_value(other), do: other

  # -- Normalisation helpers ------------------------------------------------

  defp normalize_atoms(list) when is_list(list) do
    list
    |> Enum.map(fn
      atom when is_atom(atom) -> atom
      str when is_binary(str) -> String.to_atom(str)
      _ -> nil
    end)
    |> Enum.reject(&is_nil/1)
  end

  defp normalize_atoms(_), do: []

  defp atomize_env(map) when is_map(map) do
    Enum.map(map, fn {k, v} ->
      key =
        cond do
          is_atom(k) -> k
          is_binary(k) -> String.to_atom(k)
          true -> k
        end

      {key, v}
    end)
  end

  defp atomize_env(_), do: []

  defp to_charlist_safe(s) when is_binary(s), do: String.to_charlist(s)
  defp to_charlist_safe(s), do: to_string(s) |> String.to_charlist()

  # The compiled module list comes back as a list of atoms from
  # `Cure.Project.compile_project/2`. Keep only user modules (the ones
  # generated by Cure) so bogus entries like `Elixir.Module` stray
  # imports do not end up in the `.app` file. The convention is that
  # every Cure-compiled module's atom contains at least one dot
  # (e.g. `:"Std.List"`, `:"Cure.Actor.Worker"`) or is an unqualified
  # atom produced by `mod Name`.
  defp filter_app_modules(modules) do
    modules
    |> Enum.uniq()
    |> Enum.filter(fn m -> is_atom(m) end)
    |> Enum.reject(&match?(:erlang, &1))
  end
end
