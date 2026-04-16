defmodule Cure.Project do
  @moduledoc """
  Cure project management: parse Cure.toml, resolve dependencies,
  scaffold new projects.

  ## Cure.toml Format

      [project]
      name = "my_app"
      version = "0.1.0"

      [dependencies]
      utils = { path = "../shared/utils" }

      [compiler]
      type_check = true
      optimize = true
  """

  defstruct [
    :name,
    :version,
    dependencies: [],
    compiler_opts: [],
    root: "."
  ]

  @type dep :: %{name: String.t(), path: String.t()} | %{name: String.t(), git: String.t(), tag: String.t()}
  @type t :: %__MODULE__{}

  # -- Loading -----------------------------------------------------------------

  @doc "Load a Cure.toml from the given directory (or current dir)."
  @spec load(String.t()) :: {:ok, t()} | {:error, term()}
  def load(dir \\ ".") do
    path = Path.join(dir, "Cure.toml")

    case File.read(path) do
      {:ok, content} ->
        project = parse_toml(content)
        {:ok, %{project | root: dir}}

      {:error, :enoent} ->
        {:error, :no_project_file}

      {:error, reason} ->
        {:error, {:file_error, reason}}
    end
  end

  # -- Dependency Resolution ---------------------------------------------------

  @doc "Resolve and compile all dependencies for a project."
  @spec resolve_deps(t()) :: :ok | {:error, term()}
  def resolve_deps(%__MODULE__{dependencies: deps, root: root}) do
    Enum.each(deps, fn dep ->
      case dep do
        %{path: rel_path, name: name} ->
          abs_path = Path.expand(rel_path, root)
          cure_files = Path.wildcard(Path.join(abs_path, "lib/**/*.cure"))

          Enum.each(cure_files, fn file ->
            case Cure.Compiler.compile_file(file,
                   output_dir: Path.join(root, "_build/deps/#{name}"),
                   emit_events: false
                 ) do
              {:ok, _mod, _warnings} -> :ok
              {:error, _reason} -> :ok
            end
          end)

          # Add to code path
          dep_ebin = Path.join(root, "_build/deps/#{name}")
          File.mkdir_p!(dep_ebin)
          :code.add_patha(String.to_charlist(Path.expand(dep_ebin)))

        _ ->
          :ok
      end
    end)

    :ok
  end

  # -- Scaffolding -------------------------------------------------------------

  @doc """
  Create a new Cure project in the given directory.

  Equivalent to `scaffold(name, :lib)`.
  """
  @spec init(String.t()) :: :ok
  def init(name), do: scaffold(name, :lib)

  @doc """
  Scaffold a new Cure project from a template.

  Templates:
  - `:lib` -- a basic library project (default).
  - `:app` -- a library project plus a runnable `main` and a test file.
  - `:fsm` -- a project with a starter FSM definition.
  """
  @spec scaffold(String.t(), :lib | :app | :fsm) :: :ok
  def scaffold(name, template \\ :lib) do
    File.mkdir_p!(name)
    File.mkdir_p!(Path.join(name, "lib"))
    File.mkdir_p!(Path.join(name, "test"))

    File.write!(Path.join(name, "Cure.toml"), default_toml(name))
    File.write!(Path.join(name, ".gitignore"), default_gitignore())
    File.write!(Path.join(name, "README.md"), default_readme(name))

    case template do
      :lib -> write_lib_template(name)
      :app -> write_app_template(name)
      :fsm -> write_fsm_template(name)
      _ -> write_lib_template(name)
    end

    :ok
  end

  defp default_toml(name) do
    """
    [project]
    name = "#{name}"
    version = "0.1.0"

    [dependencies]

    [compiler]
    type_check = false
    optimize = false
    """
  end

  defp default_gitignore do
    """
    /_build/
    /Cure.lock
    *.beam
    """
  end

  defp default_readme(name) do
    """
    # #{name}

    A Cure project.

        cure compile lib/
        cure test
        cure run lib/main.cure
    """
  end

  defp write_lib_template(name) do
    mod = String.capitalize(name)

    File.write!(Path.join([name, "lib", "main.cure"]), """
    mod #{mod}
      ## Public entry point.
      fn hello() -> String = "hello from #{name}"
    """)

    File.write!(Path.join([name, "test", "main_test.cure"]), """
    mod #{mod}.Test
      use Std.Test

      fn test_hello() -> Atom =
        Std.Test.assert_eq(#{mod}.hello(), "hello from #{name}")
    """)
  end

  defp write_app_template(name) do
    write_lib_template(name)
    mod = String.capitalize(name)

    File.write!(Path.join([name, "lib", "app.cure"]), """
    mod #{mod}.App
      use Std.Io

      fn main() -> Atom =
        Std.Io.println(#{mod}.hello())
    """)
  end

  defp write_fsm_template(name) do
    write_lib_template(name)
    mod = String.capitalize(name)

    File.write!(Path.join([name, "lib", "fsm.cure"]), """
    mod #{mod}.Fsm

      fsm Switch
        Off --on--> On
        On  --off--> Off
    """)
  end

  # -- Lockfile ----------------------------------------------------------------

  @doc """
  Write a Cure.lock file capturing the current resolved dependency set.

  The lockfile format is intentionally simple: one TOML table per
  dependency.
  """
  @spec write_lock(t()) :: :ok
  def write_lock(%__MODULE__{dependencies: deps, root: root}) do
    body =
      Enum.map_join(deps, "\n", fn dep ->
        name = Map.get(dep, :name, "")

        kv =
          ["path", "git", "tag", "ref"]
          |> Enum.flat_map(fn k ->
            v = Map.get(dep, String.to_atom(k))
            if v in [nil, ""], do: [], else: ["  #{k} = \"#{v}\""]
          end)
          |> Enum.join("\n")

        "[lock.#{name}]\n#{kv}"
      end)

    File.write!(Path.join(root, "Cure.lock"), body <> "\n")
  end

  @doc "Render a human-readable dependency tree."
  @spec dep_tree(t()) :: String.t()
  def dep_tree(%__MODULE__{name: name, dependencies: deps}) do
    header = "#{name}"

    children =
      Enum.map(deps, fn dep ->
        kind =
          cond do
            Map.get(dep, :path) -> "path:#{dep.path}"
            Map.get(dep, :git) -> "git:#{dep.git}"
            true -> "unknown"
          end

        "  - #{Map.get(dep, :name)} (#{kind})"
      end)

    Enum.join([header | children], "\n")
  end

  @doc """
  Resolve a git-based dependency by cloning into `_build/deps/<name>` if not
  already present, then compiling its `lib/`.
  """
  @spec resolve_git_dep(map(), String.t()) :: :ok | {:error, term()}
  def resolve_git_dep(%{name: name, git: url} = dep, root) do
    target = Path.join(root, "_build/deps/#{name}")

    unless File.dir?(Path.join(target, ".git")) do
      File.mkdir_p!(target)
      args = ["clone", "--depth", "1"] ++ ref_args(dep) ++ [url, target]
      System.cmd("git", args, stderr_to_stdout: true)
    end

    cure_files = Path.wildcard(Path.join(target, "lib/**/*.cure"))

    Enum.each(cure_files, fn file ->
      _ = Cure.Compiler.compile_file(file, output_dir: Path.join(root, "_build/deps/#{name}"), emit_events: false)
    end)

    :code.add_patha(String.to_charlist(Path.expand(Path.join(root, "_build/deps/#{name}"))))
    :ok
  end

  defp ref_args(%{tag: tag}) when is_binary(tag) and tag != "", do: ["--branch", tag]
  defp ref_args(%{ref: ref}) when is_binary(ref) and ref != "", do: ["--branch", ref]
  defp ref_args(_), do: []

  # -- Compiler Options --------------------------------------------------------

  @doc "Get compiler options from the project config."
  @spec compiler_opts(t()) :: keyword()
  def compiler_opts(%__MODULE__{compiler_opts: opts}) do
    [
      check_types: Keyword.get(opts, :type_check, false),
      optimize: Keyword.get(opts, :optimize, false)
    ]
  end

  # -- TOML Parser (minimal subset) -------------------------------------------

  defp parse_toml(content) do
    lines = String.split(content, "\n")
    {project, deps, compiler} = parse_sections(lines, nil, %{}, [], [])

    %__MODULE__{
      name: Map.get(project, "name", "unnamed"),
      version: Map.get(project, "version", "0.1.0"),
      dependencies: deps,
      compiler_opts: compiler
    }
  end

  defp parse_sections([], _section, project, deps, compiler) do
    {project, deps, compiler}
  end

  defp parse_sections([line | rest], section, project, deps, compiler) do
    trimmed = String.trim(line)

    cond do
      trimmed == "" or String.starts_with?(trimmed, "#") ->
        parse_sections(rest, section, project, deps, compiler)

      trimmed == "[project]" ->
        parse_sections(rest, :project, project, deps, compiler)

      trimmed == "[dependencies]" ->
        parse_sections(rest, :dependencies, project, deps, compiler)

      trimmed == "[compiler]" ->
        parse_sections(rest, :compiler, project, deps, compiler)

      section == :project ->
        {key, val} = parse_kv(trimmed)
        parse_sections(rest, section, Map.put(project, key, val), deps, compiler)

      section == :dependencies ->
        dep = parse_dep_line(trimmed)

        if dep,
          do: parse_sections(rest, section, project, [dep | deps], compiler),
          else: parse_sections(rest, section, project, deps, compiler)

      section == :compiler ->
        {key, val} = parse_kv(trimmed)
        atom_key = String.to_atom(key)
        bool_val = val in ["true", true]
        parse_sections(rest, section, project, deps, [{atom_key, bool_val} | compiler])

      true ->
        parse_sections(rest, section, project, deps, compiler)
    end
  end

  defp parse_kv(line) do
    case String.split(line, "=", parts: 2) do
      [key, val] ->
        {String.trim(key), String.trim(val) |> String.trim("\"")}

      _ ->
        {"", ""}
    end
  end

  defp parse_dep_line(line) do
    case Regex.run(~r/^(\w+)\s*=\s*\{(.+)\}/, line) do
      [_, name, attrs] ->
        pairs =
          Regex.scan(~r/(\w+)\s*=\s*"([^"]*)"/, attrs)
          |> Enum.map(fn [_, k, v] -> {k, v} end)
          |> Map.new()

        Map.put(pairs, "name", name)
        |> then(fn m ->
          %{name: m["name"], path: Map.get(m, "path"), git: Map.get(m, "git"), tag: Map.get(m, "tag")}
        end)

      _ ->
        nil
    end
  end
end
