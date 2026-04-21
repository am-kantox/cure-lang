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

  ## Application and release sections (v0.26.0)

  A project that ships an `app` container may additionally declare:

      [application]
      name           = "my_app"
      vsn            = "0.1.0"
      description    = ""
      applications   = ["logger", "crypto"]
      included_applications = []
      start_phases   = ["init", "warm_cache"]

      [application.env]
      port = 4000

      [release]
      name         = "my_app"
      vsn          = "0.1.0"
      include_erts = false
      applications = ["logger"]
      vm_args      = "rel/vm.args"
      sys_config   = "rel/sys.config"

  The parser accepts a minimal TOML subset: scalar string/bool/int
  values, string arrays, and nested tables (`[application.env]`).
  """

  defstruct [
    :name,
    :version,
    dependencies: [],
    compiler_opts: [],
    source_paths: ["lib"],
    root: ".",
    application: nil,
    release: nil
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

  @doc """
  Resolve and compile all dependencies for a project.

  The dependency kind dispatches per entry:

  - `path: "..."`   -- local path dependency; compiled in place.
  - `git:  "..."`   -- git dependency; cloned under `_build/deps/<name>`.
  - otherwise       -- registry dependency; resolved via
    `Cure.Project.Registry`, hash-checked, signature-verified, and
    unpacked under `_build/deps/<name>-<version>/`.

  Returns `:ok` on success, `{:error, term}` on the first hard
  failure. Transparency-log failures degrade to a warning unless
  `config :cure, strict_transparency: true` is set.
  """
  @spec resolve_deps(t()) :: :ok | {:error, term()}
  def resolve_deps(%__MODULE__{dependencies: deps, root: root}) do
    # Preferentially reuse the lockfile: if every locked version still
    # satisfies the current constraints, we skip the resolver entirely.
    registry_deps = Enum.filter(deps, &registry_dep?/1)
    top_constraints = for d <- registry_deps, into: %{}, do: {d.name, Map.get(d, :constraint, "")}

    reuse_lock? =
      case Cure.Project.Lock.read(root) do
        {:ok, lock} ->
          match?({:ok, _}, Cure.Project.Lock.resolve_with_lock(top_constraints, lock))

        _ ->
          false
      end

    result =
      Enum.reduce_while(deps, :ok, fn dep, :ok ->
        case resolve_one(dep, root, reuse_lock?) do
          :ok -> {:cont, :ok}
          {:error, _} = err -> {:halt, err}
        end
      end)

    result
  end

  defp registry_dep?(dep) do
    is_nil(Map.get(dep, :path)) and is_nil(Map.get(dep, :git))
  end

  defp resolve_one(%{path: rel_path, name: name}, root, _reuse_lock?)
       when is_binary(rel_path) and rel_path != "" do
    abs_path = Path.expand(rel_path, root)
    cure_files = Path.wildcard(Path.join(abs_path, "lib/**/*.cure"))
    dep_ebin = Path.join(root, "_build/deps/#{name}")
    File.mkdir_p!(dep_ebin)

    Enum.each(cure_files, fn file ->
      _ = Cure.Compiler.compile_file(file, output_dir: dep_ebin, emit_events: false)
    end)

    :code.add_patha(String.to_charlist(Path.expand(dep_ebin)))
    :ok
  end

  defp resolve_one(%{git: _url} = dep, root, _reuse_lock?) do
    resolve_git_dep(dep, root)
  end

  defp resolve_one(%{name: name} = dep, root, reuse_lock?) do
    version = Map.get(dep, :version)
    constraint = Map.get(dep, :constraint) || version || ">= 0.0.0"
    resolve_registry_dep(name, constraint, root, reuse_lock?)
  end

  defp resolve_one(_, _root, _reuse_lock?), do: :ok

  defp resolve_registry_dep(name, constraint, root, reuse_lock?) do
    with {:ok, version_string, sha} <- pick_version(name, constraint, root, reuse_lock?),
         {:ok, bytes, _hash} <- Cure.Project.Registry.fetch_tarball(name, version_string, sha),
         :ok <- verify_bundle(name, version_string, sha, bytes),
         :ok <- install_tarball(name, version_string, bytes, root) do
      :ok
    else
      {:error, _} = err -> err
    end
  end

  defp pick_version(name, constraint, root, true) do
    # Lock-preferred path: read the lockfile, honour the pinned version.
    case Cure.Project.Lock.read(root) do
      {:ok, lock} ->
        case Map.get(lock, name) do
          %{version: v, hash: h} when is_binary(h) and h != "" ->
            {:ok, v, strip_sha_prefix(h)}

          _ ->
            pick_version(name, constraint, root, false)
        end

      _ ->
        pick_version(name, constraint, root, false)
    end
  end

  defp pick_version(name, _constraint, _root, false) do
    with {:ok, versions} <- Cure.Project.Registry.list_versions(name),
         [top | _] <- versions do
      {:ok, top.version, String.downcase(top.sha256)}
    else
      [] -> {:error, {:no_versions, name}}
      {:error, _} = err -> err
    end
  end

  defp verify_bundle(name, version, _sha, bytes) do
    case Cure.Project.Transparency.verify(name, version, :crypto.hash(:sha256, bytes) |> Base.encode16(case: :lower)) do
      :ok -> :ok
      {:ok, :unverified} -> :ok
      {:error, _} = err -> err
    end
  end

  defp install_tarball(name, version, bytes, root) do
    target = Path.join(root, "_build/deps/#{name}-#{version}")
    File.mkdir_p!(target)
    tmp = Path.join(target, "pkg.tar.gz")
    File.write!(tmp, bytes)
    _ = :erl_tar.extract(String.to_charlist(tmp), [:compressed, cwd: String.to_charlist(target)])
    _ = File.rm(tmp)

    cure_files = Path.wildcard(Path.join(target, "**/lib/**/*.cure"))
    dep_ebin = Path.join(root, "_build/deps/#{name}-#{version}/ebin")
    File.mkdir_p!(dep_ebin)

    Enum.each(cure_files, fn file ->
      _ = Cure.Compiler.compile_file(file, output_dir: dep_ebin, emit_events: false)
    end)

    :code.add_patha(String.to_charlist(Path.expand(dep_ebin)))
    :ok
  end

  defp strip_sha_prefix("sha256:" <> rest), do: rest
  defp strip_sha_prefix(other), do: other

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

    File.write!(Path.join(name, "Cure.toml"), default_toml(name, template))
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

  defp default_toml(name, :app) do
    mod = String.capitalize(name)

    """
    [project]
    name = "#{name}"
    version = "0.1.0"

    [dependencies]

    [compiler]
    type_check = false
    optimize = false

    [application]
    name           = "#{name}"
    vsn            = "0.1.0"
    description    = ""
    applications   = ["logger"]
    start_phases   = []

    [application.env]

    [release]
    name         = "#{name}"
    vsn          = "0.1.0"
    include_erts = false
    applications = []

    # The `app` container in lib/app.cure is `app #{mod}`; the
    # compiler verifies that its name matches `[application].name`
    # above.
    """
  end

  defp default_toml(name, _template) do
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

    File.write!(Path.join([name, "lib", "root_sup.cure"]), """
    ## Root supervisor for the #{mod} application. Add child specs as
    ## the project grows.
    sup #{mod}.Root
      strategy = :one_for_one
      intensity = 3
      period = 5
      children
    """)

    File.write!(Path.join([name, "lib", "app.cure"]), """
    ## #{mod} application.
    ##
    ## Compiles to `:"Cure.App.#{mod}"`, an OTP `Application` callback
    ## module. The compiler verifies that exactly one `app` container
    ## exists in the project and that its name matches
    ## `[application].name` in `Cure.toml`.
    app #{mod}
      vsn         = "0.1.0"
      description = "#{mod}"
      root        = sup #{mod}.Root
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

  # -- Project-wide compile driver (v0.26.0) ---------------------------------

  @doc """
  Compile every `.cure` file under the project's `lib/` directory,
  enforcing the single-`app` invariant and emitting a `<name>.app`
  resource file when an `app` container is present.

  Steps:

  1. Lex+parse every candidate file with a lightweight pre-pass
     looking for `app` containers.
  2. If more than one `app` is found, return
     `{:error, {:duplicate_app, [{path, name}, ...]}}` (surfaced as
     `E051`).
  3. If exactly one `app` is found, verify its name matches
     `[application].name` (or falls back to `[project].name`).
     Mismatch returns `{:error, {:app_name_mismatch, expected, actual}}`.
  4. Compile every file via `Cure.Compiler.compile_file/2`, threading
     the declared phases through so `Cure.App.Verifier` can report
     start-phase mismatches at compile time.
  5. Emit the `.app` resource alongside the compiled `.beam` files.

  Returns `{:ok, %{modules: [...], app_module: atom() | nil}}` on
  success, `{:error, reason}` otherwise.
  """
  @spec compile_project(t(), keyword()) ::
          {:ok, map()} | {:error, term()}
  def compile_project(%__MODULE__{} = project, opts \\ []) do
    output_dir = Keyword.get(opts, :output_dir, Path.join(project.root, "_build/cure/ebin"))

    extra_paths =
      Keyword.get_lazy(opts, :paths, fn -> default_source_paths(project) end)

    emit_events? = Keyword.get(opts, :emit_events, false)
    check? = Keyword.get(opts, :check_types, false)

    cure_files =
      extra_paths
      |> Enum.flat_map(fn dir ->
        if File.dir?(dir), do: Path.wildcard(Path.join(dir, "**/*.cure")), else: []
      end)
      |> Enum.sort()

    with {:ok, app_info} <- detect_app(cure_files, project),
         :ok <- verify_app_name(app_info, project),
         {:ok, modules} <-
           compile_all_files(cure_files, output_dir, emit_events?, check?, declared_phases(project)),
         :ok <- maybe_write_app_resource(app_info, modules, project, output_dir) do
      {:ok, %{modules: modules, app_module: app_module(app_info)}}
    end
  end

  @doc false
  @spec detect_app([String.t()], t()) :: {:ok, map() | nil} | {:error, term()}
  def detect_app(files, _project) do
    # Lex+parse only enough to find `app` containers. We intentionally
    # emit no events during the pre-pass so the main compile pass
    # remains the sole emitter for LSP consumers.
    containers =
      Enum.flat_map(files, fn file ->
        case File.read(file) do
          {:ok, source} ->
            with {:ok, tokens} <-
                   Cure.Compiler.Lexer.tokenize(source, file: file, emit_events: false),
                 {:ok, ast} <-
                   Cure.Compiler.Parser.parse(tokens, file: file, emit_events: false) do
              find_app_containers(ast, file)
            else
              _ -> []
            end

          _ ->
            []
        end
      end)

    case containers do
      [] ->
        {:ok, nil}

      [single] ->
        {:ok, single}

      multiple ->
        {:error, {:duplicate_app, Enum.map(multiple, fn c -> {c.file, c.name} end)}}
    end
  end

  defp default_source_paths(%__MODULE__{root: root, source_paths: paths}) do
    Enum.map(paths || ["lib"], &Path.join(root, &1))
  end

  defp find_app_containers({:container, meta, _body}, file) do
    case Keyword.get(meta, :container_type) do
      :app -> [%{file: file, name: Keyword.get(meta, :name), meta: meta}]
      _ -> []
    end
  end

  defp find_app_containers({:block, _, children}, file) when is_list(children) do
    Enum.flat_map(children, &find_app_containers(&1, file))
  end

  defp find_app_containers(_, _), do: []

  defp verify_app_name(nil, _project), do: :ok

  defp verify_app_name(%{name: name}, project) do
    expected = app_name_for(project)
    actual = normalize_app_name(name)

    if expected == actual do
      :ok
    else
      {:error, {:app_name_mismatch, expected, actual}}
    end
  end

  @doc false
  def app_name_for(%__MODULE__{} = project) do
    case project.application do
      %{name: n} when is_binary(n) and n != "" -> normalize_app_name(n)
      _ -> normalize_app_name(project.name)
    end
  end

  defp normalize_app_name(nil), do: ""

  defp normalize_app_name(name) when is_binary(name) do
    name
    |> String.replace(".", "_")
    |> Macro.underscore()
  end

  defp declared_phases(%__MODULE__{application: %{start_phases: phases}}) when is_list(phases),
    do: phases

  defp declared_phases(_), do: nil

  defp compile_all_files(files, output_dir, emit?, check?, declared_phases) do
    base_opts = [
      output_dir: output_dir,
      emit_events: emit?,
      check_types: check?
    ]

    opts =
      if is_list(declared_phases),
        do: Keyword.put(base_opts, :declared_phases, declared_phases),
        else: base_opts

    result =
      Enum.reduce_while(files, {:ok, []}, fn file, {:ok, acc} ->
        case Cure.Compiler.compile_file(file, opts) do
          {:ok, module, _warnings} -> {:cont, {:ok, [module | acc]}}
          {:error, _} = err -> {:halt, err}
        end
      end)

    case result do
      {:ok, modules} -> {:ok, Enum.reverse(modules)}
      {:error, reason} -> {:error, {:compile_failed, reason}}
    end
  end

  defp app_module(nil), do: nil

  defp app_module(%{name: name}) do
    String.to_atom("Cure.App." <> name)
  end

  defp maybe_write_app_resource(nil, _modules, _project, _output_dir), do: :ok

  defp maybe_write_app_resource(app_info, modules, project, output_dir) do
    Cure.App.Resource.write(app_info, modules, project, output_dir: output_dir)
  end

  # -- TOML Parser (minimal subset) -------------------------------------------

  defp parse_toml(content) do
    lines = String.split(content, "\n")
    acc = %{project: %{}, deps: [], compiler: [], application: %{}, release: %{}}
    parsed = parse_lines(lines, nil, acc)

    application_map = normalize_application(parsed.application)
    release_map = normalize_release(parsed.release)

    source_paths =
      case Map.get(parsed.project, "source_paths") do
        list when is_list(list) and list != [] -> Enum.map(list, &to_string/1)
        _ -> ["lib"]
      end

    %__MODULE__{
      name: Map.get(parsed.project, "name", "unnamed"),
      version: Map.get(parsed.project, "version", "0.1.0"),
      dependencies: parsed.deps,
      compiler_opts: parsed.compiler,
      source_paths: source_paths,
      application: application_map,
      release: release_map
    }
  end

  defp parse_lines([], _section, acc), do: acc

  defp parse_lines([line | rest], section, acc) do
    trimmed = String.trim(line)

    cond do
      trimmed == "" or String.starts_with?(trimmed, "#") ->
        parse_lines(rest, section, acc)

      String.starts_with?(trimmed, "[") and String.ends_with?(trimmed, "]") ->
        header = String.slice(trimmed, 1..-2//1) |> String.trim()
        parse_lines(rest, {:table, header}, acc)

      true ->
        acc = apply_kv(section, trimmed, acc)
        parse_lines(rest, section, acc)
    end
  end

  defp apply_kv({:table, "project"}, line, acc) do
    case parse_kv(line) do
      {"", _} ->
        acc

      {key, val} ->
        # `source_paths = ["a", "b"]` is the only project-level key that
        # currently expects a non-scalar value; route it through
        # `parse_scalar/1` so the array form parses, while every other
        # field stays a plain string with quotes stripped.
        value =
          case key do
            "source_paths" -> parse_scalar(val)
            _ -> strip_quotes(val)
          end

        %{acc | project: Map.put(acc.project, key, value)}
    end
  end

  defp apply_kv({:table, "dependencies"}, line, acc) do
    case parse_dep_line(line) do
      nil -> acc
      dep -> %{acc | deps: [dep | acc.deps]}
    end
  end

  defp apply_kv({:table, "compiler"}, line, acc) do
    case parse_kv(line) do
      {"", _} ->
        acc

      {key, val} ->
        atom_key = String.to_atom(key)
        bool_val = strip_quotes(val) == "true"
        %{acc | compiler: [{atom_key, bool_val} | acc.compiler]}
    end
  end

  defp apply_kv({:table, "application"}, line, acc) do
    case parse_kv(line) do
      {"", _} -> acc
      {key, val} -> %{acc | application: Map.put(acc.application, key, parse_scalar(val))}
    end
  end

  defp apply_kv({:table, "application.env"}, line, acc) do
    case parse_kv(line) do
      {"", _} ->
        acc

      {key, val} ->
        env = Map.get(acc.application, "env", %{})
        env = Map.put(env, key, parse_scalar(val))
        %{acc | application: Map.put(acc.application, "env", env)}
    end
  end

  defp apply_kv({:table, "release"}, line, acc) do
    case parse_kv(line) do
      {"", _} -> acc
      {key, val} -> %{acc | release: Map.put(acc.release, key, parse_scalar(val))}
    end
  end

  defp apply_kv(_section, _line, acc), do: acc

  defp parse_kv(line) do
    case String.split(line, "=", parts: 2) do
      [key, val] -> {String.trim(key), String.trim(val)}
      _ -> {"", ""}
    end
  end

  defp strip_quotes(val) when is_binary(val) do
    val
    |> String.trim()
    |> String.trim("\"")
  end

  defp strip_quotes(val), do: val

  # Parse a TOML scalar: quoted string, bool, integer, string array, or
  # bare identifier. Anything unrecognised falls back to its trimmed
  # textual form so unknown keys still have *some* value.
  defp parse_scalar(raw) when is_binary(raw) do
    trimmed = String.trim(raw)

    cond do
      String.starts_with?(trimmed, "\"") and String.ends_with?(trimmed, "\"") ->
        String.slice(trimmed, 1..-2//1)

      trimmed in ["true", "false"] ->
        trimmed == "true"

      Regex.match?(~r/^-?\d+$/, trimmed) ->
        String.to_integer(trimmed)

      String.starts_with?(trimmed, "[") and String.ends_with?(trimmed, "]") ->
        inner = String.slice(trimmed, 1..-2//1)

        Regex.scan(~r/"([^"]*)"/, inner)
        |> Enum.map(fn [_, v] -> v end)

      true ->
        trimmed
    end
  end

  defp parse_scalar(other), do: other

  defp normalize_application(map) when map == %{} or map == nil, do: nil

  defp normalize_application(map) do
    %{
      name: Map.get(map, "name"),
      vsn: Map.get(map, "vsn"),
      description: Map.get(map, "description", ""),
      applications: list_of_strings(Map.get(map, "applications", [])),
      included_applications: list_of_strings(Map.get(map, "included_applications", [])),
      start_phases: list_of_strings(Map.get(map, "start_phases", [])),
      registered: list_of_strings(Map.get(map, "registered", [])),
      env: Map.get(map, "env", %{})
    }
  end

  defp normalize_release(map) when map == %{} or map == nil, do: nil

  defp normalize_release(map) do
    %{
      name: Map.get(map, "name"),
      vsn: Map.get(map, "vsn"),
      include_erts: Map.get(map, "include_erts", false),
      applications: list_of_strings(Map.get(map, "applications", [])),
      vm_args: Map.get(map, "vm_args"),
      sys_config: Map.get(map, "sys_config")
    }
  end

  defp list_of_strings(list) when is_list(list), do: Enum.map(list, &to_string/1)
  defp list_of_strings(str) when is_binary(str), do: [str]
  defp list_of_strings(_), do: []

  defp parse_dep_line(line) do
    cond do
      # Inline-table form: foo = { path = "...", version = "..." }
      match = Regex.run(~r/^(\w+)\s*=\s*\{(.+)\}/, line) ->
        [_, name, attrs] = match

        pairs =
          Regex.scan(~r/(\w+)\s*=\s*"([^"]*)"/, attrs)
          |> Enum.map(fn [_, k, v] -> {k, v} end)
          |> Map.new()

        %{
          name: name,
          path: Map.get(pairs, "path"),
          git: Map.get(pairs, "git"),
          tag: Map.get(pairs, "tag"),
          version: Map.get(pairs, "version"),
          constraint: Map.get(pairs, "constraint") || Map.get(pairs, "version")
        }

      # Simple registry form: foo = "~> 1.0"
      match = Regex.run(~r/^(\w+)\s*=\s*"([^"]+)"/, line) ->
        [_, name, constraint] = match
        %{name: name, path: nil, git: nil, tag: nil, version: constraint, constraint: constraint}

      true ->
        nil
    end
  end
end
