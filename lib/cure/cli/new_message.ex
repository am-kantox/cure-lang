defmodule Cure.CLI.NewMessage do
  @moduledoc """
  Build the post-scaffold banner printed by `cure new`.

  Splitting the message out of `Cure.CLI.cmd_new/2` keeps the CLI
  module focused on argument parsing and dispatch, and makes the
  banner trivially unit-testable: the renderer takes a project name
  and template atom and returns plain Markdown plus its ANSI-rendered
  form.

  The Markdown source is rendered via `Marcli.render/2` so the output
  picks up syntax-highlighted code fences, bullet glyphs, and bold
  headings whenever the calling terminal supports ANSI escape
  sequences. When ANSI is disabled (output redirected to a file,
  `NO_COLOR=1`, etc.), `Marcli.render/2`'s `:escape_sequences` option
  collapses the rendering to plain text so test captures and CI logs
  remain readable.
  """

  alias Cure.Stdlib.Paths

  @typedoc "Templates accepted by `cure new`."
  @type template :: :lib | :app | :fsm

  @doc """
  Render the banner for the given project name and template.

  Options:

    * `:ansi?` -- override ANSI rendering. Defaults to
      `IO.ANSI.enabled?/0`.
    * `:cure_home` -- override the `CURE_HOME` lookup, primarily for
      tests. Defaults to `Cure.Stdlib.Paths.cure_home/0`.

  When `Marcli.render/2` is unavailable (most commonly inside an
  escript, where the `:mdex` NIF cannot be loaded from the bundled
  zip archive), this function falls back to a lightweight ANSI
  highlighter that styles only headings and inline code. The plain
  Markdown source is always available via `build/3`.
  """
  @spec render(String.t(), template(), keyword()) :: String.t()
  def render(name, template, opts \\ []) do
    markdown = build(name, template, opts)
    ansi? = Keyword.get(opts, :ansi?, IO.ANSI.enabled?())

    try do
      Marcli.render(markdown, escape_sequences: ansi?)
    rescue
      # `Marcli.render/2` calls `MDEx.parse_document!/2`, which loads
      # a NIF (`MDEx.Native`). The NIF cannot be opened from inside
      # an escript archive (escripts bundle a zip and `dlopen` needs a
      # real file), so the call raises `UndefinedFunctionError`. We
      # also defensively catch any other failure mode so a malformed
      # Markdown blob never breaks `cure new`.
      _ -> fallback_render(markdown, ansi?)
    end
  end

  # Lightweight ANSI fallback used when `Marcli.render/2` cannot run.
  # Highlights `# heading`, `## heading`, and `### heading` lines, and
  # backtick-quoted inline code. Everything else is printed verbatim.
  # Mirrors marcli's default theme (h1 yellow bold, h2 cyan bold, h3
  # white bold) so the visual feel stays consistent across renderers.
  @doc false
  @spec fallback_render(String.t(), boolean()) :: String.t()
  def fallback_render(markdown, ansi?) do
    bold = ansi_or("\e[1m", ansi?)
    yellow = ansi_or("\e[33m", ansi?)
    cyan = ansi_or("\e[36m", ansi?)
    white = ansi_or("\e[37m", ansi?)
    blue = ansi_or("\e[34m", ansi?)
    reset = ansi_or("\e[0m", ansi?)

    markdown
    |> String.split("\n")
    |> Enum.map(fn line ->
      cond do
        String.starts_with?(line, "### ") ->
          bold <> white <> String.replace_prefix(line, "### ", "") <> reset

        String.starts_with?(line, "## ") ->
          bold <> cyan <> String.replace_prefix(line, "## ", "") <> reset

        String.starts_with?(line, "# ") ->
          bold <> yellow <> String.replace_prefix(line, "# ", "") <> reset

        true ->
          highlight_inline_code(line, blue, reset)
      end
    end)
    |> Enum.join("\n")
  end

  defp ansi_or(seq, true), do: seq
  defp ansi_or(_seq, false), do: ""

  defp highlight_inline_code(line, color, reset) do
    if color == "" do
      line
    else
      Regex.replace(~r/`([^`]+)`/, line, fn _, code ->
        color <> "`" <> code <> "`" <> reset
      end)
    end
  end

  @doc """
  Build the Markdown source for the new-project banner. Returns a
  binary so callers can pipe it through `Marcli.render/2` or print it
  verbatim (for example from a test).
  """
  @spec build(String.t(), template(), keyword()) :: String.t()
  def build(name, template, opts \\ []) do
    cure_home_value =
      Keyword.get_lazy(opts, :cure_home, fn -> Paths.cure_home() end)

    [
      heading_section(name, template),
      created_files_section(name, template),
      next_steps_section(name),
      cure_home_section(cure_home_value)
    ]
    |> Enum.reject(&(&1 == ""))
    |> Enum.join("\n\n")
  end

  # ---------------------------------------------------------------------------

  defp heading_section(name, template) do
    """
    # Created Cure project `#{name}`

    Template: **#{template}** (`cure new --#{template}`).
    """
    |> String.trim_trailing()
  end

  defp created_files_section(name, template) do
    files = scaffolded_files(name, template)

    bullets = Enum.map_join(files, "\n", fn file -> "- `#{file}`" end)

    """
    ## Files written
    #{bullets}
    """
    |> String.trim_trailing()
  end

  # The on-disk layout produced by `Cure.Project.scaffold/2`. Kept in
  # lockstep with `Cure.Project.write_lib_template/1` and friends so
  # the banner never lies about what was written.
  defp scaffolded_files(name, :lib) do
    [
      "#{name}/Cure.toml",
      "#{name}/.gitignore",
      "#{name}/README.md",
      "#{name}/lib/main.cure",
      "#{name}/test/main_test.cure"
    ]
  end

  defp scaffolded_files(name, :app) do
    scaffolded_files(name, :lib) ++
      [
        "#{name}/lib/root_sup.cure",
        "#{name}/lib/app.cure"
      ]
  end

  defp scaffolded_files(name, :fsm) do
    scaffolded_files(name, :lib) ++
      [
        "#{name}/lib/fsm.cure"
      ]
  end

  defp scaffolded_files(name, _other), do: scaffolded_files(name, :lib)

  defp next_steps_section(name) do
    """
    ## Next steps

    ```sh
    cd #{name}
    cure deps
    cure run lib/main.cure
    cure test
    ```

    Run `cure help` for the full command list.
    """
    |> String.trim_trailing()
  end

  # When `CURE_HOME` is set, surface where the stdlib will be
  # resolved from so the developer can spot a stale or wrong path
  # immediately. When it is not set, gently nudge the user towards
  # the recommended setup so `cure` keeps working from any directory.
  defp cure_home_section(nil) do
    """
    ## Make `cure` available everywhere

    Drop these two lines into your shell profile so the escript can
    find its standard library no matter where you invoke it from:

    ```sh
    export CURE_HOME="/path/to/cure"
    alias cure="$CURE_HOME/cure"
    ```

    `cure` will then look up `Std.*` BEAMs under `$CURE_HOME/priv/ebin`
    and `$CURE_HOME/_build/cure/ebin`, falling back to the bundled
    `priv/` directory in releases.
    """
    |> String.trim_trailing()
  end

  defp cure_home_section(home) when is_binary(home) do
    """
    ## CURE_HOME

    Detected `CURE_HOME=#{home}`. The stdlib will be resolved from:

    - `#{Path.join([home, "priv", "ebin"])}`
    - `#{Path.join([home, "_build", "cure", "ebin"])}`

    Sources for `:t` / `:doc` introspection are looked up under
    `#{Path.join([home, "priv", "std"])}` and `#{Path.join([home, "lib", "std"])}`.
    """
    |> String.trim_trailing()
  end
end
