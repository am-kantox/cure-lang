defmodule Cure.REPL do
  @moduledoc """
  Interactive REPL for Cure.

  A readline-grade read-eval-print loop:

  * Arrow keys move the cursor (left/right) and step through history
    (up/down), `Ctrl+R` opens incremental reverse-i-search, and Emacs
    shortcuts (`Ctrl+A`, `Ctrl+E`, `Ctrl+W`, `Ctrl+K`, ...) plus a
    minimal Vi mode (`:mode vi`) are supported.
  * Input is syntax-highlighted live via `Makeup.Lexers.CureLexer` +
    `Marcli.Formatter`.
  * Meta-commands are prefixed with `:`. See `:help`.
  * Multi-line input ends with a blank line or `;;`, and is also
    auto-completed when brackets balance.
  * When stdin is not a tty (CI, pipes, etc.) the REPL falls back to
    the legacy `IO.gets` loop, so automation continues to work.

  ## History
  Persisted to `~/.cure_history` (configurable). Entries are deduped
  against the immediately preceding line and capped at 10,000.

  ## Configuration

  * `:history_path` -- override the history file.
  * `:raw` -- force raw mode on or off.
  * `:theme` -- one of `:dark`, `:light`, `:mono`; defaults to `:dark`
    and automatically drops to `:mono` when `NO_COLOR` is set or stdout
    is not a tty.
  * `:mode` -- initial editing mode (`:emacs` or `:vi`).
  """

  alias Cure.Compiler.Printer
  alias Cure.REPL.{History, LineEditor, Markdown, Render, Search, Terminal, Theme}
  alias Cure.Stdlib.Preload
  alias Cure.Types.{Checker, Holes}

  defstruct n: 1,
            loaded: [],
            uses: [],
            holes: [],
            editor: nil,
            history: nil,
            history_path: nil,
            input_buffer: [],
            theme: nil,
            mode: :emacs,
            color: true,
            running: true

  @type t :: %__MODULE__{}

  @doc "Start the REPL."
  @spec start(keyword()) :: :ok
  def start(opts \\ []) do
    history_path = Keyword.get(opts, :history_path, default_history_path())
    theme = resolve_theme(opts)
    mode = resolve_mode(opts)

    # Pre-load the compiled Cure stdlib (`_build/cure/ebin`) so expressions
    # can reference `Std.List`, `Std.Math`, etc. without an explicit `:load`.
    # The helper is a no-op when the build directory is missing.
    _ = Preload.preload(examples: false)

    state = %__MODULE__{
      history: History.load(history_path),
      history_path: history_path,
      editor: LineEditor.new(mode: mode),
      theme: theme,
      mode: mode,
      color: theme.name != :mono
    }

    cond do
      Keyword.get(opts, :raw, :auto) == false ->
        banner(state)
        legacy_loop(state)

      Terminal.tty?() ->
        with_quieted_logger(fn ->
          case Terminal.enter_raw() do
            {:ok, saved} ->
              try do
                banner(state)
                raw_loop(state)
              after
                Terminal.restore(saved)
              end

              :ok

            {:error, reason} ->
              banner(state)
              raw_mode_warning(state, reason)
              legacy_loop(state)
          end
        end)

      true ->
        banner(state)
        legacy_loop(state)
    end
  end

  # Logger output interleaves badly with our raw-mode redraws: a stray
  # `[warning] ...` line from another app (MDEx NIF load, telemetry, etc.)
  # can overwrite the prompt. We raise the primary_config level to `:error`
  # for the duration of the REPL session, and restore it on exit.
  defp with_quieted_logger(fun) do
    prev = Logger.level()

    try do
      _ = Logger.configure(level: :error)
      fun.()
    after
      _ = Logger.configure(level: prev)
    end
  end

  defp raw_mode_warning(state, reason) do
    render_info(
      state,
      "(raw-mode unavailable: #{inspect(reason)}; arrows and Ctrl+R will not work -- " <>
        "falling back to line-mode input)"
    )
  end

  # ==========================================================================
  # Raw-mode key loop
  # ==========================================================================

  defp raw_loop(state) do
    prompt = prompt_for(state)
    Render.redraw(state.editor, state.n, state.theme, prompt: prompt)
    raw_loop(state, prompt)
  end

  defp raw_loop(%__MODULE__{running: false} = state, _prompt), do: save_and_bye(state)

  defp raw_loop(state, prompt) do
    key = Terminal.read_key()

    cond do
      key == :eof ->
        Render.newline()
        save_and_bye(state)

      key == {:ctrl, ?L} ->
        Render.clear_screen()
        Render.redraw(state.editor, state.n, state.theme, prompt: prompt)
        raw_loop(state, prompt)

      key == {:ctrl, ?R} ->
        state = run_search(state, prompt)
        raw_loop(state, prompt_for(state))

      key == :up ->
        state = history_prev(state)
        Render.redraw(state.editor, state.n, state.theme, prompt: prompt)
        raw_loop(state, prompt)

      key == :down ->
        state = history_next(state)
        Render.redraw(state.editor, state.n, state.theme, prompt: prompt)
        raw_loop(state, prompt)

      key == :tab ->
        state = handle_tab(state)
        Render.redraw(state.editor, state.n, state.theme, prompt: prompt)
        raw_loop(state, prompt)

      true ->
        handle_editor_key(state, key, prompt)
    end
  end

  defp handle_editor_key(state, key, prompt) do
    case LineEditor.handle(state.editor, key) do
      {:cont, ed} ->
        state = %{state | editor: ed}
        Render.redraw(state.editor, state.n, state.theme, prompt: prompt)
        raw_loop(state, prompt)

      {:signal, :submit, ed} ->
        state = %{state | editor: ed}
        Render.newline()
        state = submit(state, ed.buffer)
        if state.running, do: raw_loop(state), else: save_and_bye(state)

      {:signal, :abort, ed} ->
        Render.newline()
        render_info(state, "(aborted)")
        state = %{state | editor: ed, input_buffer: []}
        raw_loop(state)

      {:signal, :cancel, ed} ->
        state = %{state | editor: ed}
        Render.redraw(state.editor, state.n, state.theme, prompt: prompt)
        raw_loop(state, prompt)

      {:signal, :eof, _ed} ->
        Render.newline()
        save_and_bye(state)
    end
  end

  # -- History navigation ---------------------------------------------------

  defp history_prev(state) do
    draft = state.editor.buffer

    case History.prev(state.history, draft) do
      {:ok, entry, history} ->
        %{state | history: history, editor: LineEditor.set_buffer(state.editor, entry)}

      :at_top ->
        state
    end
  end

  defp history_next(state) do
    case History.next(state.history) do
      {:ok, entry, history} ->
        %{state | history: history, editor: LineEditor.set_buffer(state.editor, entry)}

      :at_bottom ->
        state
    end
  end

  # -- Tab completion --------------------------------------------------------

  defp handle_tab(state) do
    ed = state.editor

    case Cure.REPL.Completer.complete(ed.buffer, ed.cursor) do
      :none ->
        state

      {:unique, text} ->
        %{state | editor: LineEditor.set_buffer(ed, text)}

      {:partial, common, candidates} ->
        Render.newline()
        render_info(state, "  " <> Enum.join(candidates, "   "))
        new_text = apply_common(ed.buffer, ed.cursor, common)
        %{state | editor: LineEditor.set_buffer(ed, new_text)}
    end
  end

  defp apply_common(buffer, cursor, common) do
    left = String.slice(buffer, 0, cursor)
    right = String.slice(buffer, cursor..-1//1) || ""

    new_left =
      case Regex.run(~r/^(.*?)([\w:.\/~-]*)$/u, left, capture: :all_but_first) do
        [prefix, _token] -> prefix <> common
        _ -> left <> common
      end

    new_left <> right
  end

  # -- Ctrl+R search loop ----------------------------------------------------

  defp run_search(state, prompt) do
    original = state.editor.buffer
    s = Search.new(original)
    search_loop(state, s, prompt)
  end

  defp search_loop(state, s, prompt) do
    Render.redraw(state.editor, state.n, state.theme, prompt: prompt)
    Render.draw_search_status(Search.status(s, state.theme), state.theme)

    case Terminal.read_key() do
      :eof ->
        Render.clear_helpers()
        %{state | editor: LineEditor.set_buffer(state.editor, s.original)}

      key ->
        case Search.handle(s, key, state.history) do
          {:continue, s2} ->
            ed2 = LineEditor.set_buffer(state.editor, s2.match || s2.needle)
            search_loop(%{state | editor: ed2}, s2, prompt)

          {:accept, text} ->
            Render.clear_helpers()
            %{state | editor: LineEditor.set_buffer(state.editor, text)}

          {:accept_and_key, text, key} ->
            Render.clear_helpers()
            ed = LineEditor.set_buffer(state.editor, text)

            case LineEditor.handle(ed, key) do
              {:cont, ed2} -> %{state | editor: ed2}
              _ -> %{state | editor: ed}
            end

          {:cancel, text} ->
            Render.clear_helpers()
            %{state | editor: LineEditor.set_buffer(state.editor, text)}
        end
    end
  end

  # -- Submission -----------------------------------------------------------

  defp submit(state, line) do
    state = %{state | editor: LineEditor.new(mode: state.mode)}

    cond do
      line == "" and state.input_buffer == [] ->
        state

      line == "" or line == ";;" ->
        dispatch_buffer(state)

      state.input_buffer == [] and starts_with_colon?(line) ->
        state
        |> Map.put(:history, History.append(state.history, line))
        |> handle_meta(line)

      true ->
        new_state = %{state | input_buffer: state.input_buffer ++ [line]}
        joined = Enum.join(new_state.input_buffer, "\n")

        if classify_input(line) == :continue or not balanced?(joined) do
          new_state
        else
          dispatch_buffer(new_state)
        end
    end
  end

  defp dispatch_buffer(%__MODULE__{input_buffer: []} = state), do: state

  defp dispatch_buffer(%__MODULE__{input_buffer: buf} = state) do
    src = buf |> Enum.join("\n") |> String.trim()

    if src == "" do
      %{state | input_buffer: []}
    else
      state
      |> Map.put(:history, History.append(state.history, src))
      |> Map.put(:input_buffer, [])
      |> evaluate(src)
      |> Map.update!(:n, &(&1 + 1))
    end
  end

  # ==========================================================================
  # Legacy line-mode fallback
  # ==========================================================================

  defp legacy_loop(%__MODULE__{running: false} = state), do: save_and_bye(state)

  defp legacy_loop(state) do
    prompt = if state.input_buffer == [], do: "cure(#{state.n})> ", else: "       ... "

    case IO.gets(prompt) do
      :eof -> save_and_bye(state)
      {:error, _} -> save_and_bye(state)
      raw -> raw |> to_string() |> String.trim_trailing() |> legacy_process_line(state)
    end
  end

  defp legacy_process_line(line, state) do
    state = submit(state, line)
    if state.running, do: legacy_loop(state), else: save_and_bye(state)
  end

  # ==========================================================================
  # Evaluation
  # ==========================================================================

  defp evaluate(state, src) do
    mod_name = "Repl.M#{state.n}"
    uses = Enum.map(state.uses, &"  use #{&1}\n") |> Enum.join()

    source = """
    mod #{mod_name}
    #{uses}  fn main() -> Any = #{src}
    """

    case Cure.Compiler.compile_and_load(source, emit_events: false) do
      {:ok, module} ->
        try do
          result = module.main()
          render_value(state, result)
        catch
          kind, reason -> render_error(state, "#{kind}: #{inspect(reason)}")
        end

        state

      {:error, reason} ->
        render_error(state, format_error(reason))
        state
    end
  end

  # ==========================================================================
  # Meta-commands
  # ==========================================================================

  defp handle_meta(state, ":quit"), do: bye(state)
  defp handle_meta(state, ":q"), do: bye(state)
  defp handle_meta(state, ":exit"), do: bye(state)
  defp handle_meta(state, ":help"), do: print_help(state)
  defp handle_meta(state, ":h"), do: print_help(state)

  defp handle_meta(state, ":clear") do
    Render.clear_screen()
    state
  end

  defp handle_meta(state, ":env") do
    if state.uses == [] do
      render_info(state, "(no imports; no user bindings)")
    else
      Enum.each(state.uses, &render_info(state, "  use " <> &1))
    end

    state
  end

  defp handle_meta(state, ":reset") do
    render_info(state, "REPL state reset.")
    %{state | n: 1, loaded: [], uses: [], holes: [], input_buffer: []}
  end

  defp handle_meta(state, ":holes") do
    case state.holes do
      [] ->
        render_info(state, "(no holes recorded)")

      holes ->
        Enum.each(holes, fn {label, goal, ctx} ->
          render_info(state, Holes.render(label, goal, ctx))
        end)
    end

    state
  end

  defp handle_meta(state, ":reload") do
    render_info(state, "Reloading #{length(state.loaded)} file(s)")

    Enum.each(state.loaded, fn path ->
      case File.read(path) do
        {:ok, src} ->
          case Cure.Compiler.compile_and_load(src, file: path, emit_events: false) do
            {:ok, mod} -> render_info(state, "  #{path} -> #{mod}")
            {:error, reason} -> render_error(state, "  #{path}: #{format_error(reason)}")
          end

        {:error, reason} ->
          render_error(state, "  #{path}: #{reason}")
      end
    end)

    state
  end

  defp handle_meta(state, ":history"), do: cmd_history(state, 20)

  defp handle_meta(state, ":history " <> rest) do
    case Integer.parse(String.trim(rest)) do
      {n, _} when n > 0 -> cmd_history(state, n)
      _ -> cmd_history(state, 20)
    end
  end

  defp handle_meta(state, ":search " <> needle), do: cmd_search(state, String.trim(needle))
  defp handle_meta(state, ":save " <> path), do: cmd_save(state, String.trim(path))
  defp handle_meta(state, ":edit"), do: cmd_edit(state)
  defp handle_meta(state, ":edit " <> _), do: cmd_edit(state)
  defp handle_meta(state, ":time " <> expr), do: cmd_time(state, expr)
  defp handle_meta(state, ":bench " <> rest), do: cmd_bench(state, rest)
  defp handle_meta(state, ":ast " <> expr), do: cmd_ast(state, expr)
  defp handle_meta(state, ":theme " <> name), do: cmd_theme(state, String.trim(name))
  defp handle_meta(state, ":mode " <> m), do: cmd_mode(state, String.trim(m))
  defp handle_meta(state, ":color " <> v), do: cmd_color(state, String.trim(v))

  defp handle_meta(state, ":t " <> expr), do: cmd_type(state, expr)
  defp handle_meta(state, ":type " <> expr), do: cmd_type(state, expr)
  defp handle_meta(state, ":doc " <> name), do: cmd_doc(state, name)
  defp handle_meta(state, ":effects " <> expr), do: cmd_effects(state, expr)
  defp handle_meta(state, ":load " <> path), do: cmd_load(state, String.trim(path))
  defp handle_meta(state, ":use " <> mod), do: cmd_use(state, String.trim(mod))
  defp handle_meta(state, ":fmt " <> expr), do: cmd_fmt(state, expr)

  defp handle_meta(state, other) do
    render_error(state, "unknown command: #{other}. Try :help.")
    state
  end

  defp cmd_type(state, expr) do
    case Cure.quote(expr) do
      {:ok, ast} ->
        case Checker.infer_expr(ast) do
          {:ok, type} -> render_info(state, "#{expr} : #{Cure.Types.Type.display(type)}")
          {:error, reason} -> render_error(state, format_error(reason))
        end

      {:error, reason} ->
        render_error(state, format_error(reason))
    end

    state
  end

  defp cmd_doc(state, name) do
    render_info(state, "(doc lookup for `#{name}` -- requires a loaded module; not yet implemented)")
    state
  end

  defp cmd_effects(state, expr) do
    case Cure.quote(expr) do
      {:ok, ast} ->
        env = Cure.Types.Env.new()
        effects = Cure.Types.Effects.infer_effects(ast, env)

        if Enum.empty?(effects) do
          render_info(state, "#{expr} :: (pure)")
        else
          eff_str =
            effects
            |> Enum.sort()
            |> Enum.map_join(", ", &Cure.Types.Type.display_effect/1)

          render_info(state, "#{expr} :: ! #{eff_str}")
        end

      {:error, reason} ->
        render_error(state, format_error(reason))
    end

    state
  end

  defp cmd_load(state, path) do
    case File.read(path) do
      {:ok, src} ->
        case Cure.Compiler.compile_and_load(src, file: path, emit_events: false) do
          {:ok, mod} ->
            render_info(state, "loaded #{path} -> #{mod}")
            %{state | loaded: Enum.uniq([path | state.loaded])}

          {:error, reason} ->
            render_error(state, format_error(reason))
            state
        end

      {:error, reason} ->
        render_error(state, "cannot read #{path}: #{reason}")
        state
    end
  end

  defp cmd_use(state, mod) do
    render_info(state, "imported #{mod}")
    %{state | uses: Enum.uniq([mod | state.uses])}
  end

  defp cmd_fmt(state, expr) do
    case Cure.quote(expr) do
      {:ok, ast} -> render_info(state, Printer.quoted_to_string(ast))
      {:error, reason} -> render_error(state, format_error(reason))
    end

    state
  end

  defp cmd_history(state, n) do
    state.history
    |> History.tail(n)
    |> Enum.with_index(1)
    |> Enum.each(fn {entry, idx} ->
      Render.write_line(
        state.theme.dim <>
          String.pad_leading(Integer.to_string(idx), 4) <>
          state.theme.reset <>
          "  " <>
          Cure.REPL.Highlight.highlight(entry)
      )
    end)

    state
  end

  defp cmd_search(state, ""), do: state

  defp cmd_search(state, needle) do
    hits = History.grep(state.history, needle)

    case hits do
      [] ->
        render_info(state, "(no matches for #{inspect(needle)})")

      _ ->
        Enum.each(hits, &Render.write_line(Cure.REPL.Highlight.highlight(&1)))
    end

    state
  end

  defp cmd_save(state, ""), do: state

  defp cmd_save(state, path) do
    content = state.history |> History.entries() |> Enum.join("\n")

    case File.write(path, content) do
      :ok -> render_info(state, "saved session to #{path}")
      {:error, reason} -> render_error(state, "cannot write #{path}: #{reason}")
    end

    state
  end

  defp cmd_edit(state) do
    editor = System.get_env("VISUAL") || System.get_env("EDITOR") || "vi"
    tmp = Path.join(System.tmp_dir!(), "cure-repl-#{System.unique_integer([:positive])}.cure")
    File.write!(tmp, Enum.join(state.input_buffer, "\n"))

    _ = System.cmd(editor, [tmp], into: IO.stream(:stdio, :line))

    new_buffer =
      case File.read(tmp) do
        {:ok, content} -> String.split(content, "\n")
        _ -> state.input_buffer
      end

    _ = File.rm(tmp)
    %{state | input_buffer: new_buffer}
  end

  defp cmd_time(state, expr) do
    expr = String.trim(expr)
    t0 = System.monotonic_time(:microsecond)
    state = evaluate(state, expr)
    t1 = System.monotonic_time(:microsecond)
    render_info(state, "elapsed: #{format_microseconds(t1 - t0)}")
    state
  end

  defp cmd_bench(state, rest) do
    case Regex.run(~r/^(.*?)\s+(\d+)$/, String.trim(rest), capture: :all_but_first) do
      [expr, n_str] -> bench_run(state, expr, String.to_integer(n_str))
      _ -> bench_run(state, String.trim(rest), 1_000)
    end
  end

  defp bench_run(state, "", _n), do: state

  defp bench_run(state, expr, n) do
    source = """
    mod Repl.Bench#{state.n}
      fn main() -> Any = #{expr}
    """

    case Cure.Compiler.compile_and_load(source, emit_events: false) do
      {:ok, module} ->
        times =
          for _ <- 1..n do
            t0 = System.monotonic_time(:microsecond)
            _ = module.main()
            System.monotonic_time(:microsecond) - t0
          end

        sorted = Enum.sort(times)
        min = List.first(sorted)
        max = List.last(sorted)
        avg = div(Enum.sum(sorted), n)
        p95 = Enum.at(sorted, trunc(n * 0.95))

        render_info(
          state,
          "n=#{n}  min=#{format_microseconds(min)}  avg=#{format_microseconds(avg)}  p95=#{format_microseconds(p95)}  max=#{format_microseconds(max)}"
        )

      {:error, reason} ->
        render_error(state, format_error(reason))
    end

    state
  end

  defp cmd_ast(state, expr) do
    case Cure.quote(expr) do
      {:ok, ast} ->
        pretty = inspect(ast, pretty: true, limit: :infinity)
        Render.write_line(pretty)

      {:error, reason} ->
        render_error(state, format_error(reason))
    end

    state
  end

  defp cmd_theme(state, name) when name in ["dark", "light", "mono"] do
    theme = Theme.for_name(name)
    render_info(%{state | theme: theme}, "theme: #{name}")
    %{state | theme: theme, color: theme.name != :mono}
  end

  defp cmd_theme(state, other) do
    render_error(state, "unknown theme #{inspect(other)} (expected: dark, light, mono)")
    state
  end

  defp cmd_mode(state, name) when name in ["emacs", "vi"] do
    mode = if name == "vi", do: :vi_insert, else: :emacs
    render_info(state, "mode: #{name}")
    %{state | mode: mode, editor: %{state.editor | mode: mode}}
  end

  defp cmd_mode(state, other) do
    render_error(state, "unknown mode #{inspect(other)} (expected: emacs, vi)")
    state
  end

  defp cmd_color(state, "on") do
    theme = Theme.for_name(:dark)
    state = %{state | theme: theme, color: true}
    render_info(state, "colour: on")
    state
  end

  defp cmd_color(state, "off") do
    theme = Theme.for_name(:mono)
    state = %{state | theme: theme, color: false}
    Render.write_line("colour: off")
    state
  end

  defp cmd_color(state, other) do
    render_error(state, "expected :color on|off, got #{inspect(other)}")
    state
  end

  defp print_help(state) do
    md = help_markdown()

    # We deliberately do NOT pipe through `Marcli.render/2` here: Marcli
    # depends on MDEx, whose Rust NIF cannot be loaded from inside an
    # escript archive (the dynamic loader sees a path that doesn't exist
    # on disk and emits `[warning] The on_load function ... returned
    # {:error, {:load_failed, ...}}`). `Cure.REPL.Markdown.render/2`
    # covers the subset of Markdown our `:help` uses and is pure Elixir.
    Render.write_line(Markdown.render(md, state.theme))
    state
  end

  defp help_markdown do
    """
    # Cure REPL

    ## Meta-commands

    - `:t` / `:type expr` - show the inferred type of `expr`
    - `:doc name` - show the docstring of `name`
    - `:effects expr` - show the inferred effects of `expr`
    - `:load path` - compile a `.cure` file and bring its bindings in
    - `:reload` - reload all previously loaded files
    - `:use Mod` - bring a module's exports into scope
    - `:holes` - list holes from the last evaluated expression
    - `:env` - list every binding currently in scope
    - `:reset` - forget all bindings, fresh session
    - `:fmt expr` - pretty-print `expr`
    - `:history [n]` - print the last `n` (default 20) entries
    - `:search term` - non-interactive history grep
    - `:save path` - write the session transcript to `path`
    - `:edit` - open $EDITOR on the current input buffer
    - `:time expr` - evaluate and report elapsed time
    - `:bench expr [n]` - run `expr` `n` times (default 1000), report stats
    - `:ast expr` - dump parsed AST
    - `:theme dark|light|mono` - switch colour theme
    - `:mode emacs|vi` - switch editing mode
    - `:color on|off` - toggle colour output
    - `:clear` - clear the screen
    - `:help` / `:h` - show this help
    - `:quit` / `:q` / `:exit` - leave the REPL

    ## Key bindings (emacs mode)

    - `Left` / `Right` - move cursor
    - `Ctrl+A` / `Home` - beginning of line
    - `Ctrl+E` / `End` - end of line
    - `Alt+B` / `Alt+F` / `Ctrl+Left` / `Ctrl+Right` - word-wise movement
    - `Up` / `Down` - history navigation
    - `Ctrl+R` - incremental reverse history search
    - `Ctrl+K` / `Ctrl+U` - kill to end / start
    - `Ctrl+W` - kill previous word
    - `Ctrl+Y` - yank
    - `Ctrl+T` - transpose chars
    - `Ctrl+L` - clear screen
    - `Ctrl+D` - EOF on empty line, delete char otherwise
    - `Ctrl+C` - abort current input
    - `Tab` - completion for meta-commands, paths, modules, keywords
    - `Enter` - submit (or continue if the input looks incomplete)
    - `;;` on its own line - force submit a multi-line buffer

    ## Vi mode
    Press `Esc` to toggle between insert and normal mode. In normal mode:
    `h/j/k/l`, `w`/`b`/`e`, `0`/`^`/`$`, `i`/`a`/`I`/`A`, `x`, `D`, `C`,
    `u` (undo), `Ctrl+R` (redo).
    """
  end

  # ==========================================================================
  # Rendering helpers
  # ==========================================================================

  defp prompt_for(state) do
    case state.input_buffer do
      [] -> Render.prompt(state.n, state.theme, state.mode)
      _ -> Render.continuation(state.n, state.theme)
    end
  end

  defp banner(state) do
    if state.color do
      Render.write_line(
        state.theme.info <>
          "Cure REPL v#{Cure.version()}" <>
          state.theme.reset <>
          state.theme.dim <>
          "  (type :help for commands, :quit to exit)" <>
          state.theme.reset
      )
    else
      Render.write_line("Cure REPL v#{Cure.version()} (type :help for commands, :quit to exit)")
    end
  end

  defp render_value(state, value) do
    arrow = state.theme.result_arrow <> "=> " <> state.theme.reset
    body = inspect(value, pretty: true, limit: :infinity, syntax_colors: syntax_colors(state))
    Render.write_line(arrow <> body)
  end

  defp syntax_colors(%__MODULE__{color: true}) do
    [
      atom: :cyan,
      binary: :green,
      boolean: :magenta,
      nil: :magenta,
      number: :yellow,
      string: :green
    ]
  end

  defp syntax_colors(_), do: []

  defp render_info(state, msg) do
    if state.color do
      Render.write_line(state.theme.info <> msg <> state.theme.reset)
    else
      Render.write_line(msg)
    end
  end

  defp render_error(state, msg) do
    body = state.theme.error <> "error: " <> msg <> state.theme.reset
    IO.binwrite(:stderr, body <> "\n")
  end

  # ==========================================================================
  # Helpers
  # ==========================================================================

  defp starts_with_colon?(<<":", _::binary>>), do: true
  defp starts_with_colon?(_), do: false

  defp classify_input(line) do
    cond do
      String.ends_with?(line, "do") -> :continue
      String.ends_with?(line, "->") -> :continue
      String.ends_with?(line, "=") -> :continue
      String.ends_with?(line, "|") -> :continue
      String.ends_with?(line, "then") -> :continue
      String.ends_with?(line, "else") -> :continue
      String.ends_with?(line, ",") -> :continue
      String.ends_with?(line, "(") -> :continue
      true -> :complete
    end
  end

  @doc false
  def __classify_input__(line), do: classify_input(line)

  defp balanced?(src) do
    {p, b, c} =
      src
      |> String.graphemes()
      |> Enum.reduce({0, 0, 0}, fn g, {p, b, c} ->
        case g do
          "(" -> {p + 1, b, c}
          ")" -> {p - 1, b, c}
          "[" -> {p, b + 1, c}
          "]" -> {p, b - 1, c}
          "{" -> {p, b, c + 1}
          "}" -> {p, b, c - 1}
          _ -> {p, b, c}
        end
      end)

    p <= 0 and b <= 0 and c <= 0
  end

  defp resolve_theme(opts) do
    case Keyword.get(opts, :theme, :auto) do
      :auto -> if Theme.disabled?(), do: Theme.for_name(:mono), else: Theme.default()
      name -> Theme.for_name(name)
    end
  end

  defp resolve_mode(opts) do
    case Keyword.get(opts, :mode) do
      :vi -> :vi_insert
      :vi_insert -> :vi_insert
      :emacs -> :emacs
      nil -> if System.get_env("CURE_REPL_MODE") == "vi", do: :vi_insert, else: :emacs
      _ -> :emacs
    end
  end

  defp default_history_path do
    case System.user_home() do
      nil -> ".cure_history"
      home -> Path.join(home, ".cure_history")
    end
  end

  defp save_and_bye(%__MODULE__{} = state) do
    _ = History.persist(state.history)
    Render.write_line("")
    render_info(state, "Bye.")
    :ok
  end

  defp save_and_bye(_), do: :ok

  # Mark the REPL as done; the outer loop is responsible for `save_and_bye/1`
  # so we don't print the farewell twice.
  defp bye(state), do: %{state | running: false}

  defp format_error(reason) when is_binary(reason), do: reason

  defp format_error({stage, msg, _opts}) when is_atom(stage) and is_binary(msg) do
    "#{stage}: #{msg}"
  end

  defp format_error(other), do: inspect(other)

  @doc false
  def __format_error__(reason), do: format_error(reason)

  defp format_microseconds(us) when us < 1_000, do: "#{us} us"

  defp format_microseconds(us) when us < 1_000_000,
    do: :io_lib.format("~.2f ms", [us / 1_000]) |> IO.iodata_to_binary()

  defp format_microseconds(us),
    do: :io_lib.format("~.2f s", [us / 1_000_000]) |> IO.iodata_to_binary()
end
