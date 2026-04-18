defmodule Cure.REPL do
  @moduledoc """
  Interactive REPL for Cure.

  Replaces the inline single-line REPL that lived in `Cure.CLI` with a
  proper read-eval-print loop supporting multi-line input, meta-commands,
  history, and a long-lived synthetic module per session.

  ## Meta-commands

      :t expr        -- show the inferred type of `expr`
      :doc name      -- show the docstring of a function or type
      :effects expr  -- show the inferred effects of `expr`
      :load path     -- compile a `.cure` file and bring its bindings into scope
      :reload        -- reload all previously loaded files
      :use Mod       -- bring a module's exports into scope
      :holes         -- list all holes from the last evaluated expression
      :env           -- list every binding currently in scope
      :reset         -- forget all bindings and start a fresh session
      :fmt expr      -- pretty-print `expr` via `Cure.Compiler.Printer`
      :help          -- show this help
      :quit          -- exit the REPL

  ## Multi-line input

  Input ends when:

  - The current line is blank (empty after trimming), *or*
  - The current line is a single `;;` (Erlang-style hard terminator).

  ## History

  Persisted to `~/.cure_history`. Lines beginning with `:` are kept;
  blank lines are not.
  """

  alias Cure.Compiler.Printer
  alias Cure.Types.{Checker, Holes}

  defstruct n: 1,
            loaded: [],
            uses: [],
            holes: [],
            history: [],
            history_path: nil,
            input_buffer: []

  @type state :: %__MODULE__{}

  @doc "Start the REPL loop with default options."
  @spec start(keyword()) :: :ok
  def start(opts \\ []) do
    history_path = Keyword.get(opts, :history_path, default_history_path())
    state = %__MODULE__{history_path: history_path, history: load_history(history_path)}
    info("Cure REPL v#{Cure.version()} (type :help for commands, :quit to exit)")
    loop(state)
  end

  # -- Loop -------------------------------------------------------------------

  defp loop(state) do
    prompt = if state.input_buffer == [], do: "cure(#{state.n})> ", else: "       ... "

    case IO.gets(prompt) do
      :eof ->
        save_history(state)
        :ok

      {:error, _} ->
        save_history(state)
        :ok

      raw ->
        line = raw |> to_string() |> String.trim_trailing()
        process_line(line, state)
    end
  end

  defp process_line("", %__MODULE__{input_buffer: []} = state), do: loop(state)

  defp process_line("", state), do: dispatch_buffer(state)
  defp process_line(";;", state), do: dispatch_buffer(state)

  defp process_line(line, %__MODULE__{input_buffer: []} = state)
       when binary_part(line, 0, 1) == ":" do
    state
    |> Map.put(:history, [line | state.history])
    |> handle_meta(line)
    |> loop()
  end

  defp process_line(line, %__MODULE__{input_buffer: buf} = state) do
    new_state = %{state | input_buffer: buf ++ [line]}

    case classify_input(line) do
      :complete -> dispatch_buffer(new_state)
      :continue -> loop(new_state)
    end
  end

  defp classify_input(line) do
    # Heuristic: line ending with one of these tokens suggests continuation.
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

  defp dispatch_buffer(%__MODULE__{input_buffer: buf} = state) do
    src = buf |> Enum.join("\n") |> String.trim()

    if src == "" do
      loop(state)
    else
      state
      |> Map.put(:history, [src | state.history])
      |> Map.put(:input_buffer, [])
      |> evaluate(src)
      |> Map.update!(:n, &(&1 + 1))
      |> loop()
    end
  end

  # -- Evaluation -------------------------------------------------------------

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
          IO.inspect(result, label: "=>")
        catch
          kind, reason -> error("#{kind}: #{inspect(reason)}")
        end

        state

      {:error, reason} ->
        error(format_error(reason))
        state
    end
  end

  # -- Meta-commands ----------------------------------------------------------

  defp handle_meta(state, ":quit"), do: bye(state)
  defp handle_meta(state, ":q"), do: bye(state)
  defp handle_meta(state, ":exit"), do: bye(state)
  defp handle_meta(state, ":help"), do: print_help(state)
  defp handle_meta(state, ":h"), do: print_help(state)

  defp handle_meta(state, ":env") do
    if state.uses == [] do
      info("(no imports; no user bindings)")
    else
      Enum.each(state.uses, &info("  use #{&1}"))
    end

    state
  end

  defp handle_meta(state, ":reset") do
    info("REPL state reset.")
    %{state | n: 1, loaded: [], uses: [], holes: [], input_buffer: []}
  end

  defp handle_meta(state, ":holes") do
    case state.holes do
      [] ->
        info("(no holes recorded)")

      holes ->
        Enum.each(holes, fn {label, goal, ctx} ->
          info(Holes.render(label, goal, ctx))
        end)
    end

    state
  end

  defp handle_meta(state, ":reload") do
    info("Reloading #{length(state.loaded)} file(s)")

    Enum.each(state.loaded, fn path ->
      case File.read(path) do
        {:ok, src} ->
          case Cure.Compiler.compile_and_load(src, file: path, emit_events: false) do
            {:ok, mod} -> info("  #{path} -> #{mod}")
            {:error, reason} -> error("  #{path}: #{format_error(reason)}")
          end

        {:error, reason} ->
          error("  #{path}: #{reason}")
      end
    end)

    state
  end

  defp handle_meta(state, ":t " <> expr), do: cmd_type(state, expr)
  defp handle_meta(state, ":type " <> expr), do: cmd_type(state, expr)
  defp handle_meta(state, ":doc " <> name), do: cmd_doc(state, name)
  defp handle_meta(state, ":effects " <> expr), do: cmd_effects(state, expr)
  defp handle_meta(state, ":load " <> path), do: cmd_load(state, String.trim(path))
  defp handle_meta(state, ":use " <> mod), do: cmd_use(state, String.trim(mod))
  defp handle_meta(state, ":fmt " <> expr), do: cmd_fmt(state, expr)

  defp handle_meta(state, other) do
    error("unknown command: #{other}. Try :help.")
    state
  end

  defp cmd_type(state, expr) do
    case Cure.quote(expr) do
      {:ok, ast} ->
        case Checker.infer_expr(ast) do
          {:ok, type} -> info("#{expr} : #{Cure.Types.Type.display(type)}")
          {:error, reason} -> error(format_error(reason))
        end

      {:error, reason} ->
        error(format_error(reason))
    end

    state
  end

  defp cmd_doc(state, name) do
    info("(doc lookup for `#{name}` -- requires a loaded module; not yet implemented)")
    state
  end

  defp cmd_effects(state, expr) do
    case Cure.quote(expr) do
      {:ok, ast} ->
        env = Cure.Types.Env.new()
        effects = Cure.Types.Effects.infer_effects(ast, env)

        if Enum.empty?(effects) do
          info("#{expr} :: (pure)")
        else
          eff_str =
            effects
            |> Enum.sort()
            |> Enum.map_join(", ", &Cure.Types.Type.display_effect/1)

          info("#{expr} :: ! #{eff_str}")
        end

      {:error, reason} ->
        error(format_error(reason))
    end

    state
  end

  defp cmd_load(state, path) do
    case File.read(path) do
      {:ok, src} ->
        case Cure.Compiler.compile_and_load(src, file: path, emit_events: false) do
          {:ok, mod} ->
            info("loaded #{path} -> #{mod}")
            %{state | loaded: Enum.uniq([path | state.loaded])}

          {:error, reason} ->
            error(format_error(reason))
            state
        end

      {:error, reason} ->
        error("cannot read #{path}: #{reason}")
        state
    end
  end

  defp cmd_use(state, mod) do
    info("imported #{mod}")
    %{state | uses: Enum.uniq([mod | state.uses])}
  end

  defp cmd_fmt(state, expr) do
    case Cure.quote(expr) do
      {:ok, ast} -> info(Printer.quoted_to_string(ast))
      {:error, reason} -> error(format_error(reason))
    end

    state
  end

  defp print_help(state) do
    IO.puts("""
    Cure REPL meta-commands:

      :t expr           Show the inferred type of `expr`.
      :doc name         Show the docstring of `name` (if loaded).
      :effects expr     Show the inferred effects of `expr`.
      :load path        Compile and load a `.cure` file.
      :reload           Reload every previously loaded file.
      :use Mod          Add `use Mod` to subsequent inputs.
      :holes            List holes recorded during the last evaluation.
      :env              List every loaded import.
      :reset            Forget bindings and start a fresh session.
      :fmt expr         Pretty-print `expr`.
      :help             Show this help.
      :quit | :q | :exit  Leave the REPL.

    Multi-line input ends with a blank line or a single `;;`.
    History is persisted to ~/.cure_history.
    """)

    state
  end

  @spec bye(state()) :: no_return()
  defp bye(state) do
    info("Bye.")
    save_history(state)
    System.halt(0)
  end

  # -- Helpers ----------------------------------------------------------------

  defp default_history_path do
    case System.user_home() do
      nil -> ".cure_history"
      home -> Path.join(home, ".cure_history")
    end
  end

  defp load_history(nil), do: []

  defp load_history(path) do
    case File.read(path) do
      {:ok, content} -> String.split(content, "\n", trim: true)
      _ -> []
    end
  end

  defp save_history(%__MODULE__{history_path: nil}), do: :ok

  defp save_history(%__MODULE__{history_path: path, history: history}) do
    text =
      history
      |> Enum.reverse()
      |> Enum.take(-1000)
      |> Enum.join("\n")

    File.write(path, text)
  end

  defp format_error(reason) when is_binary(reason), do: reason

  defp format_error({stage, msg, _opts}) when is_atom(stage) and is_binary(msg) do
    "#{stage}: #{msg}"
  end

  defp format_error(other), do: inspect(other)

  defp info(msg), do: IO.puts(msg)
  defp error(msg), do: IO.puts(:stderr, "error: #{msg}")

  # -- Internal helpers exposed for testing -----------------------------------

  @doc false
  def __classify_input__(line), do: classify_input(line)

  @doc false
  def __format_error__(reason), do: format_error(reason)
end
