defmodule Cure.Compiler do
  @moduledoc """
  Compiler orchestrator for the Cure programming language.

  Chains together the full compilation pipeline:

      source -> Lexer -> Parser -> [Checker] -> Codegen -> BeamWriter -> .beam

  The type checker runs before codegen by default; set `check_types: false`
  (or pass `--no-type-check` to the CLI) to opt out.

  Emits pipeline events at each stage boundary.

  ## Usage

      # Compile a file
      {:ok, module, warnings} = Cure.Compiler.compile_file("hello.cure")

      # Compile a string
      {:ok, module, warnings} = Cure.Compiler.compile_string(source, file: "hello.cure")

      # Compile and load into VM (for testing / REPL)
      {:ok, module} = Cure.Compiler.compile_and_load(source)
  """

  alias Cure.Compiler.{Lexer, Parser, Codegen, BeamWriter}
  alias Cure.Types.Checker
  alias Cure.Optimizer

  @doc """
  Compile a `.cure` source file to BEAM bytecode.

  Reads the file, runs the full pipeline, and writes a `.beam` file
  to the output directory.

  ## Options

  - `:output_dir` -- directory for `.beam` output (default: `"_build/cure/ebin"`)
  - `:emit_events` -- whether to emit pipeline events (default: `true`)
  - `:check_types` -- whether to run the type checker (default: `true`).
    Set to `false` to skip type checking.
  """
  @spec compile_file(String.t(), keyword()) ::
          {:ok, module(), list()} | {:error, term()}
  def compile_file(path, opts \\ []) do
    case File.read(path) do
      {:ok, source} ->
        opts = Keyword.put_new(opts, :file, path)
        compile_string(source, opts)

      {:error, reason} ->
        {:error, {:file_read_error, path, reason}}
    end
  end

  @doc """
  Compile a Cure source string to BEAM bytecode and write to disk.

  ## Options

  - `:file` -- filename for error messages (default: `"nofile"`)
  - `:output_dir` -- directory for `.beam` output (default: `"_build/cure/ebin"`)
  - `:emit_events` -- whether to emit pipeline events (default: `true`)
  """
  @spec compile_string(String.t(), keyword()) ::
          {:ok, module(), list()} | {:error, term()}
  def compile_string(source, opts \\ []) do
    file = Keyword.get(opts, :file, "nofile")
    output_dir = Keyword.get(opts, :output_dir, "_build/cure/ebin")
    emit? = Keyword.get(opts, :emit_events, true)
    check? = Keyword.get(opts, :check_types, true)

    optimize? = Keyword.get(opts, :optimize, false)
    monomorph? = Keyword.get(opts, :monomorphise, true)
    monomorph_budget = Keyword.get(opts, :monomorph_budget, 16)
    declared_phases = Keyword.get(opts, :declared_phases)

    optimize_opts = [
      monomorphise: monomorph?,
      monomorph_budget: monomorph_budget,
      emit_events: emit?,
      file: file
    ]

    with {:ok, tokens} <- lex(source, file, emit?),
         {:ok, ast} <- parse(tokens, file, emit?),
         {:ok, _} <- maybe_check(ast, file, emit?, check?),
         {:ok, ast} <- maybe_optimize(ast, optimize?, optimize_opts),
         {:ok, forms} <- codegen(ast, file, emit?, output_dir, declared_phases) do
      # Callback-mode FSMs, typed actors, supervisors, and
      # applications are already compiled, loaded, *and* persisted to
      # `<output_dir>/<mod>.beam` by the codegen step (the dispatcher
      # passed `output_dir` through to the respective compilers). In
      # that case `forms` is one of the `{:callback_mode, module}`,
      # `{:actor, module}`, `{:supervisor, module}`, or `{:app,
      # module}` markers, and there is nothing left for this
      # orchestrator to write.
      case forms do
        {:callback_mode, mod_atom} ->
          {:ok, mod_atom, []}

        {:actor, mod_atom} ->
          {:ok, mod_atom, []}

        {:supervisor, mod_atom} ->
          {:ok, mod_atom, []}

        {:app, mod_atom} ->
          {:ok, mod_atom, []}

        forms when is_list(forms) ->
          write_beam_forms(forms, output_dir, emit?, file)
      end
    end
  end

  # `BeamWriter.compile_forms/2` returns `{:error, errors, warnings}` (3-tuple)
  # on lint/compile failures, but the public `compile_string/2`,
  # `compile_file/2`, and `compile_and_load/2` contracts are `{:ok, ...}` or
  # `{:error, reason}` (2-tuple). Normalize the BEAM-writer failure here so
  # downstream consumers (CLI, `cure check`, `mix cure.check.examples`, test
  # suites) can rely on the 2-tuple shape without `CaseClauseError` crashes.
  defp write_beam_forms(forms, output_dir, emit?, file) do
    case BeamWriter.compile_forms(forms) do
      {:ok, module, binary, warnings} ->
        case BeamWriter.write_beam(module, binary, output_dir, emit_events: emit?, file: file) do
          :ok -> {:ok, module, warnings}
          {:error, _} = err -> err
        end

      {:error, errors, _warnings} ->
        {:error, {:beam_lint_error, errors}}
    end
  end

  @doc """
  Compile a Cure source string and load the resulting module into the VM.

  Does not write a `.beam` file to disk. Useful for testing and REPL.
  """
  @spec compile_and_load(String.t(), keyword()) ::
          {:ok, module()} | {:error, term()}
  def compile_and_load(source, opts \\ []) do
    file = Keyword.get(opts, :file, "nofile")
    emit? = Keyword.get(opts, :emit_events, false)
    check? = Keyword.get(opts, :check_types, true)

    optimize? = Keyword.get(opts, :optimize, false)
    monomorph? = Keyword.get(opts, :monomorphise, true)
    monomorph_budget = Keyword.get(opts, :monomorph_budget, 16)
    declared_phases = Keyword.get(opts, :declared_phases)

    optimize_opts = [
      monomorphise: monomorph?,
      monomorph_budget: monomorph_budget,
      emit_events: emit?,
      file: file
    ]

    with {:ok, tokens} <- lex(source, file, emit?),
         {:ok, ast} <- parse(tokens, file, emit?),
         {:ok, _} <- maybe_check(ast, file, emit?, check?),
         {:ok, ast} <- maybe_optimize(ast, optimize?, optimize_opts),
         {:ok, forms} <- codegen(ast, file, emit?, nil, declared_phases) do
      # compile_and_load/2 intentionally does NOT persist bytecode to
      # disk -- it only loads into the current VM -- so we pass `nil`
      # for `output_dir` and the container compilers skip their
      # `BeamWriter.write_beam/4` calls.
      case forms do
        {:callback_mode, mod_atom} ->
          {:ok, mod_atom}

        {:actor, mod_atom} ->
          {:ok, mod_atom}

        {:supervisor, mod_atom} ->
          {:ok, mod_atom}

        {:app, mod_atom} ->
          {:ok, mod_atom}

        forms when is_list(forms) ->
          BeamWriter.compile_and_load(forms)
      end
    end
  end

  # -- Pipeline Steps ----------------------------------------------------------

  defp lex(source, file, emit?) do
    case Lexer.tokenize(source, file: file, emit_events: emit?) do
      {:ok, tokens} -> {:ok, tokens}
      {:error, reason} -> {:error, {:lex_error, reason}}
    end
  end

  defp parse(tokens, file, emit?) do
    case Parser.parse(tokens, file: file, emit_events: emit?) do
      {:ok, ast} -> {:ok, ast}
      {:error, errors} -> {:error, {:parse_error, errors}}
    end
  end

  defp maybe_optimize(ast, false, _opts), do: {:ok, ast}

  defp maybe_optimize(ast, true, opts) do
    {:ok, optimized, _stats} = Optimizer.optimize(ast, opts)
    {:ok, optimized}
  end

  defp maybe_check(_ast, _file, _emit?, false), do: {:ok, :skipped}

  defp maybe_check(ast, file, emit?, true) do
    case Checker.check_module(ast, file: file, emit_events: emit?) do
      {:ok, _} = ok -> ok
      {:error, errors} -> {:error, {:type_error, errors}}
    end
  end

  defp codegen(ast, file, emit?, output_dir, declared_phases) do
    opts = [file: file, emit_events: emit?, output_dir: output_dir]

    opts =
      if is_list(declared_phases),
        do: Keyword.put(opts, :declared_phases, declared_phases),
        else: opts

    case Codegen.compile_module(ast, opts) do
      {:ok, forms} -> {:ok, forms}
      {:error, reason} -> {:error, {:codegen_error, reason}}
    end
  end
end
