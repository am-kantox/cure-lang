defmodule Cure.Compiler do
  @moduledoc """
  Compiler orchestrator for the Cure programming language.

  Chains together the full compilation pipeline:

      source -> Lexer -> Parser -> [Checker] -> Codegen -> BeamWriter -> .beam

  The type checker is optional and can be disabled with `check_types: false`.

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
  - `:check_types` -- whether to run the type checker (default: `false`)
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
    check? = Keyword.get(opts, :check_types, false)

    optimize? = Keyword.get(opts, :optimize, false)

    with {:ok, tokens} <- lex(source, file, emit?),
         {:ok, ast} <- parse(tokens, file, emit?),
         {:ok, _} <- maybe_check(ast, file, emit?, check?),
         {:ok, ast} <- maybe_optimize(ast, optimize?),
         {:ok, forms} <- codegen(ast, file, emit?),
         {:ok, module, binary, warnings} <- BeamWriter.compile_forms(forms),
         :ok <- BeamWriter.write_beam(module, binary, output_dir, emit_events: emit?, file: file) do
      {:ok, module, warnings}
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
    check? = Keyword.get(opts, :check_types, false)

    optimize? = Keyword.get(opts, :optimize, false)

    with {:ok, tokens} <- lex(source, file, emit?),
         {:ok, ast} <- parse(tokens, file, emit?),
         {:ok, _} <- maybe_check(ast, file, emit?, check?),
         {:ok, ast} <- maybe_optimize(ast, optimize?),
         {:ok, forms} <- codegen(ast, file, emit?),
         {:ok, module} <- BeamWriter.compile_and_load(forms) do
      {:ok, module}
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

  defp maybe_optimize(ast, false), do: {:ok, ast}

  defp maybe_optimize(ast, true) do
    {:ok, optimized, _stats} = Optimizer.optimize(ast)
    {:ok, optimized}
  end

  defp maybe_check(_ast, _file, _emit?, false), do: {:ok, :skipped}

  defp maybe_check(ast, file, emit?, true) do
    case Checker.check_module(ast, file: file, emit_events: emit?) do
      {:ok, _} = ok -> ok
      {:error, errors} -> {:error, {:type_error, errors}}
    end
  end

  defp codegen(ast, file, emit?) do
    case Codegen.compile_module(ast, file: file, emit_events: emit?) do
      {:ok, forms} -> {:ok, forms}
      {:error, reason} -> {:error, {:codegen_error, reason}}
    end
  end
end
