defmodule Cure.Compiler.BeamWriter do
  @moduledoc """
  Compiles Erlang abstract forms to BEAM bytecode and writes `.beam` files.

  Wraps `:compile.forms/2` with structured error handling and pipeline
  event emission.

  ## Pipeline Events

  Emits via `Cure.Pipeline.Events`:

  - `{:codegen, :beam_written, module, meta}` -- after `.beam` file is written
  - `{:codegen, :error, error, meta}` -- on compilation or write errors
  """

  alias Cure.Pipeline.Events

  @doc """
  Compile Erlang abstract forms into BEAM bytecode.

  Returns `{:ok, module, binary, warnings}` on success,
  `{:error, errors, warnings}` on failure.
  """
  @spec compile_forms(list(), keyword()) ::
          {:ok, module(), binary(), list()} | {:error, list(), list()}
  def compile_forms(forms, opts \\ []) do
    compile_opts = [:return_errors, :return_warnings | Keyword.get(opts, :compile_opts, [])]

    case :compile.forms(forms, compile_opts) do
      {:ok, module, binary} ->
        {:ok, module, binary, []}

      {:ok, module, binary, warnings} ->
        {:ok, module, binary, warnings}

      {:error, errors, warnings} ->
        {:error, errors, warnings}

      :error ->
        {:error, [{:unknown_compilation_error, forms}], []}
    end
  end

  @doc """
  Write a compiled BEAM binary to disk.

  Creates the output directory if it does not exist. Emits a
  `:codegen, :beam_written` event on success.
  """
  @spec write_beam(module(), binary(), String.t(), keyword()) :: :ok | {:error, term()}
  def write_beam(module, binary, output_dir, opts \\ []) do
    emit? = Keyword.get(opts, :emit_events, true)
    file = Keyword.get(opts, :file, "nofile")

    File.mkdir_p!(output_dir)
    beam_path = Path.join(output_dir, "#{module}.beam")

    case File.write(beam_path, binary) do
      :ok ->
        if emit? do
          Events.emit(:codegen, :beam_written, module, Events.meta(file, 1))
        end

        :ok

      {:error, reason} ->
        if emit? do
          Events.emit(:codegen, :error, {:write_failed, beam_path, reason}, Events.meta(file, 1))
        end

        {:error, {:write_failed, beam_path, reason}}
    end
  end

  @doc """
  Compile forms and load the resulting module into the VM without writing to disk.

  Useful for testing and REPL scenarios.
  """
  @spec compile_and_load(list()) :: {:ok, module()} | {:error, term()}
  def compile_and_load(forms) do
    case compile_forms(forms) do
      {:ok, module, binary, _warnings} ->
        case :code.load_binary(module, ~c"nofile", binary) do
          {:module, ^module} -> {:ok, module}
          {:error, reason} -> {:error, {:load_failed, reason}}
        end

      {:error, errors, _warnings} ->
        {:error, {:compilation_failed, errors}}
    end
  end
end
