defmodule Cure.ExportTypes do
  @moduledoc """
  Cross-language ADT export for Cure projects (v0.32.0).

  Parses `.cure` source files, extracts `type`, `rec`, and `enum`
  container declarations, and emits equivalent schema definitions for a
  target language.

  ## Supported targets

    * `:protobuf` -- proto3 `.proto` files via `Cure.ExportTypes.Protobuf`.

  ## Usage

      # Programmatic
      {:ok, [{file, content}, ...]} =
        Cure.ExportTypes.export(".", target: :protobuf, out: "_build/cure/export/protobuf")

  ## Warnings (E068)

  Types that cannot be represented in the target language are replaced by
  a comment in the generated output and an `E068 Export Type Unmappable`
  warning is emitted to stderr. This is a warning, not a hard error:
  partial exports are still useful.
  """

  alias Cure.ExportTypes.Protobuf

  @type target :: :protobuf
  @type type_def :: map()

  @doc """
  Export all type declarations from `.cure` files under `root`.

  ## Options

    * `:target`  -- `:protobuf` (default and only supported target).
    * `:out`     -- output directory. Defaults to `_build/cure/export/<target>`.
    * `:files`   -- explicit list of `.cure` files. When given, overrides the
      automatic `lib/**/*.cure` glob.
    * `:verbose` -- when `true`, prints one line per file processed.

  Returns `{:ok, [{output_path, content}]}` on success. The caller must
  write the returned binaries to disk.
  """
  @spec export(String.t(), keyword()) :: {:ok, [{String.t(), String.t()}]} | {:error, term()}
  def export(root \\ ".", opts \\ []) do
    target = Keyword.get(opts, :target, :protobuf)
    verbose? = Keyword.get(opts, :verbose, false)

    out_dir =
      Keyword.get(opts, :out, Path.join(root, "_build/cure/export/#{target}"))

    files =
      case Keyword.get(opts, :files) do
        nil ->
          root
          |> Path.join("lib/**/*.cure")
          |> Path.wildcard()
          |> Enum.sort()

        explicit ->
          Enum.sort(explicit)
      end

    if verbose?, do: IO.puts("cure export-types: processing #{length(files)} file(s) -> #{out_dir}")

    type_defs_by_file =
      Enum.flat_map(files, fn file ->
        if verbose?, do: IO.puts("  #{file}")

        case extract_type_defs(file) do
          {:ok, defs} when defs != [] -> [{file, defs}]
          _ -> []
        end
      end)

    outputs =
      Enum.map(type_defs_by_file, fn {source_file, defs} ->
        base = source_file |> Path.basename(".cure") |> Macro.underscore()
        out_file = Path.join(out_dir, emit_filename(target, base))
        content = emit(target, defs, source_file)
        {out_file, content}
      end)

    {:ok, outputs}
  end

  # -- Type extraction -----------------------------------------------------------

  @doc false
  @spec extract_type_defs(String.t()) :: {:ok, [type_def()]} | {:error, term()}
  def extract_type_defs(path) do
    case File.read(path) do
      {:ok, source} ->
        with {:ok, tokens} <-
               Cure.Compiler.Lexer.tokenize(source, file: path, emit_events: false),
             {:ok, ast} <-
               Cure.Compiler.Parser.parse(tokens, file: path, emit_events: false) do
          {:ok, collect_type_defs(ast)}
        else
          {:error, reason} -> {:error, reason}
        end

      {:error, reason} ->
        {:error, {:file_read_error, path, reason}}
    end
  end

  defp collect_type_defs({:block, _, children}) when is_list(children) do
    Enum.flat_map(children, &collect_type_defs/1)
  end

  defp collect_type_defs({:container, meta, body}) when is_list(meta) do
    case Keyword.get(meta, :container_type) do
      :module ->
        Enum.flat_map(body, &collect_type_defs/1)

      :enum ->
        [parse_enum(meta, body)]

      :struct ->
        [parse_record(meta, body)]

      _ ->
        []
    end
  end

  defp collect_type_defs({:type_annotation, meta, _body}) when is_list(meta) do
    [parse_type_alias(meta)]
  end

  defp collect_type_defs(_), do: []

  defp parse_enum(meta, variants) do
    name = Keyword.get(meta, :name, "Unknown")
    doc = Keyword.get(meta, :doc)

    variant_defs =
      Enum.flat_map(variants, fn
        {:function_def, m, _} ->
          vname = Keyword.get(m, :name, "?")
          params = Keyword.get(m, :params, [])

          payload =
            case params do
              [] -> nil
              [{:param, pm, _pname}] -> Keyword.get(pm, :type)
              many -> {:tuple_payload, Enum.map(many, fn {:param, pm, _} -> Keyword.get(pm, :type) end)}
            end

          [%{name: vname, payload: payload}]

        {:variable, _, vname} ->
          [%{name: vname, payload: nil}]

        _ ->
          []
      end)

    %{kind: :enum, name: name, doc: doc, variants: variant_defs}
  end

  defp parse_record(meta, body) do
    name = Keyword.get(meta, :name, "Unknown")
    doc = Keyword.get(meta, :doc)

    fields =
      Enum.flat_map(body, fn
        {:param, pm, fname} ->
          type_ast = Keyword.get(pm, :type)
          [%{name: fname, type: type_ast}]

        {:field, pm, fname} ->
          type_ast = Keyword.get(pm, :type)
          [%{name: fname, type: type_ast}]

        _ ->
          []
      end)

    %{kind: :record, name: name, doc: doc, fields: fields}
  end

  defp parse_type_alias(meta) do
    name = Keyword.get(meta, :name, "Unknown")
    doc = Keyword.get(meta, :doc)
    rhs = Keyword.get(meta, :rhs)
    %{kind: :alias, name: name, doc: doc, rhs: rhs}
  end

  # -- Emission ------------------------------------------------------------------

  defp emit(:protobuf, defs, source_file) do
    Protobuf.emit(defs, source_file: source_file)
  end

  defp emit_filename(:protobuf, base), do: "#{base}.proto"
end
