defmodule Cure do
  @moduledoc """
  Cure -- dependently-typed programming language for the BEAM virtual machine
  with first-class finite state machines and SMT-backed verification.

  Cure compiles `.cure` source files to BEAM bytecode through the following pipeline:

      .cure source
        |  Cure.Compiler.Lexer        (tokenization)
        v
      Token stream
        |  Cure.Compiler.Parser       (MetaAST generation)
        v
      MetaAST (Metastatic 3-tuples)
        |  Cure.Types.Checker         (bidirectional type checking)
        v
      Typed MetaAST
        |  Cure.Compiler.Codegen      (Erlang abstract forms)
        v
      BEAM bytecode

  Every pipeline stage emits structured events through `Cure.Pipeline.Events`,
  enabling external tools (LSP, profilers, IDE plugins) to observe and react
  to compilation in real time.

  ## Internal Representation

  Cure uses [Metastatic](https://hexdocs.pm/metastatic)'s MetaAST 3-tuple
  format as its internal AST representation:

      {type_atom, keyword_meta, children_or_value}

  This enables interoperability with Metastatic's cross-language analysis
  tools and provides a well-defined, layered AST structure.
  """

  alias Cure.Compiler.{Lexer, Parser}

  @version Cure.MixProject.project()[:version]
  @doc """
  Returns the current Cure version.
  """
  @spec version :: String.t()
  def version, do: @version

  @doc """
  Parse a Cure source string into its MetaAST representation.

  Runs the full lexer-then-parser pipeline and returns the resulting
  `{type, meta, children_or_value}` tree.

  ## Options

  - `:file` -- filename for source metadata (default: `"nofile"`)
  - `:emit_events` -- whether to emit pipeline events (default: `false`)

  ## Examples

      iex> Cure.quote("42")
      {:ok, {:literal, [subtype: :integer, line: 1, col: 1], 42}}

      iex> Cure.quote("x + 1")
      {:ok, {:binary_op, [category: :arithmetic, operator: :+, line: 1, col: 3],
        [{:variable, [scope: :local, line: 1, col: 1], "x"},
         {:literal, [subtype: :integer, line: 1, col: 5], 1}]}}
  """
  @spec quote(String.t(), keyword()) :: {:ok, Parser.ast()} | {:error, term()}
  def quote(source, opts \\ []) do
    file = Keyword.get(opts, :file, "nofile")
    emit? = Keyword.get(opts, :emit_events, false)
    lex_opts = parse_opts = [file: file, emit_events: emit?]

    with {:ok, tokens} <- Lexer.tokenize(source, lex_opts),
         do: Parser.parse(tokens, parse_opts)
  end

  @doc """
  Convert a MetaAST tree back into Cure source code.

  This is the inverse of `quote/2`. Given a well-formed MetaAST, it produces
  a Cure source string that, when re-quoted, yields an equivalent AST.

  ## Options

  - `:indent` -- base indentation string (default: `"  "` -- two spaces)

  ## Examples

      iex> {:ok, ast} = Cure.quote("let x = 42")
      iex> Cure.quoted_to_string(ast)
      "let x = 42"
  """
  @spec quoted_to_string(Parser.ast(), keyword()) :: String.t()
  defdelegate quoted_to_string(ast, opts \\ []), to: Cure.Compiler.Printer
end
