defmodule Mix.Tasks.Cure.Rewrite do
  @shortdoc "Rewrite legacy `if`/`elif` constructs to `pickup`"

  @moduledoc """
  AST-driven rewriter that migrates the legacy `if`/`elif` construct
  to the v1.0.0 branching primitive `pickup` defined in
  `docs/PICKUP.md`. The rewrite is purely syntactic: every
  `{:conditional, _, _}` chain whose terminal `else` branch is
  populated is replaced with the equivalent `{:pickup, _, _}` block;
  conditionals that lack an `else` branch are left untouched so the
  rewritten program stays total (PICKUP §5.2).

  ## Modes

  By default, files are rewritten in place. Use `--check` to print
  which files would change without touching the disk (CI-friendly,
  exits non-zero when any file has pending rewrites). Use `--print`
  to dump the rewritten source to stdout.

  ## Usage

      mix cure.rewrite path/to/file.cure
      mix cure.rewrite priv/std/list.cure examples/factorial.cure
      mix cure.rewrite --check priv/std/*.cure
      mix cure.rewrite --print path/to/file.cure

  When no paths are given, the task scans `lib/std/**/*.cure` and
  `examples/**/*.cure` -- the canonical Cure source corpus. Built
  copies under `priv/std/` are deliberately skipped: they are
  regenerated from `lib/std/` on every compile.

  ## Companion specs

    * `docs/PICKUP.md` §17 -- migration guidance.
    * `docs/MATCH.md` §10 -- companion construct.

  ## Output

  The rewritten source is rendered with `Cure.Compiler.Printer`,
  whose canonical block form for `pickup` and `match` follows the
  formatter rules in PICKUP §8 and MATCH §9. Round-trip is
  preserved up to position metadata.

  ## Caveats

  Cure's layout-sensitive parser disables `:indent`/`:dedent`
  emission inside parenthesised contexts, so a multi-line `pickup`
  or `match` block cannot live inside a function-call argument
  list. The rewriter does not currently detect that context, so a
  conditional embedded as a call argument may be rewritten into a
  block that fails to re-parse. Run `--check` first; when in doubt,
  rewrite a single file at a time and recompile.
  """

  use Mix.Task

  alias Cure.Compiler.{Lexer, Parser, Printer}

  @impl Mix.Task
  def run(args) do
    Application.ensure_all_started(:cure)

    {opts, paths, _} =
      OptionParser.parse(args,
        switches: [check: :boolean, print: :boolean, write: :boolean],
        aliases: [c: :check, p: :print, w: :write]
      )

    files = expand_paths(paths)

    if files == [] do
      Mix.Shell.IO.info("No `.cure` files found to rewrite.")
    else
      initial_stats = %{rewritten: 0, unchanged: 0, errored: 0, previewed: 0}

      stats =
        Enum.reduce(files, initial_stats, fn file, acc ->
          process_file(file, opts, acc)
        end)

      summary(stats, opts)
    end
  end

  # ── Path Expansion ─────────────────────────────────────────────────────

  defp expand_paths([]) do
    (Path.wildcard("lib/std/**/*.cure") ++ Path.wildcard("examples/**/*.cure"))
    |> Enum.reject(&build_artifact?/1)
  end

  defp expand_paths(paths) do
    Enum.flat_map(paths, fn path ->
      cond do
        File.dir?(path) -> Path.wildcard(Path.join(path, "**/*.cure"))
        String.contains?(path, "*") -> Path.wildcard(path)
        true -> [path]
      end
    end)
    |> Enum.reject(&build_artifact?/1)
  end

  # Files inside `_build/`, `deps/`, or other vendored snapshots are
  # build artefacts that get regenerated on every compile; rewriting
  # them would be a no-op at best and would race with `mix compile` at
  # worst. The exclusion list mirrors the standard Elixir convention.
  defp build_artifact?(path) do
    parts = Path.split(path)
    Enum.any?(parts, &(&1 in ["_build", "deps", "node_modules", ".elixir_ls"]))
  end

  # ── File Processing ────────────────────────────────────────────────────

  defp process_file(file, opts, stats) do
    case File.read(file) do
      {:ok, source} ->
        rewrite_one(file, source, opts, stats)

      {:error, reason} ->
        Mix.Shell.IO.error("  cannot read #{file}: #{:file.format_error(reason)}")
        Map.update!(stats, :errored, &(&1 + 1))
    end
  end

  defp rewrite_one(file, source, opts, stats) do
    with {:ok, tokens} <- Lexer.tokenize(source, file: file, emit_events: false),
         {:ok, ast} <- Parser.parse(tokens, file: file, emit_events: false) do
      new_ast = rewrite(ast)

      cond do
        new_ast == ast ->
          if Keyword.get(opts, :verbose, false), do: Mix.Shell.IO.info("  unchanged: #{file}")
          Map.update!(stats, :unchanged, &(&1 + 1))

        Keyword.get(opts, :check, false) ->
          Mix.Shell.IO.info("  would rewrite: #{file}")
          Map.update!(stats, :rewritten, &(&1 + 1))

        Keyword.get(opts, :print, false) ->
          Mix.Shell.IO.info("# --- #{file} ---")
          Mix.Shell.IO.info(render(new_ast))
          Map.update!(stats, :previewed, &(&1 + 1))

        true ->
          rendered = render(new_ast)
          File.write!(file, rendered)
          Mix.Shell.IO.info("  rewrote: #{file}")
          Map.update!(stats, :rewritten, &(&1 + 1))
      end
    else
      {:error, reason} ->
        Mix.Shell.IO.error("  parse error in #{file}: #{inspect(reason)}")
        Map.update!(stats, :errored, &(&1 + 1))
    end
  end

  defp render(ast) do
    rendered = Printer.quoted_to_string(ast)
    if String.ends_with?(rendered, "\n"), do: rendered, else: rendered <> "\n"
  end

  defp summary(%{rewritten: r, unchanged: u, errored: e, previewed: p}, opts) do
    cond do
      Keyword.get(opts, :check, false) ->
        Mix.Shell.IO.info("\n#{r} file(s) need rewriting, #{u} clean, #{e} errored.")
        if r > 0, do: exit({:shutdown, 1})

      Keyword.get(opts, :print, false) ->
        Mix.Shell.IO.info("\n#{p} file(s) previewed, #{u} unchanged, #{e} errored.")

      true ->
        Mix.Shell.IO.info("\n#{r} file(s) rewritten, #{u} unchanged, #{e} errored.")
    end
  end

  # ── AST Rewrite ────────────────────────────────────────────────────────
  #
  # The rewrite is a depth-first walk over the MetaAST. Children are
  # rewritten first so that nested conditionals are flattened bottom-up
  # before their enclosing `:conditional` chain is collapsed into a
  # single `:pickup` block. The interesting logic lives in
  # `conditional_to_pickup/3`; everything else is structural.

  @doc """
  Rewrite every `{:conditional, _, _}` subtree of `ast` into a
  `{:pickup, _, _}` whose final clause is the original `else` branch.

  Conditionals that do not have an `else` branch (their final child
  is `{:literal, [subtype: :null], nil}`) cannot be migrated without
  introducing a new defaulting expression and are returned unchanged.
  """
  @spec rewrite(term()) :: term()
  def rewrite({:conditional, meta, [cond_expr, then_branch, else_branch]}) do
    cond_expr = rewrite(cond_expr)
    then_branch = rewrite(then_branch)
    else_branch = rewrite(else_branch)

    case conditional_to_pickup(cond_expr, then_branch, else_branch) do
      {:ok, clauses} ->
        {:pickup, meta, clauses}

      :no_else ->
        # PICKUP §5.2 mandates a terminator. A bare `if cond then expr`
        # has no `else`, so we cannot construct a total `pickup` from
        # it without inventing a default. Leave the conditional as-is
        # so the user can address it explicitly.
        {:conditional, meta, [cond_expr, then_branch, else_branch]}
    end
  end

  def rewrite({type, meta, children}) when is_list(children) do
    {type, meta, Enum.map(children, &rewrite/1)}
  end

  def rewrite(list) when is_list(list), do: Enum.map(list, &rewrite/1)

  def rewrite(tuple) when is_tuple(tuple) do
    tuple |> Tuple.to_list() |> Enum.map(&rewrite/1) |> List.to_tuple()
  end

  def rewrite(other), do: other

  # Walk the chain `if c1 then b1 elif c2 then b2 ... else bn` and
  # build the equivalent pickup clause list. Returns `:no_else` when
  # the chain bottoms out without a real else branch.
  @spec conditional_to_pickup(term(), term(), term()) :: {:ok, [term()]} | :no_else
  defp conditional_to_pickup(cond_expr, then_branch, else_branch) do
    case do_chain(cond_expr, then_branch, else_branch, []) do
      {:no_else, _} -> :no_else
      {:ok, clauses} -> {:ok, clauses}
    end
  end

  defp do_chain(cond_expr, then_branch, {:conditional, _meta, [c2, t2, e2]}, acc) do
    do_chain(c2, t2, e2, [{:pickup_clause, [], [cond_expr, then_branch]} | acc])
  end

  defp do_chain(_cond_expr, _then_branch, {:literal, [subtype: :null], nil}, acc) do
    {:no_else, Enum.reverse(acc)}
  end

  defp do_chain(cond_expr, then_branch, else_branch, acc) do
    clauses =
      Enum.reverse([
        {:pickup_else, [], [else_branch]},
        {:pickup_clause, [], [cond_expr, then_branch]}
        | acc
      ])

    {:ok, clauses}
  end
end
