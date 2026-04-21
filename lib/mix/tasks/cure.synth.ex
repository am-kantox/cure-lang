defmodule Mix.Tasks.Cure.Synth do
  @moduledoc """
  Synthesise candidate expressions for a typed hole.

  ## Usage

      mix cure.synth --goal Int --ctx "n=Int,m=Int"
      mix cure.synth --goal "Option(Int)" --ctx "x=Int" --max 5
      mix cure.synth --goal Atom --ctx "s=String" --effects io

  The `--goal` flag is required and takes a type string. The
  `--ctx` flag takes a comma-separated list of `name=Type` bindings
  that represent the local variables in scope at the hole's
  position. The `--effects` flag takes a comma-separated list of
  allowed effect atoms; when omitted, only pure candidates are
  returned.

  The task prints up to `--max` (default 3) candidates ranked by
  cost. Each candidate line is prefixed with its index so callers
  can pipe the result into a REPL `:synth N` insertion.
  """

  use Mix.Task

  @shortdoc "Synthesise typed-hole candidates"

  @impl Mix.Task
  def run(args) do
    Application.ensure_all_started(:cure)

    {opts, _, _} =
      OptionParser.parse(args,
        switches: [
          goal: :string,
          ctx: :string,
          effects: :string,
          max: :integer,
          depth: :integer
        ]
      )

    goal = Keyword.get(opts, :goal) || raise "--goal is required"
    ctx = parse_ctx(Keyword.get(opts, :ctx, ""))
    effects = parse_effects(Keyword.get(opts, :effects, ""))
    max_results = Keyword.get(opts, :max, 3)
    depth = Keyword.get(opts, :depth, 3)

    Mix.shell().info("goal: #{goal}")
    Mix.shell().info("ctx:  #{inspect(ctx, pretty: true)}")

    candidates =
      Cure.Types.Synth.synthesise(goal, ctx, %{},
        effects: effects,
        max: max_results,
        depth: depth
      )

    if candidates == [] do
      Mix.shell().info("No candidates found within the budget (E061).")
    else
      Mix.shell().info("\nCandidates:")

      candidates
      |> Enum.with_index(1)
      |> Enum.each(fn {c, i} ->
        effect_tag =
          if c.effects == [], do: "pure", else: "! " <> Enum.map_join(c.effects, ",", &to_string/1)

        Mix.shell().info("  #{i}. #{c.expr}  (cost #{c.cost}, #{effect_tag})")
      end)
    end
  end

  # -- Parsing helpers --------------------------------------------------------

  defp parse_ctx("") do
    %{}
  end

  defp parse_ctx(str) do
    str
    |> String.split(",", trim: true)
    |> Enum.flat_map(fn binding ->
      case String.split(binding, "=", parts: 2) do
        [name, type] -> [{String.trim(name), String.trim(type)}]
        _ -> []
      end
    end)
    |> Map.new()
  end

  defp parse_effects(""), do: []

  defp parse_effects(str) do
    str
    |> String.split(",", trim: true)
    |> Enum.map(&String.trim/1)
    |> Enum.map(&String.to_atom/1)
  end
end
