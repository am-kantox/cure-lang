defmodule Cure.MixProject do
  use Mix.Project

  @app :cure
  @version "0.23.0"
  @source_url "https://github.com/am-kantox/cure-lang"

  def project do
    [
      app: @app,
      version: @version,
      elixir: "~> 1.18",
      elixirc_paths: elixirc_paths(Mix.env()),
      start_permanent: Mix.env() == :prod,
      consolidate_protocols: Mix.env() not in [:dev, :test],
      deps: deps(),
      escript: [main_module: Cure.CLI],
      description: description(),
      docs: docs(),
      aliases: aliases(),
      package: package(),
      test_coverage: [tool: ExCoveralls],
      dialyzer: [
        plt_file: {:no_warn, ".dialyzer/dialyzer.plt"},
        plt_add_deps: :app_tree,
        plt_add_apps: [:mix, :ex_unit],
        plt_core_path: ".dialyzer",
        # 1.18 and 1.20 → until map type check is fully landed
        list_unused_filters: false,
        ignore_warnings: ".dialyzer/ignore.exs"
      ],
      name: "Cure",
      source_url: @source_url
    ]
  end

  defp elixirc_paths(:test), do: ["lib", "test/support"]
  defp elixirc_paths(_), do: ["lib"]

  def application do
    [
      extra_applications: [:logger, :inets, :ssl, :crypto, :public_key, :tools],
      mod: {Cure.Application, []}
    ]
  end

  def cli do
    [
      preferred_envs: [
        coveralls: :test,
        "coveralls.detail": :test,
        "coveralls.post": :test,
        "coveralls.html": :test,
        "coveralls.json": :test
      ]
    ]
  end

  defp deps do
    [
      # Core -- MetaAST backing
      {:metastatic, "~> 0.18"},

      # REPL -- syntax highlighting and Markdown-to-ANSI rendering
      {:marcli, "~> 0.3"},
      {:makeup, "~> 1.2"},
      {:makeup_cure, "~> 0.1"},

      # Observability -- optional, used by Cure.Telemetry when loaded
      {:telemetry, "~> 1.3", optional: true},

      # Development and documentation
      {:ex_doc, "~> 0.34", only: :dev, runtime: false},
      {:excoveralls, "~> 0.18", only: :test, runtime: false},
      {:dialyxir, "~> 1.4", only: [:dev, :test], runtime: false},
      {:credo, "~> 1.7", only: [:dev, :test], runtime: false},
      {:oeditus_credo, "~> 0.4", only: [:dev, :test], runtime: false}
    ]
  end

  defp aliases do
    [
      quality: ["format", "credo --strict"],
      "quality.ci": [
        "format --check-formatted",
        "credo --strict"
      ],
      # `mix check` runs the Cure stdlib and example regression
      # suites. Invoke alongside `mix test` (CI does both).
      check: ["cure.compile_stdlib", "cure.check"]
    ]
  end

  defp description do
    """
    Dependently-typed programming language for the BEAM virtual machine
    with first-class finite state machines and SMT-backed verification.
    """
  end

  defp package do
    [
      maintainers: ["Aleksei Matiushkin"],
      licenses: ["MIT"],
      links: %{
        "GitHub" => @source_url,
        "Changelog" => @source_url <> "/blob/main/CHANGELOG.md"
      },
      files: ~w(lib mix.exs README.md CHANGELOG.md LICENSE docs)
    ]
  end

  defp docs do
    [
      main: "readme",
      extras: [
        "README.md",
        "CHANGELOG.md",
        "docs/TUTORIAL.md",
        "docs/LANGUAGE_SPEC.md",
        "docs/TYPE_SYSTEM.md",
        "docs/DEPENDENT_TYPES.md",
        "docs/PATTERNS.md",
        "docs/BINARIES.md",
        "docs/PROOFS.md",
        "docs/PACKAGE_REGISTRY.md",
        "docs/PUBLISHING.md",
        "docs/FSM_GUIDE.md",
        "docs/STDLIB.md",
        "docs/REPL.md"
      ],
      source_url: @source_url,
      source_ref: "v#{@version}",
      formatters: ["html"],
      authors: ["Aleksei Matiushkin"],
      canonical: "https://hexdocs.pm/#{@app}"
    ]
  end
end
