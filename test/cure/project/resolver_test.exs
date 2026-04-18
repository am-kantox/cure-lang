defmodule Cure.Project.ResolverTest do
  use ExUnit.Case, async: true

  alias Cure.Project.Resolver

  describe "resolve/2" do
    test "picks the newest compatible version" do
      registry = %{
        "http" => [
          %{version: {2, 0, 0, nil}, deps: []},
          %{version: {1, 5, 0, nil}, deps: []},
          %{version: {1, 0, 0, nil}, deps: []}
        ]
      }

      assert {:ok, %{"http" => {2, 0, 0, nil}}} = Resolver.resolve(%{"http" => ">= 1.0.0"}, registry)
    end

    test "honours compound constraints" do
      registry = %{
        "http" => [
          %{version: {2, 0, 0, nil}, deps: []},
          %{version: {1, 2, 0, nil}, deps: []},
          %{version: {1, 0, 0, nil}, deps: []}
        ]
      }

      assert {:ok, %{"http" => {1, 2, 0, nil}}} =
               Resolver.resolve(%{"http" => ">= 1.0.0 and < 2.0.0"}, registry)
    end

    test "resolves a transitive dep constrained by the top-level pick" do
      registry = %{
        "app" => [
          %{version: {1, 0, 0, nil}, deps: [{"json", "~> 2.0"}]}
        ],
        "json" => [
          %{version: {3, 0, 0, nil}, deps: []},
          %{version: {2, 1, 0, nil}, deps: []},
          %{version: {2, 0, 0, nil}, deps: []}
        ]
      }

      assert {:ok, %{"app" => {1, 0, 0, nil}, "json" => {2, 1, 0, nil}}} =
               Resolver.resolve(%{"app" => "~> 1.0.0"}, registry)
    end

    test "fails with a version_conflict when no set satisfies every constraint" do
      registry = %{
        "http" => [
          %{version: {1, 0, 0, nil}, deps: [{"json", "~> 1.0"}]}
        ],
        "json" => [
          %{version: {2, 0, 0, nil}, deps: []}
        ]
      }

      # The conflict can be reported at any name in the failing path --
      # either directly on `json` (no satisfying version) or on `http`
      # (no candidate whose deps can be satisfied). Both are honest.
      assert {:error, {:version_conflict, name, _}} =
               Resolver.resolve(%{"http" => "~> 1.0.0"}, registry)

      assert name in ["http", "json"]
    end
  end
end
