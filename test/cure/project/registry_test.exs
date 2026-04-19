defmodule Cure.Project.RegistryTest do
  use ExUnit.Case, async: false

  alias Cure.Project.Registry

  # These tests deliberately avoid starting a real HTTP server; they
  # exercise the pure (non-network) surface of the module: base URL
  # selection, cache-path helpers, and hash computation. The HTTP path
  # is covered end-to-end by the registry integration harness that
  # ships separately.

  setup do
    previous = Application.get_env(:cure, :registry_url)

    on_exit(fn ->
      if previous do
        Application.put_env(:cure, :registry_url, previous)
      else
        Application.delete_env(:cure, :registry_url)
      end
    end)

    :ok
  end

  describe "base_url/0" do
    test "returns the application env value when set" do
      Application.put_env(:cure, :registry_url, "https://example.test")
      assert Registry.base_url() == "https://example.test"
    end

    test "falls back to the default when no config is present" do
      Application.delete_env(:cure, :registry_url)
      System.delete_env("CURE_REGISTRY_URL")
      assert Registry.base_url() =~ "cure-lang.org"
    end

    test "CURE_REGISTRY_URL overrides the default" do
      Application.delete_env(:cure, :registry_url)
      System.put_env("CURE_REGISTRY_URL", "https://env.example")
      assert Registry.base_url() == "https://env.example"
    end
  end

  describe "with_base_url/2" do
    test "scopes the override to the function body" do
      Application.put_env(:cure, :registry_url, "https://outer.example")

      Registry.with_base_url("https://inner.example", fn ->
        assert Registry.base_url() == "https://inner.example"
      end)

      assert Registry.base_url() == "https://outer.example"
    end
  end

  test "prune_cache/0 removes tampered cache files" do
    # System.user_home!/0 is cached at VM start, so we cannot temporarily
    # swap HOME in-process. Instead we touch the real cache directory
    # with test-specific filenames and clean up afterwards.
    cache_dir = Path.join([System.user_home!(), ".cure", "registry_cache"])
    File.mkdir_p!(cache_dir)

    bytes = "cure_registry_prune_test_hello"
    sha = :crypto.hash(:sha256, bytes) |> Base.encode16(case: :lower)
    bad_name = "cure_registry_prune_test_bad_#{:erlang.unique_integer([:positive])}"

    valid_path = Path.join(cache_dir, sha)
    bad_path = Path.join(cache_dir, bad_name)
    File.write!(valid_path, bytes)
    File.write!(bad_path, "world")

    try do
      pruned = Registry.prune_cache()
      assert pruned >= 1
      refute File.exists?(bad_path)
      assert File.exists?(valid_path)
    after
      _ = File.rm(valid_path)
      _ = File.rm(bad_path)
    end
  end
end
