defmodule Cure.Project.LockTest do
  use ExUnit.Case, async: true

  alias Cure.Project.Lock

  setup do
    tmp = Path.join(System.tmp_dir!(), "cure_lock_test_#{:erlang.unique_integer([:positive])}")
    File.mkdir_p!(tmp)
    on_exit(fn -> File.rm_rf!(tmp) end)
    {:ok, root: tmp}
  end

  test "round-trips a multi-entry lock file", %{root: root} do
    lock = %{
      "http" => %{
        name: "http",
        version: "1.2.3",
        hash: "sha256:abc",
        dependencies: [{"json", "~> 2.0"}]
      },
      "json" => %{
        name: "json",
        version: "2.1.0",
        hash: "sha256:def",
        dependencies: []
      }
    }

    :ok = Lock.write(root, lock)
    assert {:ok, parsed} = Lock.read(root)
    assert Map.keys(parsed) |> Enum.sort() == ["http", "json"]
    assert parsed["http"].version == "1.2.3"
    assert parsed["http"].hash == "sha256:abc"
    assert parsed["json"].dependencies == []
  end

  test "read/1 returns :no_lock when file is missing", %{root: root} do
    assert {:error, :no_lock} = Lock.read(root)
  end

  describe "resolve_with_lock/2" do
    test "accepts a lock whose locked version satisfies every constraint" do
      lock = %{"http" => %{name: "http", version: "1.2.3", hash: "", dependencies: []}}
      constraints = %{"http" => "~> 1.0"}
      assert {:ok, %{"http" => {1, 2, 3, nil}}} = Lock.resolve_with_lock(constraints, lock)
    end

    test "returns :stale when a constraint no longer accepts the locked version" do
      lock = %{"http" => %{name: "http", version: "2.0.0", hash: "", dependencies: []}}
      constraints = %{"http" => "~> 1.0"}
      assert :stale = Lock.resolve_with_lock(constraints, lock)
    end

    test "returns :stale when the lock is missing an entry" do
      assert :stale = Lock.resolve_with_lock(%{"http" => "~> 1.0"}, %{})
    end
  end
end
