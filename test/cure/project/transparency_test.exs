defmodule Cure.Project.TransparencyTest do
  use ExUnit.Case, async: true

  alias Cure.Project.Transparency

  defp canonical(entry) do
    entry
    |> Map.delete("hash")
    |> Enum.sort_by(fn {k, _} -> to_string(k) end)
    |> Enum.map_join(",", fn {k, v} ->
      Cure.Project.Json.encode(to_string(k)) <> ":" <> Cure.Project.Json.encode(v)
    end)
    |> then(&("{" <> &1 <> "}"))
  end

  defp make_entry(index, prev, payload) do
    base = Map.merge(%{"index" => index, "previous" => prev}, payload)
    hash = :crypto.hash(:sha256, canonical(base)) |> Base.encode16(case: :lower)
    Map.put(base, "hash", hash)
  end

  test "entry_hash/1 hashes only non-hash fields" do
    entry = %{"a" => 1, "b" => 2}
    expected = :crypto.hash(:sha256, canonical(entry)) |> Base.encode16(case: :lower)
    assert Transparency.entry_hash(entry) == expected
  end

  test "verify_chain/1 accepts a well-formed chain" do
    e1 = make_entry(0, "", %{"name" => "a", "version" => "0.1.0", "sha256" => "aa"})
    e2 = make_entry(1, e1["hash"], %{"name" => "b", "version" => "0.1.0", "sha256" => "bb"})
    assert :ok = Transparency.verify_chain([e1, e2])
  end

  test "verify_chain/1 rejects a broken link" do
    e1 = make_entry(0, "", %{"name" => "a", "version" => "0.1.0", "sha256" => "aa"})

    e2_tampered =
      %{make_entry(1, e1["hash"], %{"name" => "b", "version" => "0.1.0", "sha256" => "bb"}) | "previous" => "lol_wut"}

    assert {:error, {:chain_broken, 1}} = Transparency.verify_chain([e1, e2_tampered])
  end

  test "verify_chain/1 rejects a tampered entry whose declared hash does not match" do
    e1 = make_entry(0, "", %{"name" => "a", "version" => "0.1.0", "sha256" => "aa"})
    e2 = make_entry(1, e1["hash"], %{"name" => "b", "version" => "0.1.0", "sha256" => "bb"})
    bad = Map.put(e2, "sha256", "cc")
    assert {:error, {:chain_broken, 1}} = Transparency.verify_chain([e1, bad])
  end
end
