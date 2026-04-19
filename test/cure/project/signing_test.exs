defmodule Cure.Project.SigningTest do
  use ExUnit.Case, async: false

  alias Cure.Project.Signing

  setup do
    original_home = System.get_env("HOME")
    tmp = Path.join(System.tmp_dir!(), "cure_keys_test_#{:erlang.unique_integer([:positive])}")
    File.mkdir_p!(tmp)
    System.put_env("HOME", tmp)

    on_exit(fn ->
      case original_home do
        nil -> System.delete_env("HOME")
        h -> System.put_env("HOME", h)
      end

      File.rm_rf!(tmp)
    end)

    {:ok, home: tmp}
  end

  test "generate_keypair/1 persists a trusted keypair" do
    assert {:ok, "alice"} = Signing.generate_keypair("alice")
    assert {:ok, _priv} = Signing.load_private("alice")
    assert {:ok, _pub} = Signing.load_public("alice")
    assert %{"alice" => pub} = Signing.trusted_keys()
    assert byte_size(pub) > 0
  end

  test "sign_tarball/4 and verify/5 round-trip a valid signature" do
    {:ok, _} = Signing.generate_keypair("bob")
    tarball = "hello world"

    assert {:ok, sig} = Signing.sign_tarball("bob", "pkg", "0.1.0", tarball)
    assert :ok = Signing.verify("bob", "pkg", "0.1.0", tarball, sig)
  end

  test "verify/5 fails on tampered tarball bytes" do
    {:ok, _} = Signing.generate_keypair("eve")
    {:ok, sig} = Signing.sign_tarball("eve", "pkg", "0.1.0", "original")
    assert {:error, :signature_invalid} = Signing.verify("eve", "pkg", "0.1.0", "tampered", sig)
  end

  test "verify/5 fails when publisher is not trusted" do
    {:ok, sig} =
      :crypto.generate_key(:eddsa, :ed25519)
      |> then(fn {_pub, priv} ->
        msg = "pkg" <> <<0>> <> "0.1.0" <> <<0>> <> :crypto.hash(:sha256, "bytes")
        {:ok, :crypto.sign(:eddsa, :none, msg, [priv, :ed25519])}
      end)

    assert {:error, :no_trusted_key} =
             Signing.verify("stranger", "pkg", "0.1.0", "bytes", sig)
  end

  test "add_trusted / remove_trusted edits the trust list" do
    :ok = Signing.add_trusted("observer", <<1, 2, 3>>)
    assert Signing.trusted_keys()["observer"] == <<1, 2, 3>>
    :ok = Signing.remove_trusted("observer")
    refute Map.has_key?(Signing.trusted_keys(), "observer")
  end
end
