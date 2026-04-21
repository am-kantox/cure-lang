defmodule :cure_std_time_test do
  use ExUnit.Case, async: true

  describe "now/0 and utc_now/0" do
    test "return an :instant struct with microsecond resolution" do
      assert %{__struct__: :instant, micros: a} = :cure_std_time.now()
      assert is_integer(a)
      assert a > 0
      assert %{__struct__: :instant, micros: b} = :cure_std_time.utc_now()
      assert is_integer(b)
    end
  end

  describe "parse_iso8601/1" do
    test "parses a canonical UTC timestamp" do
      assert {:ok, %{__struct__: :instant, micros: micros}} =
               :cure_std_time.parse_iso8601("2026-04-21T15:11:46Z")

      # Round-trip the parsed value through DateTime so the test stays
      # robust against off-by-one calendar math.
      assert DateTime.from_unix!(div(micros, 1_000_000)) ==
               ~U[2026-04-21 15:11:46Z]

      assert rem(micros, 1_000_000) == 0
    end

    test "parses timestamps with fractional seconds" do
      assert {:ok, %{__struct__: :instant, micros: micros}} =
               :cure_std_time.parse_iso8601("2026-04-21T15:11:46.500Z")

      assert rem(micros, 1_000_000) == 500_000
    end

    test "rejects garbage input with InvalidFormat" do
      assert {:error, {:invalid_format, _msg}} = :cure_std_time.parse_iso8601("not-a-date")
    end

    test "rejects non-string input with InvalidFormat" do
      assert {:error, {:invalid_format, _}} = :cure_std_time.parse_iso8601(42)
    end
  end

  describe "format_iso8601/1" do
    test "round-trips a parsed Instant back to the original UTC form" do
      {:ok, inst} = :cure_std_time.parse_iso8601("2026-04-21T15:11:46Z")
      assert :cure_std_time.format_iso8601(inst) == "2026-04-21T15:11:46Z"
    end

    test "round-trips microsecond precision" do
      {:ok, inst} = :cure_std_time.parse_iso8601("2026-04-21T15:11:46.500000Z")
      assert :cure_std_time.format_iso8601(inst) == "2026-04-21T15:11:46.500000Z"
    end
  end

  describe "add/2 and diff/2" do
    test "add is inverse of diff for matching inputs" do
      {:ok, a} = :cure_std_time.parse_iso8601("2026-04-21T15:11:46Z")
      {:ok, b} = :cure_std_time.parse_iso8601("2026-04-21T15:12:46Z")

      d = :cure_std_time.diff(b, a)
      assert d == %{__struct__: :duration, micros: 60_000_000}

      back = :cure_std_time.add(a, d)
      assert back == b
    end

    test "negative durations move backward in time" do
      {:ok, a} = :cure_std_time.parse_iso8601("2026-04-21T15:11:46Z")
      d = %{__struct__: :duration, micros: -60_000_000}
      out = :cure_std_time.add(a, d)
      assert :cure_std_time.format_iso8601(out) == "2026-04-21T15:10:46Z"
    end
  end

  describe "zone/2" do
    test "UTC keeps the Instant unchanged but emits a +00:00 suffix" do
      {:ok, inst} = :cure_std_time.parse_iso8601("2026-04-21T15:11:46Z")
      assert {:ok, iso} = :cure_std_time.zone(inst, "UTC")
      assert iso =~ "+00:00"
    end

    test "explicit +HH:MM offset shifts the wall clock and stamps the suffix" do
      {:ok, inst} = :cure_std_time.parse_iso8601("2026-04-21T15:11:46Z")
      assert {:ok, iso} = :cure_std_time.zone(inst, "+02:00")
      assert iso =~ "2026-04-21T17:11:46"
      assert String.ends_with?(iso, "+02:00")
    end

    test "unknown zone name returns InvalidFormat" do
      {:ok, inst} = :cure_std_time.parse_iso8601("2026-04-21T15:11:46Z")
      assert {:error, {:invalid_format, _msg}} = :cure_std_time.zone(inst, "Mars/Olympus")
    end
  end

  describe "to_unix/1 and of_unix/1" do
    test "to_unix truncates sub-second precision" do
      inst = %{__struct__: :instant, micros: 1_000_500_000}
      assert :cure_std_time.to_unix(inst) == 1_000
    end

    test "of_unix promotes seconds to Instant" do
      assert :cure_std_time.of_unix(1_776_323_506) ==
               %{__struct__: :instant, micros: 1_776_323_506_000_000}
    end

    test "of_unix and to_unix round-trip seconds" do
      assert :cure_std_time.of_unix(0) |> :cure_std_time.to_unix() == 0
      assert :cure_std_time.of_unix(1_234_567_890) |> :cure_std_time.to_unix() == 1_234_567_890
    end
  end
end
