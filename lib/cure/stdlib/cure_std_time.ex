defmodule :cure_std_time do
  @moduledoc """
  Runtime helpers for `Std.Time` (v0.27.0).

  Targets of the `@extern` bridges in `lib/std/time.cure`. Wraps
  OTP's `Calendar` / `DateTime` / `:erlang.system_time/1` into the
  `Instant` and `Duration` record shapes (tagged maps with
  `__struct__: :instant` / `__struct__: :duration`).

  Parse errors surface as tagged tuples matching Cure's `ParseError`
  ADT (`{:invalid_format, msg}`, `{:out_of_range, msg}`) via a plain
  atom tag and single binary payload.
  """

  @struct_key :__struct__

  # -- Wall clock -------------------------------------------------------------

  def now, do: new_instant(:erlang.system_time(:microsecond))
  def utc_now, do: now()

  # -- ISO 8601 ---------------------------------------------------------------

  def parse_iso8601(s) when is_binary(s) do
    case DateTime.from_iso8601(s) do
      {:ok, %DateTime{} = dt, _offset} ->
        {:ok, new_instant(DateTime.to_unix(dt, :microsecond))}

      {:error, :invalid_format} ->
        {:error, parse_error(:invalid_format, "cannot parse ISO 8601 timestamp: #{inspect(s)}")}

      {:error, :invalid_date} ->
        {:error, parse_error(:out_of_range, "calendar date is out of range: #{inspect(s)}")}

      {:error, :invalid_time} ->
        {:error, parse_error(:out_of_range, "wall-clock time is out of range: #{inspect(s)}")}

      {:error, reason} ->
        {:error, parse_error(:invalid_format, "ISO 8601 parse failed: #{inspect(reason)}")}
    end
  end

  def parse_iso8601(_), do: {:error, parse_error(:invalid_format, "expected a string")}

  def format_iso8601(%{@struct_key => :instant, micros: micros}) when is_integer(micros) do
    iso =
      micros
      |> DateTime.from_unix!(:microsecond)
      |> DateTime.to_iso8601()

    # `DateTime.to_iso8601/1` always emits six fractional digits when built
    # through `from_unix!/2`. Drop `.000000` for whole-second instants so
    # round-trip round to the human-canonical form.
    if rem(micros, 1_000_000) == 0 do
      String.replace(iso, ".000000", "")
    else
      iso
    end
  end

  # -- Arithmetic -------------------------------------------------------------

  def add(
        %{@struct_key => :instant, micros: imicros},
        %{@struct_key => :duration, micros: dmicros}
      )
      when is_integer(imicros) and is_integer(dmicros) do
    new_instant(imicros + dmicros)
  end

  def diff(
        %{@struct_key => :instant, micros: a},
        %{@struct_key => :instant, micros: b}
      )
      when is_integer(a) and is_integer(b) do
    new_duration(a - b)
  end

  # -- Zone -------------------------------------------------------------------

  def zone(%{@struct_key => :instant, micros: micros}, name)
      when is_integer(micros) and is_binary(name) do
    case canonical_zone(name) do
      {:ok, offset_seconds, suffix} ->
        shifted =
          DateTime.from_unix!(micros + offset_seconds * 1_000_000, :microsecond)
          |> Map.put(:time_zone, name)
          |> Map.put(:zone_abbr, name)
          |> Map.put(:utc_offset, offset_seconds)
          |> Map.put(:std_offset, 0)

        base = DateTime.to_iso8601(%{shifted | time_zone: "Etc/UTC", utc_offset: 0, std_offset: 0})
        # `DateTime.to_iso8601/1` emits `Z` because we normalised to UTC;
        # replace the trailing `Z` with the real offset suffix.
        iso = String.replace_suffix(base, "Z", suffix)
        {:ok, iso}

      :error ->
        {:error, parse_error(:invalid_format, "unknown time zone: #{inspect(name)}")}
    end
  end

  # -- Unix conversions -------------------------------------------------------

  def to_unix(%{@struct_key => :instant, micros: micros}) when is_integer(micros) do
    # Truncate toward zero. `div/2` truncates toward zero in Elixir.
    div(micros, 1_000_000)
  end

  def of_unix(seconds) when is_integer(seconds) do
    new_instant(seconds * 1_000_000)
  end

  # -- Internals --------------------------------------------------------------

  defp new_instant(micros) when is_integer(micros) do
    %{@struct_key => :instant, micros: micros}
  end

  defp new_duration(micros) when is_integer(micros) do
    %{@struct_key => :duration, micros: micros}
  end

  defp parse_error(tag, message) when tag in [:invalid_format, :out_of_range] do
    {tag, message}
  end

  # Minimal zone table. "UTC" and "Etc/UTC" resolve to offset 0; explicit
  # `+HH:MM` / `-HH:MM` offsets are parsed inline. The IANA database is not
  # bundled; callers that need arbitrary zones should compose with
  # `:calendar.iso_week_number/1` and a timezone dependency.
  defp canonical_zone(name) do
    cond do
      String.upcase(name) == "UTC" or name == "Etc/UTC" ->
        {:ok, 0, "+00:00"}

      Regex.match?(~r/^[+-]\d{2}:\d{2}$/, name) ->
        <<sign::binary-size(1), hh::binary-size(2), ":", mm::binary-size(2)>> = name
        signum = if sign == "+", do: 1, else: -1
        {hi, _} = Integer.parse(hh)
        {mi, _} = Integer.parse(mm)
        {:ok, signum * (hi * 3600 + mi * 60), name}

      true ->
        :error
    end
  end
end
