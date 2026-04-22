defmodule :cure_std_regex do
  @moduledoc """
  Runtime helpers for `Std.Regex` (v0.27.0).

  Wraps OTP's `:re` module. A compiled regex is represented as a Cure
  record `%{__struct__: :regex, handle: compiled_pattern}`; match
  results are `%{__struct__: :matched, whole: ..., groups: [...]}`.

  All matching entry points accept either a compiled `%{__struct__:
  :regex, ...}` record or a raw pattern string. The string form is
  compiled on every call -- hot paths should memoise the compiled
  record to avoid the overhead.

  The `compile!/1` alternative raises the `:cure_regex_invalid`
  exception on bad patterns so callers that treat compile failure as
  programmer error can stay terse.
  """

  @struct_key :__struct__

  # -- Compile ----------------------------------------------------------------

  def compile(pattern) when is_binary(pattern) do
    case :re.compile(pattern, [:unicode]) do
      {:ok, re} -> {:ok, new_regex(re)}
      {:error, reason} -> {:error, {:invalid_pattern, format_reason(reason)}}
    end
  end

  def compile(_), do: {:error, {:invalid_pattern, "pattern must be a string"}}

  def compile_bang(pattern) when is_binary(pattern) do
    case compile(pattern) do
      {:ok, regex} -> regex
      {:error, {:invalid_pattern, msg}} -> raise ArgumentError, "invalid regex: #{msg}"
    end
  end

  # -- Predicates -------------------------------------------------------------

  def is_match(regex, input) do
    case resolve(regex) do
      {:ok, re} -> do_is_match(re, input)
      :error -> false
    end
  end

  defp do_is_match(re, input) when is_binary(input) do
    case :re.run(input, re, [{:capture, :none}]) do
      :match -> true
      :nomatch -> false
    end
  end

  defp do_is_match(_, _), do: false

  # -- Single match -----------------------------------------------------------

  def run(regex, input) when is_binary(input) do
    case resolve(regex) do
      {:ok, re} ->
        case :re.run(input, re, [{:capture, :all, :binary}]) do
          {:match, [whole | groups]} ->
            {:some, new_match(whole, groups)}

          {:match, []} ->
            :none

          :nomatch ->
            :none
        end

      :error ->
        :none
    end
  end

  def run(_, _), do: :none

  # -- All matches ------------------------------------------------------------

  def scan(regex, input) when is_binary(input) do
    case resolve(regex) do
      {:ok, re} ->
        case :re.run(input, re, [:global, {:capture, :all, :binary}]) do
          {:match, matches} ->
            Enum.map(matches, fn
              [whole | groups] -> new_match(whole, groups)
              [] -> new_match("", [])
            end)

          :nomatch ->
            []
        end

      :error ->
        []
    end
  end

  def scan(_, _), do: []

  # -- Replace ----------------------------------------------------------------

  def replace(regex, input, replacement)
      when is_binary(input) and is_binary(replacement) do
    case resolve(regex) do
      {:ok, re} ->
        :re.replace(input, re, replacement, [:global, {:return, :binary}])

      :error ->
        input
    end
  end

  def replace(_, input, _) when is_binary(input), do: input

  # -- Split ------------------------------------------------------------------

  def split(regex, input) when is_binary(input) do
    case resolve(regex) do
      {:ok, re} ->
        :re.split(input, re, [{:return, :binary}])

      :error ->
        [input]
    end
  end

  # -- Internals --------------------------------------------------------------

  defp new_regex(compiled) do
    %{@struct_key => :regex, handle: compiled}
  end

  defp new_match(whole, groups) when is_binary(whole) and is_list(groups) do
    %{@struct_key => :matched, whole: whole, groups: groups}
  end

  defp resolve(%{@struct_key => :regex, handle: re}), do: {:ok, re}

  defp resolve(pattern) when is_binary(pattern) do
    case :re.compile(pattern, [:unicode]) do
      {:ok, re} -> {:ok, re}
      {:error, _} -> :error
    end
  end

  defp resolve(_), do: :error

  # `:re.compile/2` only reports compile errors as `{reason_string,
  # position}` tuples, so that is the only shape we need to format.
  defp format_reason({reason, _position}), do: to_string(reason)
end
