defmodule Cure.Protocol.Parser do
  @moduledoc """
  Parser for the `protocol` DSL (v0.27.0).

  Accepts:

      protocol Ping.Pong with Client, Server
        Client -> Server: Ping
        Server -> Client: Pong(Int)
        loop

  Supported constructs inside the body:

    * `<Role> -> <Role>: <Tag>` or `<Role> -> <Role>: <Tag>(<TypeList>)`
    * `loop` on its own line -- marks the end-of-script as a loop
      back to the first step.
    * `end` on its own line -- explicitly terminates the protocol.
    * `choose | <branch1> | <branch2>` -- currently reserved, emits a
      friendly error pointing to future v0.28 support.

  Returns `{:ok, %Cure.Protocol.Script{}}` or `{:error, reason}`.
  """

  alias Cure.Protocol.Script

  @doc "Parse a protocol DSL string into a Script."
  @spec parse(String.t()) :: {:ok, Script.t()} | {:error, term()}
  def parse(src) when is_binary(src) do
    lines =
      src
      |> String.split(~r/\r?\n/, trim: false)
      |> Enum.map(&strip_comment/1)
      |> Enum.map(&String.trim/1)
      |> Enum.reject(&(&1 == ""))

    case lines do
      [] ->
        {:error, :empty}

      [header | body_lines] ->
        with {:ok, name, roles} <- parse_header(header),
             {:ok, body} <- parse_body(body_lines) do
          {:ok, %Script{name: name, roles: roles, body: body}}
        end
    end
  end

  # -- Header -----------------------------------------------------------------

  defp parse_header(line) do
    case Regex.run(~r/^protocol\s+([\w\.]+)\s+with\s+([\w\s,]+)$/, line) do
      [_, name, roles_str] ->
        roles =
          roles_str
          |> String.split(",", trim: true)
          |> Enum.map(&String.trim/1)
          |> Enum.reject(&(&1 == ""))

        if length(roles) >= 2 do
          {:ok, name, roles}
        else
          {:error, {:expected_at_least_two_roles, roles}}
        end

      _ ->
        {:error, {:bad_header, line}}
    end
  end

  # -- Body -------------------------------------------------------------------

  defp parse_body(lines), do: parse_steps(lines, [])

  defp parse_steps([], acc), do: {:ok, Enum.reverse(acc)}

  defp parse_steps(["loop" | rest], acc) do
    # Consume remaining steps as the loop body; anything after a
    # top-level `loop` is rejected.
    case rest do
      [] -> {:ok, Enum.reverse([{:loop, Enum.reverse(acc)}])}
      _other -> {:error, {:unexpected_after_loop, rest}}
    end
  end

  defp parse_steps(["end" | rest], acc) do
    case rest do
      [] -> {:ok, Enum.reverse([{:end_, []} | acc])}
      _other -> {:error, {:unexpected_after_end, rest}}
    end
  end

  defp parse_steps([line | rest], acc) do
    case parse_msg(line) do
      {:ok, step} -> parse_steps(rest, [step | acc])
      {:error, _} = err -> err
    end
  end

  # -- Single message ---------------------------------------------------------

  defp parse_msg(line) do
    case Regex.run(~r/^(\w+)\s*->\s*(\w+)\s*:\s*([\w]+)\s*(\((.*)\))?\s*$/, line) do
      [_, from, to, tag] ->
        {:ok, {:msg, from, to, tag, []}}

      [_, from, to, tag, _paren, args_str] ->
        args =
          args_str
          |> String.split(",", trim: true)
          |> Enum.map(&String.trim/1)
          |> Enum.reject(&(&1 == ""))

        {:ok, {:msg, from, to, tag, args}}

      _ ->
        {:error, {:bad_step, line}}
    end
  end

  # -- Helpers ----------------------------------------------------------------

  defp strip_comment(line) do
    case String.split(line, "#", parts: 2) do
      [before | _] -> before
      _ -> line
    end
  end
end
