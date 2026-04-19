defmodule :cure_std_http do
  @moduledoc """
  Runtime helpers for `Std.Http` (v0.23.0).

  Wraps OTP's `:httpc` into the `Result(Response, HttpError)` shape
  Cure expects.

  Response is a Cure record compiled to a map with a `__struct__` of
  `:response`; errors are tagged variants (`:timeout`,
  `{:bad_status, n}`, `{:network_error, msg}`).
  """

  @default_timeout 30_000
  @connect_timeout 10_000

  def get(url) when is_binary(url), do: do_request(:get, url, [], nil)

  def get(url, headers) when is_binary(url) and is_list(headers) do
    do_request(:get, url, headers, nil)
  end

  def post(url, headers, body) when is_binary(url) and is_list(headers) and is_binary(body) do
    do_request(:post, url, headers, body)
  end

  def head(url) when is_binary(url), do: do_request(:head, url, [], nil)

  defp do_request(method, url, headers, body) do
    ensure_inets()

    erl_headers =
      Enum.map(headers, fn {k, v} ->
        {String.to_charlist(k), String.to_charlist(v)}
      end)

    url_ch = String.to_charlist(url)

    request =
      case method do
        m when m in [:get, :head] ->
          {url_ch, erl_headers}

        :post ->
          ct = fetch_ct(headers)
          {url_ch, erl_headers, String.to_charlist(ct), body || ""}
      end

    opts = [timeout: @default_timeout, connect_timeout: @connect_timeout, autoredirect: true]
    resp_opts = [body_format: :binary]

    case :httpc.request(method, request, opts, resp_opts) do
      {:ok, {{_proto, status, _reason}, resp_headers, rbody}} ->
        wire_headers =
          Enum.map(resp_headers, fn {k, v} -> {to_string(k), to_string(v)} end)

        response = %{
          __struct__: :response,
          status: status,
          headers: wire_headers,
          body: IO.iodata_to_binary(rbody)
        }

        if status >= 200 and status < 400 do
          {:ok, response}
        else
          {:error, {:bad_status, status}}
        end

      {:error, :timeout} ->
        {:error, :timeout}

      {:error, reason} ->
        {:error, {:network_error, inspect(reason)}}
    end
  end

  defp ensure_inets do
    case :inets.start() do
      :ok -> :ok
      {:error, {:already_started, :inets}} -> :ok
      _ -> :ok
    end
  end

  defp fetch_ct(headers) do
    Enum.find_value(headers, "application/octet-stream", fn {k, v} ->
      if String.downcase(k) == "content-type", do: v, else: nil
    end)
  end
end
