defmodule Cure.REPL.Theme do
  @moduledoc """
  Color palette for the Cure REPL.

  Wraps a subset of `Marcli.Theme` for Markdown rendering plus a handful
  of REPL-specific colours (prompt, status line, error, info, OK). The
  theme exposes three presets:

  * `:dark` -- the default, tuned for dark terminals.
  * `:light` -- inverted palette for light backgrounds.
  * `:mono` -- all escapes empty, for `NO_COLOR`/pipes/non-tty.

  The theme is resolved once at REPL startup and threaded through
  rendering. Call `disabled?/0` to detect when colour should be stripped
  (`NO_COLOR` env var, non-tty output, or explicit `--no-color`).
  """

  defstruct name: :dark,
            prompt: "\e[1;36m",
            prompt_cont: "\e[2;36m",
            prompt_n: "\e[1;33m",
            reset: "\e[0m",
            ok: "\e[32m",
            info: "\e[36m",
            warn: "\e[33m",
            error: "\e[1;31m",
            value: "\e[0m",
            result_arrow: "\e[1;35m",
            status: "\e[7;34m",
            dim: "\e[2m",
            underline: "\e[4m",
            search: "\e[1;33m",
            match: "\e[1;33;4m"

  @type t :: %__MODULE__{
          name: atom(),
          prompt: String.t(),
          prompt_cont: String.t(),
          prompt_n: String.t(),
          reset: String.t(),
          ok: String.t(),
          info: String.t(),
          warn: String.t(),
          error: String.t(),
          value: String.t(),
          result_arrow: String.t(),
          status: String.t(),
          dim: String.t(),
          underline: String.t(),
          search: String.t(),
          match: String.t()
        }

  @doc "Return the default (`:dark`) theme."
  @spec default() :: t()
  def default, do: %__MODULE__{}

  @doc "Look up a named theme; unknown names fall back to `:dark`."
  @spec for_name(atom() | String.t()) :: t()
  def for_name(name) when is_binary(name),
    do: for_name(String.to_atom(String.downcase(name)))

  def for_name(:light) do
    %__MODULE__{
      name: :light,
      prompt: "\e[1;34m",
      prompt_cont: "\e[2;34m",
      prompt_n: "\e[1;31m",
      ok: "\e[34m",
      info: "\e[35m",
      warn: "\e[33m",
      error: "\e[1;31m",
      value: "\e[30m",
      result_arrow: "\e[1;34m",
      status: "\e[7;34m"
    }
  end

  def for_name(:mono) do
    %__MODULE__{
      name: :mono,
      prompt: "",
      prompt_cont: "",
      prompt_n: "",
      reset: "",
      ok: "",
      info: "",
      warn: "",
      error: "",
      value: "",
      result_arrow: "",
      status: "",
      dim: "",
      underline: "",
      search: "",
      match: ""
    }
  end

  def for_name(_), do: default()

  @doc """
  Detect whether colour should be disabled for the current session.

  Disabled when `NO_COLOR` is set, when `TERM=dumb`, or when stdout is
  not a terminal.
  """
  @spec disabled?() :: boolean()
  def disabled? do
    cond do
      System.get_env("NO_COLOR") not in [nil, ""] -> true
      System.get_env("TERM") in ["dumb", ""] -> true
      not File.exists?("/dev/tty") -> true
      true -> false
    end
  end

  @doc "Strip all ANSI escape sequences from `text`."
  @spec strip_ansi(String.t()) :: String.t()
  def strip_ansi(text) when is_binary(text) do
    Regex.replace(~r/\e\[[0-9;]*[A-Za-z]/, text, "")
  end

  @doc "Apply `style` around `text`, appending the theme reset."
  @spec wrap(String.t(), t(), atom()) :: String.t()
  def wrap(text, %__MODULE__{} = theme, key) when is_atom(key) do
    style = Map.get(theme, key, "")

    if style == "" do
      text
    else
      style <> text <> theme.reset
    end
  end
end
