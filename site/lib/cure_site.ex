defmodule CureSite do
  @moduledoc """
  CureSite keeps the contexts that define your domain
  and business logic.

  Contexts are also responsible for managing your data, regardless
  if it comes from the database, an external API or others.
  """

  # The top-level `mix.exs` of the Cure language project, relative to this
  # file. Resolved at compile time so the site always tracks the current
  # language version declared in that file.
  @cure_mix_exs Path.expand("../../mix.exs", __DIR__)
  @external_resource @cure_mix_exs

  @cure_version (case Regex.run(~r/@version\s+"([^"]+)"/, File.read!(@cure_mix_exs)) do
                   [_, version] -> version
                   _ -> "0.0.0"
                 end)

  @doc """
  Returns the Cure language version as declared in the top-level
  `mix.exs` of the Cure project.

  The value is read at compile time, so any change to the parent
  `mix.exs` triggers a recompilation of the modules that call this
  function.
  """
  @spec cure_version() :: String.t()
  def cure_version, do: @cure_version
end
