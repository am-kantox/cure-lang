defmodule Cure.App.Builtins do
  @moduledoc """
  Built-in application functions callable from Cure programs via
  `@extern`. Every function wraps an Erlang `:application` BIF and
  returns plain values so Cure callers see idiomatic return shapes
  (`:ok` / atoms / maps / lists) rather than tagged OTP tuples.
  """

  @doc "Ensure the application and all of its dependencies are started."
  @spec ensure_all_started(atom()) :: :ok | {:error, term()}
  def ensure_all_started(name) when is_atom(name) do
    case :application.ensure_all_started(name) do
      {:ok, _started} -> :ok
      {:error, _} = err -> err
    end
  end

  @doc "Start a loaded application by name."
  @spec start(atom()) :: :ok | {:error, term()}
  def start(name) when is_atom(name) do
    case :application.start(name) do
      :ok -> :ok
      {:error, {:already_started, _}} -> :ok
      {:error, _} = err -> err
    end
  end

  @doc "Stop a running application by name."
  @spec stop(atom()) :: :ok | {:error, term()}
  def stop(name) when is_atom(name) do
    case :application.stop(name) do
      :ok -> :ok
      {:error, {:not_started, _}} -> :ok
      {:error, _} = err -> err
    end
  end

  @doc "Fetch an environment variable for an application. Returns `nil` when unset."
  @spec get_env(atom(), atom()) :: term() | nil
  def get_env(name, key) when is_atom(name) and is_atom(key) do
    case :application.get_env(name, key) do
      {:ok, value} -> value
      :undefined -> nil
    end
  end

  @doc "Fetch an environment variable, returning a default when unset."
  @spec get_env(atom(), atom(), term()) :: term()
  def get_env(name, key, default) when is_atom(name) and is_atom(key) do
    case :application.get_env(name, key) do
      {:ok, value} -> value
      :undefined -> default
    end
  end

  @doc "Set an environment variable for an application."
  @spec put_env(atom(), atom(), term()) :: :ok
  def put_env(name, key, value) when is_atom(name) and is_atom(key) do
    :ok = :application.set_env([{name, [{key, value}]}], persistent: true)
    :ok
  end

  @doc "Return a list of `{name, description, vsn}` tuples for all running applications."
  @spec which_applications() :: [tuple()]
  def which_applications do
    :application.which_applications()
  end

  @doc "Return a list of names of applications currently loaded into the VM."
  @spec loaded_applications() :: [atom()]
  def loaded_applications do
    for {name, _desc, _vsn} <- :application.loaded_applications(), do: name
  end

  @doc """
  Start a specific start phase of an application.

  OTP does not expose a public API for invoking phases out-of-band
  (the release boot script does it for you). This function dispatches
  to the generated `start_phase/3` callback directly on the loaded
  application module so tests and tooling can exercise phases without
  a full release boot.
  """
  @spec start_phase(atom(), atom(), term()) :: term()
  def start_phase(name, phase, phase_args)
      when is_atom(name) and is_atom(phase) do
    mod = app_module(name)

    if function_exported?(mod, :start_phase, 3) do
      mod.start_phase(phase, :normal, phase_args)
    else
      {:error, {:no_start_phase, name}}
    end
  end

  defp app_module(name) do
    spec = Application.spec(name) || []

    case Keyword.get(spec, :mod) do
      {mod, _args} when is_atom(mod) -> mod
      _ -> String.to_atom("Cure.App." <> Macro.camelize(to_string(name)))
    end
  end
end
