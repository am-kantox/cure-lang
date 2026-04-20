defmodule Cure.Sup.Builtins do
  @moduledoc """
  Built-in supervisor functions callable from Cure programs via
  `@extern`. Each function delegates to `Cure.Sup.Runtime`, with some
  light unwrapping so Cure callers see plain pids and atoms instead of
  `{:ok, pid}` tuples.
  """

  alias Cure.Sup.Runtime

  @doc "Start a compiled supervisor tree. Returns the supervisor pid on success."
  @spec sup_start(module()) :: pid() | {:error, term()}
  def sup_start(sup_module) when is_atom(sup_module) do
    case Runtime.start(sup_module) do
      {:ok, pid} -> pid
      {:error, {:already_started, pid}} -> pid
      {:error, reason} -> {:error, reason}
    end
  end

  @doc "Start a supervisor tree with an explicit init argument."
  @spec sup_start_with(module(), term()) :: pid() | {:error, term()}
  def sup_start_with(sup_module, init_arg) when is_atom(sup_module) do
    case Runtime.start(sup_module, init_arg) do
      {:ok, pid} -> pid
      {:error, {:already_started, pid}} -> pid
      {:error, reason} -> {:error, reason}
    end
  end

  @doc "Stop a running supervisor tree."
  @spec sup_stop(module()) :: :ok | {:error, :not_running}
  def sup_stop(sup_module) when is_atom(sup_module) do
    Runtime.stop(sup_module)
  end

  @doc "Return the supervisor's direct children."
  @spec sup_which_children(module()) :: [tuple()] | {:error, :not_running}
  def sup_which_children(sup_module) when is_atom(sup_module) do
    Runtime.which_children(sup_module)
  end

  @doc "Return a map of `{type => count}` for the supervisor's children."
  @spec sup_count_children(module()) :: map() | {:error, :not_running}
  def sup_count_children(sup_module) when is_atom(sup_module) do
    case Runtime.lookup(sup_module) do
      {:ok, pid} -> Map.new(Supervisor.count_children(pid))
      :error -> {:error, :not_running}
    end
  end

  @doc "Look up a running supervisor by module atom; returns the pid or `nil`."
  @spec sup_lookup(module()) :: pid() | nil
  def sup_lookup(sup_module) when is_atom(sup_module) do
    case Runtime.lookup(sup_module) do
      {:ok, pid} -> pid
      :error -> nil
    end
  end

  @doc "Return the list of currently-running supervisor module atoms."
  @spec sup_list() :: [module()]
  def sup_list do
    Runtime.list()
  end
end
