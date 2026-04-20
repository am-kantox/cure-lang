defmodule Cure.Sup.Runtime do
  @moduledoc """
  Convenience API for starting and inspecting compiled Cure supervisor
  trees.

  Compiled `sup` modules expose the standard `Supervisor` behaviour;
  this module is a thin wrapper that registers running trees in an ETS
  table so they can be looked up by the supervisor's Cure name.

  The table is created lazily by `start/1` to keep the application
  boot cost at zero when no supervisor trees are in use.
  """

  @table :cure_sup_runtime

  @doc """
  Start a compiled Cure supervisor module. Returns the top-level
  supervisor pid on success.
  """
  @spec start(module(), term()) :: {:ok, pid()} | {:error, term()}
  def start(sup_module, init_arg \\ []) when is_atom(sup_module) do
    ensure_table()

    case sup_module.start_link(init_arg) do
      {:ok, pid} ->
        :ets.insert(@table, {sup_module, pid})
        {:ok, pid}

      {:error, {:already_started, pid}} = result ->
        :ets.insert(@table, {sup_module, pid})
        result

      {:error, _} = err ->
        err
    end
  end

  @doc "Stop a running supervisor tree."
  @spec stop(module()) :: :ok | {:error, :not_running}
  def stop(sup_module) when is_atom(sup_module) do
    case lookup(sup_module) do
      {:ok, pid} ->
        :ets.delete(@table, sup_module)
        :ok = Supervisor.stop(pid)

      :error ->
        {:error, :not_running}
    end
  end

  @doc "Look up the pid of a running supervisor by its compiled module atom."
  @spec lookup(module()) :: {:ok, pid()} | :error
  def lookup(sup_module) when is_atom(sup_module) do
    ensure_table()

    case :ets.lookup(@table, sup_module) do
      [{^sup_module, pid}] ->
        if Process.alive?(pid) do
          {:ok, pid}
        else
          :ets.delete(@table, sup_module)
          :error
        end

      [] ->
        :error
    end
  end

  @doc """
  Enumerate the direct children of a running supervisor. Returns a
  list of `{id, child_pid, type, modules}` tuples, the shape returned
  by `Supervisor.which_children/1`.
  """
  @spec which_children(module()) :: [tuple()] | {:error, :not_running}
  def which_children(sup_module) do
    case lookup(sup_module) do
      {:ok, pid} -> Supervisor.which_children(pid)
      :error -> {:error, :not_running}
    end
  end

  @doc "List every supervisor module this runtime is tracking."
  @spec list() :: [module()]
  def list do
    ensure_table()

    :ets.tab2list(@table)
    |> Enum.filter(fn {_, pid} -> Process.alive?(pid) end)
    |> Enum.map(fn {mod, _pid} -> mod end)
  end

  # -- Internal --------------------------------------------------------------

  defp ensure_table do
    case :ets.whereis(@table) do
      :undefined ->
        :ets.new(@table, [:set, :public, :named_table])

      _ref ->
        :ok
    end
  end
end
