defmodule CureForge do
  @moduledoc """
  Thin Elixir facade over the Cure forge application.

  The entire supervision tree is declared in six `.cure` files under
  `cure_src/`:

    * `forge_app.cure`   -- `app CureForge`
    * `forge_root.cure`  -- `sup Forge.Root`
    * `metrics.cure`     -- `actor Metrics`
    * `logger.cure`      -- `actor Logger`
    * `queue.cure`       -- `actor Queue`
    * `pool.cure`        -- `actor Pool`

  The compiled modules are, respectively, `Cure.App.CureForge`,
  `Cure.Sup.Forge.Root`, `Cure.Actor.Metrics`, `Cure.Actor.Logger`,
  `Cure.Actor.Queue`, and `Cure.Actor.Pool`. `CureForge.Application`
  starts `Cure.Sup.Forge.Root` under its own top-level `Supervisor`,
  which in turn starts the four actors under the `:one_for_one`
  strategy declared in `forge_root.cure`.

  ## Quick Start

      # The application starts the tree automatically:
      iex> {:ok, _} = Application.ensure_all_started(:cure_forge)
      iex> is_pid(Process.whereis(:"Cure.Sup.Forge.Root"))
      true

      # Enqueue three tasks, drain them into the pool, check metrics:
      iex> CureForge.submit(:ok)
      iex> CureForge.submit(:ok)
      iex> CureForge.submit({:fail, :timeout})
      iex> CureForge.drain_queue()
      iex> CureForge.metrics()
      %{requests: 2, errors: 1}

      # Log lines are buffered and can be drained:
      iex> CureForge.log("booted")
      iex> CureForge.log("first tick")
      iex> CureForge.drain_log()
      ["first tick", "booted"]

      # Application env is readable through Std.App (or Application):
      iex> Application.get_env(:cure_forge, :greeting)
      "forge ready"
  """

  require Logger

  @sup_module :"Cure.Sup.Forge.Root"
  @metrics_module :"Cure.Actor.Metrics"
  @logger_module :"Cure.Actor.Logger"
  @queue_module :"Cure.Actor.Queue"
  @pool_module :"Cure.Actor.Pool"

  # -- Module accessors ------------------------------------------------------

  @doc "Atom of the compiled root supervisor."
  @spec sup_module() :: module()
  def sup_module, do: @sup_module

  @doc "Atoms of the compiled actor modules, by supervisor id."
  @spec actor_modules() :: %{atom() => module()}
  def actor_modules do
    %{
      metrics: @metrics_module,
      logger: @logger_module,
      queue: @queue_module,
      pool: @pool_module
    }
  end

  # -- Supervisor introspection ---------------------------------------------

  @doc """
  Return the list of children as `{id, pid, type, modules}` tuples,
  in the order reported by `Supervisor.which_children/1`.
  """
  @spec which_children() :: [tuple()]
  def which_children, do: Supervisor.which_children(@sup_module)

  @doc "Return the pid of a specific supervisor child, or `nil`."
  @spec child_pid(atom()) :: pid() | nil
  def child_pid(id) do
    Enum.find_value(which_children(), fn
      {^id, pid, _type, _modules} when is_pid(pid) -> pid
      _ -> nil
    end)
  end

  @doc "Return the pid of the metrics actor."
  @spec metrics_pid() :: pid() | nil
  def metrics_pid, do: child_pid(:metrics)

  @doc "Return the pid of the logger actor."
  @spec logger_pid() :: pid() | nil
  def logger_pid, do: child_pid(:logger)

  @doc "Return the pid of the queue actor."
  @spec queue_pid() :: pid() | nil
  def queue_pid, do: child_pid(:queue)

  @doc "Return the pid of the pool actor."
  @spec pool_pid() :: pid() | nil
  def pool_pid, do: child_pid(:pool)

  # -- Metrics ---------------------------------------------------------------

  @doc "Return the current metrics snapshot `%{requests:, errors:}`."
  @spec metrics() :: %{
          required(:requests) => non_neg_integer(),
          required(:errors) => non_neg_integer()
        }
  def metrics, do: @metrics_module.get_state(metrics_pid())

  @doc "Reset the metrics counters to zero."
  @spec reset_metrics() :: :ok
  def reset_metrics, do: send_sync(metrics_pid(), :reset)

  @doc "Record an observed outcome (`:ok` or anything else) in the metrics."
  @spec observe(:ok | term()) :: :ok
  def observe(outcome), do: send_sync(metrics_pid(), [:observe, outcome])

  # -- Logger ---------------------------------------------------------------

  @doc "Buffer a log line in the logger actor."
  @spec log(binary() | term()) :: :ok
  def log(line), do: send_sync(logger_pid(), [:log, line])

  @doc """
  Drain the logger buffer. Returns the list of buffered lines
  (oldest first) and resets the buffer. Capped at `max_log_lines`
  from `Application.get_env/3`, matching the `[application.env]`
  declaration in `Cure.toml`.
  """
  @spec drain_log() :: [term()]
  def drain_log do
    pid = logger_pid()
    cap = Application.get_env(:cure_forge, :max_log_lines, 16)

    lines =
      receive_notification(pid, :drain, fn
        [:lines, buffer] -> {:ok, Enum.reverse(buffer)}
        _ -> :skip
      end)

    Enum.take(lines, cap)
  end

  @doc "Return the current logger buffer size without draining it."
  @spec log_size() :: non_neg_integer()
  def log_size do
    receive_notification(logger_pid(), :size, fn
      [:size, n] -> {:ok, n}
      _ -> :skip
    end)
  end

  # -- Queue -----------------------------------------------------------------

  @doc """
  Submit a task to the queue. A task is any term; convention is
  `:ok` for a successful task and `{:fail, reason}` for a failure.
  Tasks are drained into the pool by `drain_queue/0`.
  """
  @spec submit(term()) :: :ok
  def submit(task), do: send_sync(queue_pid(), [:enqueue, task])

  @doc "Return the current queue length."
  @spec queue_size() :: non_neg_integer()
  def queue_size do
    receive_notification(queue_pid(), :size, fn
      [:size, n] -> {:ok, n}
      _ -> :skip
    end)
  end

  @doc """
  Drain every task currently in the queue into the pool.

  For each dequeued task `t`, this function sends `{:task, t}` to
  the pool via the Melquiades Operator (`pid <-| msg` in Cure, which
  lowers to Erlang's `!`), waits for the pool to notify its outcome,
  and forwards that outcome to the metrics actor as an `:observe`
  message. The round trip exercises the full flow:

      Queue --(dequeue)--> facade --(<-|)--> Pool --(notify)--> facade --(observe)--> Metrics
  """
  @spec drain_queue() :: {:ok, non_neg_integer()}
  def drain_queue do
    drain_queue_loop(0)
  end

  defp drain_queue_loop(count) do
    q_pid = queue_pid()
    p_pid = pool_pid()

    result =
      receive_notification(q_pid, :dequeue, fn
        [:task, task] -> {:ok, {:task, task}}
        :empty -> {:ok, :empty}
        _ -> :skip
      end)

    case result do
      :empty ->
        {:ok, count}

      {:task, task} ->
        # Forward the task to the pool -- this is exactly what the
        # Melquiades Operator (`pool_pid <-| {:task, task}`) would do
        # in Cure source.
        outcome =
          receive_notification(p_pid, {:task, task}, fn
            [:done, verdict] -> {:ok, verdict}
            _ -> :skip
          end)

        # Close the loop: observe the outcome in the metrics actor.
        observe(outcome)
        drain_queue_loop(count + 1)
    end
  end

  # -- Pool ------------------------------------------------------------------

  @doc "Return the pool's current `%{done:, failed:}` snapshot."
  @spec pool_state() :: %{
          required(:done) => non_neg_integer(),
          required(:failed) => non_neg_integer()
        }
  def pool_state, do: @pool_module.get_state(pool_pid())

  @doc "Reset the pool's counters."
  @spec reset_pool() :: :ok
  def reset_pool, do: send_sync(pool_pid(), :reset)

  # -- Internals ------------------------------------------------------------

  defp send_sync(pid, msg) when is_pid(pid) do
    send(pid, msg)
    _ = :sys.get_state(pid)
    :ok
  end

  defp send_sync(nil, _msg), do: :no_target

  # Spawn a short-lived child process that becomes the actor's
  # `:caller`, send the trigger message from that child, and wait for
  # the matching notification to arrive. The child's mailbox is
  # isolated from the caller's, so multiple overlapping operations do
  # not race.
  defp receive_notification(pid, trigger, matcher) do
    parent = self()

    spawn_link(fn ->
      send(pid, trigger)
      _ = :sys.get_state(pid)

      loop = fn loop ->
        receive do
          msg ->
            case matcher.(msg) do
              {:ok, value} -> send(parent, {:cure_forge_notify, self(), value})
              :skip -> loop.(loop)
            end
        after
          1_000 -> send(parent, {:cure_forge_notify, self(), :timeout})
        end
      end

      loop.(loop)
    end)

    receive do
      {:cure_forge_notify, _child, value} -> value
    after
      1_500 -> {:error, :timeout}
    end
  end
end
