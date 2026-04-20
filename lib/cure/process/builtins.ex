defmodule Cure.Process.Builtins do
  @moduledoc """
  FFI surface for `Std.Process`.

  Most BEAM process primitives are callable directly via
  `@extern(:erlang, ...)`, but two of them benefit from a thin wrapper:

    * `proc_monitor/1` — `:erlang.monitor/2` takes a leading `:process`
      atom, which would otherwise have to be threaded through Cure
      source.

    * `proc_trap_exit/1` — `:erlang.process_flag/2` takes the tag as
      its first argument; wrapping it keeps the Cure signature a
      straightforward `(Bool) -> Bool`.
  """

  @doc "Install a process monitor; return the opaque `Ref`."
  @spec proc_monitor(pid()) :: reference()
  def proc_monitor(pid) when is_pid(pid) do
    :erlang.monitor(:process, pid)
  end

  @doc """
  Toggle `trap_exit` on the caller. Returns the *previous* value so
  callers can restore it.
  """
  @spec proc_trap_exit(boolean()) :: boolean()
  def proc_trap_exit(flag) when is_boolean(flag) do
    :erlang.process_flag(:trap_exit, flag)
  end
end
