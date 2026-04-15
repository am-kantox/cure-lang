defmodule Cure.Types.ProtocolRegistry do
  @moduledoc """
  Global protocol implementation registry backed by ETS.

  When a module with `impl Show for Int` is compiled, the implementation
  is registered here so that other modules can discover and call it.

  ## Registry Structure

  Each entry maps `{protocol_name, method_name, for_type}` to the
  module atom that provides the implementation.

  ## Usage

      # Register (done automatically during codegen)
      ProtocolRegistry.register_impl("Show", "show", "Int", :my_module)

      # Lookup (done during codegen import resolution)
      {:ok, :my_module} = ProtocolRegistry.lookup_impl("Show", "show", "Int")

      # Check if a type has an impl for a protocol
      true = ProtocolRegistry.has_impl?("Show", "Int")
  """

  @table :cure_protocol_registry

  @doc "Start the registry (creates the ETS table)."
  @spec start() :: :ok
  def start do
    if :ets.whereis(@table) == :undefined do
      :ets.new(@table, [:set, :public, :named_table])
    end

    :ok
  end

  @doc """
  Register a protocol implementation.

  Records that `module_atom` provides `method_name` for `for_type`
  under `protocol_name`.
  """
  @spec register_impl(String.t(), String.t(), String.t(), atom()) :: :ok
  def register_impl(protocol_name, method_name, for_type, module_atom) do
    ensure_table()
    key = {protocol_name, method_name, for_type}
    :ets.insert(@table, {key, module_atom})
    :ok
  end

  @doc """
  Look up which module provides a method implementation.

  Returns `{:ok, module_atom}` or `:error`.
  """
  @spec lookup_impl(String.t(), String.t(), String.t()) :: {:ok, atom()} | :error
  def lookup_impl(protocol_name, method_name, for_type) do
    ensure_table()

    case :ets.lookup(@table, {protocol_name, method_name, for_type}) do
      [{_key, module_atom}] -> {:ok, module_atom}
      [] -> :error
    end
  rescue
    ArgumentError -> :error
  end

  @doc """
  Check if a type has any implementation for a given protocol.
  """
  @spec has_impl?(String.t(), String.t()) :: boolean()
  def has_impl?(protocol_name, for_type) do
    ensure_table()

    :ets.match_object(@table, {{protocol_name, :_, for_type}, :_})
    |> Enum.any?()
  rescue
    ArgumentError -> false
  end

  @doc """
  List all implementations for a protocol.

  Returns a list of `{for_type, method_name, module_atom}` tuples.
  """
  @spec list_impls(String.t()) :: [{String.t(), String.t(), atom()}]
  def list_impls(protocol_name) do
    ensure_table()

    :ets.match_object(@table, {{protocol_name, :_, :_}, :_})
    |> Enum.map(fn {{_proto, method, for_type}, module} ->
      {for_type, method, module}
    end)
  rescue
    ArgumentError -> []
  end

  @doc "List all implementations for a given method name (across all protocols)."
  @spec list_impls_by_method(String.t()) :: [{String.t(), String.t(), atom()}]
  def list_impls_by_method(method_name) do
    ensure_table()

    :ets.match_object(@table, {{:_, method_name, :_}, :_})
    |> Enum.map(fn {{_proto, method, for_type}, module} ->
      {for_type, method, module}
    end)
  rescue
    ArgumentError -> []
  end

  @doc "Clear all registry entries (for testing)."
  @spec clear() :: :ok
  def clear do
    if :ets.whereis(@table) != :undefined do
      :ets.delete_all_objects(@table)
    end

    :ok
  end

  defp ensure_table do
    if :ets.whereis(@table) == :undefined do
      :ets.new(@table, [:set, :public, :named_table])
    end
  end
end
