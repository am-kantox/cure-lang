defmodule Cure.PGO.Profile do
  @moduledoc """
  Per-module runtime profile record consumed by the v0.31.0
  profile-guided optimiser.

  ## Shape

  Every entry tracks one `{module, function, arity}` and aggregates:

  * `:calls` -- total number of times the function was entered.
  * `:total_us` -- accumulated wall-clock microseconds spent in the
    function (when timing was attached at the call site).
  * `:branches` -- map from `site_id` (an integer assigned by codegen)
    to the number of times that branch arm was taken.
  * `:smt_queries`, `:smt_total_us` -- the SMT solver's accumulated
    work attributable to this function. Only populated when the
    runtime instrumentation hooks into `Cure.SMT.Solver.check_sat/2`.

  ## Stale-profile detection

  Every entry also carries `:def_hash` -- `:erlang.phash2/1` of the
  function_def's `meta` keyword list. The PGO loader compares this
  against the `meta` of the function it is about to optimise; a
  mismatch surfaces as `:pgo_stale` and the entry is dropped.

  ## On-disk format

  `serialise/1` produces a binary suitable for `term_to_binary/2`
  with `:compressed`; `deserialise/1` is its inverse. Files are
  written under `_build/cure/pgo/<module>.profile` by
  `Cure.PGO.Recorder.flush/1`.
  """

  @type mfa_key :: {atom(), atom(), non_neg_integer()}

  @type entry :: %{
          mfa: mfa_key(),
          def_hash: non_neg_integer(),
          calls: non_neg_integer(),
          total_us: non_neg_integer(),
          branches: %{non_neg_integer() => non_neg_integer()},
          smt_queries: non_neg_integer(),
          smt_total_us: non_neg_integer()
        }

  @type t :: %__MODULE__{
          module: atom(),
          version: pos_integer(),
          captured_at: integer(),
          entries: [entry()]
        }

  @format_version 1

  defstruct module: nil,
            version: @format_version,
            captured_at: 0,
            entries: []

  @doc "Build an empty profile for `module` with the current timestamp."
  @spec new(atom()) :: t()
  def new(module) when is_atom(module) do
    %__MODULE__{
      module: module,
      version: @format_version,
      captured_at: System.system_time(:millisecond),
      entries: []
    }
  end

  @doc "Append a per-MFA entry to the profile."
  @spec add_entry(t(), entry()) :: t()
  def add_entry(%__MODULE__{} = p, %{mfa: _} = entry) do
    %{p | entries: [entry | p.entries]}
  end

  @doc "Build a per-MFA entry from raw counters."
  @spec build_entry(mfa_key(), keyword()) :: entry()
  def build_entry(mfa, opts \\ []) do
    %{
      mfa: mfa,
      def_hash: Keyword.get(opts, :def_hash, 0),
      calls: Keyword.get(opts, :calls, 0),
      total_us: Keyword.get(opts, :total_us, 0),
      branches: Keyword.get(opts, :branches, %{}),
      smt_queries: Keyword.get(opts, :smt_queries, 0),
      smt_total_us: Keyword.get(opts, :smt_total_us, 0)
    }
  end

  @doc """
  Serialise a profile to its on-disk binary representation.
  """
  @spec serialise(t()) :: binary()
  def serialise(%__MODULE__{} = p) do
    :erlang.term_to_binary(p, [:compressed, {:minor_version, 2}])
  end

  @doc """
  Deserialise a binary back into a `Cure.PGO.Profile` struct.

  Returns `{:ok, profile}` or `{:error, reason}`.
  """
  @spec deserialise(binary()) :: {:ok, t()} | {:error, term()}
  def deserialise(binary) when is_binary(binary) do
    try do
      case :erlang.binary_to_term(binary, [:safe]) do
        %__MODULE__{version: v} = p when v <= @format_version ->
          {:ok, p}

        %__MODULE__{version: v} ->
          {:error, {:unsupported_version, v}}

        other ->
          {:error, {:not_a_profile, other}}
      end
    rescue
      e -> {:error, {:decode_failure, Exception.message(e)}}
    end
  end

  @doc "Read a profile file from disk."
  @spec read(Path.t()) :: {:ok, t()} | {:error, term()}
  def read(path) do
    with {:ok, bin} <- File.read(path),
         {:ok, p} <- deserialise(bin) do
      {:ok, p}
    end
  end

  @doc "Write a profile to disk."
  @spec write(t(), Path.t()) :: :ok | {:error, term()}
  def write(%__MODULE__{} = p, path) do
    File.mkdir_p!(Path.dirname(path))
    File.write(path, serialise(p))
  end

  @doc "Format-version baked into the on-disk binary."
  @spec format_version() :: pos_integer()
  def format_version, do: @format_version
end
