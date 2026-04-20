defmodule Cure.REPL.Terminal do
  @moduledoc """
  Raw-mode terminal I/O for the interactive REPL.

  Under an escript launcher (`./cure repl`), `:stdio` is wired through the
  BEAM group-leader which buffers input line-by-line and strips ANSI escape
  sequences on the way out. Reading raw keypresses and writing coloured
  prompts through `:stdio` therefore simply does not work. Instead, this
  module opens `/dev/tty` directly for both reading and writing:

      {:ok, read_fd}  = :file.open(~c"/dev/tty", [:read, :raw, :binary])
      {:ok, write_fd} = :file.open(~c"/dev/tty", [:write, :raw, :binary])

  The file descriptors are stashed in the REPL process' dictionary. BEAM
  itself inherits the shell's controlling terminal, so opening `/dev/tty`
  from within the Erlang VM succeeds.

  `stty` is trickier. Every port BEAM spawns (via `System.cmd/3`,
  `Port.open/2`, ...) is routed through `erl_child_setup`, which runs in
  its own session and has **no controlling terminal**. That means a
  `sh -c "stty ... </dev/tty"` child reliably fails with

      /bin/sh: cannot open /dev/tty: No such device or address

  because `open("/dev/tty", ...)` requires a controlling tty the child
  does not have. We therefore discover the *path* of BEAM's tty up-front
  (via `/proc/self/fd/{0,1,2}` on Linux, `/dev/fd/{0,1,2}` on BSD/macOS)
  and drive stty with `-F <path>` (GNU) / `-f <path>` (BSD), which makes
  stty `open(3)` the device directly -- no controlling tty required.

  Responsibilities:

    1. Put the terminal into cbreak / no-echo mode and guarantee restoration
       on any exit path (normal return, crash, signal).
    2. Decode raw byte streams from the tty into high-level key events
       (arrows, `Ctrl+*`, `Alt+*`, `Home`/`End`/`Delete`, `PgUp`/`PgDn`,
       bracketed paste, F-keys).
    3. Detect whether a controlling terminal is available so the REPL can
       fall back to the line-mode `IO.gets` loop for CI / pipes.
  """

  @read_key :cure_repl_tty_read_fd
  @write_key :cure_repl_tty_write_fd
  @state_key :cure_repl_tty_saved
  @tty_path_key :cure_repl_tty_path
  @stty_flag_key :cure_repl_stty_file_flag

  @typedoc "A single decoded keypress."
  @type key ::
          :enter
          | :tab
          | :backspace
          | :delete
          | :esc
          | :eof
          | :up
          | :down
          | :left
          | :right
          | :home
          | :end
          | :pgup
          | :pgdn
          | :word_left
          | :word_right
          | :shift_tab
          | :insert
          | {:key, binary()}
          | {:ctrl, 0..127}
          | {:alt, binary()}
          | {:fn, 1..12}
          | {:paste, binary()}
          | {:raw, binary()}

  @doc """
  True when `/dev/tty` exists and looks like an interactive terminal.
  """
  @spec tty?() :: boolean()
  def tty? do
    cond do
      not File.exists?("/dev/tty") ->
        false

      System.get_env("TERM") in [nil, "", "dumb"] ->
        false

      # OTP 26+: `prim_tty:isatty/1` gives a proper isatty(3) answer on the
      # BEAM's own stdin, without requiring us to shell out.
      function_exported?(:prim_tty, :isatty, 1) ->
        :prim_tty.isatty(:stdin) == true

      true ->
        # Older OTP: use the resolved tty path + a stty probe against it.
        case tty_path() do
          nil -> false
          path -> match?({:ok, _}, run_stty(path, ["-g"]))
        end
    end
  rescue
    _ -> false
  end

  @doc """
  Put the terminal into raw mode. Opens `/dev/tty` for both reading and
  writing and stashes the handles in the process dictionary. Returns an
  opaque handle that must be passed back to `restore/1`.
  """
  @spec enter_raw() :: {:ok, binary()} | {:error, term()}
  def enter_raw do
    with {:ok, saved} <- stty_query(),
         :ok <- stty_raw(),
         {:ok, read_fd} <- :file.open(~c"/dev/tty", [:read, :raw, :binary]),
         {:ok, write_fd} <- :file.open(~c"/dev/tty", [:write, :raw, :binary]) do
      Process.put(@read_key, read_fd)
      Process.put(@write_key, write_fd)
      Process.put(@state_key, saved)
      enable_bracketed_paste()
      {:ok, saved}
    else
      {:error, _} = err ->
        # Best-effort cleanup if we partially succeeded.
        stty_restore(Process.get(@state_key))
        err
    end
  end

  @doc "Restore the tty to the state captured by `enter_raw/0`."
  @spec restore(binary() | nil) :: :ok
  def restore(saved) do
    disable_bracketed_paste()
    close_ttys()
    stty_restore(saved || Process.get(@state_key))
    Process.delete(@read_key)
    Process.delete(@write_key)
    Process.delete(@state_key)
    :ok
  end

  @doc """
  Run `fun` inside raw-mode context; restores the terminal on any exit.
  """
  @spec with_raw_io((-> any())) :: any()
  def with_raw_io(fun) when is_function(fun, 0) do
    case enter_raw() do
      {:ok, saved} ->
        try do
          fun.()
        after
          restore(saved)
        end

      {:error, _} ->
        fun.()
    end
  end

  @doc """
  Write bytes to the terminal. Prefers `/dev/tty` when raw mode is active,
  otherwise falls back to `:stdio`.
  """
  @spec write(iodata()) :: :ok
  def write(iodata) do
    case Process.get(@write_key) do
      nil ->
        IO.binwrite(:stdio, iodata)

      fd ->
        :file.write(fd, iodata)
    end

    :ok
  end

  @doc """
  Read and decode a single keypress.
  """
  @spec read_key() :: key()
  def read_key do
    case read_byte() do
      :eof -> :eof
      b -> decode_byte(b)
    end
  end

  @doc false
  # Exposed for unit tests: decode a fully-captured byte sequence.
  @spec decode(binary()) :: key()
  def decode(<<b>>), do: decode_byte(b, fn -> :eof end)

  def decode(<<0x1B, rest::binary>>) when byte_size(rest) > 0 do
    decode_escape_rest(rest)
  end

  def decode(<<b, _::binary>>), do: decode_byte(b, fn -> :eof end)

  # -- Decoding ---------------------------------------------------------------

  defp decode_byte(b), do: decode_byte(b, &read_more/0)

  defp decode_byte(0, _), do: {:ctrl, 0}
  defp decode_byte(9, _), do: :tab
  defp decode_byte(10, _), do: :enter
  defp decode_byte(13, _), do: :enter
  defp decode_byte(127, _), do: :backspace
  defp decode_byte(8, _), do: :backspace
  defp decode_byte(4, _), do: {:ctrl, ?D}

  defp decode_byte(b, read_more) when b == 0x1B do
    case read_more.() do
      :eof -> :esc
      byte when is_integer(byte) -> decode_escape(byte, read_more)
    end
  end

  defp decode_byte(b, _) when b in 1..31, do: {:ctrl, b + 64}

  defp decode_byte(b, read_more) when b in 0xC2..0xF4 do
    needed = utf8_tail(b)
    read_utf8(<<b>>, needed, read_more)
  end

  defp decode_byte(b, _) when b in 32..126, do: {:key, <<b>>}
  defp decode_byte(b, _), do: {:raw, <<b>>}

  defp decode_escape(?[, read_more), do: decode_csi(<<>>, read_more)
  defp decode_escape(?O, read_more), do: decode_ss3(read_more)
  defp decode_escape(0x1B, _), do: :esc

  defp decode_escape(b, _read_more) when b in 32..126, do: {:alt, <<b>>}
  defp decode_escape(b, _), do: {:raw, <<0x1B, b>>}

  defp decode_escape_rest(<<?[, rest::binary>>), do: decode_csi_binary(rest)
  defp decode_escape_rest(<<?O, rest::binary>>), do: decode_ss3_binary(rest)
  defp decode_escape_rest(<<b, _::binary>>) when b in 32..126, do: {:alt, <<b>>}
  defp decode_escape_rest(bin), do: {:raw, <<0x1B>> <> bin}

  # -- CSI sequences --------------------------------------------------------

  defp decode_csi(buf, read_more) do
    case read_more.() do
      :eof -> {:raw, <<0x1B, ?[>> <> buf}
      byte when byte in 0x40..0x7E -> classify_csi(buf, byte)
      byte -> decode_csi(buf <> <<byte>>, read_more)
    end
  end

  defp decode_csi_binary(bin) do
    case :binary.match(bin, [
           <<?A>>,
           <<?B>>,
           <<?C>>,
           <<?D>>,
           <<?F>>,
           <<?H>>,
           <<?~>>,
           <<?Z>>
         ]) do
      {pos, 1} ->
        params = binary_part(bin, 0, pos)
        <<final, _::binary>> = binary_part(bin, pos, byte_size(bin) - pos)
        classify_csi(params, final)

      :nomatch ->
        {:raw, <<0x1B, ?[>> <> bin}
    end
  end

  defp classify_csi(<<>>, ?A), do: :up
  defp classify_csi(<<>>, ?B), do: :down
  defp classify_csi(<<>>, ?C), do: :right
  defp classify_csi(<<>>, ?D), do: :left
  defp classify_csi(<<>>, ?H), do: :home
  defp classify_csi(<<>>, ?F), do: :end
  defp classify_csi(<<>>, ?Z), do: :shift_tab

  defp classify_csi("1;5", ?C), do: :word_right
  defp classify_csi("1;5", ?D), do: :word_left
  defp classify_csi("1;5", ?A), do: :up
  defp classify_csi("1;5", ?B), do: :down
  defp classify_csi("1;3", ?C), do: :word_right
  defp classify_csi("1;3", ?D), do: :word_left
  defp classify_csi("1;2", ?Z), do: :shift_tab

  defp classify_csi("1", ?~), do: :home
  defp classify_csi("7", ?~), do: :home
  defp classify_csi("4", ?~), do: :end
  defp classify_csi("8", ?~), do: :end
  defp classify_csi("2", ?~), do: :insert
  defp classify_csi("3", ?~), do: :delete
  defp classify_csi("5", ?~), do: :pgup
  defp classify_csi("6", ?~), do: :pgdn
  defp classify_csi("11", ?~), do: {:fn, 1}
  defp classify_csi("12", ?~), do: {:fn, 2}
  defp classify_csi("13", ?~), do: {:fn, 3}
  defp classify_csi("14", ?~), do: {:fn, 4}
  defp classify_csi("15", ?~), do: {:fn, 5}
  defp classify_csi("17", ?~), do: {:fn, 6}
  defp classify_csi("18", ?~), do: {:fn, 7}
  defp classify_csi("19", ?~), do: {:fn, 8}
  defp classify_csi("20", ?~), do: {:fn, 9}
  defp classify_csi("21", ?~), do: {:fn, 10}
  defp classify_csi("23", ?~), do: {:fn, 11}
  defp classify_csi("24", ?~), do: {:fn, 12}

  defp classify_csi("200", ?~), do: read_paste()
  defp classify_csi(params, final), do: {:raw, <<0x1B, ?[>> <> params <> <<final>>}

  # -- SS3 sequences --------------------------------------------------------

  defp decode_ss3(read_more) do
    case read_more.() do
      :eof -> {:raw, <<0x1B, ?O>>}
      ?A -> :up
      ?B -> :down
      ?C -> :right
      ?D -> :left
      ?H -> :home
      ?F -> :end
      ?P -> {:fn, 1}
      ?Q -> {:fn, 2}
      ?R -> {:fn, 3}
      ?S -> {:fn, 4}
      byte -> {:raw, <<0x1B, ?O, byte>>}
    end
  end

  defp decode_ss3_binary(<<byte, _::binary>>), do: decode_ss3(fn -> byte end)
  defp decode_ss3_binary(<<>>), do: {:raw, <<0x1B, ?O>>}

  # -- UTF-8 ----------------------------------------------------------------

  defp utf8_tail(b) when b in 0xC2..0xDF, do: 1
  defp utf8_tail(b) when b in 0xE0..0xEF, do: 2
  defp utf8_tail(b) when b in 0xF0..0xF4, do: 3

  defp read_utf8(acc, 0, _), do: {:key, acc}

  defp read_utf8(acc, n, read_more) do
    case read_more.() do
      :eof -> {:raw, acc}
      byte -> read_utf8(acc <> <<byte>>, n - 1, read_more)
    end
  end

  # -- Bracketed paste ------------------------------------------------------

  defp read_paste, do: read_paste("")

  defp read_paste(acc) do
    case read_byte() do
      :eof ->
        {:paste, acc}

      0x1B ->
        # Possible paste-end sequence ESC [ 2 0 1 ~. `read_n/1` always
        # returns a binary (possibly empty), so two clauses exhaustively
        # cover the shape of `tail`.
        case read_n(5) do
          "[201~" -> {:paste, acc}
          other -> read_paste(acc <> <<0x1B>> <> other)
        end

      b ->
        read_paste(acc <> <<b>>)
    end
  end

  # -- Raw byte I/O ---------------------------------------------------------

  defp read_byte do
    case Process.get(@read_key) do
      nil ->
        # No tty handle: fall back to the group leader (legacy loop scenario).
        case IO.binread(:stdio, 1) do
          :eof -> :eof
          {:error, _} -> :eof
          <<b>> -> b
          bin when is_binary(bin) and byte_size(bin) > 0 -> :binary.first(bin)
        end

      fd ->
        case :file.read(fd, 1) do
          {:ok, <<b>>} -> b
          {:ok, bin} when is_binary(bin) and byte_size(bin) > 0 -> :binary.first(bin)
          :eof -> :eof
          {:error, _} -> :eof
        end
    end
  end

  defp read_n(n) do
    case Process.get(@read_key) do
      nil ->
        case IO.binread(:stdio, n) do
          bin when is_binary(bin) -> bin
          _ -> ""
        end

      fd ->
        case :file.read(fd, n) do
          {:ok, bin} when is_binary(bin) -> bin
          _ -> ""
        end
    end
  end

  defp read_more do
    case read_byte() do
      :eof -> :eof
      b -> b
    end
  end

  # -- stty helpers (operate on BEAM's controlling tty) ----------------------
  #
  # Children spawned via `System.cmd/3` (and any other `Port.open`-based
  # mechanism) live in a session that has no controlling terminal, so
  # `sh -c "stty ... </dev/tty"` fails with ENXIO. We avoid that by
  # resolving the tty *path* once from BEAM's side (which *does* have a
  # controlling tty) and passing it to stty with `-F` / `-f`.

  defp stty_query do
    with {:ok, path} <- require_tty_path(),
         {:ok, out} <- run_stty(path, ["-g"]) do
      {:ok, String.trim(out)}
    end
  rescue
    e -> {:error, e}
  end

  defp stty_raw do
    with {:ok, path} <- require_tty_path(),
         {:ok, _} <- run_stty(path, ~w[-icanon -echo -isig min 1 time 0]) do
      :ok
    end
  rescue
    e -> {:error, e}
  end

  defp stty_restore(nil), do: :ok

  defp stty_restore(saved) when is_binary(saved) do
    with {:ok, path} <- require_tty_path() do
      _ = run_stty(path, [saved])
      :ok
    else
      _ -> :ok
    end
  rescue
    _ -> :ok
  end

  # Run stty against a specific device path. Tries GNU-style `-F` first
  # and falls back to BSD/macOS-style `-f`. The detected flag is cached
  # in the process dictionary to avoid repeated probes.
  defp run_stty(path, args) do
    case Process.get(@stty_flag_key) do
      nil -> run_stty_probing(path, args)
      flag -> run_stty_with_flag(flag, path, args)
    end
  end

  defp run_stty_probing(path, args) do
    case System.cmd("stty", ["-F", path | args], stderr_to_stdout: true) do
      {out, 0} ->
        Process.put(@stty_flag_key, "-F")
        {:ok, out}

      {err_f, _code_f} ->
        case System.cmd("stty", ["-f", path | args], stderr_to_stdout: true) do
          {out, 0} ->
            Process.put(@stty_flag_key, "-f")
            {:ok, out}

          {_err_lower, code} ->
            {:error, {code, err_f}}
        end
    end
  rescue
    e -> {:error, e}
  end

  defp run_stty_with_flag(flag, path, args) do
    case System.cmd("stty", [flag, path | args], stderr_to_stdout: true) do
      {out, 0} -> {:ok, out}
      {err, code} -> {:error, {code, err}}
    end
  rescue
    e -> {:error, e}
  end

  defp require_tty_path do
    case tty_path() do
      nil -> {:error, :no_tty_path}
      path -> {:ok, path}
    end
  end

  # Resolve the filesystem path of BEAM's controlling terminal by walking
  # the per-process fd symlinks. BEAM inherits the shell's tty on fds
  # 0/1/2 when launched as an escript, so at least one of those will point
  # to a `/dev/pts/*`, `/dev/tty*`, or `/dev/console` node. We cache the
  # first match for the lifetime of the REPL process.
  defp tty_path do
    case Process.get(@tty_path_key) do
      nil ->
        path = detect_tty_path()
        if is_binary(path), do: Process.put(@tty_path_key, path)
        path

      cached ->
        cached
    end
  end

  defp detect_tty_path do
    Enum.find_value(tty_fd_candidates(), fn candidate ->
      case File.read_link(candidate) do
        {:ok, target} -> if tty_like?(target), do: target, else: nil
        _ -> nil
      end
    end)
  end

  defp tty_fd_candidates do
    [
      "/proc/self/fd/0",
      "/proc/self/fd/1",
      "/proc/self/fd/2",
      "/dev/fd/0",
      "/dev/fd/1",
      "/dev/fd/2"
    ]
  end

  # `File.read_link/1` (our only caller via `detect_tty_path/0`) always
  # hands us a binary on its success path, so a non-binary fallback here
  # would be unreachable dead code.
  defp tty_like?(path) when is_binary(path) do
    String.starts_with?(path, "/dev/pts/") or
      String.starts_with?(path, "/dev/ttys") or
      String.starts_with?(path, "/dev/tty") or
      path == "/dev/console"
  end

  defp close_ttys do
    case Process.get(@read_key) do
      nil -> :ok
      fd -> :file.close(fd)
    end

    case Process.get(@write_key) do
      nil -> :ok
      fd -> :file.close(fd)
    end
  end

  defp enable_bracketed_paste, do: write("\e[?2004h")
  defp disable_bracketed_paste, do: write("\e[?2004l")
end
