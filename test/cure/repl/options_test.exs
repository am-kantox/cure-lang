defmodule Cure.REPL.OptionsTest do
  use ExUnit.Case, async: true

  alias Cure.REPL.Options

  describe "switches/0" do
    test "exposes the exact switch definition used by the CLI" do
      switches = Options.switches()

      assert Keyword.fetch!(switches, :raw) == :boolean
      assert Keyword.fetch!(switches, :theme) == :string
      assert Keyword.fetch!(switches, :mode) == :string
      assert Keyword.fetch!(switches, :history) == :string
      assert Keyword.fetch!(switches, :no_history) == :boolean
      assert Keyword.fetch!(switches, :error_device) == :string
    end
  end

  describe "build_opts/1" do
    test "returns empty opts and empty warnings when nothing is parsed" do
      assert {[], []} = Options.build_opts([])
    end

    test "translates --raw and --no-raw" do
      assert {[raw: true], []} = Options.build_opts(raw: true)
      assert {[raw: false], []} = Options.build_opts(raw: false)
    end

    test "translates --theme names, including auto" do
      assert {[theme: :dark], []} = Options.build_opts(theme: "dark")
      assert {[theme: :light], []} = Options.build_opts(theme: "light")
      assert {[theme: :mono], []} = Options.build_opts(theme: "mono")
      assert {[theme: :auto], []} = Options.build_opts(theme: "auto")
    end

    test "translates --mode names" do
      assert {[mode: :emacs], []} = Options.build_opts(mode: "emacs")
      assert {[mode: :vi], []} = Options.build_opts(mode: "vi")
    end

    test "translates --history and --no-history" do
      assert {[history_path: "/tmp/h"], []} = Options.build_opts(history: "/tmp/h")
      assert {[history_path: nil], []} = Options.build_opts(history: "")
      assert {[history_path: nil], []} = Options.build_opts(no_history: true)
      assert {[], []} = Options.build_opts(no_history: false)
    end

    test "translates --error-device values" do
      assert {[error_device: :stdio], []} = Options.build_opts(error_device: "stdio")
      assert {[error_device: :stderr], []} = Options.build_opts(error_device: "stderr")
      assert {[error_device: :stdio], []} = Options.build_opts(error_device: "standard_io")
      assert {[error_device: :stderr], []} = Options.build_opts(error_device: "standard_error")
    end

    test "surfaces an unknown --theme as a warning, drops the option" do
      assert {[], [warning]} = Options.build_opts(theme: "neon")
      assert warning =~ "unknown --theme"
      assert warning =~ "neon"
    end

    test "surfaces an unknown --mode as a warning, drops the option" do
      assert {[], [warning]} = Options.build_opts(mode: "nano")
      assert warning =~ "unknown --mode"
    end

    test "surfaces an unknown --error-device as a warning, drops the option" do
      assert {[], [warning]} = Options.build_opts(error_device: "tty")
      assert warning =~ "unknown --error-device"
    end

    test "composes multiple switches in the input order" do
      parsed = [raw: false, theme: "mono", error_device: "stdio", no_history: true]

      {opts, warnings} = Options.build_opts(parsed)

      assert [_, _, _, _] = opts
      assert [] = warnings
      assert Keyword.get(opts, :raw) == false
      assert Keyword.get(opts, :theme) == :mono
      assert Keyword.get(opts, :error_device) == :stdio
      assert Keyword.get(opts, :history_path) == nil
    end

    test "later occurrences of the same option win" do
      assert {[theme: :mono], []} = Options.build_opts(theme: "dark", theme: "mono")
    end

    test "collects all warnings in input order" do
      parsed = [theme: "neon", mode: "nano", error_device: "tty"]

      {opts, warnings} = Options.build_opts(parsed)

      assert [] = opts
      assert [w1, w2, w3] = warnings
      assert w1 =~ "--theme"
      assert w2 =~ "--mode"
      assert w3 =~ "--error-device"
    end

    test "ignores unknown switches without crashing" do
      assert {[], []} = Options.build_opts(bogus: true)
    end
  end

  describe "parse/1" do
    test "parses a raw CLI-style argument list end-to-end" do
      args = ~w(--no-raw --theme=mono --error-device=stdio --no-history)

      {opts, warnings} = Options.parse(args)

      assert [] = warnings
      assert Keyword.get(opts, :raw) == false
      assert Keyword.get(opts, :theme) == :mono
      assert Keyword.get(opts, :error_device) == :stdio
      assert Keyword.get(opts, :history_path) == nil
    end

    test "surfaces warnings for invalid values rather than raising" do
      {opts, warnings} = Options.parse(~w(--theme=neon))

      assert [] = opts
      assert [warning] = warnings
      assert warning =~ "--theme"
    end
  end
end
