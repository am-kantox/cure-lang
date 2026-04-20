defmodule Cure.REPL.RenderTest do
  use ExUnit.Case, async: true

  alias Cure.REPL.{Render, Theme}

  describe "move_cursor_to_column/1" do
    test "col == 0 returns just a carriage return (no off-by-one CUF)" do
      assert "\r" = Render.move_cursor_to_column(0)
    end

    test "col > 0 returns CR + CUF with the exact column" do
      assert "\r\e[1C" = IO.iodata_to_binary(Render.move_cursor_to_column(1))
      assert "\r\e[12C" = IO.iodata_to_binary(Render.move_cursor_to_column(12))
    end
  end

  describe "encode_search_status/3" do
    setup do
      %{theme: Theme.for_name(:mono)}
    end

    test "descends with CRLF, clears the row, writes the status, ascends with \\e[1A",
         %{theme: theme} do
      io = Render.encode_search_status("(reverse-i-search): map", theme, 11)
      bin = IO.iodata_to_binary(io)

      # Relative descent that will scroll if at the bottom row.
      assert String.starts_with?(bin, "\r\n")
      # Clears the helper row.
      assert bin =~ "\r\e[2K"
      # The status body is present verbatim.
      assert bin =~ "(reverse-i-search): map"
      # Comes back up exactly one physical row via relative motion.
      assert bin =~ "\e[1A"
      # Finishes by restoring the prompt-row column.
      assert String.ends_with?(bin, "\r\e[11C")
    end

    test "never emits the fragile \\e7 / \\e8 (DECSC/DECRC) pair", %{theme: theme} do
      bin = IO.iodata_to_binary(Render.encode_search_status("hit", theme, 4))
      refute bin =~ "\e7"
      refute bin =~ "\e8"
    end

    test "col == 0 emits a bare CR at the tail (no \\e[0C)", %{theme: theme} do
      bin = IO.iodata_to_binary(Render.encode_search_status("hit", theme, 0))
      assert String.ends_with?(bin, "\e[1A\r")
      refute bin =~ "\e[0C"
    end

    test "embeds the theme's status escape around the status body" do
      dark = Theme.default()
      bin = IO.iodata_to_binary(Render.encode_search_status("hit", dark, 3))
      assert bin =~ dark.status <> "hit" <> dark.reset
    end
  end

  describe "encode_clear_helpers/1" do
    test "descends, clears, ascends, restores the cursor column" do
      bin = IO.iodata_to_binary(Render.encode_clear_helpers(7))
      assert String.starts_with?(bin, "\r\n")
      assert bin =~ "\r\e[2K"
      assert bin =~ "\e[1A"
      assert String.ends_with?(bin, "\r\e[7C")
    end

    test "never emits the fragile \\e7 / \\e8 (DECSC/DECRC) pair" do
      bin = IO.iodata_to_binary(Render.encode_clear_helpers(4))
      refute bin =~ "\e7"
      refute bin =~ "\e8"
    end

    test "col == 0 still ends in a bare CR (no off-by-one CUF)" do
      bin = IO.iodata_to_binary(Render.encode_clear_helpers(0))
      assert String.ends_with?(bin, "\e[1A\r")
      refute bin =~ "\e[0C"
    end
  end
end
