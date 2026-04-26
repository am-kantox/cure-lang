defmodule Cure.CLI.NewMessageTest do
  use ExUnit.Case, async: true

  alias Cure.CLI.NewMessage

  describe "build/3 -- :lib template" do
    test "mentions the project name and template" do
      md = NewMessage.build("acme", :lib, cure_home: nil)

      assert md =~ "acme"
      assert md =~ "lib"
    end

    test "lists the canonical scaffolded files" do
      md = NewMessage.build("acme", :lib, cure_home: nil)

      assert md =~ "acme/Cure.toml"
      assert md =~ "acme/lib/main.cure"
      assert md =~ "acme/test/main_test.cure"
      assert md =~ "acme/.gitignore"
      assert md =~ "acme/README.md"
    end

    test "includes the standard next-step commands" do
      md = NewMessage.build("acme", :lib, cure_home: nil)

      assert md =~ "cd acme"
      assert md =~ "cure deps"
      assert md =~ "cure run lib/main.cure"
      assert md =~ "cure test"
    end
  end

  describe "build/3 -- :app template" do
    test "lists the application-specific scaffolded files" do
      md = NewMessage.build("acme", :app, cure_home: nil)

      assert md =~ "acme/lib/app.cure"
      assert md =~ "acme/lib/root_sup.cure"
    end
  end

  describe "build/3 -- :fsm template" do
    test "lists the FSM-specific scaffolded files" do
      md = NewMessage.build("acme", :fsm, cure_home: nil)

      assert md =~ "acme/lib/fsm.cure"
      refute md =~ "acme/lib/app.cure"
      refute md =~ "acme/lib/root_sup.cure"
    end
  end

  describe "CURE_HOME hint" do
    test "shows the recommended `export` and `alias` snippet when CURE_HOME is unset" do
      md = NewMessage.build("acme", :lib, cure_home: nil)

      assert md =~ "CURE_HOME"
      assert md =~ ~s(export CURE_HOME=)
      assert md =~ ~s(alias cure=)
    end

    test "shows the resolved paths when CURE_HOME is set" do
      md = NewMessage.build("acme", :lib, cure_home: "/opt/cure")

      assert md =~ "Detected `CURE_HOME=/opt/cure`"
      assert md =~ Path.join(["/opt/cure", "priv", "ebin"])
      assert md =~ Path.join(["/opt/cure", "_build", "cure", "ebin"])
      assert md =~ Path.join(["/opt/cure", "priv", "std"])
      assert md =~ Path.join(["/opt/cure", "lib", "std"])
    end
  end

  describe "render/3" do
    test "wraps the Markdown body in ANSI escape sequences when enabled" do
      output = NewMessage.render("acme", :lib, ansi?: true, cure_home: nil)

      assert is_binary(output)
      # Marcli emits at least one ANSI escape sequence for headings
      # (bold + colour).
      assert output =~ ~r/\e\[/
      assert output =~ "acme"
    end

    test "produces plain text when ANSI is disabled" do
      output = NewMessage.render("acme", :lib, ansi?: false, cure_home: nil)

      refute output =~ ~r/\e\[/
      assert output =~ "acme"
      assert output =~ "Next steps"
    end
  end

  describe "fallback_render/2" do
    test "styles markdown headings and inline code with ANSI codes" do
      md = """
      # Heading 1
      ## Heading 2
      Some text with `code`.
      """

      ansi = NewMessage.fallback_render(md, true)
      plain = NewMessage.fallback_render(md, false)

      assert ansi =~ ~r/\e\[/
      assert ansi =~ "Heading 1"
      assert ansi =~ "Heading 2"
      refute plain =~ ~r/\e\[/
      assert plain =~ "Heading 1"
      assert plain =~ "Heading 2"
      assert plain =~ "code"
    end
  end
end
