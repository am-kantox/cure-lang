defmodule Cure.CLITest do
  use ExUnit.Case, async: false

  import ExUnit.CaptureIO

  describe "cure version" do
    test "prints version" do
      output = capture_io(fn -> Cure.CLI.main(["version"]) end)
      assert output =~ "Cure"
      assert output =~ Mix.Project.config()[:version]
    end
  end

  describe "cure help" do
    test "prints help text" do
      output = capture_io(fn -> Cure.CLI.main(["help"]) end)
      assert output =~ "Usage: cure"
      assert output =~ "compile"
      assert output =~ "run"
      assert output =~ "check"
      assert output =~ "lsp"
    end

    test "no args shows help" do
      output = capture_io(fn -> Cure.CLI.main([]) end)
      assert output =~ "Usage: cure"
    end

    test "--help flag shows help" do
      output = capture_io(fn -> Cure.CLI.main(["--help"]) end)
      assert output =~ "Usage: cure"
    end
  end

  describe "cure compile" do
    test "compiles a .cure file" do
      output =
        capture_io(fn ->
          Cure.CLI.main(["compile", "examples/hello.cure", "-o", "_build/test_cli_ebin"])
        end)

      assert output =~ "Cure.Hello"
      File.rm_rf!("_build/test_cli_ebin")
    end

    test "compiles a directory" do
      output =
        capture_io(fn ->
          Cure.CLI.main(["compile", "examples/", "-o", "_build/test_cli_ebin"])
        end)

      assert output =~ "->"
      File.rm_rf!("_build/test_cli_ebin")
    end

    test "no path shows error" do
      output =
        capture_io(:stderr, fn ->
          Cure.CLI.main(["compile"])
        end)

      assert output =~ "Usage"
    end
  end

  describe "cure run" do
    test "compiles and runs a .cure file with main/0" do
      # Create a temp file with main
      path = Path.join(System.tmp_dir!(), "cure_cli_test.cure")

      File.write!(path, """
      mod CliRun
        fn main() -> Int = 42
      """)

      output = capture_io(fn -> Cure.CLI.main(["run", path]) end)
      assert output =~ "42"
    after
      :code.purge(:"Cure.CliRun")
      :code.delete(:"Cure.CliRun")
    end

    test "compiles module without main" do
      path = Path.join(System.tmp_dir!(), "cure_cli_nomain.cure")

      File.write!(path, """
      mod NoMain
        fn foo() -> Int = 99
      """)

      output = capture_io(fn -> Cure.CLI.main(["run", path]) end)
      assert output =~ "no main/0"
    after
      :code.purge(:"Cure.NoMain")
      :code.delete(:"Cure.NoMain")
    end
  end

  describe "cure check" do
    test "valid file passes" do
      output =
        capture_io(fn ->
          Cure.CLI.main(["check", "examples/hello.cure"])
        end)

      assert output =~ "OK"
    end
  end

  describe "cure stdlib" do
    test "compiles stdlib" do
      output =
        capture_io(fn ->
          Cure.CLI.main(["stdlib", "-o", "_build/test_stdlib_ebin"])
        end)

      assert output =~ "Compiling Cure standard library"
      assert output =~ "Output:"
      File.rm_rf!("_build/test_stdlib_ebin")
    end
  end

  describe "unknown command" do
    test "prints error" do
      output =
        capture_io(:stderr, fn ->
          Cure.CLI.main(["foobar"])
        end)

      assert output =~ "Unknown command"
    end
  end
end
