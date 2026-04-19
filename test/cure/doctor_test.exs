defmodule Cure.DoctorTest do
  use ExUnit.Case, async: false

  alias Cure.Doctor

  setup do
    tmp = Path.join(System.tmp_dir!(), "cure_doctor_#{:erlang.unique_integer([:positive])}")
    File.mkdir_p!(tmp)
    on_exit(fn -> File.rm_rf!(tmp) end)
    {:ok, root: tmp}
  end

  test "reports Elixir / OTP / registry information", %{root: root} do
    report = Doctor.run(root)
    assert is_map(report)
    codes = Enum.map(report.findings, & &1.code)
    assert "DOC-ENV-01" in codes
    assert "DOC-ENV-REG" in codes
  end

  test "flags a missing Cure.toml", %{root: root} do
    report = Doctor.run(root)
    assert Enum.any?(report.findings, &(&1.code == "DOC-PROJ-NOFILE"))
    refute report.ok?
  end

  test "reports DOC-PROJ-01 when Cure.toml exists", %{root: root} do
    File.write!(Path.join(root, "Cure.toml"), """
    [project]
    name = "example"
    version = "0.1.0"

    [dependencies]
    """)

    report = Doctor.run(root)
    assert Enum.any?(report.findings, &(&1.code == "DOC-PROJ-01"))
  end
end
