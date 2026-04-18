# Ensure the Cure standard library is compiled to BEAM before the suite
# runs.
#
# Several test files (notably `test/cure/stdlib/iter_test.exs`,
# `test/cure/stdlib/pbt_test.exs`, and anything else that relies on
# `Cure.Stdlib.Preload.preload/1`) expect
# `_build/cure/ebin/Cure.Std.*.beam` to exist at startup. Locally we
# usually have the beams lying around from a previous `mix cure.compile_stdlib`
# invocation, so everything works. In CI (and on any truly fresh
# checkout) there is no `_build/cure/ebin` yet, so the preload helper
# silently does nothing and the tests above fail with
# `UndefinedFunctionError: function :"Cure.Std.Iter".from_list/1 is undefined`.
#
# Running the compile task here pays the cost once per suite, guarantees
# the beams are present, and keeps the dependency explicit.
stdlib_ebin = Path.expand("../_build/cure/ebin", __DIR__)
stdlib_sentinel = Path.join(stdlib_ebin, "Cure.Std.Iter.beam")

unless File.exists?(stdlib_sentinel) do
  IO.puts("test_helper: compiling Cure stdlib (one-time)")
  Mix.Task.run("cure.compile_stdlib")
end

ExUnit.start()
