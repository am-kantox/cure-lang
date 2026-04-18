[
  # Dialyzer reports false positives for `if state.emit_events` guards
  # and pattern_match_cov in the Parser module.
  {"lib/cure/compiler/parser.ex", :pattern_match},
  {"lib/cure/compiler/parser.ex", :pattern_match_cov},

  # -- MapSet opaqueness false positives (Elixir 1.20-rc / OTP 29+) ----------
  #
  # `MapSet.t()` in Elixir 1.20 is deliberately NOT opaque
  # (`@type t(value) :: %__MODULE__{map: internal(value)}` where
  # `internal(value) :: %{optional(value) => term()}`), but its runtime
  # representation is built on top of `:sets.set()` which IS opaque in OTP.
  # Every call site that passes a MapSet through a public MapSet function
  # triggers `call_without_opaque` / `contract_with_opaque` because dialyzer
  # observes the declared `%MapSet{map: map()}` shape alongside the inferred
  # `%MapSet{map: :sets.set(_)}` shape and considers them incompatible. See
  # https://github.com/elixir-lang/elixir/blob/main/lib/elixir/lib/map_set.ex
  # for the rationale (struct key name kept for backwards compatibility with
  # the pre-1.15 implementation). There is nothing to fix at the call site.
  {"lib/cure/compiler/codegen.ex", :call_without_opaque},
  {"lib/cure/types/checker.ex", :call_without_opaque},
  {"lib/cure/types/effects.ex", :call_without_opaque},
  {"lib/cure/types/env.ex", :call_without_opaque},
  {"lib/cure/types/env.ex", :contract_with_opaque},
  {"lib/cure/types/pattern_checker.ex", :call_without_opaque},
  {"lib/cure/types/totality.ex", :call_without_opaque}
]
