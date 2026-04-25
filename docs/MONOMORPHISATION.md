# Monomorphisation

The Cure optimiser specialises polymorphic functions whose call sites
all use concrete types. Specialised clones are smaller, easier to
inline, and more amenable to constant folding -- the rest of the v0.31.0
optimisation pipeline runs against a tighter signature.

The pass is wired in front of `Cure.Optimizer.Inline` so the inliner
sees the specialised forms directly. It is on by default whenever
`--optimize` is in effect; opt out with `--no-monomorphise`.

## Algorithm

`Cure.Optimizer.Monomorphise.run/2` runs in four phases:

1. **Collect.** Walk the module body and gather every
   `{:function_def, _, _}` whose declared signature (resolved via
   `Cure.Types.Type.resolve/1`) mentions at least one
   `{:type_var, _}`. `@extern` functions are excluded; the optimiser
   never specialises functions whose body lives outside the Cure
   compilation unit.
2. **Discover.** Walk every `{:function_call, _, _}` node. For each
   call into a known-polymorphic local function, infer the
   argument types via a lightweight oracle (literals, lists,
   tuples, lambdas, record constructions, and calls into known
   local non-polymorphic functions). Run `Cure.Types.Unify.unify_many/1`
   between the formal parameter types and the inferred argument
   types. Drop call sites where any argument type cannot be inferred,
   or where the substitution still leaves a type variable unsolved.
3. **Materialise.** For each unique substitution, synthesise a
   specialised clone. The clone's name is
   `<original>__<6-hex-hash-of-substitution>` (a 6-character
   `phash2/1` digest, base 16, lower-case, zero-padded). The clone's
   visibility is `:private` so it does not appear in the module's
   export list. The clone carries a `:specialised_from` meta key for
   tooling.
4. **Rewrite.** Every call site whose substitution lines up with a
   registered specialisation has its `:name` meta rewritten to the
   mangled clone's name. The original generic `function_def` is
   **always** retained alongside the specialisations so cross-module
   callers, protocol-registry dispatch, and dynamic `apply/3` keep
   working unchanged.

## Name mangling

The mangled suffix is the lower-case 6-character base-16 representation
of `:erlang.phash2(canonicalised_substitution) rem 16_777_216`. The
canonicalisation strips refinement predicates and recursively
canonicalises nested types so two structurally-identical substitutions
produce the same hash regardless of where they came from.

```
fn id(x: T) -> T = x
fn use_int() -> Int = id(42)        -- rewrites to id__223a2c(42)
fn use_str() -> String = id("hi")   -- rewrites to id__17522e("hi")
```

The hash is stable across recompilations: the same
`(name, substitution)` pair always maps to the same suffix.

## Budget

To keep BEAM bytecode size bounded, the pass caps the number of
specialisations at `[compiler].monomorph_budget` per source function.
The default is **16**.

When the cap is exceeded, the pass keeps the first 16 unique
specialisations (in the order they were first encountered), falls
back to the original generic clone for everything else, and emits
`:monomorph_budget_exceeded` -- a `:type_warning` pipeline event
under code **E064 Monomorphisation Budget Exhausted**.

You can tune the budget per project:

```toml
[compiler]
monomorph_budget = 32
```

Or one-off via the optimiser API:

```elixir
Cure.Optimizer.optimize(ast, monomorph_budget: 32)
```

## Limitations (v0.31.0)

* **Local only.** Specialisation is per compilation unit. Cross-module
  polymorphic calls flow through the protocol registry as before.
* **Conservative type inference.** Argument types are inferred from
  literals, lists, tuples, lambdas, record constructions, and known
  local non-polymorphic returns. Variable references and other
  compound expressions cause the call site to fall back to the
  generic clone.
* **Bytecode parity.** Specialised clones share the original body
  verbatim. The optimiser delivers value by routing future passes
  (Inline, ConstantFold, ...) through the cloned site so each
  specialisation evolves independently.

## Pipeline events

* `:monomorph_specialised` -- `{name, arity, subst, mangled}` per
  specialised clone.
* `:monomorph_skipped` -- `{name, arity, reason, count}` where
  `reason in [:not_polymorphic, :partial_solution, :budget_exhausted]`.

Subscribe via:

```elixir
Cure.Pipeline.Events.subscribe(:type_checker, :monomorph_specialised)
```
