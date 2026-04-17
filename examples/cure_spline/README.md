# CureSpline

A real-world example showcasing Cure: a **natural cubic spline**
interpolation library, written almost entirely in `.cure`, reachable from
Elixir via a thin wrapper.

Give it a handful of `(x, y)` knots and it gives you back a smooth
`C`-continuous curve you can evaluate, differentiate, and sample anywhere
within the fitted domain.

## Why a spline?

Cubic splines are the canonical "draw a smooth line through these points"
algorithm -- they show up in animation easing, font rendering, time-series
smoothing, physical simulation, UI layout, and plenty of other places.
Implementing them is a pleasant exercise in numerics: you solve a
tridiagonal system (the Thomas algorithm), precompute per-segment cubic
coefficients, and then evaluation is a handful of multiplications.

Splines are also a great fit for demonstrating what Cure is good at:

  * **Records** with named fields (`Knot`, `Segment`, `Spline`, `Row`,
    `ReducedRow`).
  * **Pattern matching** on lists with `[]` / `[h | t]` / `[a, b]` and
    ADT constructors (`Ok(v)`, `Error(e)`).
  * **Result** types for validation (empty knots, non-increasing x).
  * **Recursion** over lists -- the Thomas algorithm is expressed as two
    tail-recursive list passes.
  * **Elixir interop** -- records compile to BEAM maps, `Ok/Error`
    constructors to `{:ok, _}` / `{:error, _}`, and externs let a Cure
    module reach into an Elixir helper (`CureSpline.Float.fdiv/2`).

## The math, in one paragraph

Given `n + 1` knots with strictly increasing `x_0 < x_1 < ... < x_n`, the
natural cubic spline is the smoothest piecewise cubic that passes through
every knot and has vanishing second derivative at `x_0` and `x_n`. It is
determined by the `n - 1` interior second derivatives `M_1, ..., M_{n-1}`,
which solve the tridiagonal system

    h_{i-1} M_{i-1} + 2 (h_{i-1} + h_i) M_i + h_i M_{i+1}
        = 6 [ (y_{i+1} - y_i) / h_i  -  (y_i - y_{i-1}) / h_{i-1} ]

with `h_i = x_{i+1} - x_i` and boundary `M_0 = M_n = 0`. Once the `M_i`
are known, each segment has a closed-form cubic
`S_i(x) = a + b t + c t^2 + d t^3` with `t = x - x_i` and
`a, b, c, d` computed directly from the knots and the `M_i`.

## The architecture

```
                 .cure                         .ex
    ┌─────────────────────────┐   ┌─────────────────────────────┐
    │   cure_src/spline.cure  │   │   lib/cure_spline.ex        │
    │                         │   │                             │
    │   records:              │   │   CureSpline.fit/1          │
    │     Knot, Segment,      │   │   CureSpline.evaluate/2     │
    │     Spline, Row,        │   │   CureSpline.derivative/2   │
    │     ReducedRow          │   │   CureSpline.sample/2       │
    │                         │   │   CureSpline.demo/0         │
    │   algorithm:            │   │                             │
    │     build_rows          │   └──────────┬──────────────────┘
    │     thomas_forward      │              │
    │     thomas_back         │              │ calls
    │     build_segments      │              ▼
    │     eval_seg, diff_seg  │   ┌─────────────────────────────┐
    │                         │   │  :"Cure.Spline" (.beam)     │
    │   public API:           │   └──────────┬──────────────────┘
    │     fit, evaluate,      │              │ @extern
    │     evaluate_clamped,   │              ▼
    │     derivative, sample  │   ┌─────────────────────────────┐
    └─────────────────────────┘   │  CureSpline.Float.fdiv/2    │
                                  │  (Elixir helper: A / B)     │
                                  └─────────────────────────────┘
```

`cure_src/spline.cure` is compiled to `_build/cure/ebin/Cure.Spline.beam`
by the `mix compile_cure` task, which runs automatically before `mix
compile` via an alias in `mix.exs`.

## The extern trick

At the moment Cure's `/` operator lowers to Erlang's integer `div/2`, so
`1.0 / 3.0` would crash at runtime. The spline module sidesteps this with
a three-line Elixir helper:

```elixir
defmodule CureSpline.Float do
  def fdiv(a, b), do: a / b
  def to_float(n) when is_integer(n), do: n * 1.0
  def to_float(n) when is_float(n), do: n
end
```

and the Cure side pulls it in as an external:

```cure
@extern(Elixir.CureSpline.Float, :fdiv, 2)
local fn fdiv(a: Float, b: Float) -> Float
```

Every float division in the spline module -- and there are many -- goes
through this seam. The rest of the arithmetic (`+`, `-`, `*`) works fine
because Cure maps those to Erlang operators that already do the right
thing on floats.

## Project layout

    cure_spline/
      cure_src/
        spline.cure             -- natural cubic spline in Cure
      lib/
        cure_spline.ex          -- Elixir API + demo
        cure_spline/
          float.ex              -- @extern target for float primitives
          application.ex        -- OTP application
        mix/tasks/
          compile_cure.ex       -- compiles cure_src/*.cure
      test/
        cure_spline_test.exs    -- 25 assertions covering error paths,
                                    knot interpolation, linear exactness,
                                    sin(x) accuracy, C1 continuity, and
                                    the sampling API

## Usage

```bash
# Fetch dependencies (pulls in cure from ../..)
mix deps.get

# Compile (runs .cure compilation first, then Elixir)
mix compile

# Run the full test suite
mix test

# Render the built-in demo
mix run -e 'CureSpline.demo()'
```

### From Elixir

```elixir
{:ok, spline} =
  CureSpline.fit([
    {0.0,  0.00},
    {1.0,  0.84},
    {2.0,  0.91},
    {3.0,  0.14},
    {4.0, -0.76},
    {5.0, -0.96},
    {6.0, -0.28}
  ])

{:ok, y}     = CureSpline.evaluate(spline, 2.5)
{:ok, dydx}  = CureSpline.derivative(spline, 2.5)
clamped      = CureSpline.evaluate_clamped(spline, 100.0)
points       = CureSpline.sample(spline, 50)
```

### Demo output

`CureSpline.demo/0` fits a spline to eleven samples of `sin(x)` over
`[0, 2pi]` and prints a small ASCII plot. A typical run produces:

    cure_spline demo: natural cubic spline through 11 samples of sin(x)
    domain: [0.0, 2pi], segments: 10

         y=1.00
        |            o*****o                                          |
        |         ***       ***                                       |
        |       **             **                                     |
        |     *o                 o*                                   |
        |    *                     *                                  |
        |   *                       *                                 |
        | **                         **                               |
        |o                             o                             o|
        |                               **                         ** |
        |                                 *                       *   |
        |                                  *                     *    |
        |                                   *o                 o*     |
        |                                     **             **       |
        |                                       ***       ***         |
        |                                          o*****o            |
         y=-1.00
         x: 0.00 -> 6.28

Knots are marked with `o`, interpolated samples with `*`. The maximum
deviation from the true `sin(x)` over 201 test points is below `5.0e-3`.

## Accuracy and performance

The test suite asserts several properties of the fitted spline:

  * **Interpolation** -- `S(x_i) == y_i` for every knot (to `1e-9`).
  * **Linear exactness** -- a spline fit to `y = 3x + 1` reproduces
    `3x + 1` everywhere (to `1e-9`).
  * **Reasonable `sin(x)` accuracy** -- 11 knots over `[0, 2pi]` give a
    maximum error below `5e-3` at 201 test points.
  * **C1 continuity** -- the one-sided derivatives at every interior
    knot agree to within `1e-6`.

Segment lookup is a linear scan. For the small-to-medium knot counts
typical of animation, easing, and GUI work this is plenty; if you need
thousands of knots you can swap the scan for binary search without
touching the algorithm.

## Further reading

  * `docs/LANGUAGE_SPEC.md` -- Cure syntax reference
  * `docs/TYPE_SYSTEM.md` -- bidirectional checking, refinement types
  * `examples/records.cure` -- record construction and functional update
  * `examples/cure_turnstile` -- same project layout, but for an FSM
