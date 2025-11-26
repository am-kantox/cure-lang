# Cure: A Programming Language with Dependent Types and Formal Verification for BEAM

**TL;DR**: `Cure` is a functional programming language for the BEAM virtual machine (Erlang/Elixir) that brings mathematical proofs of code correctness directly at compile time. Using SMT solvers ([Z3](https://github.com/Z3Prover/z3)/[CVC5](https://github.com/cvc5/cvc5)), `Cure` checks value-dependent types, verifies finite state machines, and guarantees the absence of entire classes of bugs before the program even runs.

---

## What is Cure and Why Do We Need It?

### The Problem with Modern Development

Testing is unavoidable, but for some mission-critical parts of code, we'd like stronger guarantees—like proofs of correctness. All things being equal, this doesn't make sense for small e-commerce sites or landing pages, but a trading platform, drone control system, or medical software deserve something more serious than slapdash tests.

At the same time, all existing languages that allow proving correctness are either not production-ready, written by aliens for aliens, or force you to write the entire project under the same conditions (an HTTP request from a user doesn't need type checking and correctness guarantees, and the overhead—like compilation time and actual writing time—is quite significant to ignore).

For years I wrote critical subsystems in Idris, manually translated to Elixir, and it worked for me—but was terribly annoying. Yes, during translation (at any boundary with the external world)—mathematical provability is lost, but it's an acceptable risk (for me). I know for sure that if the "interface" is carefully checked, the code inside will work as needed.

But Idris has its own problems, I don't consider Haskell-like syntax acceptable for adult programming, and translating back and forth each time is quite tedious. And I thought: what if I write my own language that compiles to BEAM and transparently links with Erlang, Elixir, Gleam, and even LFE?

I only need three things from a language:

* Dependent types and solvers
* FSMs in the core, with all the bells and whistles
* No `if`-`then`-`else`

And I simply created [Cure](https://cure-lang.org)

**Traditional approach**:
```erlang
%% Erlang - checks only at runtime
safe_divide(A, B) when B =/= 0 ->
    {ok, A / B};
safe_divide(_, 0) ->
    {error, division_by_zero}.
```

Yes, it works. But what if you forget the check? What if the logic becomes more complex and a new execution path appears?

**Cure's approach**:
```cure
# Cure - mathematical proof at the type level
def safe_divide(a: Int, b: {x: Int | x != 0}): Int =
  a / b
  
# The compiler will PROVE that b will never be zero
# Or the program won't compile
```

### Cure's Philosophy

Cure stands on three pillars:

1. **Verification over convenience** — when correctness is critical, syntactic sugar is secondary
2. **Mathematical proofs instead of hopes** — the compiler doesn't just check types, it PROVES program properties
3. **BEAM as foundation** — all the power of Erlang OTP, but with type-level correctness guarantees

---

## Dependent Types: What and Why?

### Simple Example

Regular types say: "this is an integer." Dependent types say: "this is an integer greater than zero and less than the list length."

```cure
# Type depends on VALUE
def head(v: Vector(T, n)): T when n > 0 =
  nth(v, 0)
  
# Compiler will PROVE that:
# 1. Vector is non-empty (n > 0)
# 2. Index 0 is always valid
# 3. Result has type T

# Trying to call head on an empty vector?
# ❌ COMPILATION ERROR
```

### Real Example: Safe List Access

```cure
# Safe access - mathematically proven
def safe_access(v: Vector(Int, n), idx: {i: Int | 0 <= i < n}): Int =
  nth(v, idx)  # No checks - compiler ALREADY proved safety!

# Usage
let my_vector = ‹5, 10, 15, 20›  # Vector(Int, 4)

safe_access(my_vector, 2)   # ✅ OK - 2 < 4
safe_access(my_vector, 10)  # ❌ COMPILATION ERROR - 10 >= 4
```

Notice: **no runtime checks**. The compiler mathematically proved that `idx` is always valid. This isn't just "type checking"—it's a **mathematical proof**.

---

## SMT Solvers and Formal Verification

### What is an SMT Solver?

SMT (Satisfiability Modulo Theories) is a mathematical engine that checks whether a solution exists for a system of logical equations.

Imagine the problem:
```
Given: x > 0, y > 0, x + y = 10
Question: can x = 15?
```

An SMT solver will **mathematically prove** that no—if x = 15, then y = -5, which violates the condition y > 0.

### How Cure Uses Z3

Cure integrates Z3—the most powerful SMT solver from Microsoft Research—directly into the compiler:

```cure
# Function with guards
def classify_age(age: Int): Atom =
  match age do
    n when n < 0 -> :invalid
    0 -> :newborn
    n when n < 18 -> :minor
    n when n < 65 -> :adult
    n when n >= 65 -> :senior
  end
```

**What the compiler does with Z3**:

1. Translates guards into SMT formulas:
   ```smt
   (assert (< n 0))      ; first case
   (assert (= n 0))      ; second case
   (assert (and (>= n 0) (< n 18)))  ; third case
   ...
   ```

2. Z3 checks **coverage completeness**:
   - Are all cases covered?
   - Are there overlaps?
   - Are there unreachable branches?

3. Guarantees:
   ```
   ✓ All integers are covered
   ✓ Each number will fall into exactly one case
   ✓ No dead code
   ```

### Finite State Machine Verification

FSMs (Finite State Machines) are the heart of many BEAM systems. I personally wrote a whole [library](https://hexdocs.pm/finitomata) for FSM support with "verifications" in Elixir, but those were, of course, crutches made from sticks. Cure has real **verifiable finite state machines** out of the box:

```cure
record TrafficLight do
  cycles: Int
  emergency_stops: Int
end

fsm TrafficLight{cycles: 0, emergency_stops: 0} do
  Red --> |timer| Green
  Green --> |timer| Yellow
  Yellow --> |timer| Red
  
  Green --> |emergency| Red
  Yellow --> |emergency| Red
end
```

Z3 will check that: ① there are no deadlocks, ② all states are reachable, ③ there are no undefined transitions, and ④ invariants are preserved. And all this **at compile time**!

### Pipes

I'm not a purist, I just made pipes monadic. More details [here](https://github.com/am-kantox/cure-lang/blob/main/docs/PIPE_OPERATOR.md).

---

## Current Project Status

### ✅ What Works (Version 0.7.0 — November 2025)

**Fully functional implementation:**

1. **Compiler (100% functional)**
   - Lexical analysis with position tracking
   - Parsing to AST with error recovery
   - Dependent type system with constraint checking
   - BEAM bytecode generation
   - OTP integration

2. **Standard Library (12 modules)**
   - `Std.Core` — basic types and functions
   - `Std.Io` — input-output (in embryonic state, I can't figure out if I need it at all)
   - `Std.List` — list operations (`map/2`, `filter/2`, `fold/3`, `zip_with/2`)
   - `Std.Vector` — operations on lists of specific length
   - `Std.Fsm` — finite state machine operations
   - `Std.Result` / `Std.Option` — error handling
   - `Std.Vector` — indexed vectors
   - And others...

3. **FSM Runtime**
   - FSM compilation to `gen_statem` behaviors
   - Mermaid notation for FSM (`State1 --> |event| State2`)
   - Runtime operations (spawn, cast, state query)
   - Integration with OTP supervision trees

4. **Type Optimization (25-60% speedup)**
   - Monomorphization
   - Function specialization
   - Inlining
   - Dead code elimination

5. **Function Guards with SMT Verification**
   ```cure
   def abs(x: Int): Int =
     match x do
       n when n < 0 -> -n
       n when n >= 0 -> n
     end
   # Z3 will check coverage completeness!
   ```

6. **BEAM Integration**
   - [×] Full compatibility with Erlang/Elixir
   - [ ] Hot code loading
   - [?] Distributed computing — ahem :) almost
   - [×] OTP behaviours

### 🚧 In Development

- **Type Classes/Traits** — polymorphic interfaces (parser ready, awaiting implementation)
- **String interpolation** — template strings
- **CLI SMT integration** — running Z3 from command line (API ready)

### 📊 Statistics

- **~15,000 lines** of compiler code (Erlang)
- **~2,000 lines** of standard library (Cure)
- **35+ documents** of technical documentation
- **6 working examples** in `examples/`
- **100% coverage** of core function tests

---

## LSP and MCP: Development Comfort

**And that's not all, surprisingly. I have to work quite a lot with Cure code myself, so a full-fledged LSP and MCP are being developed in parallel.**

### Language Server Protocol (LSP)

Cure comes with a full-fledged LSP server for IDEs:

**Features:**
- **Real-time diagnostics** — errors right in the editor
- **Hover information** — types and documentation on Ctrl+hover
- **Go to definition** — code navigation
- **Code completion** (still quite average)
- **Code actions** (everything the solver can output — out of the box)
- **Type holes** — `_` for type inference (like holes in Idris)

**Integration:** Hypothetically, should work in any editor with LSP support. Tested only in `NeoVim`.

**Example:**
```cure
# Hole                  ⇓
def factorial(n: Int): _ =
  match n do
    0 -> 1
    n -> n * factorial(n - 1)
  end
  
# Hover will show inferred `Int`, and `<leader>ca` will insert it in place
```

### Model Context Protocol (MCP)

Cure supports MCP — Anthropic's new protocol for integration with AI assistants:

**What this provides:**
- 🤖 **AI-assisted coding** — Claude/GPT understands project context
- 📚 **Smart search** — semantic search through codebase
- 🔍 **Type-aware refactoring** — AI knows about types
- 📖 **Documentation on the fly** — generating docs from code

**Architecture:**
```
┌─────────────┐
│   Claude    │ ← MCP Protocol
│   /GPT      │
└──────┬──────┘
       │
┌──────▼──────────────┐
│   MCP Server        │
│  (Cure integration) │
├─────────────────────┤
│ • Code search       │
│ • Type queries      │
│ • Documentation     │
│ • Refactoring hints │
└─────────────────────┘
```

---

## How to Try Cure

### Installation

**Requirements:**
- Erlang/OTP 28+
- Make
- Git
- (Optional) Z3 for SMT verification

**Steps:**

```bash
# 1. Clone the repository
git clone https://github.com/am-kantox/cure-lang.git
cd cure-lang

# 2. Build the compiler
make all

# 3. Check installation
./cure --version
# Cure v0.7.0 (November 2025)

# 4. Run tests
make test
# ✓ All tests passed
```

### First Program

Create `hello.cure`:

```cure
module Hello do
  export [main/0]
  
  import Std.Io [println]
  
  def main(): Int =
    println("Hello from Cure!")
    0
end
```

Compile and run:

```bash
./run_cure.sh hello.cure
# Hello from Cure!
```

### Examples Out of the Box (they sometimes break)

```bash
# FSM: traffic light
./cure examples/06_fsm_traffic_light.cure
erl -pa _build/ebin -noshell -eval "'TrafficLightFSM':main(), init:stop()."

# List operations
./cure examples/01_list_basics.cure
erl -pa _build/ebin -noshell -eval "'ListBasics':main(), init:stop()."

# Pattern matching with guards
./cure examples/04_pattern_guards.cure
erl -pa _build/ebin -noshell -eval "'PatternGuards':main(), init:stop()."

# Error handling through Result
./cure examples/02_result_handling.cure
erl -pa _build/ebin -noshell -eval "'ResultHandling':main(), init:stop()."
```

---

## Compiler Architecture

### Compilation Pipeline

```
┌──────────────┐
│  hello.cure  │ Source File
└──────┬───────┘
       │
       ▼
┌──────────────────┐
│   Lexer          │ Tokenization
│  (cure_lexer)    │ • Keywords, operators
└──────┬───────────┘ • Position tracking
       │
       ▼
┌──────────────────┐
│   Parser         │ AST Generation
│ (cure_parser)    │ • Syntax analysis
└──────┬───────────┘ • Error recovery
       │
       ▼
┌──────────────────┐
│  Type Checker    │ Type Inference
│(cure_typechecker)│ • Dependent types
│                  │ • Constraint solving
│  ┌─────────────┐ │
│  │ Z3 Solver   │ │ SMT Verification
│  │ (cure_smt)  │ │
│  └─────────────┘ │
└──────┬───────────┘
       │
       ▼
┌──────────────────┐
│  Optimizer       │ Type-Directed Opts
│(cure_optimizer)  │ • Monomorphization
└──────┬───────────┘ • Inlining
       │
       ▼
┌──────────────────┐
│  Code Generator  │ BEAM Bytecode
│ (cure_codegen)   │ • Module generation
└──────┬───────────┘ • OTP integration
       │
       ▼
┌──────────────────┐
│   Hello.beam     │ Executable
└──────────────────┘
```

### Z3 Integration

```erlang
%% Simplified example from cure_guard_smt.erl
verify_guard_completeness(Guards, Type) ->
    %% 1. Generate SMT formulas
    SMTFormulas = lists:map(fun guard_to_smt/1, Guards),
    
    %% 2. Check coverage
    Coverage = z3_check_coverage(SMTFormulas, Type),
    
    %% 3. Find gaps
    case Coverage of
        complete -> 
            {ok, verified};
        {incomplete, Gap} -> 
            {error, {missing_case, Gap}};
        {overlapping, Cases} -> 
            {error, {redundant_guards, Cases}}
    end.
```

### FSM Compilation

```cure
# Original FSM
fsm Light do
  Red --> |timer| Green
  Green --> |timer| Red
end

# Compiles to gen_statem
-module('Light').
-behaviour(gen_statem).

callback_mode() -> state_functions.

red({call, From}, {event, timer}, Data) ->
    {next_state, green, Data, [{reply, From, ok}]}.

green({call, From}, {event, timer}, Data) ->
    {next_state, red, Data, [{reply, From, ok}]}.
```

---

### What Cure is NOT Good For

- Rapid prototyping (use Elixir)
- General-purpose web development (Phoenix does it great)
- Scripts and glue code
- Projects with frequently changing requirements

### Comparison with Other Languages

| Feature | Cure | Erlang | Elixir | Idris/Agda |
|---------|------|--------|--------|------------|
| Dependent types | ✅ | ❌ | ❌ | ✅ |
| SMT verification | ✅ | ❌ | ❌ | Partially |
| BEAM VM | ✅ | ✅ | ✅ | ❌ |
| FSM as primitive | ✅ | Libraries | Libraries | ❌ |
| OTP compatibility | ✅ | ✅ | ✅ | ❌ |
| Production ready | 🚧 | ✅ | ✅ | Research |
| Learning curve | High | Medium | Low | Very high |

### Project Philosophy

Cure doesn't try to replace Erlang or Elixir. It's a **specialized tool** for tasks where:

1. **Correctness > Development Speed**
2. **Mathematical Proofs > Unit Tests**
3. **Compile-time Guarantees > Runtime Checks**

As Tony Hoare said:
> There are two ways of constructing a software design: One way is to make it so simple that there are obviously no deficiencies, and the other way is to make it so complicated that there are no obvious deficiencies.

---

## Roadmap and Future

### Short-term Plans (2025–2026)

- [ ] **Typeclasses/Traits** — polymorphic interfaces
- [ ] **CLI SMT integration** — Z3 directly from command line
- [ ] **LSP improvements** — code completion, refactoring
- [ ] **Stdlib expansion** — more utility functions

### Medium-term (2026)

- [?] **Effect system** — tracking effects like in Koka
- [ ] **Package manager** — dependency management
- [ ] **Distributed FSMs** — verifiable distributed state machines
- [ ] **Gradual typing** — compatibility with dynamic Erlang
- [?] **Macro system** — compile-time metaprogramming

### Long-term Vision

Cure aims to become the **language of choice** for critical systems on BEAM:

1. **Formal methods become mainstream** — not a niche for academics, but an industry standard
2. **Mathematical guarantees on BEAM** — Erlang reliability + Cure correctness
3. **Verification tooling** — like unit tests today, SMT checks tomorrow

---

## Resources and Links

### Documentation

- **Official documentation**: `/docs` in repository
- **Language specification**: `docs/LANGUAGE_SPEC.md`
- **Type system guide**: `docs/TYPE_SYSTEM.md`
- **FSM**: `docs/FSM_USAGE.md`
- **Standard library**: `docs/STD_SUMMARY.md`

### Code Examples

- **Basic examples**: `examples/01_list_basics.cure`
- **FSM demo**: `examples/06_fsm_traffic_light.cure`
- **Guards and pattern matching**: `examples/04_pattern_guards.cure`
- **Dependent types**: `examples/dependent_types_demo.cure`

### Scientific Foundations

- (**I owe this book the existence of the language in principle**) Alessandro Gianola: "SMT-based Safety Verification of Data-Aware Processes"
- Z3 Solver: https://github.com/Z3Prover/z3
- SMT-LIB Standard: http://smtlib.cs.uiowa.edu/
- Idris tutorial: https://docs.idris-lang.org/

---

## P.S. Frequently Asked Questions

**Q: Is Cure production-ready?**  
A: The compiler is functional, stdlib works, but the project is young. For critical systems, thorough testing is recommended. Version 1.0 is expected in 2026.

**Q: Do I need to know type theory?**  
A: Basic usage doesn't require deep knowledge. For advanced features (dependent types, SMT), understanding the basics is desirable.

**Q: Is it compatible with Erlang/Elixir?**  
A: Yes! Cure compiles to BEAM bytecode and is fully compatible with OTP. You can call Erlang modules and vice versa.

**Q: Why not extend Elixir instead of a new language?**  
A: Dependent types require a fundamentally different compiler architecture. Adding them to a dynamic language is impossible without losing guarantees.

**Q: How fast is Cure code?**  
A: Comparable to Erlang. Type optimizations provide 25-60% speedup. Zero runtime overhead from types.

**Q: Can I write web apps in Cure?**  
A: Take Phoenix, write critical pieces in Cure and link BEAM from Elixir. I'll make this process transparent for `mix`. In principle, Cure makes sense to use **only** for systems where verification is needed. A website or app will do fine without it.
