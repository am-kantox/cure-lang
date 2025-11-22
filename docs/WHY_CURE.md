# Why Cure?

**A principled language for the BEAM that focuses on what's missing, not what's already there.**

## The Problem

The BEAM ecosystem is rich with excellent languages: Erlang's battle-tested reliability, Elixir's developer ergonomics, LFE's Lisp elegance, Gleam's type safety. Each excels at what it does.

But something was missing.

## The Vision

Cure isn't trying to replace these languages—it's designed to **complement** them. Think of it as a specialized tool that fills specific gaps while leveraging the vast BEAM ecosystem through interoperability.

### What Cure Brings to BEAM

#### 🎯 **1. Dependent Types with SMT Verification**

For the first time on BEAM, you can express and **verify** invariants at compile time:

```cure
# The type system proves this is safe—no runtime checks needed
def safe_head(v: Vector(T, n)): T when n > 0 =
  head(v)
```

Vector operations that can't fail. Array access that's proven safe. Constraints that the **solver** validates, not you.

#### 🎆 **2. FSMs as First-Class Citizens**

State machines aren't a pattern in Cure—they're **native syntax** with compile-time safety:

```cure
fsm TrafficLight do
  Red --> |timer| Green
  Green --> |timer| Yellow  
  Yellow --> |timer| Red
  
  Green --> |emergency| Red
end
```

The SMT solver verifies your state machine properties: reachability, deadlock freedom, invariant preservation. Before you even run it.

#### 🚫 **3. No If-Then-Else. Seriously.**

Cure forces you to think in **pattern matching** and **exhaustive cases**:

```cure
# This is an error—non-exhaustive match
def classify(x: Int): Atom =
  match x do
    n when n >= 0 -> :positive
    # Compiler error: missing cases! (Use `x: Nat` to compile)
  end

# This compiles—all cases handled
def classify(x: Int): Atom =
  match x do
    n when n < 0 -> :negative
    0 -> :zero
    n when n > 0 -> :positive
  end
```

No forgotten edge cases. No hidden branches. Every decision point is **explicit and proven complete**.

## The Philosophy

### Half General-Purpose, Half DSL

Cure is intentionally **opinionated**:

- **General-purpose** enough for real applications
- **Specialized** enough to enforce correctness by construction
- **Interoperable** enough to use Erlang/Elixir libraries for everything else

Need JSON parsing? Use an Erlang library. Need web routing? Call Elixir's Phoenix. Need **mathematically verified state machines with dependent types**? That's what Cure is for.

### Focus on Verification, Not Features

Other BEAM languages compete on features. Cure competes on **correctness guarantees**:

- **SMT-backed type checking**: Your types are theorems, proven by Z3/CVC5
- **FSM verification**: State machines validated for safety properties
- **Exhaustive patterns**: The compiler proves you handled every case

## When to Use Cure

✅ **Perfect for:**
- Safety-critical finite state machines
- Systems with complex invariants
- Domains where correctness > convenience
- Embedded systems requiring BEAM's reliability + mathematical guarantees
- Trading systems, industrial control, medical devices, aerospace

❌ **Not ideal for:**
- Rapid prototyping (use Elixir)
- Scripts and glue code (use Elixir/Erlang)
- When you need maximum ecosystem libraries (stick to Erlang/Elixir)
- General web development (Phoenix is excellent)

## The Trade-Off

You give up:
- Some syntactic flexibility
- `if-then-else` convenience
- A few language features better implemented elsewhere

You gain:
- **Mathematical proofs** of correctness
- **Verified state machines** that can't reach invalid states
- **Dependent types** that prevent entire classes of bugs
- Code that **provably** handles all cases

## The BEAM Advantage

Because Cure compiles to BEAM bytecode, you get all of this:

- ✅ OTP's fault tolerance and supervision trees
- ✅ Hot code reloading in production
- ✅ Distributed computing primitives
- ✅ Interoperability with the entire Erlang/Elixir ecosystem
- ✅ Battle-tested VM with 30+ years of production hardening

Plus verification guarantees no other BEAM language provides.

## The Bottom Line

**Cure isn't trying to be the only language you use on BEAM. It's trying to be the language you reach for when correctness matters more than convenience.**

If you're building a traffic control system, not a todo app. If you're managing financial transactions, not rendering HTML. If you're controlling industrial equipment, not parsing CSV files.

If you need to **prove** your code is correct, not just test it.

That's why Cure exists.

---

## Additional Goodness

`Cure` comes with LSP for any editor.

---

**Cure: Verification-first programming for the BEAM.**

*For everything else, there's Erlang, Elixir, LFE, and Gleam. Use them. They're excellent. But when you need dependent types, SMT-verified FSMs, and exhaustive pattern matching—Cure is here for you.*
