defmodule Cure.Compiler.Errors do
  @moduledoc """
  Formats compiler errors into human-readable messages with source locations.

  Handles errors from every pipeline stage: lexer, parser, type checker,
  codegen, and FSM verifier.

  ## Example output

      error: type mismatch in function 'bad'
       --> hello.cure:3
        | declared return type Int but body has type String
  """

  @doc """
  Format a compiler error into a human-readable string.

  Accepts error tuples from any pipeline stage and a file path for context.
  """
  @spec format_error(term(), String.t()) :: String.t()
  def format_error(error, file \\ "nofile")

  # -- Type Errors -------------------------------------------------------------

  def format_error(errors, file) when is_list(errors) do
    # A bare list reaches this clause from `Cure.Types.Checker.check_module/2`,
    # which returns `{:error, errors}` directly; joining with a blank line
    # keeps multi-error output readable.
    Enum.map_join(errors, "\n\n", &format_error(&1, file))
  end

  def format_error({:type_error, errors}, file) when is_list(errors) do
    format_error(errors, file)
  end

  def format_error({:type_mismatch, message, meta}, file) do
    line = Keyword.get(meta, :line, 0)
    format_diagnostic("error", "type mismatch", file, line, message)
  end

  def format_error({:unbound_variable, message, meta}, file) do
    line = Keyword.get(meta, :line, 0)
    format_diagnostic("error", "unbound variable", file, line, message)
  end

  def format_error({:arity_mismatch, message, meta}, file) do
    line = Keyword.get(meta, :line, 0)
    format_diagnostic("error", "arity mismatch", file, line, message)
  end

  # -- Parse Errors ------------------------------------------------------------

  def format_error({:parse_error, errors}, file) when is_list(errors) do
    format_error(errors, file)
  end

  def format_error({:unexpected_token, token_type, line, col}, file) do
    format_diagnostic("error", "unexpected token", file, line, "unexpected #{token_type} at column #{col}")
  end

  def format_error({:parse_recovered, token_type, line, col}, file) do
    format_diagnostic(
      "error",
      "parse error (E063)",
      file,
      line,
      "unexpected #{token_type} at column #{col}; subsequent tokens skipped until next statement boundary"
    )
  end

  def format_error({:expected, expected, :got, got, line, col}, file) do
    format_diagnostic("error", "syntax error", file, line, "expected #{expected}, got #{got} at column #{col}")
  end

  def format_error({:lambda_block_unterminated, line, col, code}, file) do
    format_diagnostic(
      "error",
      "lambda block unterminated (#{code})",
      file,
      line,
      "multi-statement lambda body at column #{col} was not closed with '}' or 'end'"
    )
  end

  # -- Lex Errors --------------------------------------------------------------

  def format_error({:lex_error, reason}, file) do
    format_diagnostic("error", "lexer error", file, 0, inspect(reason))
  end

  # -- Codegen Errors ----------------------------------------------------------

  def format_error({:codegen_error, reason}, file) do
    format_diagnostic("error", "codegen error", file, 0, inspect(reason))
  end

  def format_error({:beam_lint_error, errors}, file) do
    # erl_lint errors come as `[{file_info, [{line, module, payload}, ...]}]`.
    lines =
      errors
      |> Enum.flat_map(fn
        {_file_info, entries} when is_list(entries) -> entries
        other -> [other]
      end)
      |> Enum.map(fn
        {line, :erl_lint, {:undefined_function, {fn_name, arity}}} ->
          "line #{line}: undefined function #{fn_name}/#{arity}"

        {line, module, payload} ->
          "line #{line}: #{module}: #{inspect(payload)}"

        other ->
          inspect(other)
      end)

    format_diagnostic("error", "BEAM lint error", file, 0, Enum.join(lines, "\n      | "))
  end

  def format_error({:expected_module, _ast}, file) do
    format_diagnostic("error", "codegen error", file, 0, "expected a module definition")
  end

  def format_error({:unsupported_container, type}, file) do
    format_diagnostic("error", "codegen error", file, 0, "unsupported container type: #{type}")
  end

  # -- App / release errors (E051-E055) ----------------------------------------

  def format_error({:app_verification_failed, errors}, file) when is_list(errors) do
    Enum.map_join(errors, "\n\n", &format_error(&1, file))
  end

  def format_error({:duplicate_app, occurrences}, _file) do
    paths = Enum.map_join(occurrences, "\n      | ", fn {p, n} -> "#{p} -> app #{n}" end)

    format_diagnostic(
      "error",
      "duplicate application (E051)",
      "Cure.toml",
      0,
      "more than one `app` container in the project:\n      | #{paths}"
    )
  end

  def format_error({:app_name_mismatch, expected, actual}, _file) do
    format_diagnostic(
      "error",
      "app name mismatch (E051)",
      "Cure.toml",
      0,
      "`app #{actual}` does not match [application].name = \"#{expected}\""
    )
  end

  def format_error({:missing_application, _info}, _file) do
    format_diagnostic(
      "error",
      "missing application (E052)",
      "Cure.toml",
      0,
      "`cure release` requires the project to declare exactly one `app` container"
    )
  end

  def format_error({:start_phase_missing, phase, meta}, file) do
    line = Keyword.get(meta, :line, 0)

    format_diagnostic(
      "error",
      "start phase mismatch (E053)",
      file,
      line,
      "phase #{inspect(phase)} declared in [application].start_phases has no `on_phase` clause"
    )
  end

  def format_error({:start_phase_unexpected, phase, meta}, file) do
    line = Keyword.get(meta, :line, 0)

    format_diagnostic(
      "error",
      "start phase mismatch (E053)",
      file,
      line,
      "`on_phase #{inspect(phase)}` has no matching entry in [application].start_phases"
    )
  end

  def format_error({:invalid_root, ast, meta}, file) do
    line = Keyword.get(meta, :line, 0)

    format_diagnostic(
      "error",
      "unresolved root supervisor (E054)",
      file,
      line,
      "`root = ...` must be a `sup Name`, dotted module path, or atom literal: #{inspect(ast)}"
    )
  end

  def format_error({:invalid_app_name, value, meta}, file) do
    line = Keyword.get(meta, :line, 0)

    format_diagnostic(
      "error",
      "invalid application name",
      file,
      line,
      "`app` container name must be a non-empty dotted path; got #{inspect(value)}"
    )
  end

  def format_error({:invalid_applications, value, meta}, file) do
    line = Keyword.get(meta, :line, 0)

    format_diagnostic(
      "error",
      "invalid applications list",
      file,
      line,
      "`applications = ...` must be a list of atom literals; got #{inspect(value)}"
    )
  end

  def format_error({:invalid_included_applications, value, meta}, file) do
    line = Keyword.get(meta, :line, 0)

    format_diagnostic(
      "error",
      "invalid included_applications list",
      file,
      line,
      "`included_applications = ...` must be a list of atom literals; got #{inspect(value)}"
    )
  end

  def format_error({:invalid_env, value, meta}, file) do
    line = Keyword.get(meta, :line, 0)

    format_diagnostic(
      "error",
      "invalid env",
      file,
      line,
      "`env = %{...}` must be a map with atom keys; got #{inspect(value)}"
    )
  end

  def format_error({:release_build_failed, module, reason}, _file) do
    format_diagnostic(
      "error",
      "release build failed (E055)",
      "Cure.toml",
      0,
      "systools/#{module} reported: #{inspect(reason)}"
    )
  end

  def format_error({:release_build_failed, reason}, _file) do
    format_diagnostic(
      "error",
      "release build failed (E055)",
      "Cure.toml",
      0,
      inspect(reason)
    )
  end

  # -- FSM Verifier Errors -----------------------------------------------------

  def format_error({:unreachable_state, message, meta}, file) do
    line = Keyword.get(meta, :line, 0)
    format_diagnostic("error", "unreachable state", file, line, message)
  end

  def format_error({:deadlock, message, meta}, file) do
    line = Keyword.get(meta, :line, 0)
    format_diagnostic("error", "deadlock", file, line, message)
  end

  def format_error({:invalid_terminal, message, meta}, file) do
    line = Keyword.get(meta, :line, 0)
    format_diagnostic("error", "invalid terminal state", file, line, message)
  end

  # -- File Errors -------------------------------------------------------------

  def format_error({:file_read_error, path, reason}, _file) do
    format_diagnostic("error", "file error", path, 0, "cannot read file: #{:file.format_error(reason)}")
  end

  # -- Catch-all ---------------------------------------------------------------

  def format_error(error, file) do
    format_diagnostic("error", "compilation error", file, 0, inspect(error))
  end

  # -- "Did you mean?" Suggestions ---------------------------------------------

  # -- Error Catalog ------------------------------------------------------------

  @error_catalog %{
    "E001" => """
    E001: Type Mismatch

    A function's body type does not match its declared return type,
    or an argument type does not match the parameter type.

    Example:
      fn add(a: Int, b: Int) -> String = a + b
      # Error: declared return type String but body has type Int

    Fix: change the return type annotation or the function body.
    """,
    "E002" => """
    E002: Unbound Variable

    A variable is referenced that has not been defined in the current scope.

    Example:
      fn foo() -> Int = x + 1
      # Error: undefined variable 'x'

    Fix: define the variable with let, or check for typos.
    """,
    "E003" => """
    E003: Arity Mismatch

    A function is called with the wrong number of arguments.

    Example:
      fn add(a: Int, b: Int) -> Int = a + b
      fn main() -> Int = add(1)  # Error: expects 2 arguments, got 1

    Fix: provide the correct number of arguments.
    """,
    "E004" => """
    E004: Non-Exhaustive Match

    A match expression does not cover all possible values of the scrutinee type.

    Example:
      match x
        true -> "yes"
      # Warning: missing pattern for 'false'

    Fix: add the missing patterns or a wildcard (_ -> ...).
    """,
    "E005" => """
    E005: Constraint Violation

    A function with a guard constraint is called with arguments that
    may violate the constraint.

    Example:
      fn safe_div(a: Int, b: Int) -> Int when b != 0 = a / b
      fn main() -> Int = safe_div(10, 0)  # Warning: b != 0 may be violated

    Fix: ensure the arguments satisfy the guard condition.
    """,
    "E006" => """
    E006: Effect Violation

    A function performs an effect that is not declared in its effect
    annotation. Either add the missing effect to the `!` annotation or
    remove the effectful operation.

    Example:
      fn pure_add(a: Int, b: Int) -> Int = println("adding"); a + b
      # Error: undeclared effect Io

    Fix: annotate as `fn pure_add(a: Int, b: Int) -> Int ! Io` or
    remove the println call.
    """,
    "E007" => """
    E007: Unused Variable

    A variable is defined but never referenced. Prefix unused variables
    with `_` to suppress this warning.

    Example:
      fn foo() -> Int =
        let x = 42
        0
      # Warning: unused variable 'x'

    Fix: use the variable or rename it to `_x`.
    """,
    "E008" => """
    E008: Undocumented Public Function

    A public function has no `##` doc comment. This warning is only
    emitted when `cure doc --strict` is used.

    Fix: add a `##` doc comment above the function definition.
    """,
    "E009" => """
    E009: Unreachable Clause

    A pattern matching clause is shadowed by a prior clause and can
    never be reached.

    Example:
      fn classify(x: Int) -> String
        | _ -> "other"
        | 0 -> "zero"   # Unreachable: wildcard above catches everything

    Fix: reorder the clauses so more specific patterns come first.
    """,
    "E010" => """
    E010: Missing Effect Annotation

    A public function performs side effects but has no `!` annotation.
    This warning is only emitted when `--strict-effects` is enabled.

    Fix: add an effect annotation, e.g. `fn greet() -> Atom ! Io`.
    """,
    "E011" => """
    E011: Missing Implicit Argument

    Implicit unification could not solve every implicit parameter at a
    call site. The unification trace shows which constraint failed.

    Fix: pass the implicit explicitly with `{T = ConcreteType}`, or
    constrain the explicit arguments so the implicit can be inferred.
    """,
    "E012" => """
    E012: Sigma Destructuring Failure

    A pattern attempted to destructure a sigma value into shapes that
    don't agree with its declared first or second component.

    Fix: ensure the pattern matches the sigma's structure, or relax
    the type to a plain tuple where dependency is not required.
    """,
    "E013" => """
    E013: Totality Failure

    A function annotated `@total true` is not provably total. Either
    coverage is incomplete or a recursive call doesn't shrink any
    structural argument.

    Fix: add the missing patterns, restructure the recursion to use
    a smaller sub-term, or remove `@total true` if partiality is OK.
    """,
    "E014" => """
    E014: Unfilled Hole

    The compiler reached a `?name` or `??` placeholder. This is
    informational by default; when running `cure check --strict`
    every hole becomes an error.

    Fix: replace the hole with a real expression of the reported
    goal type.
    """,
    "E015" => """
    E015: Refinement Counterexample

    A value flowing into a refinement-typed parameter could violate
    the refinement predicate. The Z3 model gives a concrete witness.

    Fix: tighten the caller's invariants, change the refinement to
    accept the witness, or guard the call with a runtime check.
    """,
    "E016" => """
    E016: Dependent Type Mismatch

    A function's dependent return type, after substituting the
    call-site arguments and normalising, does not match the expected
    type at the use site.

    Fix: check that the actual arguments produce the expected
    relationship (e.g. `m + n` versus the literal length).
    """,
    "E017" => """
    E017: Equality Proof Mismatch

    `refl(x)` was used to inhabit `Eq(T, a, b)` where `a` and `b` are
    not definitionally equal to `x`.

    Fix: if the equality is true but not definitional, prove it using
    `Std.Equal.trans/2`, `Std.Equal.cong/2`, or a `rewrite` step.
    """,
    "E018" => """
    E018: Path-sensitive Refinement Conflict

    A path-sensitive refinement extracted from an `if`/`match` guard
    contradicts a previously declared refinement on the same variable.

    Fix: split the guard into incompatible sub-cases, or relax the
    declared refinement.
    """,
    "E019" => """
    E019: Implicit Argument Solved Inconsistently

    The same implicit argument was solved to two different types from
    different parts of the call site.

    Fix: pass the implicit explicitly, or ensure the call-site
    arguments agree on the inferred type.
    """,
    "E020" => """
    E020: Doctest Mismatch

    A `cure>` doctest produced a different value from its `=>`
    expected line.

    Fix: update either the doctest expectation or the function it
    documents.
    """,
    "E021" => """
    E021: Unknown Record Field in Pattern

    A record pattern references a field that is not declared in the
    record's schema.

    Example:
      rec Point
        x: Int
        y: Int

      fn f(p: Point) -> Int =
        match p
          Point{z: v} -> v   # Error: Point has no field 'z'

    Fix: use one of the declared fields, or remove the clause.
    """,
    "E022" => """
    E022: Record Pattern Field Type Mismatch

    A sub-pattern inside a record pattern is incompatible with the
    declared type of that field.

    Example:
      rec Person
        age: Int

      match p
        Person{age: "forty"} -> ...   # Error: age is Int, not String

    Fix: change the sub-pattern or the field type so they agree.
    """,
    "E023" => """
    E023: Non-Literal Map Pattern Key

    Map keys in pattern position must be literal values (atoms,
    integers, strings, etc.). Bound variables may be used as keys
    only when they are already in scope; in that case they are
    looked up, not bound.

    Example:
      match m
        %{key(): v} -> v   # Error: function calls not allowed as keys

    Fix: use a literal key, or pre-compute the key with `let`.
    """,
    "E024" => """
    E024: Unbound Pin Variable

    The pin operator `^x` was used on a name that is not in scope at
    the pattern's position. The pin operator only compares against
    previously bound values.

    Example:
      match tag
        ^status -> :hit   # Error: 'status' is not bound

    Fix: bind the variable with `let` before the match, or drop the
    `^` if you intended to introduce a fresh binding.
    """,
    "E025" => """
    E025: Non-Exhaustive Nested Match

    A `match` expression with nested patterns does not cover every
    inhabitant of the scrutinee type. The compiler prints a concrete
    witness for the missing case.

    Example:
      match %[r]
        %[Ok(_)] -> :ok
      # Warning: missing pattern `%[Error(_)]`

    Fix: add the missing clause or a wildcard.
    """,
    "E026" => """
    E026: Proof Shape Mismatch

    A binding inside a `proof` container does not elaborate to an
    `Eq(T, a, b)` proof or a refinement-subtype proof. Proof
    containers are intended exclusively for propositional laws.

    Example:
      proof Arithmetic
        fn meaning() -> Int = 42   # Error: not a proof shape

    Fix: move ordinary code into a `mod` container; keep `proof`
    containers for functions returning `Eq(...)` or for refinement
    witnesses.
    """,
    "E027" => """
    E027: assert_type Assertion Failed

    The `assert_type expr : T` builtin was used but the type
    inferred for `expr` is not compatible with `T`.

    Example:
      fn f() -> Int = assert_type 42 : String
      # Error: assert_type expected String, got Int

    Fix: either change the asserted type or the expression. The
    wrapper disappears at runtime, so nothing breaks at runtime when
    it succeeds.
    """,
    "E028" => """
    E028: Record Default Type Mismatch

    A record field declared with a default value has a default whose
    inferred type does not match the declared field type.

    Example:
      rec Person
        name: String = 0       # Error: name is String, default is Int

    Fix: change the default or the declared field type.
    """,
    "E029" => """
    E029: Mutual Recursion Not Structural

    Two or more functions annotated with `@total true` call each other
    in a cycle in which no argument shrinks structurally on every
    path through the cycle. The compiler cannot prove termination.

    Example:
      @total true
      fn a(x: Nat) -> Nat = b(x)

      @total true
      fn b(x: Nat) -> Nat = a(x)
      # Error: neither clause decreases

    Fix: restructure the cycle so some structural argument shrinks
    on every path, or drop `@total true` if partiality is acceptable.
    """,
    "E030" => """
    E030: Package Version Conflict

    The dependency resolver could not find a set of versions that
    satisfies every constraint in `Cure.toml` and the transitive
    dependency graph.

    Example:
      # Cure.toml declares http ~> 1.0
      # but dep Foo requires http ~> 2.0
      # Error: no version of http satisfies both ~> 1.0 and ~> 2.0

    Fix: relax one of the constraints, or pin to a compatible
    version.
    """,
    "E031" => """
    E031: Binary Pattern Not Exhaustive

    A sequence of binary patterns (in a `match`, function head, `let`,
    or comprehension generator) does not cover every byte-length
    inhabitant of the scrutinee's Bitstring type.

    Example:
      fn first_byte(buf: Bitstring) -> Int =
        match buf
          <<b, _rest::binary>> -> b
      # Warning: missing pattern `<<>>`

    Fix: add the missing shape (typically `<<>>` or a size-0 case),
    provide a catch-all arm, or narrow the scrutinee type with a
    `byte_size` refinement so the uncovered cases are ruled out
    statically.
    """,
    "E032" => """
    E032: Function Type Payload Invalid

    An ADT constructor payload carries a value whose type cannot be
    resolved. The most common trigger is a bare identifier that does
    not refer to a declared type. Function-type payloads
    (e.g. `On(Int -> Int)` and `On((Int, Int) -> Int)`) are allowed
    and compile to first-class functions at runtime.

    Example:
      type Callback = On(DoesNotExist) | Off   # Error: unknown type

    Fix: use a concrete type, a declared type alias, or a function
    arrow for callable payloads.
    """,
    "E033" => """
    E033: Multi-line Type Layout Invalid

    A `type` ADT declaration spans multiple lines but the layout
    cannot be absorbed by `parse_type_def/1`. This usually means the
    continuation lines are not indented beyond the `type` keyword or
    a leading `|` is followed by a closing `:dedent` instead of a
    variant name.

    Example:
      type Shape =
      | Circle(Int)   # error: continuation lines must be indented

    Fix: indent every continuation line at the same column inside
    the parent block, for example:
      type Shape =
        | Circle(Int)
        | Square(Int)
    """,
    "E034" => """
    E034: Let Pattern Not Exhaustive

    A `let` binding destructures its RHS with a pattern that does
    not cover every inhabitant of the RHS type. The binding still
    compiles -- Erlang's `=` raises at runtime on a failed match --
    but the compiler surfaces the gap as a warning so you can decide
    whether to widen the pattern or mark the let partial.

    Example:
      fn first_ok(r: Result(Int, String)) -> Int =
        let Ok(x) = r       # warning: missing `Error(_)`
        x

    Fix: rewrite as a `match` with every branch covered, add a
    wildcard by widening to `let _ = r`, or annotate the let's
    AST metadata with `partial: true` (reserved for tooling that
    knows the pattern is acceptable by construction).
    """,
    "E035" => """
    E035: Lambda Block Unterminated

    A multi-statement lambda body (v0.22.0) opened a brace block or
    began an `end`-terminated block but never closed it. The parser
    reached the end of the enclosing expression without seeing `}`
    or `end`.

    Example:
      map(xs, fn (x) -> { x + 1; x * 2 ) # Error: missing '}'
      map(xs, fn (x) -> x + 1; x * 2)    # Error: missing 'end'

    Fix: close the block with a matching `}` for brace-delimited
    bodies or with `end` for end-terminated ones. If the body is a
    single expression, use the v0.19.0 single-expression or indented
    form without `{` and without `;`.
    """,
    "E036" => """
    E036: Binary Comprehension Source Not Bitstring

    A binary comprehension generator `for <<pattern <- source>>`
    requires `source` to be a `Bitstring` (or a refinement of it).
    An Int, List, or other shape cannot drive byte-level iteration.

    Example:
      [b for <<b <- 123>>]   # Error: 123 is Int, not Bitstring

    Fix: pass a `Bitstring` value, for example a string literal
    (`"abc"`) or a `<<...>>` construction.
    """,
    "E038" => """
    E038: Registry Fetch Failed

    A call to the Cure package registry returned a non-2xx status or
    hit a transport error. The failure is surfaced through
    `Cure.Pipeline.Events` on the `:registry` stage; rerun with
    `--verbose` for the HTTP status or transport reason.

    Fix: verify the registry URL (env `CURE_REGISTRY_URL`), check
    network connectivity, or retry after the upstream incident is
    resolved.
    """,
    "E039" => """
    E039: Registry Hash Mismatch

    A tarball downloaded from the registry does not match the sha256
    the index declared for that version. This is treated as an
    unconditional error: the bytes are discarded and the install
    aborts.

    Fix: run `cure deps update` to force a re-resolution against the
    current index. If the mismatch persists, the registry entry is
    corrupt and should be reported upstream.
    """,
    "E040" => """
    E040: Registry Package Not Found

    The registry index has no entry for the requested package name.

    Fix: check the spelling in `Cure.toml`, confirm the package is
    published, or search the index with `cure search <query>`.
    """,
    "E041" => """
    E041: Registry Signature Invalid

    A tarball's Ed25519 signature failed verification against the
    trusted public key for its publisher. The install is aborted.

    Fix: either trust the publisher's key explicitly
    (`cure keys generate / cure keys list`) or reject the package
    until the publisher rotates a compromised key.
    """,
    "E042" => """
    E042: Transparency Log Unreachable

    The registry's transparency log did not respond to the pre-install
    verification request. By default the install continues with an
    :unverified annotation; set `config :cure,
    strict_transparency: true` to make this a hard failure.

    Fix: check connectivity to the registry's `/log` endpoint, or
    accept the unverified install if you trust the transport.
    """,
    "E037" => """
    E037: Binary Segment Size Non-Linear

    The compiler tried to emit a `byte_size(rest) ==
    byte_size(scrutinee) - sum_of_preceding_sizes` refinement for a
    trailing `rest::binary` segment, but one of the preceding
    segments carries a size expression the SMT translator cannot
    linearise (for example an arbitrary runtime expression, or a
    non-byte-aligned specifier). The refinement is downgraded to
    plain `Bitstring` and the pipeline emits this warning so you
    can choose whether to tighten the pattern or accept the
    looser type.

    Example:
      fn f(buf: Bitstring, n: Int) -> Int =
        match buf
          <<head::size(n)-unit(3), rest::binary>> -> ...
                    # warning: non-byte-aligned head size (E037)

      Fix: use byte-aligned sizes (multiples of 8 bits) or explicit
      literal sizes so the arithmetic can be emitted; otherwise accept
      that `rest` binds to plain `Bitstring` and let runtime pattern
      matching enforce the remaining invariants.
    """,
    "E045" => """
    E045: Untyped Send

    The Melquiades operator `<-|` (or its unicode form `\u2709`) was
    applied to a bare `Pid` receiver. Untyped sends bypass the
    per-inbox protocol check and fall back to raw Erlang semantics.
    The warning only fires under strict mode (`@strict_inbox true`)
    so existing FFI callers remain undisturbed.

    Example:
      fn relay(pid: Pid, msg: Atom) -> Atom =
        pid <-| msg       # warning under @strict_inbox

    Fix: narrow the parameter to `Pid(Inbox)` where `Inbox` is the
    actor's inbox ADT, or drop `@strict_inbox` for this module.
    """,
    "E046" => """
    E046: Inbox Mismatch

    A message type flowing into `<-|` is not a subtype of the
    receiver's declared inbox ADT. The send would deliver a value the
    actor's `on_message` cannot pattern-match.

    Example:
      actor Counter
        on_message
          (:inc, n) -> n + 1

      fn bad(pid: Pid(Counter.Inbox)) -> Atom = pid <-| :reset
      # Error: :reset is not one of {:inc, _} | {:dec, _}

    Fix: send one of the declared inbox variants, or extend the
    actor's inbox ADT to include the new message.
    """,
    "E047" => """
    E047: Supervisor Unknown Child

    A `sup` child spec references a module name that doesn't resolve
    to a compiled actor, supervisor, FSM, or externally declared OTP
    module. The runtime would crash at `start_link/1` time.

    Example:
      sup App.Root
        children
          Missing as worker   # Error: unknown module `Missing`

    Fix: compile the referenced actor/supervisor first, or declare it
    as external via the child spec's dotted form (`App.External as e`).
    """,
    "E048" => """
    E048: Supervisor Cycle

    A supervisor tree contains a cycle: either a supervisor lists
    itself as a child, or two supervisors reference each other
    transitively. Starting such a tree would recurse forever.

    Example:
      sup A
        children
          sup A as self   # Error: supervisor A lists itself

    Fix: remove the self-reference, or restructure so the shared
    subtree lives in a third, stand-alone supervisor.
    """,
    "E049" => """
    E049: Actor Handler Non-Exhaustive

    An actor's `on_message` clauses do not cover every variant of
    the declared inbox ADT. Missing inbox messages would fall through
    to the runtime's generic `handle_info/2`, leaving the actor in an
    unexpected state.

    Example:
      actor Counter
        inbox = Inc | Dec | Reset
        on_message
          Inc -> state(n + 1)
          Dec -> state(n - 1)
          # Warning: missing pattern `Reset`

    Fix: add the missing clause, or a wildcard catch-all when falling
    through is intentional.
    """,
    "E050" => """
    E050: Invalid Supervisor Strategy

    A `sup` container declared a `strategy`, `restart`, or `shutdown`
    value outside the closed set the supervisor behaviour accepts.

    Valid strategies: `:one_for_one`, `:one_for_all`, `:rest_for_one`,
    `:simple_one_for_one`.
    Valid restarts:  `:permanent`, `:transient`, `:temporary`.
    Valid shutdowns: `:brutal_kill`, `:infinity`, or a positive
    integer timeout in milliseconds.

    Example:
      sup App.Bad
        strategy = :one_for_many   # Error: unknown strategy

    Fix: pick one of the declared values listed above.
    """,
    "E051" => """
    E051: Duplicate Application

    A Cure project may declare at most one `app` container. The
    project-wide compile driver scans every `.cure` file under `lib/`
    and aborts with this error when it finds two or more.

    Example:
      lib/foo_app.cure:
        app Foo
      lib/bar_app.cure:
        app Bar         # Error: duplicate application

    The same code surfaces when the `app` container's name does not
    match `[application].name` in `Cure.toml` (which itself defaults
    to `[project].name`).

    Fix: keep one `app` per project; if the mismatch was deliberate,
    update either the `app` declaration or `[application].name`.
    """,
    "E052" => """
    E052: Missing Application

    `cure release` (or `mix cure.release`) was invoked against a
    project that does not declare an `app` container. The release
    boot script needs an `Application` callback module to start.

    Fix: add an `app` container under `lib/`, or remove the
    `[release]` table from `Cure.toml` if you only need a library.
    """,
    "E053" => """
    E053: Start Phase Mismatch

    `[application].start_phases` and the `app` container's
    `on_phase :name` clauses disagree. Every declared phase needs a
    handler, and every handler needs a declaration; otherwise the
    OTP boot script would either crash on a missing callback or
    silently never invoke a written one.

    Example:
      Cure.toml:
        [application]
        start_phases = ["init", "warm_cache"]

      lib/app.cure:
        app Demo
          on_phase :init
            (...) -> :ok
          # Missing :warm_cache

    Fix: add the missing handler or drop the entry from
    `start_phases`.
    """,
    "E054" => """
    E054: Unresolved Root Supervisor

    The `root = ...` declaration inside an `app` container did not
    resolve to a known supervisor module. `root` accepts:

      * A `sup Name` soft-keyword form (resolves to `:"Cure.Sup.Name"`).
      * A bare PascalCase identifier (also resolves to `:"Cure.Sup.Name"`).
      * A dotted module path (`App.Root` -> `:"App.Root"`).
      * An atom literal (`:my_app_sup`).

    Example:
      app Demo
        root = 42        # Error: not a module reference

    Fix: replace the value with one of the four accepted forms; for
    a phase-only application without a root supervisor, omit the
    `root` line entirely.
    """,
    "E055" => """
    E055: Release Build Failed

    `cure release` invoked `:systools.make_script/2` (or one of the
    file-write steps that follow) and got back an error. The exact
    payload is included in the diagnostic.

    Common causes:
      * A dependency listed under `[release].applications` is not
        loaded -- `mix deps.compile` it first or remove it.
      * `[release].vm_args` or `[release].sys_config` points at a
        path that does not exist.
      * The project's `.app` resource is malformed (typically when
        `[application]` mixes types -- e.g. an integer in the
        `applications` list).

    Fix: address the underlying systools error, then re-run
    `cure release`.
    """,
    "E063" => """
    E063: Parse Error (recovered)

    A statement contained a syntax error from which the parser
    recovered by skipping tokens until the next statement boundary
    (newline, dedent, or definition-opening keyword such as `fn`,
    `mod`, `rec`, etc.). Subsequent definitions in the same file are
    still reported.

    A file that contains this error will also contain one or more
    primary parse errors (e.g. `:unexpected_token`) that identify
    the root cause. Fix those first; E063 errors will disappear once
    the primary error is resolved.

    Example:
      mod M
        fn foo() -> ???bad     # primary parse error here
        fn bar() -> Int = 0    # still parsed; E063 recovery consumed
                               # the tokens between the two fns

    Fix: address the root syntax error. E063 diagnostics are
    informational and do not indicate a new, independent bug.
    """
  }

  @doc """
  Look up an error code explanation.

  Returns `{:ok, text}` or `:error` if the code is unknown.
  """
  @spec explain(String.t()) :: {:ok, String.t()} | :error
  def explain(code) do
    case Map.get(@error_catalog, String.upcase(code)) do
      nil -> :error
      text -> {:ok, String.trim(text)}
    end
  end

  @doc """
  Return all known error codes with a one-line summary each.

  Each element is `{code, title, brief}` where `title` is the short name
  (e.g. "Type Mismatch") and `brief` is the first descriptive sentence.
  The list is sorted by code.
  """
  @spec list_all() :: [{String.t(), String.t(), String.t()}]
  def list_all do
    @error_catalog
    |> Enum.map(fn {code, text} ->
      lines = text |> String.trim() |> String.split("\n") |> Enum.map(&String.trim/1)

      title =
        case lines do
          [first | _] ->
            case String.split(first, ":", parts: 2) do
              [_, name] -> String.trim(name)
              _ -> first
            end

          _ ->
            code
        end

      brief =
        lines
        |> Enum.drop(1)
        |> Enum.find("", &(&1 != ""))

      {code, title, brief}
    end)
    |> Enum.sort_by(fn {code, _, _} -> code end)
  end

  @doc """
  Suggest similar names for typos using Levenshtein distance.
  """
  @spec suggest(String.t(), [String.t()]) :: String.t() | nil
  def suggest(name, candidates) do
    candidates
    |> Enum.map(fn c -> {c, levenshtein(name, c)} end)
    |> Enum.filter(fn {_, d} -> d > 0 and d <= 2 end)
    |> Enum.sort_by(fn {_, d} -> d end)
    |> case do
      [{best, _} | _] -> best
      _ -> nil
    end
  end

  @doc """
  Format an error with source context showing the offending line.
  """
  @spec format_with_source(term(), String.t(), String.t()) :: String.t()
  def format_with_source(error, file, source) do
    base = format_error(error, file)
    line_num = extract_line(error)

    if line_num > 0 and source != "" do
      lines = String.split(source, "\n")

      case Enum.at(lines, line_num - 1) do
        nil ->
          base

        src_line ->
          col = extract_col(error)
          caret = if col > 0, do: "\n      | #{String.duplicate(" ", col - 1)}^", else: ""
          base <> "\n      | #{src_line}" <> caret
      end
    else
      base
    end
  end

  # -- Formatting Helper -------------------------------------------------------

  defp format_diagnostic(severity, category, file, line, message) do
    location =
      cond do
        line > 0 ->
          " --> " <> Cure.Term.Hyperlink.file_line_link(file, line)

        file in ["", "nofile", nil] ->
          " --> #{file}"

        true ->
          " --> " <> Cure.Term.Hyperlink.file_link(file)
      end

    """
    #{severity}: #{category}
    #{location}
      | #{message}\
    """
    |> String.trim_trailing()
  end

  defp extract_line({_, _, meta}) when is_list(meta), do: Keyword.get(meta, :line, 0)
  defp extract_line({_, _, line, _col}) when is_integer(line), do: line
  defp extract_line(_), do: 0

  defp extract_col({_, _, _line, col}) when is_integer(col), do: col
  defp extract_col(_), do: 0

  # Levenshtein distance for typo suggestions
  defp levenshtein(s, t) do
    s_len = String.length(s)
    t_len = String.length(t)
    s_chars = String.graphemes(s)
    t_chars = String.graphemes(t)

    if s_len == 0 do
      t_len
    else
      if t_len == 0 do
        s_len
      else
        prev_row = Enum.to_list(0..t_len)

        Enum.reduce(Enum.with_index(s_chars, 1), prev_row, fn {s_ch, i}, row ->
          first = [i]

          rest =
            Enum.reduce(Enum.with_index(t_chars, 1), {first, row}, fn {t_ch, j}, {new_row, old_row} ->
              cost = if s_ch == t_ch, do: 0, else: 1

              val =
                Enum.min([
                  Enum.at(old_row, j) + 1,
                  List.last(new_row) + 1,
                  Enum.at(old_row, j - 1) + cost
                ])

              {new_row ++ [val], old_row}
            end)

          elem(rest, 0)
        end)
        |> List.last()
      end
    end
  end
end
