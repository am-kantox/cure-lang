# Cure FSM Implementation Status

## Summary

We've designed a complete FSM system for Cure with Mermaid-style syntax, gen_server-based runtime, and SMT verification support.

## What Has Been Done

### 1. API Design ✅

- **Defined FSM syntax**: `fsm RecordType{...} do State --> |event| State end`
- **Specified handler signature**: `def event(from: StateName, event: Event, payload: Payload): Result(State, FsmError)`
- **Designed API functions**: `start_fsm/1`, `fsm_cast/2`, `fsm_advertise/2`, `fsm_state/1`
- **Non-deterministic transitions**: Handlers return target state explicitly

### 2. Example Code ✅

Created `examples/turnstile.cure` demonstrating:
- Custom payload record (`TurnstilePayload`)
- FSM definition with Mermaid transitions
- Handler functions with business logic
- Complete demo showing FSM lifecycle

### 3. Type Definitions ✅

Updated `lib/std/fsm.cure` with:
- Core types: `FsmName`, `StateName`, `Event`, `State`, `FsmError`
- Generic payload support (any type, not just key-value lists)
- Function signatures matching the API design
- Placeholder implementations

### 4. Documentation ✅

Created comprehensive documentation:
- `docs/FSM_API_DESIGN.md` - User-facing API documentation
- `docs/FSM_IMPLEMENTATION_STRATEGY.md` - Implementation plan
- Inline documentation in code files

### 5. Runtime Infrastructure ✅

- **FSM runtime header updated**: Added `initial_payload` field to `#fsm_definition{}`
- **API wrapper created**: `cure_fsm_cure_api.erl` bridges Cure and Erlang
- **Existing runtime**: `cure_fsm_runtime.erl` gen_server already implemented

## What Needs to Be Done

### Phase 1: Parser (High Priority)

**File**: `src/parser/cure_parser.erl`

Tasks:
1. Add lexer support for `-->` token
2. Implement `parse_fsm_definition/1` function
3. Parse `fsm RecordType{...} do` header
4. Parse transition syntax: `State --> |event| TargetState`
5. Build AST with `#fsm_def{}` record
6. Extract initial state (first transition)
7. Group transitions by state into `#state_def{}` records

### Phase 2: Type Checking (High Priority)

**File**: `src/types/cure_typechecker.erl`

Tasks:
1. Add `check_fsm_definition/2` function
2. Validate payload record type exists
3. Verify initial payload matches record fields
4. Extract and validate all state names
5. Find handler functions for each event
6. Verify handler signatures match specification
7. Check transition consistency

### Phase 3: SMT Verification (Medium Priority)

**File**: `src/verification/cure_smt_solver.erl`

Tasks:
1. Add `verify_fsm_safety/1` function
2. Implement reachability analysis
3. Detect unreachable states
4. Detect deadlock states (no outgoing transitions)
5. Verify handler return values are valid states
6. Check payload type consistency across transitions

### Phase 4: Code Generation (High Priority)

**File**: `src/codegen/cure_codegen.erl`

Tasks:
1. Add `generate_fsm_definition/2` function
2. Generate `'__fsm_definition__'/0` function
3. Build transition table: `#{(State, Event) => {Target, Guard, Handler}}`
4. Generate handler wrapper functions
5. Convert Cure `Result` types to Erlang tuples
6. Handle `Ok({state, payload})` and `Error(reason)` cases

### Phase 5: Runtime Updates (Low Priority)

**File**: `src/fsm/cure_fsm_runtime.erl`

Tasks:
1. Update `init/1` to use `initial_payload` field
2. Modify `handle_fsm_event/3` to call handlers with new signature
3. Handle `{ok, {NextState, NewPayload}}` return values
4. Handle `{error, Reason}` return values (stay in current state)
5. Update transition lookup to support non-deterministic transitions

### Phase 6: Standard Library (Low Priority)

**File**: `lib/std/fsm.cure`

Tasks:
1. Implement FFI calls to `cure_fsm_cure_api.erl`
2. Add proper FFI syntax (depends on Cure's FFI mechanism)
3. Ensure types match between Cure and Erlang

### Phase 7: Testing (High Priority)

Tasks:
1. Write parser tests for FSM syntax
2. Write type checker tests
3. Write codegen tests
4. Write runtime integration tests
5. Compile and run `examples/turnstile.cure`
6. Verify expected output

## Technical Decisions Made

1. **Mermaid-style syntax**: `State --> |event| State` for clarity
2. **First state is initial**: Simplifies parsing and makes intent clear
3. **Non-deterministic transitions**: Handlers return target state explicitly
4. **Generic payload**: Any Cure type, not restricted to key-value lists
5. **Result type**: Handlers return `Result(State, FsmError)` for safety
6. **Gen_server runtime**: Leverage existing, battle-tested Erlang infrastructure
7. **SMT verification**: Formal verification of FSM properties during compilation

## Key Files

```
examples/
  └── turnstile.cure           ✅ Complete example

lib/std/
  └── fsm.cure                  ✅ Type definitions (needs FFI implementation)

src/fsm/
  ├── cure_fsm_runtime.erl      ✅ Gen_server runtime (needs minor updates)
  ├── cure_fsm_runtime.hrl      ✅ Updated with initial_payload
  ├── cure_fsm_cure_api.erl     ✅ Cure API wrapper
  └── cure_fsm_builtins.erl     ✅ Existing (may need updates)

src/parser/
  ├── cure_parser.erl           ⏳ Needs FSM parsing
  └── cure_ast.hrl              ✅ FSM records already defined

src/types/
  └── cure_typechecker.erl      ⏳ Needs FSM type checking

src/verification/
  └── cure_smt_solver.erl       ⏳ Needs FSM verification

src/codegen/
  └── cure_codegen.erl          ⏳ Needs FSM code generation

docs/
  ├── FSM_API_DESIGN.md         ✅ Complete
  ├── FSM_IMPLEMENTATION_STRATEGY.md  ✅ Complete
  └── FSM_STATUS.md             ✅ This file
```

## Immediate Next Steps

1. **Lexer**: Add `-->` and `|` token support
2. **Parser**: Implement FSM parsing in `cure_parser.erl`
3. **Testing**: Create simple FSM examples to test parser
4. **Type Checking**: Implement FSM validation
5. **Code Generation**: Generate Erlang code from FSM AST

## Questions for Consideration

1. **FFI Syntax**: How should FFI calls be written in Cure? `@ffi(...)` or another syntax?
2. **Error Messages**: What format should FSM compilation errors use?
3. **Debugging**: Should we generate debug information for FSM transitions?
4. **Performance**: Should we optimize the transition table (compile-time vs runtime)?
5. **Backward Compatibility**: Do we need to support the old FSM syntax during transition?

## Success Criteria

The implementation will be considered complete when:

1. ✅ `examples/turnstile.cure` compiles without errors
2. ✅ `examples/turnstile.cure` runs and produces expected output  
3. ✅ All unit tests pass
4. ✅ SMT verification detects unreachable states and deadlocks
5. ✅ Documentation is comprehensive and accurate
6. ✅ Performance is acceptable (< 1ms for typical FSM operations)

## Conclusion

The FSM design is complete and well-documented. The next phase is implementation, starting with the parser. The existing infrastructure (runtime, AST, SMT solver) provides a solid foundation. The main work is connecting these pieces through the parser, type checker, and code generator.
