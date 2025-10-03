# Cure Programming Language

A strongly-typed, dependently-typed programming language for the BEAM virtual machine with built-in finite state machines and actor model primitives.

## Features

- **Dependent Types**: Rich type system with types that can depend on values
- **Built-in FSMs**: Finite state machines as first-class language constructs
- **Actor Model**: Native support for Erlang/Elixir-style processes and message passing
- **BEAM Target**: Compiles to BEAM bytecode for excellent concurrency and fault tolerance
- **Hot Code Loading**: Support for live system updates
- **Pattern Matching**: Advanced pattern matching with dependent type constraints

## Project Structure

```
cure/
├── src/
│   ├── lexer/          # Tokenization and lexical analysis
│   ├── parser/         # Syntax analysis and AST generation
│   ├── types/          # Dependent type system implementation
│   ├── codegen/        # BEAM bytecode generation
│   ├── fsm/            # Finite state machine primitives
│   └── runtime/        # Runtime system integration
├── lib/                # Standard library
├── test/               # Test suite
├── examples/           # Example programs
└── docs/              # Language specification and documentation
```

## Getting Started

TODO: Add build and installation instructions

## Language Examples

### Simple Function with Dependent Types
```cure
def vector_length(v: Vector(n: Nat)): Nat = n

def safe_head(list: List(T, n: Nat)) -> Option(T) when n > 0 = 
  Some(list.head)

def safe_head(list: List(T, 0)) -> Option(T) = 
  None
```

### Finite State Machine
```cure
fsm TrafficLight do
  states: [Red, Yellow, Green]
  
  state Red do
    timeout(30_000) -> Yellow
  end
  
  state Yellow do
    timeout(5_000) -> Green
  end
  
  state Green do
    timeout(25_000) -> Red
    event(:emergency) -> Red
  end
end
```

### Process Communication
```cure
def counter_process(count: Int) do
  receive do
    {:increment} -> counter_process(count + 1)
    {:get, pid} -> 
      send(pid, {:count, count})
      counter_process(count)
    {:stop} -> :ok
  end
end
```

## License

TODO: Add license

## Contributing

TODO: Add contributing guidelines