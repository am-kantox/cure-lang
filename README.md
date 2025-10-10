# Cure Programming Language

A strongly-typed, dependently-typed programming language for the BEAM virtual machine with built-in finite state machines and a **complete import system**.

🚀 **NEW: Complete Import System & Runtime Success!** (October 2025)

## Features

- **🚀 Complete Import System**: Full module resolution with `import Module [functions]` syntax
- **📚 Standard Library**: Working `Std` module with essential functions (`print/1`, `show/1`, `map/2`, `fold/3`, `zip_with/3`)
- **🎯 Runtime Verification**: Successfully compiles and executes dependent types examples!
- **🎆 Dependent Types**: Rich type system with types that can depend on values - length-indexed vectors, bounded arrays
- **🎆 Higher-Kinded Types**: Complete functors, monads, type constructors with kind signatures
- **Built-in FSMs**: Finite state machines as first-class language constructs
- **BEAM Target**: Compiles to BEAM bytecode for excellent concurrency and fault tolerance
- **Advanced Pattern Matching**: Pattern matching with dependent type constraints
- **Hot Code Loading**: Support for live system updates

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

### Quick Start
```bash
# Build the compiler
make all

# Try the working dependent types example!
./cure examples/dependent_types_simple.cure

# Run the compiled program
erl -pa _build/ebin -noshell -eval "'DependentTypes':demo_all(), init:stop()."

# Expected output:
# === Dependent Types Demonstration ===
# All operations below are compile-time verified for safety!
# === Vector Operations ===
# Dot product: 32.0
# Vector sum: [5.0, 7.0, 9.0]
# Scaled vector: [2.0, 4.0, 6.0]

# Show help
./cure --help
```

### Installation
**Prerequisites**: Erlang/OTP 20+, Make, Unix-like environment

```bash
# Clone and build
git clone <repository>
cd cure
make all

# Verify installation
./cure --version

# Run tests
make test
```

### Command Line Interface
The Cure compiler includes a comprehensive CLI for compiling `.cure` files to BEAM bytecode.

Basic usage:
```bash
cure [OPTIONS] <input-file>
```

Key options:
- `-o, --output <file>`: Specify output file
- `-d, --output-dir <dir>`: Set output directory
- `--verbose`: Enable detailed output
- `--no-type-check`: Skip type checking

See [docs/CLI_USAGE.md](docs/CLI_USAGE.md) for complete documentation.

## Language Examples

### 🚀 Working Import System with Dependent Types (NEW!)
```cure
module DependentTypes do
  export [demo_all/0, vector_operations/0]

  # Import standard library functions
  import Std [List, Result]
  
  # Length-indexed vectors with compile-time safety
  def make_vec3(x: Float, y: Float, z: Float): Vector(Float, 3) =
    [x, y, z]
  
  # Safe vector operations - length checked at compile time
  def dot_product(v1: Vector(Float, n), v2: Vector(Float, n)): Float =
    zip_with(v1, v2, fn(x, y) -> x * y end)
    |> fold(0.0, fn(x, acc) -> acc + x end)
  
  def vector_operations(): Unit =
    let v1 = make_vec3(1.0, 2.0, 3.0)
    let v2 = make_vec3(4.0, 5.0, 6.0)
    
    let dot_result = dot_product(v1, v2)  # 32.0
    print("Dot product: " ++ show(dot_result))
    
    let sum = vector_add(v1, v2)  # [5.0, 7.0, 9.0]
    print("Vector sum: " ++ show(sum))
end

# Successfully compiles and runs!
# Output:
# === Dependent Types Demonstration ===
# Dot product: 32.0
# Vector sum: [5.0, 7.0, 9.0]
```

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