# Contributing to Cure

Thank you for your interest in contributing to the Cure programming language! This document provides guidelines and information for contributors.

## Table of Contents

- [Code of Conduct](#code-of-conduct)
- [Getting Started](#getting-started)
- [Development Workflow](#development-workflow)
- [Code Style](#code-style)
- [Testing](#testing)
- [Documentation](#documentation)
- [Submitting Changes](#submitting-changes)
- [Areas for Contribution](#areas-for-contribution)

## Code of Conduct

This project is a research and educational endeavor. We expect all contributors to:

- Be respectful and constructive in discussions
- Focus on technical merit and learning
- Help newcomers understand the codebase
- Document your changes clearly
- Write tests for new features

## Getting Started

### Prerequisites

- Erlang/OTP 20 or later
- Make
- Git
- Rebar3 (for code formatting)
- Optional: Z3 or CVC5 for SMT solver features

### Setting Up Your Development Environment

```bash
# Clone the repository
git clone <repository-url>
cd cure

# Build the project
make all

# Run tests to verify your setup
make test

# Run specific test suites
erl -pa _build/ebin -s <test_module> run -s init stop
```

## Development Workflow

### Project Structure

```
cure/
├── src/
│   ├── lexer/          # Tokenization (cure_lexer.erl)
│   ├── parser/         # Parsing and AST (cure_parser.erl, cure_ast.hrl)
│   ├── types/          # Type system (cure_typechecker.erl, cure_types.erl)
│   ├── codegen/        # Code generation (cure_codegen.erl, cure_guard_codegen.erl)
│   ├── fsm/            # FSM support (cure_fsm_runtime.erl)
│   ├── smt/            # SMT solver integration (cure_smt_solver.erl)
│   ├── lsp/            # Language server (cure_lsp_server.erl)
│   └── runtime/        # Runtime support (cure_runtime.erl)
├── lib/                # Standard library (.cure files)
├── test/               # Test suites
├── examples/           # Example programs
└── docs/               # Documentation
```

### Branching Strategy

Since this project uses Jujutsu (jj) for version control:

1. Create a new change: `jj new`
2. Make your modifications
3. Commit: `jj commit -m "Description"`
4. Export to git: `jj git export`
5. Push: `jj git push`

If you're using git directly:

1. Create a feature branch: `git checkout -b feature/your-feature`
2. Make your changes
3. Commit with descriptive messages
4. Push and create a pull request

## Code Style

### Erlang Code

We use `rebar3 fmt` for consistent Erlang formatting:

```bash
# Format all Erlang files
rebar3 fmt

# Check formatting without changes
rebar3 fmt --check
```

### Style Guidelines

- **Indentation**: 4 spaces (no tabs)
- **Line Length**: 100 characters maximum
- **Comments**: Use `%` for single-line, `%%` for section headers
- **Documentation**: Use `-doc` attributes for functions
- **Naming**: 
  - Functions: `snake_case`
  - Modules: `snake_case`
  - Types: `PascalCase`
  - Variables: `PascalCase` or `snake_case`

### Cure Language Code

- Use consistent indentation (2 or 4 spaces)
- Document complex type signatures
- Add comments for non-obvious logic
- Follow examples in `examples/` directory

## Testing

### Writing Tests

Tests should be placed in the `test/` directory and follow the `*_test.erl` naming convention.

```erlang
-module(my_feature_test).
-export([run/0]).

run() ->
    io:format("Running My Feature Tests...~n"),
    
    Tests = [
        fun test_basic_functionality/0,
        fun test_edge_cases/0
    ],
    
    % Run tests and report results
    % ... (follow pattern from existing tests)
    ok.

test_basic_functionality() ->
    io:format("  Testing basic functionality...~n"),
    % Your test code here
    ok.
```

### Running Tests

```bash
# Run all tests
make test

# Run specific test
erl -pa _build/ebin -s my_feature_test run -s init stop

# Test categories
erl -pa _build/ebin -s lexer_test run -s init stop           # Lexer tests
erl -pa _build/ebin -s parser_test run -s init stop          # Parser tests
erl -pa _build/ebin -s types_test run -s init stop           # Type system tests
erl -pa _build/ebin -s fsm_test run -s init stop             # FSM tests
erl -pa _build/ebin -s stdlib_comprehensive_test run -s init stop  # Stdlib tests
```

### Test Coverage Goals

- All new features should have tests
- Aim for 80%+ code coverage
- Include both positive and negative test cases
- Test edge cases and error conditions

## Documentation

### Module Documentation

Use Erlang's `-moduledoc` and `-doc` attributes:

```erlang
-module(my_module).

-moduledoc """
# My Module

Brief description of the module's purpose.

## Features

- Feature 1
- Feature 2

## Usage

```erlang
Example usage code
```
""".

-export([my_function/1]).

-doc """
Description of what my_function does.

## Arguments
- `Arg1` - Description

## Returns
- Description of return value

## Examples
```erlang
my_function(arg).
% => result
```
""".
-spec my_function(term()) -> term().
my_function(Arg) ->
    % Implementation
    Arg.
```

### Generating Documentation

```bash
# Generate HTML documentation (after doc target is added to Makefile)
make docs

# View documentation
open _build/docs/index.html
```

## Submitting Changes

### Before Submitting

1. **Format your code**: `rebar3 fmt`
2. **Run tests**: `make test`
3. **Update documentation**: Add/update relevant docs
4. **Write a good commit message**:
   ```
   Brief summary (50 chars or less)
   
   Detailed explanation of the changes, why they were made,
   and any relevant context. Wrap at 72 characters.
   
   - Bullet points for specific changes
   - Reference issues if applicable
   ```

### Commit Message Format

```
Component: Brief description

Detailed explanation of what changed and why.

- Specific change 1
- Specific change 2

Files modified:
- path/to/file1.erl
- path/to/file2.erl
```

### Pull Request Process

1. Ensure all tests pass
2. Update CHANGELOG.md if applicable
3. Add examples for new features
4. Request review from maintainers
5. Address review feedback promptly

## Areas for Contribution

### High Priority

- **Standard Library Expansion**: Add more data structures and utilities
- **Error Messages**: Improve error reporting and diagnostics
- **Performance**: Optimize hot paths in compiler and runtime
- **Documentation**: Improve user guides and API documentation
- **Examples**: Create more example programs demonstrating features

### Medium Priority

- **IDE Support**: Enhance LSP server features (completion, refactoring)
- **Build System**: Improve incremental compilation
- **Testing**: Add more comprehensive test suites
- **Tooling**: Development tools and debugging support

### Research/Experimental

- **Linear Types**: Resource management and memory safety
- **Effect System**: Track computational effects
- **Macro System**: Compile-time metaprogramming
- **Gradual Typing**: Mixed static/dynamic typing
- **Distributed FSMs**: Cross-node coordination

### Good First Issues

- Fix typos in documentation
- Add test cases for existing features
- Improve error messages
- Write examples for features
- Add inline code documentation

## Questions?

- Check existing documentation in `docs/`
- Look at similar code in the codebase
- Review test files for usage examples
- Open an issue for clarification

## License

By contributing to Cure, you agree that your contributions will be licensed under the same license as the project (TBD).

---

Thank you for contributing to Cure! Your efforts help make dependently-typed functional programming more accessible on the BEAM.
