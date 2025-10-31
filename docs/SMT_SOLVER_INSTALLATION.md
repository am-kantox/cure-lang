# SMT Solver Installation Guide

This guide explains how to install Z3 and CVC5 SMT solvers for use with the Cure compiler's dependent type verification system.

---

## Z3 SMT Solver (Recommended)

### Ubuntu/Debian
```bash
# Install from official repositories (Ubuntu 20.04+)
sudo apt-get update
sudo apt-get install z3

# Verify installation
z3 --version
# Expected output: Z3 version 4.8.x or later
```

### From Source (Latest Version)
```bash
# Install dependencies
sudo apt-get install python3 git cmake build-essential

# Clone and build
git clone https://github.com/Z3Prover/z3.git
cd z3
python3 scripts/mk_make.py
cd build
make
sudo make install

# Verify
z3 --version
```

### Testing Z3
Create a test file `test.smt2`:
```smt2
(set-logic QF_LIA)
(declare-const x Int)
(declare-const y Int)
(assert (> x y))
(assert (> y 0))
(check-sat)
(get-model)
```

Run:
```bash
z3 -smt2 test.smt2
# Expected output:
# sat
# (model
#   (define-fun y () Int 1)
#   (define-fun x () Int 2)
# )
```

---

## CVC5 SMT Solver (Alternative)

### Ubuntu/Debian (Binary Release)
```bash
# Download latest release
wget https://github.com/cvc5/cvc5/releases/download/cvc5-1.0.8/cvc5-Linux
chmod +x cvc5-Linux
sudo mv cvc5-Linux /usr/local/bin/cvc5

# Verify installation
cvc5 --version
```

### From Source
```bash
# Install dependencies
sudo apt-get install cmake libgmp-dev

# Clone and build
git clone https://github.com/cvc5/cvc5.git
cd cvc5
./configure.sh
cd build
make
sudo make install

# Verify
cvc5 --version
```

### Testing CVC5
Using the same `test.smt2`:
```bash
cvc5 --lang smt2 test.smt2
# Expected similar output to Z3
```

---

## Using with Cure

### Erlang API Level

The SMT solver is available at the Erlang API level and can be used programmatically:

```erlang
% Start solver
{ok, Pid} = cure_smt_process:start_solver(z3, 5000).

% Check constraint
Result = cure_smt_solver:check_constraint(Constraint, Env).

% Stop solver
cure_smt_process:stop_solver(Pid).
```

### CLI Integration (Not Yet Implemented)

**Status**: ⚠️ CLI options for SMT solver integration are **planned but not yet implemented**.

The following options are documented for future implementation:

```bash
# Planned (not yet available):
./cure --smt-solver z3 examples/dependent_types.cure
./cure --no-smt examples/dependent_types.cure
./cure --smt-timeout 10000 examples/dependent_types.cure
```

**Current CLI Options**: See `cure --help` for currently available options.

---

## Troubleshooting

### "Solver not found" error
- Check installation: `which z3` or `which cvc5`
- Ensure solver is in PATH
- Try absolute path in Cure config

### Timeout errors
- Increase timeout: `--smt-timeout 30000`
- Simplify constraints
- Check solver is responding: `z3 -smt2 -in` (interactive mode)

### Permission errors
- Ensure solver executable: `chmod +x /usr/local/bin/z3`
- Check PATH: `echo $PATH`

---

## Performance Tips

1. **Use Z3 as primary**: Generally faster for arithmetic constraints
2. **Set appropriate timeouts**: Start with 5s, increase if needed
3. **Cache results**: Cure caches constraint checking results
4. **Use symbolic fallback for simple constraints**: No solver overhead

---

## Version Requirements

- **Z3**: Version 4.8.0 or later
- **CVC5**: Version 1.0.0 or later

Older versions may work but are untested.

---

## Integration Status

- ✅ **SMT Solver Implementation**: Complete at Erlang API level
- ✅ **Z3 Support**: Fully implemented and tested
- ⚠️ **CLI Integration**: Not yet implemented (requires adding CLI flags)
- 📋 **CVC5 Support**: Stub exists, full implementation planned

---

**Last Updated:** October 31, 2025
