# Cure Programming Language - Build System
ERLC = erlc
ERL = erl
ELIXIR = elixir
MIX = mix

# Directories
SRC_DIR = src
LIB_DIR = lib
TEST_DIR = test
LSP_DIR = lsp
BUILD_DIR = _build
EBIN_DIR = $(BUILD_DIR)/ebin
LIB_EBIN_DIR = $(BUILD_DIR)/lib
LSP_EBIN_DIR = $(BUILD_DIR)/lsp

# Source files
UTILS_SRC = $(SRC_DIR)/cure_utils.erl
LEXER_SRC = $(wildcard $(SRC_DIR)/lexer/*.erl)
PARSER_SRC = $(wildcard $(SRC_DIR)/parser/*.erl)
TYPES_SRC = $(wildcard $(SRC_DIR)/types/*.erl)
CODEGEN_SRC = $(wildcard $(SRC_DIR)/codegen/*.erl)
FSM_SRC = $(wildcard $(SRC_DIR)/fsm/*.erl)
RUNTIME_SRC = $(wildcard $(SRC_DIR)/runtime/*.erl)
CLI_SRC = $(SRC_DIR)/cure_cli.erl
LSP_SRC = $(wildcard $(LSP_DIR)/*.erl)

# Cure standard library files
CURE_STD_SRC = $(wildcard $(LIB_DIR)/*.cure $(LIB_DIR)/std/*.cure)

# Test files (exclude problematic advanced tests and EUnit-dependent tests for now)
TEST_SRC = $(filter-out $(TEST_DIR)/dependent_types_advanced_test.erl $(TEST_DIR)/codegen_advanced_test.erl $(TEST_DIR)/fsm_advanced_test.erl $(TEST_DIR)/monomorphization_test.erl $(TEST_DIR)/inlining_test.erl $(TEST_DIR)/nat_type_test.erl, $(wildcard $(TEST_DIR)/*.erl))

# Working test modules by category
BASIC_TESTS = $(TEST_DIR)/test_runner.erl $(TEST_DIR)/fsm_simple_test.erl $(TEST_DIR)/types_simple_test.erl $(TEST_DIR)/codegen_simple_test.erl
INTEGRATION_TESTS = $(TEST_DIR)/integration_test.erl
PERFORMANCE_TESTS = $(TEST_DIR)/performance_test.erl

ALL_SRC = $(UTILS_SRC) $(LEXER_SRC) $(PARSER_SRC) $(TYPES_SRC) $(CODEGEN_SRC) $(FSM_SRC) $(RUNTIME_SRC) $(CLI_SRC)
BEAM_FILES = $(patsubst $(SRC_DIR)/%.erl,$(EBIN_DIR)/%.beam,$(ALL_SRC))
TEST_BEAM_FILES = $(patsubst $(TEST_DIR)/%.erl,$(EBIN_DIR)/%.beam,$(TEST_SRC))
CURE_STD_BEAM_FILES = $(patsubst $(LIB_DIR)/%.cure,$(LIB_EBIN_DIR)/%.beam,$(CURE_STD_SRC))
LSP_BEAM_FILES = $(patsubst $(LSP_DIR)/%.erl,$(LSP_EBIN_DIR)/%.beam,$(LSP_SRC))

# Compiler options
ERLC_OPTS = +debug_info -I include -I src/parser -I src/fsm -I src/types -o $(EBIN_DIR)

.PHONY: all clean test test-basic test-integration test-performance docs setup compiler tests compile-file stdlib stdlib-clean stdlib-check lsp lsp-deps lsp-scripts lsp-shell

all: setup compiler stdlib

setup:
	@mkdir -p $(BUILD_DIR)
	@mkdir -p $(EBIN_DIR)
	@mkdir -p $(EBIN_DIR)/lexer
	@mkdir -p $(EBIN_DIR)/parser
	@mkdir -p $(EBIN_DIR)/types
	@mkdir -p $(EBIN_DIR)/codegen
	@mkdir -p $(EBIN_DIR)/fsm
	@mkdir -p $(EBIN_DIR)/runtime
	@mkdir -p $(LIB_EBIN_DIR)
	@mkdir -p $(LIB_EBIN_DIR)/std
	@mkdir -p $(LSP_EBIN_DIR)

compiler: $(BEAM_FILES)
	@echo "Cure compiler built successfully"

# Compile Cure standard library
stdlib: compiler $(CURE_STD_BEAM_FILES)
	@echo "Cure standard library compilation completed"
	@FAILED_FILES=$$(find $(LIB_EBIN_DIR) -name "*.failed" 2>/dev/null | wc -l); \
	if [ $$FAILED_FILES -gt 0 ]; then \
		echo "Warning: $$FAILED_FILES standard library files failed to compile"; \
		echo "Failed files:"; \
		find $(LIB_EBIN_DIR) -name "*.failed" -exec echo "  {}" \; 2>/dev/null || true; \
		echo "Standard library partially compiled - some functionality may be limited"; \
	else \
		echo "All standard library files compiled successfully"; \
	fi

# Clean standard library build artifacts
stdlib-clean:
	@echo "Cleaning Cure standard library build artifacts..."
	rm -rf $(LIB_EBIN_DIR)
	find $(BUILD_DIR) -name "*.failed" -delete 2>/dev/null || true
	@echo "Standard library artifacts cleaned"

# Check if standard library is compiled
stdlib-check: compiler
	@echo "Checking Cure standard library compilation..."
	@MISSING_COUNT=0; \
	MISSING_FILES_LIST=""; \
	for cure_file in $(CURE_STD_SRC); do \
		beam_file=$$(echo "$$cure_file" | sed 's|$(LIB_DIR)|$(LIB_EBIN_DIR)|' | sed 's|\.cure$$|\.beam|'); \
		if [ ! -f "$$beam_file" ]; then \
			MISSING_COUNT=$$((MISSING_COUNT + 1)); \
			MISSING_FILES_LIST="$$MISSING_FILES_LIST  $$beam_file\n"; \
		fi; \
	done; \
	if [ $$MISSING_COUNT -gt 0 ]; then \
		echo "Missing compiled standard library files:"; \
		printf "$$MISSING_FILES_LIST"; \
		echo "Run 'make stdlib' to compile the standard library."; \
		false; \
	else \
		echo "All standard library files are compiled."; \
	fi

# Force recompile standard library
stdlib-rebuild: stdlib-clean stdlib
	@echo "Cure standard library rebuilt successfully"

# Compile tests
tests: compiler $(TEST_BEAM_FILES)
	@echo "Tests compiled successfully"

# Pattern rule for compiling Erlang files
$(EBIN_DIR)/%.beam: $(SRC_DIR)/%.erl
	@echo "Compiling $<..."
	@mkdir -p $(@D)
	$(ERLC) $(ERLC_OPTS) $<

# Pattern rule for compiling test files
$(EBIN_DIR)/%.beam: $(TEST_DIR)/%.erl
	@echo "Compiling test $<..."
	$(ERLC) $(ERLC_OPTS) $<

# Pattern rule for compiling LSP files
$(LSP_EBIN_DIR)/%.beam: $(LSP_DIR)/%.erl
	@echo "Compiling LSP $<..."
	@mkdir -p $(@D)
	$(ERLC) +debug_info -I include -I src/parser -I src/fsm -I src/types -o $(LSP_EBIN_DIR) $<

# Pattern rule for compiling Cure standard library files
$(LIB_EBIN_DIR)/%.beam: $(LIB_DIR)/%.cure
	@echo "Compiling Cure stdlib $<..."
	@mkdir -p $(@D)
	@if [ -f "cure" ]; then \
		if ./cure "$<" -o "$@" --verbose 2>/dev/null; then \
			echo "Successfully compiled $< -> $@"; \
		else \
			echo "Warning: Failed to compile $<, continuing with other files"; \
			touch "$@.failed"; \
		fi; \
	else \
		echo "Warning: cure compiler not found, skipping $<"; \
		touch "$@.failed"; \
	fi

# Clean build artifacts
clean:
	rm -rf $(BUILD_DIR)
	find . -name "*.failed" -delete 2>/dev/null || true
	@echo "Build artifacts cleaned"

# Run tests
test: tests
	@echo "Running Cure compiler test suite..."
	$(ERL) -pa $(EBIN_DIR) -pa $(LIB_EBIN_DIR) -pa $(LIB_EBIN_DIR)/std -noshell -s test_runner run_all -s init stop

# Run only basic tests
test-basic: tests
	@echo "Running basic tests..."
	$(ERL) -pa $(EBIN_DIR) -pa $(LIB_EBIN_DIR) -pa $(LIB_EBIN_DIR)/std -noshell -s test_runner run_basic -s init stop

# Run only integration tests 
test-integration: tests
	@echo "Running integration tests..."
	$(ERL) -pa $(EBIN_DIR) -pa $(LIB_EBIN_DIR) -pa $(LIB_EBIN_DIR)/std -noshell -s test_runner run_integration -s init stop

# Run performance tests
test-performance: tests
	@echo "Running performance tests..."
	$(ERL) -pa $(EBIN_DIR) -pa $(LIB_EBIN_DIR) -pa $(LIB_EBIN_DIR)/std -noshell -s test_runner run_performance -s init stop

# Generate documentation
docs:
	@echo "Generating documentation..."
	# TODO: Add documentation generation

# Install the compiler
install: compiler
	@echo "Installing Cure compiler..."
	# TODO: Add installation logic

# Build LSP server
lsp: compiler $(LSP_BEAM_FILES) lsp-scripts
	@echo "Cure LSP server built successfully"

# Create LSP executable scripts
lsp-scripts:
	@echo "Creating LSP executable scripts..."
	@chmod +x cure-lsp cure-lsp.sh
	@echo "LSP scripts are now executable"

# Development shell
shell: compiler
	$(ERL) -pa $(EBIN_DIR) -pa $(LIB_EBIN_DIR) -pa $(LIB_EBIN_DIR)/std

# LSP development shell
lsp-shell: compiler lsp
	$(ERL) -pa $(EBIN_DIR) -pa $(LSP_EBIN_DIR) -pa $(LIB_EBIN_DIR) -pa $(LIB_EBIN_DIR)/std

# Lint code
lint:
	@echo "Linting Cure source code..."
	# TODO: Add linting with dialyzer or similar

# Format code
format:
	@echo "Formatting Cure source code..."
	rebar3 fmt

# Compile a specific .cure file
compile-file: compiler stdlib
	@if [ -z "$(CURE_FILE)" ]; then \
		echo "Usage: make compile-file CURE_FILE=path/to/file.cure [OUTPUT=output.beam]"; \
		echo "Example: make compile-file CURE_FILE=examples/simple.cure"; \
		exit 1; \
	fi
	@if [ ! -f "$(CURE_FILE)" ]; then \
		echo "Error: File $(CURE_FILE) not found"; \
		exit 1; \
	fi
	@echo "Compiling $(CURE_FILE)..."
	@if [ -n "$(OUTPUT)" ]; then \
		./cure "$(CURE_FILE)" -o "$(OUTPUT)" --verbose; \
	else \
		./cure "$(CURE_FILE)" --verbose; \
	fi

# Show help
help:
	@echo "Cure Programming Language Build System"
	@echo ""
	@echo "Available targets:"
	@echo "  all        - Build the complete compiler (default)"
	@echo "  compiler   - Build compiler components"
	@echo "  lsp        - Build LSP server for IDE integration"
	@echo "  stdlib     - Compile Cure standard library"
	@echo "  stdlib-clean - Clean standard library build artifacts"
	@echo "  stdlib-check - Check if standard library is compiled"
	@echo "  stdlib-rebuild - Force rebuild of standard library"
	@echo "  tests      - Compile test files"
	@echo "  test       - Run complete test suite (basic + integration)"
	@echo "  test-basic - Run only basic unit tests"
	@echo "  test-integration - Run only integration tests"
	@echo "  test-performance - Run performance benchmark tests"
	@echo "  clean      - Remove build artifacts"
	@echo "  docs       - Generate documentation"
	@echo "  install    - Install the compiler"
	@echo "  shell      - Start Erlang shell with Cure modules loaded"
	@echo "  lsp-shell  - Start Erlang shell with LSP modules loaded"
	@echo "  lint       - Run static analysis"
	@echo "  format     - Format source code"
	@echo "  compile-file - Compile a single .cure file (Usage: make compile-file CURE_FILE=file.cure)"
	@echo "  help       - Show this help"
