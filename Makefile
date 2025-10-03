# Cure Programming Language - Build System
ERLC = erlc
ERL = erl
ELIXIR = elixir
MIX = mix

# Directories
SRC_DIR = src
LIB_DIR = lib
TEST_DIR = test
BUILD_DIR = _build
EBIN_DIR = $(BUILD_DIR)/ebin

# Source files
LEXER_SRC = $(wildcard $(SRC_DIR)/lexer/*.erl)
PARSER_SRC = $(wildcard $(SRC_DIR)/parser/*.erl)
TYPES_SRC = $(wildcard $(SRC_DIR)/types/*.erl)
CODEGEN_SRC = $(wildcard $(SRC_DIR)/codegen/*.erl)
FSM_SRC = $(wildcard $(SRC_DIR)/fsm/*.erl)
RUNTIME_SRC = $(wildcard $(SRC_DIR)/runtime/*.erl)

ALL_SRC = $(LEXER_SRC) $(PARSER_SRC) $(TYPES_SRC) $(CODEGEN_SRC) $(FSM_SRC) $(RUNTIME_SRC)
BEAM_FILES = $(patsubst $(SRC_DIR)/%.erl,$(EBIN_DIR)/%.beam,$(ALL_SRC))

# Compiler options
ERLC_OPTS = +debug_info -I include -I src/parser -o $(EBIN_DIR)

.PHONY: all clean test docs setup compiler

all: setup compiler

setup:
	@mkdir -p $(BUILD_DIR)
	@mkdir -p $(EBIN_DIR)
	@mkdir -p $(EBIN_DIR)/lexer
	@mkdir -p $(EBIN_DIR)/parser
	@mkdir -p $(EBIN_DIR)/types
	@mkdir -p $(EBIN_DIR)/codegen
	@mkdir -p $(EBIN_DIR)/fsm
	@mkdir -p $(EBIN_DIR)/runtime

compiler: $(BEAM_FILES)
	@echo "Cure compiler built successfully"

# Pattern rule for compiling Erlang files
$(EBIN_DIR)/%.beam: $(SRC_DIR)/%.erl
	@echo "Compiling $<..."
	@mkdir -p $(@D)
	$(ERLC) $(ERLC_OPTS) $<

# Clean build artifacts
clean:
	rm -rf $(BUILD_DIR)
	@echo "Build artifacts cleaned"

# Run tests
test: compiler
	@echo "Running tests..."
	$(ERL) -pa $(EBIN_DIR) -s cure_test run -s init stop

# Generate documentation
docs:
	@echo "Generating documentation..."
	# TODO: Add documentation generation

# Install the compiler
install: compiler
	@echo "Installing Cure compiler..."
	# TODO: Add installation logic

# Development shell
shell: compiler
	$(ERL) -pa $(EBIN_DIR)

# Lint code
lint:
	@echo "Linting Cure source code..."
	# TODO: Add linting with dialyzer or similar

# Format code
format:
	@echo "Formatting Cure source code..."
	# TODO: Add code formatting

# Show help
help:
	@echo "Cure Programming Language Build System"
	@echo ""
	@echo "Available targets:"
	@echo "  all        - Build the complete compiler (default)"
	@echo "  compiler   - Build compiler components"
	@echo "  clean      - Remove build artifacts"
	@echo "  test       - Run test suite"
	@echo "  docs       - Generate documentation"
	@echo "  install    - Install the compiler"
	@echo "  shell      - Start Erlang shell with Cure modules loaded"
	@echo "  lint       - Run static analysis"
	@echo "  format     - Format source code"
	@echo "  help       - Show this help"