#!/bin/bash
# Cure Language Server startup script

SCRIPT_DIR="$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)"

exec erl -noinput -noshell \
  -pa "$SCRIPT_DIR/_build/ebin" \
  -pa "$SCRIPT_DIR/_build/lsp" \
  -pa "$SCRIPT_DIR/_build/lib" \
  -pa "$SCRIPT_DIR/_build/lib/std" \
  -pa "$SCRIPT_DIR/_build/default/lib/jsx/ebin" \
  -eval "cure_lsp:start(), receive stop -> ok end" \
  -s init stop
