#!/bin/bash

# Test LSP initialization message
INIT_MSG='{"jsonrpc":"2.0","id":1,"method":"initialize","params":{"processId":null,"rootUri":"file:///opt/Proyectos/Ammotion/cure","capabilities":{}}}'
CONTENT_LENGTH=${#INIT_MSG}

printf "Content-Length: %d\r\n\r\n%s" "$CONTENT_LENGTH" "$INIT_MSG" | timeout 3 ../cure-lsp start 2>&1
