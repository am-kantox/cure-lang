#!/bin/bash
# Build script for Cure Language static website

set -e

echo "Building Cure Language Website"
echo "==============================="
echo ""

# Step 1: Generate API documentation with ex_doc
echo "1. Generating API documentation with ex_doc..."
rebar3 ex_doc
echo "   ✓ API documentation generated"
echo ""

# Step 2: Create site directory structure
echo "2. Creating site directory structure..."
mkdir -p site/api site/docs site/media site/css site/js
echo "   ✓ Directories created"
echo ""

# Step 3: Copy ex_doc output to site
echo "3. Copying API documentation to site..."
cp -r docs/_build/* site/api/
echo "   ✓ API documentation copied"
echo ""

# Step 4: Copy media assets
echo "4. Copying media assets..."
cp media/*.png site/media/
echo "   ✓ Media assets copied"
echo ""

# Step 5: Convert markdown documentation to HTML
echo "5. Converting markdown documentation to HTML..."
python3 site/convert_docs.py
echo "   ✓ Documentation converted"
echo ""

echo "==============================="
echo "✓ Website built successfully!"
echo ""
echo "Site location: $(pwd)/site/"
echo ""
echo "To serve locally:"
echo "  cd site && python3 -m http.server 8000"
echo "  Then visit: http://localhost:8000"
echo ""
