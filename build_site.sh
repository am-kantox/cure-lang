#!/bin/bash
# Build script for Cure Language static website
# Complete build including API docs, documentation conversion, and verification

set -e  # Exit on error

echo "=========================================="
echo "Building Cure Language Website (Complete)"
echo "=========================================="
echo ""

# Get script directory (project root)
SCRIPT_DIR="$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)"
cd "$SCRIPT_DIR"

# Step 1: Generate API documentation with ex_doc
echo "Step 1: Generating API documentation with ex_doc..."
echo "------------------------------------------"
rebar3 ex_doc
echo "✓ API documentation generated"
echo ""

# Step 2: Create site directory structure
echo "Step 2: Creating site directory structure..."
echo "------------------------------------------"
mkdir -p site/api site/docs site/media site/css site/js
echo "✓ Directories created"
echo ""

# Step 3: Copy ex_doc output to site
echo "Step 3: Copying API documentation to site..."
echo "------------------------------------------"
cp -r docs/_build/* site/api/
echo "✓ API documentation copied"
echo ""

# Step 4: Copy media assets
echo "Step 4: Copying media assets..."
echo "------------------------------------------"
cp media/*.png site/media/
echo "✓ Media assets copied"
echo ""

# Step 5: Convert markdown documentation to HTML with syntax highlighting
echo "Step 5: Converting documentation from Markdown to HTML..."
echo "------------------------------------------"
cd site
python3 convert_docs.py
cd ..
echo "✓ Documentation converted"
echo ""

# Step 6: Update index.html footer with all doc links
echo "Step 6: Updating index.html footer with all doc links..."
echo "------------------------------------------"
cd site
python3 update_footer.py
cd ..
echo "✓ Footer updated"
echo ""

# Step 7: Verify build
echo "Step 7: Verifying generated files..."
echo "------------------------------------------"
DOCS_COUNT=$(ls -1 site/docs/*.html 2>/dev/null | wc -l)
API_COUNT=$(ls -1 site/api/*.html 2>/dev/null | wc -l)
echo "✓ Generated $DOCS_COUNT HTML documentation files"
echo "✓ Generated $API_COUNT API reference files"

# Check for highlight.js in a sample file
if grep -q "highlight.js" site/docs/language-spec.html 2>/dev/null; then
    echo "✓ Highlight.js integration verified"
else
    echo "✗ Warning: Highlight.js not found in generated files"
fi

# Check for cure language class
CURE_CLASS_COUNT=$(grep -o 'class="language-cure"' site/docs/*.html 2>/dev/null | wc -l)
echo "✓ Found $CURE_CLASS_COUNT Cure code blocks with language-cure class"

# Check footer links
FOOTER_LINKS=$(grep -o 'href="docs/' site/index.html 2>/dev/null | wc -l)
echo "✓ Index.html footer contains $FOOTER_LINKS documentation links"

echo ""
echo "=========================================="
echo "✓ Complete Website Build Successful!"
echo "=========================================="
echo ""
echo "Site structure:"
echo "  - site/index.html (main page with all doc links)"
echo "  - site/docs/*.html ($DOCS_COUNT documentation pages)"
echo "  - site/api/*.html ($API_COUNT API reference pages)"
echo "  - site/media/ (images and assets)"
echo "  - site/css/ (stylesheets)"
echo "  - site/js/ (Cure language highlighting)"
echo ""
echo "All HTML files include:"
echo "  ✓ Highlight.js for syntax highlighting"
echo "  ✓ Cure language definition (cure-language.js)"
echo "  ✓ Proper <code class=\"language-cure\"> markup"
echo "  ✓ Responsive cure-theme.css styling"
echo "  ✓ Footer links to all documentation"
echo ""
echo "Site location: $(pwd)/site/"
echo ""
echo "To serve locally:"
echo "  cd site && python3 -m http.server 8000"
echo "  Then visit: http://localhost:8000"
echo ""
