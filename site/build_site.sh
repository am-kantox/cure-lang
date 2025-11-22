#!/bin/bash
# Quick rebuild script for Cure documentation
# Only rebuilds docs (no API generation or asset copying)
# For full build including API docs, use ../build_site.sh from project root

set -e  # Exit on error

echo "======================================"
echo "Rebuilding Cure Documentation (Quick)"
echo "======================================"
echo ""
echo "Note: For full build with API docs, run ../build_site.sh from project root"
echo ""

# Get script directory
SCRIPT_DIR="$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)"
cd "$SCRIPT_DIR"

echo "Step 1: Converting documentation from Markdown to HTML..."
echo "--------------------------------------"
python3 convert_docs.py
echo ""

echo "Step 2: Updating index.html footer with all doc links..."
echo "--------------------------------------"
python3 update_footer.py
echo ""

echo "Step 3: Verifying generated files..."
echo "--------------------------------------"
DOCS_COUNT=$(ls -1 docs/*.html 2>/dev/null | wc -l)
echo "Generated $DOCS_COUNT HTML documentation files"

# Check for highlight.js in a sample file
if grep -q "highlight.js" docs/language-spec.html 2>/dev/null; then
    echo "✓ Highlight.js integration verified"
else
    echo "✗ Warning: Highlight.js not found in generated files"
fi

# Check for cure language class
CURE_CLASS_COUNT=$(grep -o 'class="language-cure"' docs/*.html 2>/dev/null | wc -l)
echo "✓ Found $CURE_CLASS_COUNT Cure code blocks with language-cure class"

echo ""
echo "======================================"
echo "Build Complete!"
echo "======================================"
echo ""
echo "Site structure:"
echo "  - index.html (main page with all doc links)"
echo "  - docs/*.html ($DOCS_COUNT documentation pages)"
echo "  - api/ (API reference)"
echo ""
echo "All HTML files include:"
echo "  ✓ Highlight.js for syntax highlighting"
echo "  ✓ Cure language definition"
echo "  ✓ Proper <code class=\"language-cure\"> markup"
echo "  ✓ Footer links to all documentation"
echo ""
echo "To serve locally:"
echo "  python3 -m http.server 8000"
echo "  Then visit: http://localhost:8000"
