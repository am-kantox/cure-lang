#!/usr/bin/env python3
"""
Generate individual HTML pages for each Cure example file.
"""

import os
import html
from pathlib import Path

# Template for individual example pages
EXAMPLE_TEMPLATE = '''<!DOCTYPE html>
<html lang="en">
<head>
    <meta charset="UTF-8">
    <meta name="viewport" content="width=device-width, initial-scale=1.0">
    <title>{title} - Cure Example</title>
    <meta name="description" content="{description}">
    <link rel="icon" type="image/png" href="../media/logo-128x128.png">
    <link rel="stylesheet" href="../css/style.css">
    <link rel="stylesheet" href="../css/cure-theme.css">
</head>
<body>
    <!-- Header -->
    <header class="site-header">
        <div class="nav-container">
            <div class="logo-section">
                <img src="../media/logo-128x128.png" alt="Cure Logo" class="logo">
                <div>
                    <h1 class="site-title">Cure</h1>
                    <p class="site-tagline">Verification-First Programming</p>
                </div>
            </div>
            <nav class="main-nav">
                <ul>
                    <li><a href="../index.html">Home</a></li>
                    <li><a href="../examples.html">Examples</a></li>
                    <li><a href="../docs.html">Documentation</a></li>
                    <li><a href="https://cure-lang.org/api/index.html">API Reference</a></li>
                </ul>
            </nav>
        </div>
    </header>

    <!-- Example Content -->
    <div class="container">
        <div class="example-page">
            <a href="../examples.html" class="back-link">← Back to Examples</a>
            
            <h1>{title}</h1>
            <p>{description}</p>

            <h2>Source Code</h2>
            <pre><code class="language-cure">{code}</code></pre>
        </div>
    </div>

    <!-- Footer -->
    <footer class="site-footer">
        <div class="footer-content">
            <div class="footer-section">
                <h4>Documentation</h4>
                <ul>
                    <li><a href="../docs.html">Getting Started</a></li>
                    <li><a href="https://cure-lang.org/api/index.html">API Reference</a></li>
                </ul>
            </div>

            <div class="footer-section">
                <h4>Examples</h4>
                <ul>
                    <li><a href="../examples.html">Browse Examples</a></li>
                </ul>
            </div>

            <div class="footer-section">
                <h4>Resources</h4>
                <ul>
                    <li><a href="https://github.com/cure-lang/cure">GitHub</a></li>
                </ul>
            </div>
        </div>

        <div class="footer-bottom">
            <p>&copy; 2025 Cure Programming Language</p>
        </div>
    </footer>

    <!-- Syntax Highlighting -->
    <script src="https://cdnjs.cloudflare.com/ajax/libs/highlight.js/11.11.1/highlight.min.js"></script>
    <script src="../js/cure-language.js"></script>
    <script>
        hljs.highlightAll();
    </script>
</body>
</html>
'''

def extract_description(content):
    """Extract description from first comment lines."""
    lines = content.split('\n')
    description_lines = []
    for line in lines:
        line = line.strip()
        if line.startswith('#') and not line.startswith('##'):
            # Remove leading # and whitespace
            desc = line.lstrip('#').strip()
            if desc and not desc.startswith('Example'):
                description_lines.append(desc)
        elif line and not line.startswith('#'):
            break
    
    if description_lines:
        return ' '.join(description_lines)
    return "Cure language example demonstrating various features"

def extract_title(filename):
    """Extract a readable title from filename."""
    # Remove .cure extension
    name = filename.replace('.cure', '')
    # Replace underscores with spaces
    name = name.replace('_', ' ')
    # Capitalize
    return name.title()

def generate_example_page(cure_file_path, output_dir):
    """Generate HTML page for a single Cure example file."""
    with open(cure_file_path, 'r', encoding='utf-8') as f:
        content = f.read()
    
    filename = os.path.basename(cure_file_path)
    title = extract_title(filename)
    description = extract_description(content)
    
    # HTML escape the code
    code_escaped = html.escape(content)
    
    # Generate HTML
    html_content = EXAMPLE_TEMPLATE.format(
        title=html.escape(title),
        description=html.escape(description),
        code=code_escaped
    )
    
    # Write output file
    output_filename = filename.replace('.cure', '.html')
    output_path = os.path.join(output_dir, output_filename)
    
    with open(output_path, 'w', encoding='utf-8') as f:
        f.write(html_content)
    
    print(f"Generated: {output_filename}")

def main():
    # Paths
    script_dir = Path(__file__).parent
    project_root = script_dir.parent
    examples_source_dir = project_root / 'examples'
    examples_output_dir = script_dir / 'examples'
    
    # Ensure output directory exists
    examples_output_dir.mkdir(exist_ok=True)
    
    # Find all .cure files in examples directory
    cure_files = sorted(examples_source_dir.glob('*.cure'))
    
    print(f"Found {len(cure_files)} Cure example files")
    print(f"Generating HTML pages...\n")
    
    for cure_file in cure_files:
        generate_example_page(cure_file, examples_output_dir)
    
    print(f"\nGenerated {len(cure_files)} example pages in {examples_output_dir}")

if __name__ == '__main__':
    main()
