#!/usr/bin/env python3
"""
Convert Markdown documentation files to HTML for the Cure website
"""

import os
import re
from pathlib import Path
import markdown
from markdown.extensions.codehilite import CodeHiliteExtension
from markdown.extensions.fenced_code import FencedCodeExtension
from markdown.extensions.tables import TableExtension
from markdown.extensions.toc import TocExtension

# HTML template for documentation pages
DOC_TEMPLATE = """<!DOCTYPE html>
<html lang="en">
<head>
    <meta charset="UTF-8">
    <meta name="viewport" content="width=device-width, initial-scale=1.0">
    <title>{title} - Cure Documentation</title>
    <meta name="description" content="{description}">
    <link rel="icon" type="image/png" href="../media/logo-128x128.png">
    <link rel="stylesheet" href="../css/style.css">
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
                    <li><a href="../docs.html">Documentation</a></li>
                    <li><a href="../api/index.html">API Reference</a></li>
                </ul>
            </nav>
        </div>
    </header>

    <!-- Main Content -->
    <div class="doc-page">
        <div class="doc-nav">
            <a href="../docs.html">← Back to Documentation</a>
        </div>
        
        {content}
    </div>

    <!-- Footer -->
    <footer class="site-footer">
        <div class="footer-content">
            <div class="footer-section">
                <h4>Documentation</h4>
                <ul>
                    <li><a href="../docs.html">Getting Started</a></li>
                    <li><a href="language-spec.html">Language Specification</a></li>
                    <li><a href="type-system.html">Type System</a></li>
                    <li><a href="fsm-usage.html">FSM Guide</a></li>
                </ul>
            </div>

            <div class="footer-section">
                <h4>Reference</h4>
                <ul>
                    <li><a href="../api/index.html">API Reference</a></li>
                    <li><a href="std-summary.html">Standard Library</a></li>
                    <li><a href="feature-reference.html">Feature Reference</a></li>
                    <li><a href="cli-usage.html">CLI Usage</a></li>
                </ul>
            </div>

            <div class="footer-section">
                <h4>Resources</h4>
                <ul>
                    <li><a href="editor-setup.html">Editor Setup</a></li>
                    <li><a href="project-overview.html">Project Overview</a></li>
                    <li><a href="cure-ultimate-description.html">Ultimate Guide</a></li>
                </ul>
            </div>
        </div>

        <div class="footer-bottom">
            <p>&copy; 2025 Cure Programming Language. Verification-first programming for the BEAM.</p>
        </div>
    </footer>
</body>
</html>
"""

def markdown_to_html(markdown_text):
    """Convert Markdown to HTML using python-markdown"""
    md = markdown.Markdown(
        extensions=[
            'extra',  # Includes tables, fenced code, etc.
            'codehilite',  # Syntax highlighting for code blocks
            'toc',  # Table of contents
            'nl2br',  # Newline to <br>
            'sane_lists',  # Better list handling
        ],
        extension_configs={
            'codehilite': {
                'linenums': False,
                'guess_lang': True,
            },
        }
    )
    return md.convert(markdown_text)

def slugify(text):
    """Convert text to URL-friendly slug"""
    text = text.lower()
    text = re.sub(r'[^a-z0-9]+', '-', text)
    text = text.strip('-')
    return text

def convert_doc(markdown_file, output_dir):
    """Convert a single markdown file to HTML"""
    with open(markdown_file, 'r', encoding='utf-8') as f:
        markdown_content = f.read()
    
    # Extract title from first H1
    title_match = re.search(r'^#\s+(.+)$', markdown_content, re.MULTILINE)
    title = title_match.group(1) if title_match else Path(markdown_file).stem
    
    # Extract description from first paragraph after title
    desc_match = re.search(r'^#.+?\n\n(.+?)(?:\n\n|$)', markdown_content, re.DOTALL)
    description = desc_match.group(1).strip()[:150] if desc_match else f"Cure documentation: {title}"
    description = re.sub(r'[*_`#]', '', description)
    
    # Convert markdown to HTML
    html_content = markdown_to_html(markdown_content)
    
    # Generate filename
    filename = slugify(Path(markdown_file).stem) + '.html'
    
    # Fill template
    html = DOC_TEMPLATE.format(
        title=title,
        description=description,
        content=html_content
    )
    
    # Write output
    output_file = os.path.join(output_dir, filename)
    with open(output_file, 'w', encoding='utf-8') as f:
        f.write(html)
    
    print(f"Converted: {markdown_file} -> {output_file}")
    return filename

def main():
    """Main conversion function"""
    # Directories
    docs_source = Path(__file__).parent.parent / 'docs'
    docs_output = Path(__file__).parent / 'docs'
    
    # Create output directory
    docs_output.mkdir(exist_ok=True)
    
    # Find all markdown files
    markdown_files = list(docs_source.glob('*.md'))
    
    print(f"Found {len(markdown_files)} markdown files")
    print(f"Converting from: {docs_source}")
    print(f"Converting to: {docs_output}")
    print("-" * 60)
    
    # Convert each file
    converted = []
    for md_file in sorted(markdown_files):
        try:
            html_file = convert_doc(md_file, docs_output)
            converted.append(html_file)
        except Exception as e:
            print(f"Error converting {md_file}: {e}")
    
    print("-" * 60)
    print(f"Successfully converted {len(converted)} files")

if __name__ == '__main__':
    main()
