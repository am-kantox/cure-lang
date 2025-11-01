#!/usr/bin/env python3
"""
Convert Markdown documentation files to HTML for the Cure website
"""

import os
import re
from pathlib import Path

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

    <!-- Pill Decoration -->
    <img src="../media/pill-512x512.png" alt="" class="pill-decoration">

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
    """Convert basic Markdown to HTML"""
    html = markdown_text
    
    # Code blocks
    html = re.sub(r'```(\w+)?\n(.*?)```', r'<pre><code>\2</code></pre>', html, flags=re.DOTALL)
    
    # Headers
    html = re.sub(r'^######\s+(.*?)$', r'<h6>\1</h6>', html, flags=re.MULTILINE)
    html = re.sub(r'^#####\s+(.*?)$', r'<h5>\1</h5>', html, flags=re.MULTILINE)
    html = re.sub(r'^####\s+(.*?)$', r'<h4>\1</h4>', html, flags=re.MULTILINE)
    html = re.sub(r'^###\s+(.*?)$', r'<h3>\1</h3>', html, flags=re.MULTILINE)
    html = re.sub(r'^##\s+(.*?)$', r'<h2>\1</h2>', html, flags=re.MULTILINE)
    html = re.sub(r'^#\s+(.*?)$', r'<h1>\1</h1>', html, flags=re.MULTILINE)
    
    # Bold and italic
    html = re.sub(r'\*\*\*(.+?)\*\*\*', r'<strong><em>\1</em></strong>', html)
    html = re.sub(r'\*\*(.+?)\*\*', r'<strong>\1</strong>', html)
    html = re.sub(r'\*(.+?)\*', r'<em>\1</em>', html)
    html = re.sub(r'___(.+?)___', r'<strong><em>\1</em></strong>', html)
    html = re.sub(r'__(.+?)__', r'<strong>\1</strong>', html)
    html = re.sub(r'_(.+?)_', r'<em>\1</em>', html)
    
    # Inline code
    html = re.sub(r'`([^`]+)`', r'<code>\1</code>', html)
    
    # Links
    html = re.sub(r'\[([^\]]+)\]\(([^\)]+)\)', r'<a href="\2">\1</a>', html)
    
    # Unordered lists
    lines = html.split('\n')
    in_ul = False
    result = []
    for line in lines:
        if re.match(r'^\s*[-*+]\s+', line):
            if not in_ul:
                result.append('<ul>')
                in_ul = True
            item = re.sub(r'^\s*[-*+]\s+', '', line)
            result.append(f'<li>{item}</li>')
        else:
            if in_ul:
                result.append('</ul>')
                in_ul = False
            result.append(line)
    if in_ul:
        result.append('</ul>')
    html = '\n'.join(result)
    
    # Ordered lists
    lines = html.split('\n')
    in_ol = False
    result = []
    for line in lines:
        if re.match(r'^\s*\d+\.\s+', line):
            if not in_ol:
                result.append('<ol>')
                in_ol = True
            item = re.sub(r'^\s*\d+\.\s+', '', line)
            result.append(f'<li>{item}</li>')
        else:
            if in_ol:
                result.append('</ol>')
                in_ol = False
            result.append(line)
    if in_ol:
        result.append('</ol>')
    html = '\n'.join(result)
    
    # Paragraphs
    lines = html.split('\n')
    result = []
    for line in lines:
        if line.strip() and not line.strip().startswith('<'):
            result.append(f'<p>{line}</p>')
        else:
            result.append(line)
    
    return '\n'.join(result)

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
