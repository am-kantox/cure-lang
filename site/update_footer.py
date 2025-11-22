#!/usr/bin/env python3
"""
Update index.html footer to include links to all generated documentation
"""

import os
import re
from pathlib import Path

def get_doc_files():
    """Get all HTML files from docs directory with their titles"""
    docs_dir = Path(__file__).parent / 'docs'
    doc_files = []
    
    for html_file in sorted(docs_dir.glob('*.html')):
        # Read file to extract title
        with open(html_file, 'r', encoding='utf-8') as f:
            content = f.read()
            title_match = re.search(r'<title>([^<]+) - Cure Documentation</title>', content)
            if title_match:
                title = title_match.group(1)
            else:
                title = html_file.stem.replace('-', ' ').title()
        
        doc_files.append((html_file.name, title))
    
    return sorted(doc_files, key=lambda x: x[1])

def update_index_footer():
    """Update index.html footer with all doc links"""
    index_file = Path(__file__).parent / 'index.html'
    
    # Read current index.html
    with open(index_file, 'r', encoding='utf-8') as f:
        content = f.read()
    
    # Get all documentation files
    doc_files = get_doc_files()
    
    # Split into groups of ~12 for footer columns
    chunk_size = 12
    chunks = [doc_files[i:i + chunk_size] for i in range(0, len(doc_files), chunk_size)]
    
    # Generate footer HTML for each column
    footer_sections = []
    
    # First column: Key docs
    footer_sections.append('''            <div class="footer-section">
                <h4>Documentation</h4>
                <ul>
                    <li><a href="docs.html">Getting Started</a></li>
                    <li><a href="docs/language-spec.html">Language Specification</a></li>
                    <li><a href="docs/type-system.html">Type System</a></li>
                    <li><a href="docs/fsm-usage.html">FSM Guide</a></li>
                </ul>
            </div>''')
    
    # Second column: Reference
    footer_sections.append('''            <div class="footer-section">
                <h4>Reference</h4>
                <ul>
                    <li><a href="api/index.html">API Reference</a></li>
                    <li><a href="docs/std-summary.html">Standard Library</a></li>
                    <li><a href="docs/feature-reference.html">Feature Reference</a></li>
                    <li><a href="docs/cli-usage.html">CLI Usage</a></li>
                </ul>
            </div>''')
    
    # Third column: All documentation (first chunk)
    if chunks:
        links_html = '\n'.join(
            f'                    <li><a href="docs/{fname}">{title[:35]}</a></li>'
            for fname, title in chunks[0][:10]
        )
        footer_sections.append(f'''            <div class="footer-section">
                <h4>All Documentation</h4>
                <ul>
{links_html}
                </ul>
            </div>''')
    
    # Combine all sections
    new_footer_content = '\n\n'.join(footer_sections)
    
    # Replace footer content
    # Find the footer section
    footer_pattern = r'(<footer class="site-footer">.*?<div class="footer-content">)(.*?)(</div>\s*<div class="footer-bottom">)'
    
    def replace_footer(match):
        return match.group(1) + '\n' + new_footer_content + '\n        ' + match.group(3)
    
    new_content = re.sub(footer_pattern, replace_footer, content, flags=re.DOTALL)
    
    # Write updated content
    with open(index_file, 'w', encoding='utf-8') as f:
        f.write(new_content)
    
    print(f"Updated index.html footer with {len(doc_files)} documentation links")

if __name__ == '__main__':
    update_index_footer()
