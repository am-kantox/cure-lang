# Cure Programming Language - Static Website

This directory contains the static website for the Cure programming language.

## Structure

```
site/
├── index.html              # Main landing page
├── docs.html               # Documentation index
├── css/
│   └── style.css          # Main stylesheet
├── media/                  # Images and assets
│   ├── logo-128x128.png   # Logo/favicon
│   ├── ad.png             # Marketing banner
│   └── logo-bottle.png    # Hero image
├── docs/                   # Converted documentation (HTML)
│   ├── language-spec.html
│   ├── type-system.html
│   ├── fsm-usage.html
│   └── ...
└── api/                    # Ex_doc generated API reference
    ├── index.html
    ├── cure_*.html
    └── ...
```

## Building the Site

### Complete Build (Recommended)

```bash
# From project root
./build_site.sh
```

This does a **complete build**:
1. Generate API documentation with `rebar3 ex_doc`
2. Create site directory structure
3. Copy API documentation to site
4. Copy media assets
5. Convert all Markdown documentation to HTML
6. Apply `class="language-cure"` to all Cure code blocks
7. Include highlight.js and cure-language.js
8. Update index.html footer with all doc links
9. Verify build with detailed statistics

### Quick Docs-Only Rebuild

When you only update documentation (no code changes):

```bash
cd site
./build_site.sh
```

This **only rebuilds documentation** (faster):
- Skips API generation
- Skips asset copying
- Just converts docs and updates footer

### Manual Steps

1. **Generate API documentation:**
   ```bash
   cd ..
   rebar3 ex_doc
   ```

2. **Convert documentation:**
   ```bash
   cd site
   python3 convert_docs.py      # Converts MD to HTML
   python3 update_footer.py     # Updates index.html footer
   ```

### Build Features

- ✅ All HTML files include highlight.js (v11.11.1)
- ✅ Custom Cure language syntax highlighting
- ✅ Proper `<code class="language-cure">` markup for all Cure code
- ✅ Responsive cure-theme.css included
- ✅ Footer links to all 35+ documentation pages
- ✅ Auto-detection of Cure code patterns in unmarked blocks

## Deploying

The site is pure static HTML/CSS with no dependencies. Deploy to any static hosting:

### GitHub Pages
```bash
# From site directory
git init
git add .
git commit -m "Initial site"
git branch -M gh-pages
git remote add origin <your-repo>
git push -u origin gh-pages
```

### Netlify/Vercel
Simply point to the `site/` directory as the publish directory.

### Apache/Nginx
Copy the entire `site/` directory to your web root.

## Local Development

Serve locally with any HTTP server:

```bash
# Python
python3 -m http.server 8000

# Node.js
npx http-server

# PHP
php -S localhost:8000
```

Then visit http://localhost:8000

## Updating Documentation

When you update markdown files in `docs/`:

```bash
cd site
./build_site.sh  # Full rebuild
# or
python3 convert_docs.py && python3 update_footer.py  # Just docs
```

When you update the Erlang implementation:

```bash
rebar3 ex_doc
cp -r docs/_build/* site/api/
```

## Scripts

- **build_site.sh** - Complete site build with verification
- **convert_docs.py** - Convert Markdown to HTML with syntax highlighting
- **update_footer.py** - Update index.html footer with all doc links

All scripts automatically:
- Mark Cure code blocks with `language-cure` class
- Include highlight.js and cure-language.js
- Generate responsive HTML from Markdown
- Create proper footer links

## Features

- ✅ Responsive design
- ✅ Modern CSS with gradients and animations
- ✅ Clean navigation structure
- ✅ Comprehensive documentation coverage
- ✅ API reference integration
- ✅ SEO-friendly with meta tags
- ✅ Fast loading (no external dependencies)

## Customization

### Colors
Edit CSS variables in `css/style.css`:
```css
:root {
  --cure-primary: #6366f1;
  --cure-secondary: #8b5cf6;
  --cure-accent: #ec4899;
  ...
}
```

### Content
- Main page: Edit `index.html`
- Documentation index: Edit `docs.html`
- Individual docs: Update markdown in `../docs/` and regenerate

### Images
Replace files in `media/` directory while keeping the same names.
