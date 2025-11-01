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
│   ├── pill-512x512.png   # Decorative element
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

1. **Generate API documentation:**
   ```bash
   cd ..
   rebar3 ex_doc
   ```

2. **Copy assets and convert docs:**
   ```bash
   # From the project root:
   ./build_site.sh
   ```
   
   Or manually:
   ```bash
   mkdir -p site/api site/docs site/media site/css
   cp -r docs/_build/* site/api/
   cp media/*.png site/media/
   python3 site/convert_docs.py
   ```

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
python3 site/convert_docs.py
```

When you update the Erlang implementation:

```bash
rebar3 ex_doc
cp -r docs/_build/* site/api/
```

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
