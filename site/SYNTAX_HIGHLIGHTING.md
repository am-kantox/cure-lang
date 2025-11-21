# Cure Syntax Highlighting for highlight.js

This document describes the syntax highlighting implementation for Cure code examples on the website.

## Overview

The Cure website now includes comprehensive syntax highlighting using [highlight.js](https://highlightjs.org/) with a custom language definition and theme based on the `vicure` Vim syntax highlighting.

## Files

### Language Definition
- **`site/js/cure-language.js`** - Custom highlight.js language definition for Cure
  - Defines keywords, operators, literals, and syntax patterns
  - Handles comments, strings, atoms, numbers, and types
  - Recognizes FSM constructs, function definitions, and module declarations
  - Supports string interpolation with `#{...}` syntax

### Theme
- **`site/css/cure-theme.css`** - Custom highlight.js theme based on vicure
  - Color scheme optimized for readability
  - Distinct colors for different language constructs:
    - **Purple** (#7c3aed) - Keywords, operators
    - **Red** (#dc2626) - Built-in constructors, numbers
    - **Cyan** (#0891b2) - Functions, atoms/symbols
    - **Blue** (#0284c7) - Type names
    - **Green** (#059669) - Strings
    - **Gray** (#6b7280) - Comments
    - **Amber** (#b45309) - String interpolation

## Integration

### Main Pages
The following pages have been updated with highlight.js integration:
- `site/index.html` - Homepage with code examples
- `site/docs.html` - Documentation index page
- All 70+ documentation pages in `site/docs/*.html`

### HTML Structure
Each page includes:
```html
<!-- In <head> -->
<link rel="stylesheet" href="css/cure-theme.css">

<!-- Before </body> -->
<script src="https://cdnjs.cloudflare.com/ajax/libs/highlight.js/11.11.1/highlight.min.js"></script>
<script src="js/cure-language.js"></script>
<script>
    hljs.highlightAll();
</script>
```

### Code Blocks
To enable syntax highlighting, use the `language-cure` class:
```html
<pre><code class="language-cure">
# Your Cure code here
def example(): Int = 42
</code></pre>
```

## Testing

A test page has been created to verify the syntax highlighting:
- **`site/test-highlighting.html`** - Comprehensive test cases

Open this file in a browser to verify:
- Keywords are highlighted correctly
- FSM syntax is properly colored
- Comments, strings, atoms, and numbers are distinct
- Type names and function definitions are recognizable
- Pattern matching and guards are highlighted

## Language Features Covered

The syntax highlighting supports all major Cure language features:

### Keywords
- Control flow: `def`, `end`, `do`, `match`, `when`, `let`, `in`
- Modules: `module`, `import`, `export`
- FSMs: `fsm`, `state`, `states`, `initial`, `event`, `timeout`, `transition`
- Processes: `process`, `receive`, `send`, `spawn`
- Types: `record`, `type`, `typeclass`, `trait`, `instance`, `impl`, `class`
- Verification: `property`, `invariant`, `eventually`, `always`, `until`

### Built-in Types
- `Ok`, `Error`, `Some`, `None`, `Unit`
- `Nat`, `Atom`, `Zero`, `Succ`, `Pred`, `Self`

### Literals
- Booleans: `true`, `false`
- Numbers: integers and floats
- Strings with interpolation: `"text #{expr}"`
- Atoms: `:atom` and `'quoted atom'`

### Operators
- Arithmetic: `+`, `-`, `*`, `/`, `%`
- Comparison: `<`, `>`, `<=`, `>=`, `==`, `!=`, `<>`
- Logical: `and`, `or`, `not`
- Functional: `=>`, `->`, `-->`, `::`, `|>`
- Composition: `++`, `--`
- Functor/Applicative: `<$`, `$>`, `<*>`, `*>`, `<*`
- Monad: `>>=`, `>>`

## Maintenance

### Updating the Language Definition
To add new keywords or change syntax patterns:
1. Edit `site/js/cure-language.js`
2. Update the `keywords` object for new keywords
3. Add new patterns to the `contains` array for new syntax
4. Test changes in `site/test-highlighting.html`

### Updating the Theme
To modify colors or styling:
1. Edit `site/css/cure-theme.css`
2. Adjust color values using Tailwind color palette references
3. Test across multiple examples to ensure readability

### Adding to New Pages
For new HTML pages in the site:
1. Add CSS link: `<link rel="stylesheet" href="../css/cure-theme.css">`
2. Add scripts before `</body>`:
   ```html
   <script src="https://cdnjs.cloudflare.com/ajax/libs/highlight.js/11.11.1/highlight.min.js"></script>
   <script src="../js/cure-language.js"></script>
   <script>hljs.highlightAll();</script>
   ```
3. Use `class="language-cure"` on code blocks

## References

- [highlight.js Documentation](https://highlightjs.readthedocs.io/)
- [highlight.js Language Definition Guide](https://highlightjs.readthedocs.io/en/latest/language-guide.html)
- [highlight.js Theme Guide](https://highlightjs.readthedocs.io/en/latest/theme-guide.html)
- Vicure Vim syntax: `vicure/syntax/cure.vim`

## Browser Compatibility

The syntax highlighting works on all modern browsers that support:
- ES5 JavaScript
- CSS3
- Modern DOM APIs

Tested on:
- Chrome/Edge (Chromium)
- Firefox
- Safari
- Opera

## Performance

- Language definition: ~7KB
- Theme CSS: ~4.3KB
- highlight.js core: Loaded from CDN (cached)
- Minimal performance impact on page load
- Syntax highlighting is applied on page load automatically
