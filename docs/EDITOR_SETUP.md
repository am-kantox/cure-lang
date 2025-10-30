# Editor Setup for Cure String Literals

This guide helps you configure your editor to easily input Unicode curly quotes (`'` and `'`) for Cure charlist literals.

## Quick Reference

Cure uses different quote characters for different purposes:

| Character | Unicode | Usage | Example |
|-----------|---------|-------|---------|
| `"` | U+0022 | String literals | `"hello"` |
| `'` | U+2018 | Charlist start | `'hello'` |
| `'` | U+2019 | Charlist end | `'hello'` |
| `'` | U+0027 | Atoms | `'my_atom'` |

## Operating System Methods

### macOS

**System-wide Keyboard Shortcuts:**
- Left curly quote `'`: <kbd>Option</kbd> + <kbd>]</kbd>
- Right curly quote `'`: <kbd>Option</kbd> + <kbd>Shift</kbd> + <kbd>]</kbd>

**Text Substitution (Automatic):**
1. Open System Preferences → Keyboard → Text
2. Add entries:
   - Replace: `''` → With: `''` (two single curly quotes)
   - Or configure your preferred trigger

### Linux

**Compose Key Method:**
1. Set a compose key in your keyboard settings
2. Use sequences:
   - `'` (left): <kbd>Compose</kbd> <kbd><</kbd> <kbd>'</kbd>
   - `'` (right): <kbd>Compose</kbd> <kbd>></kbd> <kbd>'</kbd>

**XKB Custom Layout:**
Create a custom keyboard layout in `~/.config/xkb/symbols/custom`:

```
partial alphanumeric_keys
xkb_symbols "cure_quotes" {
    include "us(basic)"
    key <AC10> { [ apostrophe, quotedbl, U2018, U2019 ] };
};
```

Apply with: `setxkbmap -option "custom:cure_quotes"`

### Windows

**AutoHotkey Script:**

Save as `cure_quotes.ahk`:

```autohotkey
; Cure Charlist Quotes
; Press Alt+[ for left curly quote
; Press Alt+] for right curly quote

![ ::SendInput {U+2018}  ; Alt+[
!] ::SendInput {U+2019}  ; Alt+]
```

Run the script on startup.

## Editor-Specific Configurations

### VS Code

**Method 1: Custom Keybindings**

Add to `keybindings.json`:

```json
[
  {
    "key": "alt+[",
    "command": "type",
    "args": { "text": "'" },
    "when": "editorTextFocus && editorLangId == 'cure'"
  },
  {
    "key": "alt+]",
    "command": "type",
    "args": { "text": "'" },
    "when": "editorTextFocus && editorLangId == 'cure'"
  }
]
```

**Method 2: Snippets**

Add to Cure language snippets:

```json
{
  "Charlist Literal": {
    "prefix": "cl",
    "body": "'$1'",
    "description": "Insert charlist literal with curly quotes"
  }
}
```

**Method 3: Text Expander Extension**

Install an extension like "Text Expander" and configure:
- `'c` → `'` (left curly quote)
- `c'` → `'` (right curly quote)

### Vim/Neovim

**Method 1: Insert Mode Mappings**

Add to `.vimrc` or `init.vim`:

```vim
" Cure charlist quotes
inoremap <A-[> '
inoremap <A-]> '

" Or use digraphs (Ctrl+K followed by code)
" '<' for U+2018, '>' for U+2019
```

**Method 2: Abbreviations**

```vim
" Auto-expand ''c to charlist quotes
autocmd FileType cure inoreabbrev ''c ''
```

**Method 3: Custom Digraphs**

```vim
digraphs c< 8216  " '<
digraphs c> 8217  " '>
```

Then use: <kbd>Ctrl+K</kbd> <kbd>c</kbd> <kbd><</kbd> for `'`

### Emacs

**Method 1: Custom Keybindings**

Add to `.emacs` or `init.el`:

```elisp
;; Cure charlist quotes
(define-key cure-mode-map (kbd "M-[") 
  (lambda () (interactive) (insert "'")))
(define-key cure-mode-map (kbd "M-]") 
  (lambda () (interactive) (insert "'")))
```

**Method 2: Abbrev Mode**

```elisp
(define-abbrev cure-mode-abbrev-table "'c" "''")
```

**Method 3: YASnippet**

Create `cure-mode/charlist.yasnippet`:

```
# -*- mode: snippet -*-
# name: charlist
# key: cl
# --
'$1'$0
```

### Sublime Text

**Method 1: Key Bindings**

Add to `Preferences → Key Bindings`:

```json
[
  {
    "keys": ["alt+["],
    "command": "insert_snippet",
    "args": {"contents": "'"}
  },
  {
    "keys": ["alt+]"],
    "command": "insert_snippet",
    "args": {"contents": "'"}
  }
]
```

**Method 2: Snippets**

Create `cure-charlist.sublime-snippet`:

```xml
<snippet>
    <content><![CDATA['$1']]></content>
    <tabTrigger>cl</tabTrigger>
    <scope>source.cure</scope>
    <description>Charlist Literal</description>
</snippet>
```

### IntelliJ IDEA / WebStorm

**Live Templates:**

1. Go to Settings → Editor → Live Templates
2. Create new template group "Cure"
3. Add template:
   - Abbreviation: `cl`
   - Template text: `'$END$'`
   - Applicable in: Cure files

**Keymap:**

1. Settings → Keymap
2. Search for "Insert Live Template"
3. Add shortcut: <kbd>Alt</kbd>+<kbd>[</kbd> for `'`, <kbd>Alt</kbd>+<kbd>]</kbd> for `'`

### Atom

**Snippets:**

Add to `snippets.cson`:

```cson
'.source.cure':
  'Charlist Literal':
    'prefix': 'cl'
    'body': "'$1'"
```

**Keybindings:**

Add to `keymap.cson`:

```cson
'atom-text-editor[data-grammar="source cure"]':
  'alt-[': 'snippets:insert-text-left-curly-quote'
  'alt-]': 'snippets:insert-text-right-curly-quote'
```

## Language Server / LSP Support

If you're using a Cure language server, it can provide:

**Auto-Closing Pairs:**
- Typing `'` automatically inserts `'`
- Cursor positioned between quotes

**Snippet Completion:**
- Type `char` or `cl` → charlist literal template

**Diagnostics:**
- Warns when using ASCII `'` for charlists
- Suggests correction to Unicode quotes

## Copy-Paste Method

If configuring your editor is too complex, you can:

1. Create a file `snippets.txt` with commonly-used patterns:
   ```
   '' (empty charlist)
   'hello'
   'world'
   ```

2. Copy-paste as needed

3. Or use a clipboard manager with pre-configured snippets

## Testing Your Setup

Create a test file `test.cure`:

```cure
module Test

% String literal (straight quotes)
str = "hello"

% Charlist literal (curly quotes)
chars = 'hello'

% Atom (ASCII single quote)
atom = 'my_atom'
```

Verify:
- `"hello"` → String
- `'hello'` → Charlist
- `'my_atom'` → Atom

## Troubleshooting

### Characters Not Displaying

**Issue:** Curly quotes show as boxes or question marks

**Solution:** Ensure your editor uses a Unicode-aware font:
- Recommended fonts: Fira Code, JetBrains Mono, Source Code Pro
- Enable UTF-8 encoding in editor settings

### Incorrect Character Inserted

**Issue:** Wrong Unicode character inserted

**Solution:** 
- Verify the Unicode codepoints: U+2018 (left) and U+2019 (right)
- Check your keyboard layout or input method
- Use `xxd` or a Unicode inspector to verify characters

### Auto-Pairing Conflicts

**Issue:** Editor's auto-pairing interferes with charlist quotes

**Solution:**
- Disable auto-pairing for single quotes in Cure files
- Configure language-specific settings
- Use explicit keybindings instead of relying on editor defaults

## Alternative: ASCII Syntax (Not Recommended)

If Unicode input is impossible in your environment, you can use ASCII escapes:

```cure
% ASCII-only alternative (compiler support may vary)
chars = \u{2018}hello\u{2019}
```

However, this is **not recommended** as it's harder to read and write.

## Contributing

Found a better method for your editor? Please contribute:

1. Fork the Cure repository
2. Update this document with your configuration
3. Submit a pull request

See [CONTRIBUTING.md](../CONTRIBUTING.md) for guidelines.

## Resources

- [Unicode Character Table](https://unicode-table.com/)
- [Curly Quotes vs Straight Quotes](https://en.wikipedia.org/wiki/Quotation_mark)
- [Cure String Documentation](STRINGS.md)

## Support

Need help configuring your editor?

- Open an issue on GitHub
- Join the Cure community chat
- Check the FAQ in the main documentation

Happy coding! 🎉
