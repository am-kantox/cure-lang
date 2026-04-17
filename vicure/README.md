# Vicure - Cure Language Plugin for Neovim/Vim

[![Language](https://img.shields.io/badge/language-Cure-blue.svg)](https://github.com/Oeditus/cure)
[![Editor](https://img.shields.io/badge/editor-Neovim%20%7C%20Vim-green.svg)](https://neovim.io/)
[![License](https://img.shields.io/badge/license-MIT-brightgreen.svg)](LICENSE)

Comprehensive syntax highlighting, indentation, and filetype detection for the [Cure programming language](https://github.com/Oeditus/cure) in Neovim and Vim.

## Features

**Complete Syntax Support**
- Keywords: `def`, `module`, `fsm`, `typeclass`, `trait`, `instance`, `impl`, etc.
- Modern type system: Typeclasses, traits, records, and dependent types
- String interpolation with `#{...}` syntax
- Pattern matching and guards
- FSM (Finite State Machine) constructs
- Erlang interop with `curify`

**Smart Highlighting**
- Semantic distinction between types, typeclasses, and traits
- Function definitions and module names
- Operators and delimiters
- Comments with TODO/FIXME/NOTE/XXX highlighting
- Atoms (`:symbol` and `'quoted atoms'`)

**Auto-Indentation**
- Intelligent indentation for all block types
- Proper handling of nested structures
- Bracket-aware indentation

**Editor Defaults (ftplugin)**
- 2-space indentation with `expandtab`
- `commentstring = "# %s"` so `gcc` / `Comment.nvim` / `vim-commentary` work
- Trimmed `formatoptions`: no paragraph auto-reflow, no auto-wrap, no
  forced comment leader after `o` / `O`
- Ships `b:autoformat = 0` and `b:disable_autoformat = 1` so LunarVim,
  `conform.nvim`, and `none-ls`/`null-ls` skip Cure buffers on save
  (the LSP formatter was lossy; see [Formatting](#formatting))

**Easy Installation**
- Works with all major plugin managers
- Manual installation supported
- Zero configuration required

## Quick Start

### Installation

#### Using [lazy.nvim](https://github.com/folke/lazy.nvim) (Recommended)

Create `~/.config/nvim/lua/plugins/cure.lua`:

```lua
return {
  dir = "/path/to/cure/vicure",
  ft = "cure",
}
```

Or add to your main plugin configuration:

```lua
{
  dir = "/opt/Proyectos/Oeditus/cure/vicure",
  ft = "cure",
}
```

#### Using [packer.nvim](https://github.com/wbthomason/packer.nvim)

```lua
use {
  '/opt/Proyectos/Oeditus/cure/vicure',
  ft = 'cure'
}
```

#### Using [vim-plug](https://github.com/junegunn/vim-plug)

```vim
Plug '/opt/Proyectos/Oeditus/cure/vicure'
```

#### Manual Installation

```bash
# For Neovim
mkdir -p ~/.config/nvim/{syntax,ftdetect,ftplugin,indent}
cp vicure/syntax/cure.vim   ~/.config/nvim/syntax/
cp vicure/ftdetect/cure.vim ~/.config/nvim/ftdetect/
cp vicure/ftplugin/cure.vim ~/.config/nvim/ftplugin/
cp vicure/indent/cure.vim   ~/.config/nvim/indent/

# For Vim
mkdir -p ~/.vim/{syntax,ftdetect,ftplugin,indent}
cp vicure/syntax/cure.vim   ~/.vim/syntax/
cp vicure/ftdetect/cure.vim ~/.vim/ftdetect/
cp vicure/ftplugin/cure.vim ~/.vim/ftplugin/
cp vicure/indent/cure.vim   ~/.vim/indent/
```

### Usage

1. Open any `.cure` file - syntax highlighting activates automatically
2. Check filetype: `:set filetype?` (should show `cure`)
3. View active syntax groups: `:syntax`

## Syntax Showcase

### Typeclasses and Traits

```cure
# Haskell-style typeclass
typeclass Show(T) do
  def show(x: T): String
end

# Rust-style trait
trait Display(T) do
  def display(x: T): String
end

# Instance implementation
instance Show(Person) do
  def show(p: Person): String =
    "Person{name: #{p.name}, age: #{p.age}}"
end

# Trait implementation
impl Display for Person do
  def display(p: Person): String =
    "#{p.name} (#{p.age} years old)"
end
```

### Records and Types

```cure
record Person do
  name: String
  age: Int
  email: String
end

type UserId = Int
type Result(T, E) = Ok(T) | Error(E)
```

### Generic Functions with Constraints

```cure
def debug_value(x: T): T where Show(T) =
  println(show(x))
  x

def map_list(xs: List(T), f: T -> U): List(U) =
  match xs do
    [] -> []
    [head | tail] -> [f(head) | map_list(tail, f)]
  end
```

### FSM Definitions

```cure
fsm TrafficLight do
  states: [Red, Yellow, Green]
  initial: Red
  
  state Red do
    on timer -> Green
    timeout 30 -> Yellow
  end
  
  state Green do
    on timer -> Yellow
    on emergency -> Red
  end
end
```

### Erlang Interop

```cure
curify io_format(format: String, args: List): Unit =
  erlang io format/2
```

## Highlighting Groups

The plugin uses standard Vim highlight groups for maximum color scheme compatibility:

- Keywords (`Statement`): `def`, `match`, `when`
- Typeclasses/Traits (`Structure`): `typeclass Show(T)`
- Types (`Type`): `String`, `Int`, `Person`
- Functions (`Function`): `def calculate(x)`
- Instances/Impls (`Special`): `instance Show(Int)`
- Operators (`Operator`): `->`, `|>`, `::`
- Strings (`String`): `"Hello #{name}"`
- Comments (`Comment`): `# TODO: ...`
- Atoms (`Constant`): `:ok`, `'atom'`

## Testing

A comprehensive test file is included:

```bash
nvim vicure/test_syntax.cure
```

This 156-line file demonstrates all supported features:
- Records, types, typeclasses, traits
- Instances and implementations
- Generic functions with constraints
- FSMs and state machines
- Pattern matching and guards
- String interpolation
- Erlang interop

## Formatting

The Cure LSP advertises `textDocument/formatting`, routed through
`Cure.Compiler.Formatter` -- a **safe, source-preserving formatter**
that only performs rewrites whose effect on the AST is a provable
no-op. Plain `#` comments, string/regex/char literals, and doc
comments are preserved byte-for-byte; every rewrite is
round-trip-validated against the original parse tree before the LSP
emits an edit. Format-on-save is safe by default.

What the formatter does:

- Normalises `\r\n` line endings to `\n`.
- Strips trailing horizontal whitespace from code lines.
- Expands leading tabs (a Cure lexer error) to two spaces.
- Collapses runs of two or more consecutive blank lines to one.
- Adds spaces around a fixed set of binary operators
  (`==`, `!=`, `<=`, `>=`, `|>`, `->`, `=>`, `<>`, `+=`, `-=`, `*=`,
  `/=`, `=`, `+`, `-`, `*`, `/`, `%`), with heuristics that leave
  unary `-`/`*`, variadic `*args`/`**kwargs`, and exponent signs
  alone.
- Ensures exactly one trailing newline.

If you prefer the old behaviour (no format-on-save at all), opt out
per-buffer:

```vim
" In ~/.config/nvim/after/ftplugin/cure.vim
let b:autoformat = 0
let b:disable_autoformat = 1
```

The destructive AST pretty printer is still reachable on the CLI via
`cure fmt --aggressive`, which strips plain `#` comments and any
non-canonical whitespace in exchange for a fully canonical buffer.

## Configuration

### Custom Colors

Customize highlighting in your Neovim config:

```lua
-- In init.lua
vim.api.nvim_set_hl(0, 'cureFunctionDef', { fg = '#61AFEF' })
vim.api.nvim_set_hl(0, 'cureKeyword', { fg = '#C678DD' })
vim.api.nvim_set_hl(0, 'cureType', { fg = '#E5C07B' })
vim.api.nvim_set_hl(0, 'cureTypeclassName', { fg = '#56B6C2' })
```

Or in Vimscript:

```vim
" In init.vim
hi cureFunctionDef guifg=#61AFEF
hi cureKeyword guifg=#C678DD
hi cureType guifg=#E5C07B
hi cureTypeclassName guifg=#56B6C2
```

### Indentation Settings

Adjust indentation width (default: 2 spaces):

```lua
vim.api.nvim_create_autocmd("FileType", {
  pattern = "cure",
  callback = function()
    vim.opt_local.shiftwidth = 2
    vim.opt_local.tabstop = 2
    vim.opt_local.expandtab = true
  end,
})
```

## Troubleshooting

### Syntax highlighting not working

1. Verify filetype: `:set filetype?`
2. Force set: `:set filetype=cure`
3. Reload file: `:e`
4. Check syntax: `:syntax` (should show `cure*` groups)

### Indentation not working

Ensure filetype plugins are enabled:

```lua
vim.cmd('filetype plugin indent on')
```

### Save is reformatting / stripping comments

The default formatter (`Cure.Compiler.Formatter`, used by the LSP
and by `cure fmt`) is source-preserving: it does not touch comments
or non-code layout. If you are seeing comments disappear, another
tool is almost certainly running `cure fmt --aggressive` or a fork
of the old AST-based printer on save. Verify with:

```vim
:echo &filetype
:lua =vim.b.autoformat
:lua =vim.b.disable_autoformat
:lua =vim.lsp.get_active_clients({ bufnr = 0 })
```

If `filetype` is not `cure`, `vim.filetype.add({ extension = { cure = 'cure' } })`
is missing from your config. If a non-Cure LSP is attached, make sure
its `root_dir`/`filetypes` do not claim `.cure` files.

As a one-shot kill switch for the current buffer:

```vim
:lua vim.b.autoformat = false
:lua vim.b.disable_autoformat = true
" with conform.nvim:
:FormatDisable
```

### Wrong colors

Try a different color scheme or create custom highlights (see Configuration above).

## Supported Color Schemes

Tested and works well with:
- [OneDark](https://github.com/joshdick/onedark.vim)
- [Gruvbox](https://github.com/morhetz/gruvbox)
- [Nord](https://github.com/arcticicestudio/nord-vim)
- [Catppuccin](https://github.com/catppuccin/nvim)
- [Tokyo Night](https://github.com/folke/tokyonight.nvim)
- [Dracula](https://github.com/dracula/vim)

Should work with any color scheme that defines standard highlight groups.

## Language Server Protocol (LSP)

For IDE features like go-to-definition, hover, and completion, see the main Cure LSP documentation in `/lsp/`.

The LSP provides:
- Real-time diagnostics
- Go-to-definition
- Hover information
- Code completion
- Find references

## Contributing

Contributions are welcome! To improve the syntax plugin:

1. Edit `syntax/cure.vim` for syntax rules
2. Edit `indent/cure.vim` for indentation
3. Test with `test_syntax.cure`
4. Update documentation
5. Submit a pull request

## Documentation

- [NEOVIM_PLUGIN.md](NEOVIM_PLUGIN.md) - Detailed plugin documentation
- [CHANGELOG.md](CHANGELOG.md) - Version history and updates
- [MODERNIZATION_SUMMARY.md](MODERNIZATION_SUMMARY.md) - Recent improvements

## License

This plugin is part of the Cure programming language project.

## Related Projects

- [Cure Language](https://github.com/Oeditus/cure) - The main Cure compiler and runtime
- [Cure LSP](../cure-lsp) - Language Server Protocol launcher
- [Cure Documentation](../docs/) - Language documentation and guides

## Support

- Report issues: [GitHub Issues](https://github.com/Oeditus/cure/issues)
- Discussions: [GitHub Discussions](https://github.com/Oeditus/cure/discussions)
- Documentation: [Cure Docs](../docs/)

---

Made for the Cure programming language community
