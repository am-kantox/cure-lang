# Cure Syntax Highlighting for Neovim

This directory contains syntax highlighting, indentation, and filetype detection for the Cure programming language in Neovim/Vim.

## Installation

### Manual Installation

Copy the files to your Neovim configuration directory:

```bash
# For Neovim (recommended)
mkdir -p ~/.config/nvim/syntax ~/.config/nvim/ftdetect ~/.config/nvim/indent
cp syntax/cure.vim ~/.config/nvim/syntax/
cp ftdetect/cure.vim ~/.config/nvim/ftdetect/
cp indent/cure.vim ~/.config/nvim/indent/

# For Vim
mkdir -p ~/.vim/syntax ~/.vim/ftdetect ~/.vim/indent
cp syntax/cure.vim ~/.vim/syntax/
cp ftdetect/cure.vim ~/.vim/ftdetect/
cp indent/cure.vim ~/.vim/indent/
```

### Using a Plugin Manager

#### lazy.nvim

Add to your `~/.config/nvim/lua/plugins/cure.lua`:

```lua
return {
  dir = "/opt/Proyectos/Ammotion/cure",
  ft = "cure",
  config = function()
    vim.api.nvim_create_autocmd({"BufRead", "BufNewFile"}, {
      pattern = "*.cure",
      callback = function()
        vim.bo.filetype = "cure"
      end,
    })
  end,
}
```

#### packer.nvim

Add to your `init.lua`:

```lua
use {
  '/opt/Proyectos/Ammotion/cure',
  ft = 'cure'
}
```

#### vim-plug

Add to your `init.vim`:

```vim
Plug '/opt/Proyectos/Ammotion/cure'
```

## Features

### Syntax Highlighting

The plugin provides syntax highlighting for:

- **Keywords**: `def`, `def_erl`, `curify`, `module`, `fsm`, `state`, `match`, `case`, `when`, `where`, etc.
- **Type System Keywords**: `typeclass`, `trait`, `instance`, `impl`, `derive`, `class`
- **FSM Constructs**: `fsm`, `state`, `states`, `initial`, `event`, `timeout`, `transition`, etc.
- **Operators**: `->`, `|>`, `::`, `++`, `--`, `==`, `!=`, etc.
- **Types**: Type names (capitalized identifiers)
- **Constructors**: `Ok`, `Error`, `Some`, `None`, `Unit`
- **Boolean literals**: `true`, `false`
- **Numbers**: Integers and floats
- **Strings**: With escape sequences and `#{}` interpolation support
- **Atoms**: `:atom` and `'quoted atoms'`
- **Comments**: `# comment` with TODO/FIXME/NOTE/XXX highlighting
- **Function definitions**: Highlighted function names (including `curify` wrappers)
- **Module/FSM/Record names**: Highlighted structure names
- **Typeclass/Trait names**: Highlighted interface names
- **Instance/Implementation**: Highlighted instance declarations

### Indentation

Automatic indentation for:
- `do...end` blocks
- `module...end` blocks
- `fsm...end` blocks
- `state...end` blocks
- `typeclass...end` and `trait...end` blocks
- `instance...end` and `impl...end` blocks
- `match...end` and `case...of...end` expressions
- Function definitions (including `curify`)
- Bracket pairs `()`, `[]`, `{}`

### Filetype Detection

Automatically detects `.cure` files and sets the appropriate filetype.

## Testing

To verify the installation:

1. Open a `.cure` file in Neovim:
   ```bash
   nvim examples/advanced_traffic_light.cure
   ```

2. Check the filetype:
   ```vim
   :set filetype?
   ```
   Should show: `filetype=cure`

3. Check syntax highlighting is active:
   ```vim
   :syntax
   ```
   Should show various `cure*` syntax groups.

## Color Scheme Compatibility

The syntax file uses standard Vim highlight groups, so it will work with any color scheme:

- `Keyword` - Language keywords
- `Type` - Type names and constructors
- `Function` - Function names in definitions
- `Operator` - Operators
- `String` - String literals
- `Number`/`Float` - Numeric literals
- `Comment` - Comments
- `Constant` - Atoms
- `Special` - String interpolations
- `Structure` - Module/FSM/Record names

## Examples

```cure
# Comment highlighting
module TrafficLight do
  # Keywords: module, do, end
  # Structure name: TrafficLight
  
  # Record definition
  record Color do
    red: Int
    green: Int
    blue: Int
  end
  
  # Typeclass definition
  typeclass Show(T) do
    def show(x: T): String
  end
  
  # Instance implementation
  instance Show(Color) do
    def show(c: Color): String =
      "Color(#{c.red}, #{c.green}, #{c.blue})"
  end
  
  fsm SimpleFSM do
    # FSM-specific keywords
    states: [Red, Green, Yellow]
    initial: Red
    
    state Red do
      event(:timer) -> Green
    end
  end
  
  def calculate_area(radius: Float): Float =
    # Function definition highlighting
    # Type annotations
    3.14159 * radius * radius
  
  # Generic function with where clause
  def debug_value(x: T): T where Show(T) =
    println(show(x))
    x
  
  def interpolation_demo(name: String): String =
    # String interpolation
    "Hello #{name}!"
    
  # Pattern matching
  def handle_result(result: Result(Int, String)): String =
    match result do
      Ok(value) -> "Success: #{value}"
      Error(msg) -> "Failed: #{msg}"
    end
    
  # Curify Erlang function
  curify io_format(format: String, args: List): Unit =
    erlang io format/2
end
```

## Troubleshooting

### Syntax highlighting not working

1. Ensure the files are in the correct locations
2. Restart Neovim: `:q` then reopen
3. Force reload: `:e` in the buffer
4. Check filetype: `:set filetype=cure`

### Indentation not working

Check that `filetype indent on` is enabled in your config:

```vim
filetype plugin indent on
```

Or in Lua:

```lua
vim.cmd('filetype plugin indent on')
```

### Colors look wrong

Try a different color scheme or customize the highlighting in your config:

```vim
" Customize Cure syntax colors
hi cureFunctionDef guifg=#61AFEF
hi cureKeyword guifg=#C678DD
hi cureType guifg=#E5C07B
```

## Contributing

To add new features or fix issues with the syntax highlighting:

1. Edit `syntax/cure.vim` for syntax rules
2. Edit `indent/cure.vim` for indentation rules
3. Edit `ftdetect/cure.vim` for filetype detection
4. Test with example `.cure` files
5. Submit improvements to the Cure project

## License

This syntax plugin is part of the Cure programming language project.
