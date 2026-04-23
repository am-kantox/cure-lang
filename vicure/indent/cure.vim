" Vim indent file
" Language:    Cure
" Maintainer:  Cure project
" Last Change: 2026 Apr 23
" Target:      Cure 0.28.2 (Talk Back)
"
" Cure uses indentation-based blocks. The following line shapes open a
" new indented block:
"
"   `mod Name`, `fn name(...) -> T`, `fsm Name`, `rec Name`,
"   `proto Name`, `impl T for U`, `type Name = ...`, `actor Name with ...`,
"   `sup Name`, `app Name`, `proof Name`, `use Mod.Path`,
"   `match expr`, `if cond then`, `else`, `with`, `receive`,
"   `for x in xs`, `try`, and any line ending with `=`, `->`, `then`,
"   `else`, `do`, `of`, or `with`.
"
" Multi-clause bodies use `| pattern -> body`. `@decorator` lines sit
" immediately above a header and should NOT open a new block on their
" own -- the header on the next line is what opens the block.

if exists("b:did_indent")
  finish
endif
let b:did_indent = 1

setlocal indentexpr=GetCureIndent()
setlocal indentkeys=0{,0},0),0],!^F,o,O,=\|,=else,=then,=end
setlocal autoindent
setlocal nosmartindent

if exists("*GetCureIndent")
  finish
endif

" Patterns for lines that open a new block.
" `mod`, `fn`, `fsm`, `rec`, `proto`, `impl`, `type`, `actor`, `sup`,
" `app`, `proof`, `use`, `match`, `for`, `try`, `receive` are the
" canonical v0.28 container / control headers.
let s:block_header = '\v^\s*(mod|fn|fsm|rec|proto|impl|type|actor|sup|app|proof|use|match|for|try|receive)>'

" Lines that clearly end with an "open body" marker.
let s:opens_body = '\v(\=|-\>|<then>|<else>|<do>|<of>|<with>)\s*(#.*)?$'

" A standalone `@attribute` line: `@record`, `@derive(Foo)`, etc.
" Treated as a decorator; the next line should NOT be indented just
" because of the attribute. It's the real header below it that opens
" the block.
let s:attribute_line = '\v^\s*\@[A-Za-z_][A-Za-z0-9_]*(\([^)]*\))?\s*(#.*)?$'

function! s:BracketDelta(line) abort
  let l:stripped = substitute(a:line, '\v#.*$', '', '')
  let l:stripped = substitute(l:stripped, "\\v'([^'\\\\]|\\\\.)*'", "''", 'g')
  let l:stripped = substitute(l:stripped, '\v"([^"\\]|\\.)*"', '""', 'g')
  let l:opens  = len(substitute(l:stripped, '[^({[]', '', 'g'))
  let l:closes = len(substitute(l:stripped, '[^)}\]]', '', 'g'))
  return l:opens - l:closes
endfunction

" Walk back past attribute-only lines to the line that actually drives
" indentation. This is what lets `@record\nfsm Foo\n  Bar --x--> Baz`
" indent the transition correctly.
function! s:PrevDrivingLine(lnum) abort
  let l:n = a:lnum
  while l:n > 0
    let l:n = prevnonblank(l:n - 1)
    if l:n <= 0
      return 0
    endif
    if getline(l:n) !~# s:attribute_line
      return l:n
    endif
  endwhile
  return 0
endfunction

function! GetCureIndent() abort
  let l:anchor = s:PrevDrivingLine(v:lnum)
  if l:anchor == 0
    return 0
  endif

  let l:prev = getline(l:anchor)
  let l:cur  = getline(v:lnum)
  let l:ind  = indent(l:anchor)
  let l:sw   = shiftwidth()

  " ---- increase indent after block-opening lines -------------------------
  if l:prev =~# s:block_header && l:prev !~# '\v\)\s*\=\s*\S'
    " Header line: a `fn foo(x) -> T` header with no body yet opens a block,
    " but `fn foo() -> T = expr` keeps the body on the same line.
    if l:prev !~# '\v\=\s*\S'
      let l:ind += l:sw
    endif
  endif

  if l:prev =~# s:opens_body
    let l:ind += l:sw
  endif

  " Unclosed brackets pull the next line in one shiftwidth.
  let l:delta = s:BracketDelta(l:prev)
  if l:delta > 0
    let l:ind += l:sw
  elseif l:delta < 0
    let l:ind += l:sw * l:delta
  endif

  " ---- decrease indent for continuation / closing lines ------------------
  " Guard/multi-clause continuation lines realign to the header.
  if l:cur =~# '\v^\s*\|'
    let l:ind -= l:sw
  endif

  " `else` / `elif` align with the matching `if`.
  if l:cur =~# '\v^\s*(else|elif)>'
    let l:ind -= l:sw
  endif

  " A line starting with `end` (legacy block terminator) outdents.
  if l:cur =~# '\v^\s*end>'
    let l:ind -= l:sw
  endif

  " A line starting with a closing bracket outdents one level.
  if l:cur =~# '\v^\s*[)}\]]'
    let l:ind -= l:sw
  endif

  if l:ind < 0
    return 0
  endif
  return l:ind
endfunction
