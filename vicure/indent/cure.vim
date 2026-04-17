" Vim indent file
" Language:    Cure
" Maintainer:  Cure project
" Last Change: 2026 Apr 17
" Target:      Cure 0.17.0 (Proofs & Polish)
"
" Cure uses indentation-based blocks. Headers like `mod Name`, `fn name(...) ->`,
" `fsm Name`, `rec Name`, `proto Name`, `impl T for U`, `type Name = ...`,
" `match expr`, `if cond then`, `else`, and any line ending with `=` or `->`
" open a new indented block. Multi-clause bodies use `| pattern -> body`.

if exists("b:did_indent")
  finish
endif
let b:did_indent = 1

setlocal indentexpr=GetCureIndent()
setlocal indentkeys=0{,0},0),0],!^F,o,O,=\|,=else,=then
setlocal autoindent
setlocal nosmartindent

if exists("*GetCureIndent")
  finish
endif

" Patterns for lines that open a new block
let s:block_header = '\v^\s*(mod|fn|fsm|rec|proto|impl|type|match|for|try)\s'

" Lines that clearly end with an "open body" marker
let s:opens_body = '\v(\=|-\>|<then>|<else>|<do>|<of>)\s*(#.*)?$'

" Lines that are pure bracket continuations to track
let s:openers  = '[({[]'
let s:closers  = '[)}\]]'

function! s:BracketDelta(line) abort
  let l:stripped = substitute(a:line, '\v#.*$', '', '')
  let l:stripped = substitute(l:stripped, "\\v'([^'\\\\]|\\\\.)*'", "''", 'g')
  let l:stripped = substitute(l:stripped, '\v"([^"\\]|\\.)*"', '""', 'g')
  let l:opens  = len(substitute(l:stripped, '[^({[]', '', 'g'))
  let l:closes = len(substitute(l:stripped, '[^)}\]]', '', 'g'))
  return l:opens - l:closes
endfunction

function! GetCureIndent() abort
  let l:lnum  = prevnonblank(v:lnum - 1)
  if l:lnum == 0
    return 0
  endif

  let l:prev  = getline(l:lnum)
  let l:cur   = getline(v:lnum)
  let l:ind   = indent(l:lnum)
  let l:sw    = shiftwidth()

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

  " ---- decrease indent for continuation / closing lines -----------------
  " Guard/multi-clause continuation lines realign to the header.
  if l:cur =~# '\v^\s*\|'
    let l:ind -= l:sw
  endif

  " `else` / `elif` align with the matching `if`.
  if l:cur =~# '\v^\s*(else|elif)>'
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
