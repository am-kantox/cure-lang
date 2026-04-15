" Vim indent file
" Language: Cure
" Maintainer: Generated for Cure Programming Language

if exists("b:did_indent")
  finish
endif
let b:did_indent = 1

setlocal indentexpr=GetCureIndent()
setlocal indentkeys=0{,0},0),0],!^F,o,O,e,=end,=do,=else,=of,=when
setlocal autoindent
setlocal nosmartindent

function! GetCureIndent()
  let lnum = prevnonblank(v:lnum - 1)
  if lnum == 0
    return 0
  endif

  let ind = indent(lnum)
  let line = getline(lnum)
  let cline = getline(v:lnum)

  " Increase indent after do, ->, then, else, of, when
  if line =~# '\v(do|then|else|of|-\>)\s*$'
    let ind += shiftwidth()
  endif

  " Increase indent after module, fsm, record, typeclass, trait, instance, state, def
  if line =~# '\v^\s*(module|fsm|record|typeclass|trait|instance|impl|state|def|def_erl|curify|match|case)\s'
    let ind += shiftwidth()
  endif

  " Increase indent for unclosed brackets
  let open_brackets = len(substitute(line, '[^{[(]', '', 'g'))
  let close_brackets = len(substitute(line, '[^}\])]', '', 'g'))
  if open_brackets > close_brackets
    let ind += shiftwidth()
  endif

  " Decrease indent for end, closing brackets
  if cline =~# '^\s*end\>'
    let ind -= shiftwidth()
  endif

  if cline =~# '^\s*[}\])]'
    let ind -= shiftwidth()
  endif

  " Decrease indent for else, of
  if cline =~# '^\s*\(else\|of\)\>'
    let ind -= shiftwidth()
  endif

  return ind < 0 ? 0 : ind
endfunction
