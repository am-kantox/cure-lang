" Vim filetype plugin
" Language:    Cure
" Maintainer:  Cure project
" Last Change: 2026 Apr 17
" Target:      Cure 0.17.0 (Proofs & Polish)
"
" Per-buffer defaults for editing .cure files. The rest of the plugin
" (ftdetect, syntax, indent) is installed alongside this file.
"
" Format-on-save is safe for Cure: the LSP delegates to
" Cure.Compiler.Formatter, a source-preserving formatter that
" round-trip-validates its output against the original AST. Plain `#`
" comments, string/regex literals, and doc comments are preserved
" byte-for-byte. The `cure fmt` CLI defaults to the same safe path;
" the destructive AST rewrite is behind the `--aggressive` flag.
"
" This ftplugin does NOT force-disable format-on-save any more. If you
" still want to opt out per-buffer, set b:autoformat = 0 and
" b:disable_autoformat = 1 yourself in
" ~/.config/nvim/after/ftplugin/cure.vim.

if exists('b:did_ftplugin')
  finish
endif
let b:did_ftplugin = 1

" --- Editing defaults -------------------------------------------------------
setlocal expandtab
setlocal shiftwidth=2
setlocal softtabstop=2
setlocal tabstop=2
setlocal commentstring=#\ %s

" Keep comment continuation (`r`, `c`) but drop the behaviours that
" reformat paragraphs and force-comment new lines in code blocks:
"   a - automatic paragraph formatting
"   t - text auto-wrap at textwidth
"   o - auto-insert comment leader after `o`/`O`
setlocal formatoptions-=a
setlocal formatoptions-=t
setlocal formatoptions-=o

" --- Undo hook for ftplugin unload ------------------------------------------
let b:undo_ftplugin = 'setlocal expandtab< shiftwidth< softtabstop< tabstop<'
      \ . ' commentstring< formatoptions<'
