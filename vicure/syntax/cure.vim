" Vim syntax file
" Language:    Cure
" Maintainer:  Cure project
" Last Change: 2026 Apr 17
" Target:      Cure 0.17.0 (Proofs & Polish)

if exists("b:current_syntax")
  finish
endif

syn case match

" --- Comments ---------------------------------------------------------------
" Doc comments (##) come before line comments (#) so the longer match wins.
syn match  cureDocComment "\v##.*$" contains=cureTodo,@Spell
syn match  cureComment    "\v#.*$"  contains=cureTodo,@Spell
syn keyword cureTodo contained TODO FIXME NOTE XXX HACK BUG

" --- Strings ----------------------------------------------------------------
" Strings support #{...} interpolation and \n \r \t \\ \" escapes.
syn region cureString
      \ matchgroup=cureStringDelim
      \ start=+"+ skip=+\\.+ end=+"+
      \ contains=cureEscape,cureInterpolation,@Spell
syn match  cureEscape         contained "\v\\[ntr\\\"']"
syn region cureInterpolation  contained
      \ matchgroup=cureInterpolationDelim
      \ start="#{" end="}"
      \ contains=TOP

" --- Numbers ----------------------------------------------------------------
syn match cureFloat  "\v<\d+\.\d+([eE][+-]?\d+)?>"
syn match cureNumber "\v<0x[0-9a-fA-F]+>"
syn match cureNumber "\v<0b[01]+>"
syn match cureNumber "\v<\d+>"

" --- Atoms ------------------------------------------------------------------
syn match  cureAtom       "\v\:[a-z_][a-zA-Z0-9_]*[!?]?"
syn region cureQuotedAtom start=+'+ skip=+\\.+ end=+'+ contains=cureEscape

" --- Keywords ---------------------------------------------------------------
" Control flow
syn keyword cureKeyword if then else elif match return throw try catch finally
syn keyword cureKeyword when where use local in for

" Declarations
syn keyword cureDeclaration fn mod rec fsm proto impl type let

" FSM lifecycle (callback-mode, v0.16+)
syn keyword cureFsmCallback on_transition on_enter on_exit on_failure on_timer

" Literal constants
syn keyword cureBoolean true false
syn keyword cureConstant nil

" Built-in types the stdlib ships with
syn keyword cureBuiltinType Int Float Bool String Atom
syn keyword cureBuiltinType List Tuple Map Set Pair
syn keyword cureBuiltinType Option Result Unit Nat Vector
syn keyword cureBuiltinType Sigma Pi Eq DPair

" Well-known constructors / canonical proofs
syn keyword cureConstructor Ok Error Some None
syn keyword cureConstructor Zero Succ Pred Self refl

" --- Operators --------------------------------------------------------------
syn keyword cureOperator and or not

" Arrows and pipes (multi-char first so they win)
syn match cureOperator "\v-\>"
syn match cureOperator "\v\<-"
syn match cureOperator "\v\=\>"
syn match cureOperator "\v\|\>"

" Comparison
syn match cureOperator "\v\=\="
syn match cureOperator "\v!\="
syn match cureOperator "\v\<\="
syn match cureOperator "\v\>\="
syn match cureOperator "\v\<\>"

" Monad / applicative / functor sugar
syn match cureOperator "\v\>\>\="
syn match cureOperator "\v\>\>"
syn match cureOperator "\v\<\*\>"
syn match cureOperator "\v\<\*"
syn match cureOperator "\v\*\>"
syn match cureOperator "\v\<\$"
syn match cureOperator "\v\$\>"

" Range
syn match cureOperator "\v\.\.\="
syn match cureOperator "\v\.\."

" Cons / list / misc
syn match cureOperator "\v::"
syn match cureOperator "\v\+\+"
syn match cureOperator "\v--"
syn match cureOperator "\v\|\|"
syn match cureOperator "\v\&\&"

" Single-char math / assignment / guard heads
syn match cureOperator "\v[+\-*/%]"
syn match cureOperator "\v\="
syn match cureOperator "\v[<>]"
syn match cureOperator "\v\|"

" --- Delimiters -------------------------------------------------------------
syn match cureDelimiter "\v[(),;]"
" Tuple prefix `%[...]` -- highlight the `%` distinctly
syn match cureTuplePrefix "\v\%\ze\["

" --- Identifiers, function / module / type heads ----------------------------
" Dotted module path (e.g. Std.Vector, Cure.Types.Pi)
syn match cureModulePath "\v<[A-Z][A-Za-z0-9_]*(\.[A-Z][A-Za-z0-9_]*)+>"

" Type / constructor identifiers (CamelCase)
syn match cureType "\v<[A-Z][A-Za-z0-9_]*>"

" Lowercase identifiers (functions, variables). Allow trailing ? or !.
syn match cureIdentifier "\v<[a-z_][A-Za-z0-9_]*[!?]?>"

" Function definition heads: `fn name(...)`
syn match cureFunctionDef "\vfn\s+\zs[a-z_][A-Za-z0-9_]*[!?]?"

" Module heads: `mod Name` or `mod Std.Pair`
syn match cureModuleHead "\vmod\s+\zs[A-Z][A-Za-z0-9_]*(\.[A-Z][A-Za-z0-9_]*)*"

" Record, fsm, proto heads
syn match cureRecordHead "\vrec\s+\zs[A-Z][A-Za-z0-9_]*"
syn match cureFsmHead    "\vfsm\s+\zs[A-Z][A-Za-z0-9_]*"
syn match cureProtoHead  "\vproto\s+\zs[A-Z][A-Za-z0-9_]*"

" `impl Trait` or `impl Trait for Type`
syn match cureImplHead "\vimpl\s+\zs[A-Z][A-Za-z0-9_]*"
syn match cureImplFor  "\vimpl\s+[A-Z][A-Za-z0-9_]*\s+for\s+\zs[A-Z][A-Za-z0-9_]*"

" `type Name` heads (ADT / alias / refinement)
syn match cureTypeHead "\vtype\s+\zs[A-Z][A-Za-z0-9_]*"

" Type annotation after `:` -- a leading type name in `name: Type`
syn match cureTypeAnnotation "\v:\s*\zs[A-Z][A-Za-z0-9_]*(\.[A-Z][A-Za-z0-9_]*)*"

" --- Highlight links --------------------------------------------------------
hi def link cureComment           Comment
hi def link cureDocComment        SpecialComment
hi def link cureTodo              Todo

hi def link cureString            String
hi def link cureStringDelim       String
hi def link cureEscape            SpecialChar
hi def link cureInterpolation     Special
hi def link cureInterpolationDelim SpecialChar

hi def link cureNumber            Number
hi def link cureFloat             Float

hi def link cureAtom              Constant
hi def link cureQuotedAtom        Constant

hi def link cureKeyword           Statement
hi def link cureDeclaration       Keyword
hi def link cureFsmCallback       Keyword
hi def link cureBoolean           Boolean
hi def link cureConstant          Constant

hi def link cureBuiltinType       Type
hi def link cureConstructor       StorageClass

hi def link cureOperator          Operator
hi def link cureDelimiter         Delimiter
hi def link cureTuplePrefix       Special

hi def link cureModulePath        Structure
hi def link cureType              Type
hi def link cureIdentifier        Identifier

hi def link cureFunctionDef       Function
hi def link cureModuleHead        PreProc
hi def link cureRecordHead        PreProc
hi def link cureFsmHead           PreProc
hi def link cureProtoHead         PreProc
hi def link cureImplHead          Special
hi def link cureImplFor           Type
hi def link cureTypeHead          PreProc
hi def link cureTypeAnnotation    TypeDef

let b:current_syntax = "cure"
