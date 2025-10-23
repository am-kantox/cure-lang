" Vim syntax file
" Language: Cure
" Maintainer: Generated for Cure Programming Language
" Latest Revision: 2025

if exists("b:current_syntax")
  finish
endif

" Keywords
syn keyword cureKeyword def end do match when let in as
syn keyword cureKeyword module import export process fsm state states initial event timeout
syn keyword cureKeyword receive send spawn transition guard action invariant eventually always until property
syn keyword cureKeyword record type fn

" Boolean literals
syn keyword cureBoolean true false

" Result/Option constructors
syn keyword cureConstructor Ok Error Some None Unit ok error

" Operators
syn keyword cureOperator and or not
syn match cureOperator "\v\="
syn match cureOperator "\v\-\>"
syn match cureOperator "\v\:\:"
syn match cureOperator "\v\|>"
syn match cureOperator "\v\+\+"
syn match cureOperator "\v\-\-"
syn match cureOperator "\v\+"
syn match cureOperator "\v\-"
syn match cureOperator "\v\*"
syn match cureOperator "\v\/"
syn match cureOperator "\v\%"
syn match cureOperator "\v\<\="
syn match cureOperator "\v\>\="
syn match cureOperator "\v\=\="
syn match cureOperator "\v\!\="
syn match cureOperator "\v\<"
syn match cureOperator "\v\>"
syn match cureOperator "\v\|"

" Delimiters
syn match cureDelimiter "\v\("
syn match cureDelimiter "\v\)"
syn match cureDelimiter "\v\["
syn match cureDelimiter "\v\]"
syn match cureDelimiter "\v\{"
syn match cureDelimiter "\v\}"
syn match cureDelimiter "\v\,"
syn match cureDelimiter "\v\;"
syn match cureDelimiter "\v\:"
syn match cureDelimiter "\v\."

" Numbers
syn match cureNumber "\v<\d+>"
syn match cureFloat "\v<\d+\.\d+>"

" Strings with interpolation support
syn region cureString start='"' end='"' contains=cureInterpolation,cureEscape
syn match cureEscape contained "\\[ntr\\\"]"
syn region cureInterpolation contained matchgroup=cureInterpolationDelim start="#{" end="}" contains=TOP

" Atoms
syn match cureAtom "\v\:[a-zA-Z_][a-zA-Z0-9_?]*"
syn region cureQuotedAtom start="'" end="'" contains=cureEscape

" Comments
syn match cureComment "\v#.*$" contains=cureTodo
syn keyword cureTodo contained TODO FIXME NOTE XXX

" Identifiers (must come after keywords)
" Type identifiers (start with uppercase)
syn match cureType "\v<[A-Z][a-zA-Z0-9_]*>"
" Function/variable identifiers (start with lowercase or underscore)
syn match cureIdentifier "\v<[a-z_][a-zA-Z0-9_?]*>"

" Function definitions
syn match cureFunctionDef "\v(def|def_erl)\s+\zs[a-z_][a-zA-Z0-9_?]*"

" Module names
syn match cureModule "\v(module|import)\s+\zs[A-Z][a-zA-Z0-9_]*"

" FSM names
syn match cureFsmName "\v(fsm)\s+\zs[A-Z][a-zA-Z0-9_]*"

" Record names
syn match cureRecordName "\v(record)\s+\zs[A-Z][a-zA-Z0-9_]*"

" Type annotations
syn match cureTypeAnnotation "\v\:\s*[A-Z][a-zA-Z0-9_]*"

" Highlighting links
" Use Statement for flow control keywords to get distinct color from types
hi def link cureKeyword Statement
hi def link cureBoolean Boolean
" Use StorageClass for constructors to distinguish from types
hi def link cureConstructor StorageClass
hi def link cureOperator Operator
hi def link cureDelimiter Delimiter
hi def link cureNumber Number
hi def link cureFloat Float
hi def link cureString String
hi def link cureEscape SpecialChar
hi def link cureInterpolation Special
hi def link cureInterpolationDelim SpecialChar
hi def link cureAtom Constant
hi def link cureQuotedAtom Constant
hi def link cureComment Comment
hi def link cureTodo Todo
" Use Type for type names - distinct from keywords
hi def link cureType Type
hi def link cureIdentifier Identifier
hi def link cureFunctionDef Function
" Use PreProc for module/structure definitions for better distinction
hi def link cureModule PreProc
hi def link cureFsmName PreProc
hi def link cureRecordName PreProc
" Use TypeDef for type annotations to distinguish from type names
hi def link cureTypeAnnotation TypeDef

let b:current_syntax = "cure"
