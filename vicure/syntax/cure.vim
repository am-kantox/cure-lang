" Vim syntax file
" Language: Cure
" Maintainer: Generated for Cure Programming Language
" Latest Revision: 2025

if exists("b:current_syntax")
  finish
endif

" Keywords
syn keyword cureKeyword def defp def_erl end do if then else match case of when let in as
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
syn match cureFunctionDef "\v(def|defp|def_erl)\s+\zs[a-z_][a-zA-Z0-9_?]*"

" Module names
syn match cureModule "\v(module|import)\s+\zs[A-Z][a-zA-Z0-9_]*"

" FSM names
syn match cureFsmName "\v(fsm)\s+\zs[A-Z][a-zA-Z0-9_]*"

" Record names
syn match cureRecordName "\v(record)\s+\zs[A-Z][a-zA-Z0-9_]*"

" Type annotations
syn match cureTypeAnnotation "\v\:\s*[A-Z][a-zA-Z0-9_]*"

" Highlighting links
hi def link cureKeyword Keyword
hi def link cureBoolean Boolean
hi def link cureConstructor Type
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
hi def link cureType Type
hi def link cureIdentifier Identifier
hi def link cureFunctionDef Function
hi def link cureModule Structure
hi def link cureFsmName Structure
hi def link cureRecordName Structure
hi def link cureTypeAnnotation Type

let b:current_syntax = "cure"
