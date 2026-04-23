" Filetype detection for Cure
"
" `.cure` source files are the language proper; `Cure.toml` is the
" project manifest and is best edited as TOML.

au BufRead,BufNewFile *.cure    set filetype=cure
au BufRead,BufNewFile Cure.toml set filetype=toml
