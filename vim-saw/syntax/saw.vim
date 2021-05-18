syn keyword SAWKeyword do let include import
hi link SAWKeyword Keyword
setlocal commentstring=//%s " is this useless? the doc says only used for folding
setlocal comments=s1:/*,mb:*,ex:*/,://"
syntax match SAWComment "\v//.*$" contains=@Spell
syntax region SAWComment start="/\*" end="\*/" contains=@Spell
highlight link SAWComment Comment
setlocal formatoptions=tcqr
