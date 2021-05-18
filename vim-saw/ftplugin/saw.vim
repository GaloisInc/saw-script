" mappings to copy top-level statements that can then be pasted in a SAW REPL
" running in a vim terminal window
nnoremap <C-c> vip:call Join_and_copy(visualmode())<CR><CR>
nnoremap <C-y> vip:call Copy(visualmode())<CR><CR>

" a mapping to paste in terminal mode:
tnoremap <C-p> <C-w>""
