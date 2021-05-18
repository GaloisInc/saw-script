" mappings to copy top-level statements that can then be pasted in a SAW REPL
" running in a vim terminal window
nnoremap <C-c> vip:<C-u>call Join_and_copy(visualmode())<CR><CR>
nnoremap <C-y> vip:<C-u>call Copy(visualmode())<CR><CR>
vnoremap <C-c> :<C-u>call Join_and_copy(visualmode())<CR><CR>
vnoremap <C-y> :<C-u>call Copy(visualmode())<CR><CR>
" a mapping to paste in terminal mode:
tnoremap <C-p> <C-w>""
