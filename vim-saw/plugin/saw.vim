" a function that overrides vim-slime's default behavior:
function SlimeOverride_EscapeText_saw(text)
  " create temp buffer
  keepalt split __saw_slime_temp_buffer__
  setlocal buftype=nofile
  setlocal bufhidden=delete
  " paste text in buffer
  set paste
  exe "normal! i" . a:text . "\<Esc>"
  set nopaste
  " remove blank things:
  silent! keepp g/^\s*\n/d
  silent! keepp g/^\n/d
  silent! keepp g/^\s*\/\/.*\n/d
  silent! keepp %s/\/\/.*$//eg " remove end-of-line comments
  let res = join(getline(1, '$'), "\\\n") " copy buffer contents into res, adding a backslash at the end of each line
  bdelete __saw_slime_temp_buffer__ " delete temp buffer
  return res . "\n"
endfunction
