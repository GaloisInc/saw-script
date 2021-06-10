" a function that overrides vim-slime's default behavior:
function SlimeOverride_EscapeText_saw(text)
  " create temp buffer
  split __saw_slime_temp_buffer__
  setlocal buftype=nofile
  " paste text in buffer
  set paste
  exe "normal! i" . a:text . "\<Esc>"
  set nopaste
  " remove blank things
  silent! keepp g/^\s*\n/d
  silent! keepp g/^\n/d
  silent! keepp g/^\s*\/\/.*\n/d
  silent! keepp %s/\(\/\/.*\)$//eg " remove end-of-line comments
  " copy buffer contents into res, adding a backslash at the end of each line
  let res = join(getline(1, '$'), "\\\n")
  " q " close scratch split
  bdelete __saw_slime_temp_buffer__ " delete temp buffer (the following didn't work reliably: setlocal bufhidden=delete)
  return res . "\n"
endfunction
