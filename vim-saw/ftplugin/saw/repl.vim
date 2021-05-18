function Join_and_copy(type)
  if a:type ==# 'V' " only do stuff in line-wise visual mode
    normal! `<v`>y
    split __scratch__
    setlocal buftype=nofile
    setlocal bufhidden=delete
    normal! p
    call DeleteBlank()
    " join lines and yank:
    normal! ggVGJyy
    q " close scratch split
  endif
endfunction

function DeleteBlank()
  %g/^\s*\n/d
  %g/^\n/d
  %g/^\s*\/\/.*\n/d
  %s/\/\/.*\n/\r/eg " remove end-of-line comments
endfunction


function Copy(type)
  if a:type ==# 'V' " only do stuff in line-wise visual mode
    normal! `<v`>y
    split __scratch__
    setlocal buftype=nofile
    setlocal bufhidden=delete
    normal! p
    call DeleteBlank()
    %s/\n/\\\r/g " add backslash at end of lines
    " remove last line (is blank)
    normal! Gdd
    " remove backslash at end of (new) last line:
    normal! G$x
    " yank:
    normal! ggVGy
    q " close scratch split
  endif
endfunction
