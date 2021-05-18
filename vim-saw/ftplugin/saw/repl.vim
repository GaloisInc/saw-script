function Join_and_copy(type)
  if a:type ==# 'V' " only do stuff in line-wise visual mode
    normal! `<v`>y
    split __scratch__
    setlocal buftype=nofile
    setlocal bufhidden=delete
    normal! p
    normal! Gdd
    %s/^\s*\/\/.*\n//eg " delete blank lines
    %s/\/\/.*\n/\r/eg " remove end-of-line comments
    " join lines and yank:
    normal! ggVGJyy
    q " close scratch split
  endif
endfunction

function Copy(type)
  if a:type ==# 'V' " only do stuff in line-wise visual mode
    normal! `<v`>y
    split __scratch__
    setlocal buftype=nofile
    setlocal bufhidden=delete
    normal! p
    normal! Gdd
    %s/^\s*\/\/.*\n//eg " delete blank lines
    %s/\/\/.*\n/\r/eg " remove end-of-line comments
    %s/\n/\\\r/g " add backslash at end of lines
    " remove backslash at end of last line:
    normal! G$x
    " yank:
    normal! ggVGy
    q " close scratch split
  endif
endfunction
