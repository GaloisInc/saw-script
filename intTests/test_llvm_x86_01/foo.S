global foo
foo:
        mov rax, [rdi]
        add rsi, rax
        mov [rdi], rsi
        ret
global _start
_start:
        mov rax, 60
        syscall
