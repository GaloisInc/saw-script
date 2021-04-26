global increment
increment:
        mov rax, [rdi]
        add rax, 1
        mov [rdi], rax
        ret
global _start
_start:
        mov rax, 60
        syscall
