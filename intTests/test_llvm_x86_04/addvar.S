section .bss
global var
var:    resq 1
section .text
global addvar
addvar:
        mov rax, [rdi]
        mov rbx, var
        add rax, 1
        mov [rdi], rax
        ret
global _start
_start:
        mov rax, 60
        syscall
