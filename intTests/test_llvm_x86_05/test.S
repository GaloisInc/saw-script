section .bss
section .text
global returntest
returntest:
        mov rax, 42
        ret
global _start
_start:
        mov rax, 60
        syscall
