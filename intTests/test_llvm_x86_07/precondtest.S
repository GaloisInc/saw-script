section .bss
section .text
global precondtest
precondtest:
	mov rax, rdi
        ret
global _start
_start:
        mov rax, 60
        syscall
