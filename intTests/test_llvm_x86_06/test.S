section .bss
section .text
foo:
	ret
global discoverytest
discoverytest:
        lea rax, [rsp]
	call foo
        lea rsp, [rax]
        ret
global _start
_start:
        mov rax, 60
        syscall
