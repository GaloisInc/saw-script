global foo
foo:
        mov rax, 42
        ret
global _start
_start:
        mov rax, 60
        syscall
