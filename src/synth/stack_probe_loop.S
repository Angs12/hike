.text
.globl main
.type main,@function
main:
 sub $48,%rsp
 lea -0x2000(%rsp),%r11
.Lprobe:
 sub $0x1000,%rsp
 cmp %r11,%rsp
 jne .Lprobe
 add $0x2030,%rsp
 ret
.size main,.-main
.section .note.GNU-stack,"",@progbits
