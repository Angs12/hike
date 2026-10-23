/* Stack arguments pushed in blocks that precede the call block.  The
   function is written in assembly so the compiler cannot fold the
   branch: one stack argument is pushed in the entry block, the other in
   one of two sibling blocks, and the call block pushes nothing. */
#include <stdio.h>

__asm__(
    ".text\n"
    ".globl hike_pred_printf\n"
    ".type hike_pred_printf, @function\n"
    "hike_pred_printf:\n"
    "    pushq %rbp\n"
    "    movq %rsp, %rbp\n"
    "    subq $8, %rsp\n"
    "    pushq $7\n"
    "    testl %edi, %edi\n"
    "    je 1f\n"
    "    pushq $6\n"
    "    jmp 2f\n"
    "1:  pushq $60\n"
    "2:  leaq hike_pred_fmt(%rip), %rdi\n"
    "    movl $1, %esi\n"
    "    movl $2, %edx\n"
    "    movl $3, %ecx\n"
    "    movl $4, %r8d\n"
    "    movl $5, %r9d\n"
    "    xorl %eax, %eax\n"
    "    call printf@PLT\n"
    "    movq %rbp, %rsp\n"
    "    popq %rbp\n"
    "    ret\n"
    ".size hike_pred_printf, .-hike_pred_printf\n"
    ".section .rodata\n"
    "hike_pred_fmt:\n"
    "    .string \"%ld %ld %ld %ld %ld %ld %ld\\n\"\n"
    ".text\n");

void hike_pred_printf(int select);

int main(void) {
  hike_pred_printf(1);
  hike_pred_printf(0);
  return 0;
}
