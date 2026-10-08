/* switch_shared_case.c
 * A jump-table case block with two predecessors: case 0 sets the
 * compared registers to constants and falls into case 1, which the
 * table also reaches directly.  The BIR names only the fallthrough as
 * case 1's edge; the dispatch edge exists only as the resolved table
 * destination.  A walk that took the fallthrough for case 1's only
 * predecessor folds case 1's compare to case 0's constants, so a
 * direct entry with x >= y would take the x < y arm.  Hand-written so
 * the shared block survives every compiler and level. */
#include <stdio.h>

int sel(int k, int a, int b);

__asm__(
    ".text\n"
    ".globl sel\n"
    ".type sel, @function\n"
    "sel:\n"
    "  movl %edi, %edi\n"
    "  cmpq $2, %rdi\n"
    "  ja .Lsel_def\n"
    "  movl %esi, %eax\n"
    "  movl %edx, %ecx\n"
    "  leaq .Lsel_tbl(%rip), %rdx\n"
    "  movslq (%rdx,%rdi,4), %rsi\n"
    "  addq %rsi, %rdx\n"
    "  jmp *%rdx\n"
    ".Lsel_c0:\n"
    "  movl $3, %eax\n"
    "  movl $5, %ecx\n"
    ".Lsel_c1:\n"
    "  cmpl %ecx, %eax\n"
    "  jl .Lsel_lt\n"
    "  leal 200(%rcx), %eax\n"
    "  ret\n"
    ".Lsel_lt:\n"
    "  leal 100(%rax), %eax\n"
    "  ret\n"
    ".Lsel_c2:\n"
    "  movl $300, %eax\n"
    "  ret\n"
    ".Lsel_def:\n"
    "  movl $-1, %eax\n"
    "  ret\n"
    ".size sel, .-sel\n"
    ".section .rodata\n"
    ".p2align 2\n"
    ".Lsel_tbl:\n"
    "  .long .Lsel_c0-.Lsel_tbl\n"
    "  .long .Lsel_c1-.Lsel_tbl\n"
    "  .long .Lsel_c2-.Lsel_tbl\n"
    ".text\n");

int main(void) {
    long acc = 0;
    for (int i = 0; i < 12; i++) {
        int r = sel(i % 4, i, 6 - i);
        printf("sel(%d)=%d\n", i % 4, r);
        acc += r;
    }
    printf("switch_shared_case: acc=%ld\n", acc);
    return 0;
}
