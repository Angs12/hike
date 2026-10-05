/*
 * flag_idioms.c
 * Stress pattern: constant-flag and constant-combination jcc idioms the
 * jump compiler's atom and combine rules must consume.  The inline asm
 * forces shapes the compilers do not emit from plain C:
 *   xor; jz     -> ZF := 1 consumed as a constant-true atom
 *   xor; jb     -> CF := 0 consumed as a constant-false atom
 *   xor; jbe    -> CF|ZF of two constants (const/const combine)
 *   or v,v; jbe -> CF const false | ZF relation (const/relation combine)
 * Every branch outcome is fixed by the idiom, so the output is stable.
 */
#include <stdio.h>

int main(void) {
    unsigned long x = 0;
    __asm__ volatile(
        "xorl %%eax, %%eax\n\t"
        "jz 1f\n\t"
        "movq $1, %0\n"
        "1:\n\t"
        : "+r"(x)
        :
        : "eax", "cc");
    unsigned long y = 0;
    __asm__ volatile(
        "xorl %%eax, %%eax\n\t"
        "jb 2f\n\t"
        "movq $1, %0\n"
        "2:\n\t"
        : "+r"(y)
        :
        : "eax", "cc");
    unsigned long z = 0;
    __asm__ volatile(
        "xorl %%eax, %%eax\n\t"
        "jbe 3f\n\t"
        "movq $1, %0\n"
        "3:\n\t"
        : "+r"(z)
        :
        : "eax", "cc");
    volatile unsigned long v = 7;
    unsigned long w = 0;
    __asm__ volatile(
        "orl %1, %1\n\t"
        "jbe 4f\n\t"
        "movq $1, %0\n"
        "4:\n\t"
        : "+r"(w)
        : "r"((unsigned)v)
        : "cc");
    printf("flag_idioms: %lu %lu %lu %lu\n", x, y, z, w);
    return 0;
}
