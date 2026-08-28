/*
 * fptr_table.c
 * Stress pattern: indirect calls through function pointers.
 * An array of 4 function pointers (each callee has its own stack
 * locals and takes stack arguments) is dispatched through a runtime
 * index computed from a loop counter; results are accumulated and a
 * checksum is printed.
 */
#include <stdio.h>

static unsigned long fn0(unsigned long a, unsigned long b) {
    unsigned long l1 = a + 1;
    unsigned long l2 = b * 2;
    return l1 + l2 + 3;
}

static unsigned long fn1(unsigned long a, unsigned long b) {
    unsigned long t1 = a * 3;
    unsigned long t2 = b ^ 0x55UL;
    return t1 + t2 + 7;
}

static unsigned long fn2(unsigned long a, unsigned long b) {
    unsigned long u1 = a ^ b;
    unsigned long u2 = a * b;
    return u1 + u2 + 11;
}

static unsigned long fn3(unsigned long a, unsigned long b) {
    unsigned long w1 = a * 2;
    unsigned long w2 = b * 3;
    return (w1 ^ w2) + 13;
}

int main(void) {
    unsigned long (*tbl[4])(unsigned long, unsigned long) = { fn0, fn1, fn2, fn3 };
    unsigned long acc = 0;
    unsigned long i;

    for (i = 0; i < 12; i++) {
        unsigned long idx = (i * 7 + 3) % 4;   /* runtime index, not a constant */
        unsigned long arg = i * 13 + 5;        /* runtime argument */
        acc += tbl[idx](arg, arg + 2);         /* indirect call through pointer */
    }
    printf("fptr_table: checksum=%lu\n", acc);
    return 0;
}
