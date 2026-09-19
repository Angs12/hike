/* fn_table_disp.c
 * T4 stress: handler-table dispatch with STACK-passed arguments.
 * Three handlers take eight long arguments each — beyond the six SysV
 * integer registers, so the last two flow through the outgoing stack
 * area at -O0 (the promotion class).  The dispatch is
 * handlers[opcode](a,...,h) with a RUNTIME opcode: the VSA sees a
 * bounded multi-target set (never a singleton), so every site takes
 * the pointer call into the handlers' memory-convention thunks, while
 * the thunks forward the unpacked window slots into the promoted
 * bodies.  The result checksum makes the whole round trip observable. */
#include <stdio.h>

__attribute__((noinline)) static long h0(long a, long b, long c, long d,
                                         long e, long f, long g, long h) {
    long l1 = a + g; /* g, h arrive on the stack at -O0 */
    long l2 = b * h;
    return l1 + l2 + c + d + e + f + 1;
}

__attribute__((noinline)) static long h1(long a, long b, long c, long d,
                                         long e, long f, long g, long h) {
    long l1 = a ^ (g + 3);
    long l2 = (b + h) * 2;
    return l1 + l2 + c - d + e + f + 2;
}

__attribute__((noinline)) static long h2(long a, long b, long c, long d,
                                         long e, long f, long g, long h) {
    long l1 = (a - g) * 3;
    long l2 = b ^ (h + 1);
    return l1 + l2 + c + d - e + f + 3;
}

int main(void) {
    long (*handlers[3])(long, long, long, long, long, long, long, long) = {
        h0, h1, h2
    };
    long acc = 0;
    for (long i = 0; i < 9; i++) {
        long op = (i * 5 + 2) % 3; /* runtime index: a multi-target set */
        acc += handlers[op](i, i + 1, i + 2, i + 3,
                            i + 4, i + 5, i + 6, i + 7);
    }
    printf("fn_table_disp: acc=%ld\n", acc);
    return 0;
}
