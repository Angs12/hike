/*
 * tail_callish.c
 * Stress pattern: tail-position calls with stack args.
 * a -> b -> c -> d, where every return is exactly the result of a
 * call in tail position and every link passes stack arguments,
 * driven by a runtime value. gcc -O0 will not tail-call optimize
 * these, so each link remains a real call with a fresh frame.
 */
#include <stdio.h>

static unsigned long d(unsigned long x, unsigned long y) {
    unsigned long t1 = x * 2;
    unsigned long t2 = y + 1;
    return t1 + t2;
}

static unsigned long c(unsigned long x) {
    unsigned long u = x + 3;
    return d(u, x);
}

static unsigned long b(unsigned long x) {
    unsigned long w = x + 5;
    return c(w);
}

static unsigned long a(unsigned long x) {
    unsigned long z = x + 7;
    return b(z);
}

int main(void) {
    volatile unsigned long rseed = 80;  /* stack local; prevents constant folding */
    unsigned long seed = rseed + 4;     /* runtime seed, read from the stack */
    unsigned long r = a(seed);
    printf("tail_callish: result=%lu\n", r);
    return 0;
}
