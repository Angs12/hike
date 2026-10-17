/* An aggregate returned in the SysV SSE class: two doubles come back in
 * XMM0:XMM1.  The second value depends on the first, so the compiler
 * keeps the arithmetic scalar and the pair is only ever split across the
 * two return registers.  The inputs ride volatiles so nothing folds at
 * -O2, and each result feeds the next call so both lanes stay live. */

#include <stdio.h>

typedef struct { double a, b; } DPair;

__attribute__((noinline, optimize("no-tree-vectorize", "no-tree-slp-vectorize")))
static DPair scale(double x, double y) {
    DPair p;
    p.a = x * 1.5 + 1.0;
    p.b = p.a * y * 0.25 - 2.0;
    return p;
}

int main(void) {
    volatile double x = 3.0, y = 8.0;
    DPair p = scale(x, y);
    DPair q = scale(p.b, p.a);
    DPair r = scale(q.b, q.a);
    printf("p=%.3f,%.3f q=%.3f,%.3f r=%.3f,%.3f\n", p.a, p.b, q.a, q.b, r.a, r.b);
    return 0;
}
