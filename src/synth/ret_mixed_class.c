/* Aggregates whose two eightbytes fall in different SysV classes:
 * {long, double} returns in RAX and XMM0, {double, long} in XMM0 and
 * RAX.  Each half depends on runtime inputs, and each result feeds the
 * next call so both lanes stay live at -O2. */

#include <stdio.h>

typedef struct { long l; double d; } LD;
typedef struct { double d; long l; } DL;

__attribute__((noinline)) static LD make_ld(long a, double b) {
    LD r = { a * 3 + 1, b * 0.5 + 2.0 };
    return r;
}

__attribute__((noinline)) static DL make_dl(double a, long b) {
    DL r = { a * 2.0 - 1.0, b * 5 + 2 };
    return r;
}

int main(void) {
    volatile long x = 11;
    volatile double y = 6.0;
    LD p = make_ld(x, y);
    DL q = make_dl(p.d, p.l);
    LD r = make_ld(q.l, q.d);
    printf("p=%ld,%.3f q=%.3f,%ld r=%ld,%.3f\n", p.l, p.d, q.d, q.l, r.l, r.d);
    return 0;
}
