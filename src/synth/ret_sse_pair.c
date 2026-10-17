/* Aggregates returned in the SysV SSE class: two eightbytes of doubles
 * (XMM0:XMM1) and four floats packed two per eightbyte (XMM0:XMM1).
 * The inputs ride volatiles so nothing folds at -O2, and each result
 * feeds the next call so both lanes stay live. */

#include <stdio.h>

typedef struct { double a, b; } DPair;
typedef struct { float a, b, c, d; } F4;

__attribute__((noinline)) static DPair scale(double x, double y) {
    DPair p = { x * 1.5 + 1.0, y * 0.25 - 2.0 };
    return p;
}

__attribute__((noinline)) static F4 lanes(float x, float y) {
    F4 r = { x + 1.0f, y * 2.0f, x - y, x * y };
    return r;
}

int main(void) {
    volatile double x = 3.0, y = 8.0;
    volatile float u = 1.5f, v = 4.0f;
    DPair p = scale(x, y);
    DPair q = scale(p.b, p.a);
    F4 f = lanes(u, v);
    F4 g = lanes(f.c, f.d);
    printf("p=%.3f,%.3f q=%.3f,%.3f\n", p.a, p.b, q.a, q.b);
    printf("f=%.3f,%.3f,%.3f,%.3f g=%.3f,%.3f,%.3f,%.3f\n",
           f.a, f.b, f.c, f.d, g.a, g.b, g.c, g.d);
    return 0;
}
