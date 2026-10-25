/* long_double.c
 * Stress: x87 extended precision (long double).  Parsing through
 * strtold (an ST0 return), arithmetic in every operand form, compares
 * that branch on fcomi/fucomi flags, integer and float conversions in
 * both directions (fild, fistp under the truncating control word,
 * fld/fstp of float and double), a long double returned in ST0 across
 * a lifted call, and printf of long double arguments.  Every input crosses a
 * volatile boundary so the x87 code survives -O2. */

#include <stdio.h>
#include <stdlib.h>

volatile long double lx = 2.5L;
volatile long double ly = -0.1L;
volatile double dz = 1.0 / 3.0;
volatile float fz = 0.1f;
volatile long long ix = 1234567890123LL;
volatile int iy = -7;
volatile short sz = 300;
volatile const char *text = "3.14159265358979323846264338327950288";

__attribute__((noinline)) long double scale(long double a, long double b) {
    return a * b + a / b - (b - a);
}

__attribute__((noinline)) long double pick(long double a, long double b) {
    return a < b ? a : b;
}

int main(void) {
    long double parsed = strtold((const char *)text, NULL);
    long double a = lx, b = ly;

    printf("parsed=%.18Lf\n", parsed);
    printf("sum=%.18Lf diff=%.18Lf\n", a + b, a - b);
    printf("prod=%.18Lf quot=%.18Lf\n", a * b, a / b);
    printf("scale=%.18Lf pick=%.18Lf\n", scale(a, b), pick(a, b));
    printf("mixed=%.18Lf\n", a * dz + b * fz - (long double)iy * sz);

    printf("lt=%d le=%d eq=%d ne=%d\n", a < b, b <= a, a == b, a != parsed);

    long double ints = (long double)ix + (long double)iy;
    printf("ints=%.3Lf\n", ints);

    printf("trunc=%lld %d\n", (long long)(a * 3.0L), (int)(b * 25.0L));

    double d = (double)parsed;
    float f = (float)parsed;
    printf("narrow=%.17g %.9g\n", d, f);
    return 0;
}
