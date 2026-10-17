/* FP arguments and an FP return: a function taking four doubles and a
 * double/int mix returns its value in YMM0 (the SysV FP return), the
 * callers keep the FP lanes live across the call, and one call site
 * goes through a volatile so nothing folds at -O2. */

#include <stdio.h>

static double mix4(double a, double b, double c, double d) {
    return a * 0.5 + b * 0.25 + c - d;
}

static double fact_f(double x) {
    double r = 1.0;
    for (int i = 2; i <= 6; i++) r *= (double)i;
    return r + x;
}

int main(void) {
    volatile double x = 2.0;
    volatile double y = 4.0;
    double r1 = mix4(x, y, 1.5, 0.25);
    double r2 = fact_f(r1);
    double r3 = mix4(r2, r1, r1, r2);
    printf("r1=%.4f r2=%.4f r3=%.4f\n", r1, r2, r3);
    return 0;
}
