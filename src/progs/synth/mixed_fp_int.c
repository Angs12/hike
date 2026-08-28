#include <stdio.h>

/* STRESS: mixed FP/int calling convention — a function taking alternating
 * int/double arguments, so GPRs and XMM registers are both used for
 * argument passing. It returns a combined value: sum of the int args
 * plus the sum of the (cast) double args. */

static double combine(int a, double b, int c, double d,
                      int e, double f, int g, double h) {
    double ints = (double)(a + c + e + g);
    double fps = b + d + f + h;
    return ints + fps;
}

int main(void) {
    double total = 0.0;
    for (int i = 0; i < 4; i++) {
        total += combine(i * 2,     (double)i * 0.5,
                         i * 2 + 1, (double)i * 1.5,
                         i * 2 + 2, (double)i * 2.5,
                         i * 2 + 3, (double)i * 3.5);
    }
    printf("total = %.1f\n", total);
    return 0;
}
