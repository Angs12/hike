#include <stdio.h>
#include <stdarg.h>

/* STRESS: va_copy handling — iterate the SAME va_list twice.
 * First pass (over the original list) sums the args; a va_copy taken
 * before the first pass is used for a second, independent pass that
 * prints each value. */

static int two_pass(int count, ...) {
    va_list ap, ap2;
    va_start(ap, count);
    va_copy(ap2, ap);               /* snapshot before first pass consumes */

    int sum = 0;
    for (int i = 0; i < count; i++) /* pass 1: sum */
        sum += va_arg(ap, int);
    va_end(ap);

    printf("second pass:");
    for (int i = 0; i < count; i++) /* pass 2: print (same values) */
        printf(" %d", va_arg(ap2, int));
    printf("\n");
    va_end(ap2);
    return sum;
}

int main(void) {
    int total = 0;
    for (int i = 0; i < 3; i++) {
        /* 6 varargs: 5 fit in GPRs after 'count', the 6th spills to the
         * stack — exercises both register save area and stack spill */
        total += two_pass(6, i + 1, i + 2, i + 3, i + 4, i + 5, i + 6);
    }
    printf("total = %d\n", total);
    return 0;
}
