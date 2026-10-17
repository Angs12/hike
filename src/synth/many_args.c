#include <stdio.h>

/* STRESS: stack argument area beyond register args — a function taking
 * TWELVE int arguments. On x86-64 SysV only the first 6 go in GPRs;
 * args 7-12 are spilled onto the caller's stack. main passes
 * loop-derived values. */

static long sum12(int a1, int a2, int a3, int a4, int a5, int a6,
                  int a7, int a8, int a9, int a10, int a11, int a12) {
    return (long)a1 + a2 + a3 + a4 + a5 + a6
         + a7 + a8 + a9 + a10 + a11 + a12;
}

int main(void) {
    long total = 0;
    for (int i = 0; i < 5; i++) {
        total += sum12(i,     i + 1,  i + 2,  i + 3,  i + 4,  i + 5,
                       i + 6, i + 7,  i + 8,  i + 9,  i + 10, i + 11);
    }
    printf("sum = %ld\n", total);
    return 0;
}
