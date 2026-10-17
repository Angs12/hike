/* bss_arrays.c
 * T18 prep: .bss objects — an array, a scalar, a double, a byte array —
 * all zero-init, written at runtime indices, then read back.
 * The zero-init proof (read BEFORE any write) pins the zero-initializer
 * semantics of a carved .bss component (`internal global T
 * zeroinitializer`); the runtime writes pin the write-closed rule (a
 * component converts together or not at all); the untouched bytes print
 * their zero-init.  Volatile indices keep the accesses runtime at -O2. */

#include <stdio.h>
#include <string.h>

static long b_arr[64];
static int b_scalar;
static double b_d;
static unsigned char b_bytes[32];

static unsigned long bits_of(double d) {
    unsigned long u;
    memcpy(&u, &d, sizeof u);
    return u;
}

int main(void) {
    volatile int k = 9;
    unsigned long sum = 0;

    /* zero-init proof: read every .bss object BEFORE any write */
    unsigned long zero_sum = 0;
    for (int i = 0; i < 64; i++)
        zero_sum += (unsigned long)b_arr[i];
    zero_sum += (unsigned long)(unsigned)b_scalar;
    zero_sum += b_bytes[0] + b_bytes[31];
    zero_sum += bits_of(b_d);

    /* runtime writes (the write-closed components) */
    for (int i = 0; i < 64; i++)
        b_arr[i] = 3 * i + 1;
    b_scalar = -7;
    b_d = 0.125;
    b_bytes[k] = 200;
    b_bytes[31] = 14;

    /* read back */
    for (int i = 0; i < 64; i++)
        sum += (unsigned long)b_arr[i];
    sum += (unsigned long)(unsigned)b_scalar;
    sum += bits_of(b_d);
    sum += b_bytes[k];
    sum += b_bytes[0]; /* the untouched byte keeps its zero-init */

    printf("zero=%lu sum=%lu b0=%u b9=%u\n",
           zero_sum, sum, b_bytes[0], b_bytes[k]);
    return 0;
}
