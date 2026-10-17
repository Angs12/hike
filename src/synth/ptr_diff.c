/* ptr_diff.c
 * T18 prep: pointer difference WITHIN one object (the base cancels —
 * exact at any granularity, printed directly) and ACROSS two adjacent
 * objects (two section bases in one subtraction — the case that forces
 * the merge rule; printed only through what the ABI guarantees: the
 * byte difference of two 8-aligned objects is a multiple of 8, and the
 * objects are distinct).  The within-object diff also drives a
 * runtime-indexed access — anchored arithmetic propagates the anchor.
 * The volatile indices keep every difference a runtime computation. */

#include <stdio.h>
#include <stdint.h>

static long pa[32] = { 1,   2,   3,   4,   5,   6,   7,   8,
                       9,   10,  11,  12,  13,  14,  15,  16,
                       17,  18,  19,  20,  21,  22,  23,  24,
                       25,  26,  27,  28,  29,  30,  31,  32 };
static long pb[32] = { 100, 101, 102, 103, 104, 105, 106, 107,
                       108, 109, 110, 111, 112, 113, 114, 115,
                       116, 117, 118, 119, 120, 121, 122, 123,
                       124, 125, 126, 127, 128, 129, 130, 131 };

int main(void) {
    volatile int i = 5, j = 20;

    /* within-object difference: 15 elements, ABI-stable */
    long d_in = &pa[j] - &pa[i];

    /* the diff drives runtime-indexed accesses in BOTH objects */
    pa[i + d_in] += 100; /* pa[j] */
    pb[j - d_in] += d_in; /* pb[i] */

    /* cross-object difference: two section bases, one subtraction —
     * the merge-rule shape.  Normalized prints only. */
    long d_cross = (long)((uintptr_t)&pb[0] - (uintptr_t)&pa[0]);
    int cross_mod8 = (int)(d_cross % 8); /* 0: alignment-guaranteed */
    int cross_nonzero = (d_cross != 0);  /* 1: distinct objects */

    unsigned long sum = 0;
    for (int t = 0; t < 32; ++t)
        sum += (unsigned long)pa[t] + (unsigned long)pb[t];

    printf("d_in=%ld sum=%lu cross_mod8=%d cross_nonzero=%d\n",
           d_in, sum, cross_mod8, cross_nonzero);
    return 0;
}
