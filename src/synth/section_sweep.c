/* section_sweep.c
 * T18 prep: a bounded whole-region operation — a loop that reads AND
 * writes EVERY byte of one .data object (the whole-section-sweep
 * constraint shape: the sweep's range is a partition member that merges
 * whatever components the per-object accesses would have carved inside
 * the swept object) alongside normal per-object accesses to distinct
 * neighbors, which stay separate components.
 * The volatile key keeps the transform runtime at -O2. */

#include <stdio.h>

/* the swept object: nonzero initializer bytes across the array (.data) */
static unsigned char sweep[128] = {
    1,   2,   3,   4,   5,   6,   7,   8,   9,   10,  11,  12,  13,  14,  15,  16,
    0,   0,   27,  28,  0,   0,   31,  32,  0,   0,   35,  36,  0,   0,   39,  40,
    41,  42,  0,   0,   45,  46,  0,   0,   49,  50,  0,   0,   53,  54,  0,   0,
    57,  58,  0,   0,   61,  62,  0,   0,   65,  66,  0,   0,   69,  70,  0,   0,
    73,  74,  0,   0,   77,  78,  0,   0,   81,  82,  0,   0,   85,  86,  0,   0,
    89,  90,  0,   0,   93,  94,  0,   0,   97,  98,  0,   0,   101, 102, 0,   0,
    105, 106, 0,   0,   109, 110, 0,   0,   113, 114, 0,   0,   117, 118, 0,   0,
    121, 122, 0,   0,   125, 126, 0,   0,   129, 130, 0,   0,   133, 0,   0,   200,
};

/* distinct per-object neighbors, accessed at constant/runtime scalars */
static unsigned char before[16] = { 9, 8, 7, 6, 5, 4, 3, 2 };
static unsigned long after = 0x1234567UL;

int main(void) {
    volatile unsigned char key = 0x5a;
    volatile unsigned idx = 3;
    unsigned long acc = 0, acc2 = 0;

    /* normal per-object accesses alongside the sweep */
    before[idx] += 1;
    after += 9;

    /* THE SWEEP: every byte of sweep[] read then written (runtime bound) */
    for (unsigned i = 0; i < 128; ++i) {
        unsigned char v = sweep[i];
        sweep[i] = (unsigned char)(v * 31u + key);
        acc += v;
    }
    /* second pass reads back the transformed bytes */
    for (unsigned i = 0; i < 128; ++i)
        acc2 += sweep[i];

    printf("acc=%lu acc2=%lu b=%u a=%lu\n", acc, acc2, before[idx], after);
    return 0;
}
