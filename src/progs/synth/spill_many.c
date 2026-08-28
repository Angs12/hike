/*
 * spill_many.c
 * Stress pattern: heavy memory-op density (register spills at -O0).
 * ~24 local unsigned longs plus two local structs are initialized and
 * re-read/re-written in shuffled order with interleaved arithmetic so
 * many values are simultaneously live; a folded checksum is printed.
 */
#include <stdio.h>

struct pair { unsigned long x; unsigned long y; };

static unsigned long hammer(unsigned long seed) {
    unsigned long v0, v1, v2, v3, v4, v5, v6, v7, v8, v9;
    unsigned long v10, v11, v12, v13, v14, v15, v16, v17, v18, v19;
    unsigned long v20, v21, v22, v23;
    struct pair s1, s2;
    unsigned long acc;

    /* shuffled init: each statement reads a variable written earlier */
    v0  = seed + 1;
    v17 = v0 * 3;
    v5  = v17 ^ 0x9e3779b97f4a7c15UL;
    v11 = v5 + 9;
    v2  = v11 << 4;
    v20 = v2 - 13;
    v8  = v20 * 7;
    s1.x = v8 + 2;
    s1.y = v8 * 3;
    v14 = s1.x + s1.y;
    v23 = v14 >> 2;
    v3  = v23 * 11;
    v9  = v3 + 5;
    v18 = v9 ^ 0xbf58476d1ce4e5b9UL;
    v6  = v18 - 17;
    v12 = v6 << 2;
    v21 = v12 + 19;
    v0  = v21 ^ v5;
    v15 = v0 * 3;
    v1  = v15 + 7;
    v10 = v1 >> 1;
    v19 = v10 * 5;
    v4  = v19 - 11;
    v16 = v4 ^ v8;
    v22 = v16 + 23;
    v7  = v22 * 2;
    v13 = v7 - 3;
    s2.x = v13 + v0;
    s2.y = v13 * v22;

    /* pass 1: shuffled arithmetic over many simultaneously live values */
    v1  = v1 + v23 + s2.y;
    v9  = v9 * v14 + v2;
    v17 = v17 ^ v6 ^ v11;
    v5  = v5 + v20 * 2;
    v21 = v21 - v3 + v12;
    s1.x = s1.x * 3 + v16;
    v7  = v7 + (v15 ^ v18);
    v13 = v13 * 5 + v4;
    v22 = v22 ^ (v10 + v19);
    v2  = v2 + v8 * v23;

    /* pass 2: interleaved reads/writes, shuffled order */
    v0  = v13 + v21;
    v14 = v5 ^ v1;
    v23 = v9 * 3 + v7;
    v3  = v17 - v22;
    v18 = v12 ^ v2;
    s2.x = s2.x + v0;
    v11 = v11 * 7 + v14;
    v16 = v16 ^ v23;
    v8  = v8 + v3 * 2;
    v20 = v20 - v18;
    v6  = v6 ^ v11;
    v15 = v15 + v16;
    v12 = v12 * v8;
    v19 = v19 ^ v20;
    v4  = v4 + v6 * 3;
    s2.y = s2.y - v15;
    v10 = v10 ^ v12;

    /* fold every live value into the checksum */
    acc = v0;
    acc = acc * 31 + v1;
    acc = acc * 31 + v2;
    acc = acc * 31 + v3;
    acc = acc * 31 + v4;
    acc = acc * 31 + v5;
    acc = acc * 31 + v6;
    acc = acc * 31 + v7;
    acc = acc * 31 + v8;
    acc = acc * 31 + v9;
    acc = acc * 31 + v10;
    acc = acc * 31 + v11;
    acc = acc * 31 + v12;
    acc = acc * 31 + v13;
    acc = acc * 31 + v14;
    acc = acc * 31 + v15;
    acc = acc * 31 + v16;
    acc = acc * 31 + v17;
    acc = acc * 31 + v18;
    acc = acc * 31 + v19;
    acc = acc * 31 + v20;
    acc = acc * 31 + v21;
    acc = acc * 31 + v22;
    acc = acc * 31 + v23;
    acc = acc * 31 + s1.x;
    acc = acc * 31 + s1.y;
    acc = acc * 31 + s2.x;
    acc = acc * 31 + s2.y;
    return acc;
}

int main(void) {
    volatile unsigned long rseed = 170;  /* stack local; prevents constant folding */
    unsigned long seed = rseed + 3;      /* runtime seed, read from the stack */
    unsigned long ck = hammer(seed);
    printf("spill_many: checksum=%lu\n", ck);
    return 0;
}
