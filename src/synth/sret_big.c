#include <stdio.h>

/* STRESS: sret stack-arg convention — a 96-byte struct (12 longs) is
 * returned BY VALUE from a callee, forcing the hidden sret pointer
 * argument on x86-64 SysV. The caller then indexes the returned struct
 * with a runtime index (also dynamic-GEP) and prints a checksum. */

typedef struct { long v[12]; } Big; /* 96 bytes > 16 -> sret */

static Big build(int base) {
    Big b; /* local struct that gets copied out through the sret slot */
    for (int i = 0; i < 12; i++)
        b.v[i] = (long)(base + i) * (base + i + 1);
    return b;
}

static long checksum(Big *b, int n) {
    long cs = 0;
    for (int i = 0; i < n; i++)
        cs += b->v[i % 12] * (i + 1); /* runtime index into sret struct */
    return cs;
}

int main(void) {
    Big a = build(3);
    Big c = build(7);
    long cs = checksum(&a, 17) + checksum(&c, 23);
    printf("checksum = %ld\n", cs);
    return 0;
}
