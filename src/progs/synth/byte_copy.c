/*
 * byte_copy.c
 * Stress pattern: byte-granular stack memory ops.
 * A byte-wise copy loop moves data between two stack buffers with a
 * runtime length (derived via strlen); the destination buffer is
 * checksummed byte by byte and the checksums are printed.
 */
#include <stdio.h>

static unsigned long copy_bytes(char *dst, const char *src, unsigned long n) {
    unsigned long i;
    unsigned long cksum = 0;

    for (i = 0; i < n; i++) {
        dst[i] = src[i];                 /* byte-granular store */
    }
    for (i = 0; i < n; i++) {
        cksum = cksum * 33 + (unsigned long)(unsigned char)dst[i];
    }
    return cksum;
}

int main(void) {
    char src[64];
    char dst[64];
    unsigned long i;
    volatile unsigned long rlen = 64;  /* stack local; prevents constant folding */
    unsigned long L = rlen;            /* runtime length, read from the stack */
    unsigned long len1, len2, ck1, ck2;

    for (i = 0; i < L; i++) {
        src[i] = (char)((i * 7 + 3) & 0x7f);   /* deterministic pattern */
    }
    len1 = L - 1;            /* runtime length 63 */
    len2 = L / 2 + 1;        /* runtime length 33 */
    ck1 = copy_bytes(dst, src, len1);
    ck2 = copy_bytes(dst, src, len2);
    printf("byte_copy: ck1=%lu ck2=%lu\n", ck1, ck2);
    return 0;
}
