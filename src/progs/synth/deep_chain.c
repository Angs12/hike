/*
 * deep_chain.c
 * Stress pattern: deep call chain with per-frame locals.
 * f1 -> f2 -> ... -> f10; every level declares local arrays and
 * structs, transforms them, and passes values down; f10 computes and
 * returns the final result, which is printed.
 */
#include <stdio.h>
#include <string.h>

struct cell { unsigned long lo; unsigned long hi; };

static unsigned long f10(unsigned long v, struct cell c) {
    unsigned long arr[3];
    arr[0] = c.lo;
    arr[1] = c.hi;
    arr[2] = v;
    return arr[0] + arr[1] * 2 + arr[2] * 3 + 1;
}

static unsigned long f9(unsigned long v, struct cell c) {
    unsigned long buf[4];
    struct cell c2;
    buf[0] = c.lo + 1;
    buf[1] = c.hi * 3;
    buf[2] = v ^ 0xabcdUL;
    buf[3] = buf[0] + buf[1];
    c2.lo = buf[1] ^ buf[3];
    c2.hi = buf[0] + buf[2];
    return f10(v + 1, c2);
}

static unsigned long f8(unsigned long v, struct cell c) {
    unsigned long buf[4];
    struct cell c2;
    buf[0] = c.lo * 5;
    buf[1] = c.hi - 7;
    buf[2] = v + buf[0];
    buf[3] = buf[1] ^ buf[2];
    c2.lo = buf[2] + buf[3];
    c2.hi = buf[0] * buf[1];
    return f9(v + 2, c2);
}

static unsigned long f7(unsigned long v, struct cell c) {
    unsigned long buf[4];
    struct cell c2;
    buf[0] = c.lo ^ 0x1234UL;
    buf[1] = c.hi + 9;
    buf[2] = v * 3;
    buf[3] = buf[0] - buf[1];
    c2.lo = buf[1] + buf[3];
    c2.hi = buf[2] ^ buf[0];
    return f8(v + 3, c2);
}

static unsigned long f6(unsigned long v, struct cell c) {
    unsigned long buf[4];
    struct cell c2;
    buf[0] = c.lo * 7;
    buf[1] = c.hi ^ 0xbeefUL;
    buf[2] = v + 11;
    buf[3] = buf[2] * 2;
    c2.lo = buf[0] ^ buf[2];
    c2.hi = buf[1] + buf[3];
    return f7(v + 4, c2);
}

static unsigned long f5(unsigned long v, struct cell c) {
    unsigned long buf[4];
    struct cell c2;
    buf[0] = c.lo + 3;
    buf[1] = c.hi * 11;
    buf[2] = buf[0] ^ buf[1];
    buf[3] = v ^ buf[2];
    c2.lo = buf[1] - buf[3];
    c2.hi = buf[0] + buf[3];
    return f6(v + 5, c2);
}

static unsigned long f4(unsigned long v, struct cell c) {
    unsigned long buf[4];
    struct cell c2;
    buf[0] = c.lo * 13;
    buf[1] = c.hi + 5;
    buf[2] = v - 1;
    buf[3] = buf[0] ^ buf[1];
    c2.lo = buf[2] + buf[3];
    c2.hi = buf[0] * buf[1];
    return f5(v + 6, c2);
}

static unsigned long f3(unsigned long v, struct cell c) {
    unsigned long buf[4];
    struct cell c2;
    buf[0] = c.lo ^ 0x0f0fUL;
    buf[1] = c.hi * 3;
    buf[2] = v + buf[0];
    buf[3] = buf[1] - buf[2];
    c2.lo = buf[2] ^ buf[3];
    c2.hi = buf[0] + buf[1];
    return f4(v + 7, c2);
}

static unsigned long f2(unsigned long v, struct cell c) {
    unsigned long buf[4];
    struct cell c2;
    buf[0] = c.lo * 2;
    buf[1] = c.hi + 17;
    buf[2] = v ^ 0x2aUL;
    buf[3] = buf[0] + buf[2];
    c2.lo = buf[1] ^ buf[3];
    c2.hi = buf[2] * 3;
    return f3(v + 8, c2);
}

static unsigned long f1(unsigned long v, struct cell c) {
    unsigned long buf[4];
    struct cell c2;
    buf[0] = c.lo + 1;
    buf[1] = c.hi * 2;
    buf[2] = v + buf[0];
    buf[3] = buf[1] ^ buf[2];
    c2.lo = buf[3] + buf[0];
    c2.hi = buf[2] * buf[1];
    return f2(v + 9, c2);
}

int main(void) {
    struct cell c0;
    volatile unsigned long rseed = 229;  /* stack local; prevents constant folding */
    unsigned long seed = rseed + 1;      /* runtime seed, read from the stack */
    c0.lo = seed + 2;
    c0.hi = seed * 3;
    printf("deep_chain: result=%lu\n", f1(seed, c0));
    return 0;
}
