/* A function whose result returns in BOTH RAX and RDX: a 16-byte
 * all-integer struct (two eightwords) rides the SysV INTEGER pair.
 * The halves depend on runtime args so nothing folds, and one call
 * site goes through a volatile so the pair survives at -O2. */

#include <stdio.h>

typedef struct { unsigned long lo; unsigned long hi; } Pair;

static Pair make_pair(unsigned long a, unsigned long b) {
    Pair p;
    p.lo = a * 3 + 1;
    p.hi = b * 5 + 2;
    return p;
}

int main(void) {
    volatile unsigned long x = 11;
    volatile unsigned long y = 23;
    Pair p = make_pair(x, y);
    Pair q = make_pair(p.lo, p.hi);
    printf("lo=%lu hi=%lu lo2=%lu hi2=%lu\n",
           p.lo, p.hi, q.lo, q.hi);
    return 0;
}
