/*
 * setjmp_loop.c
 * Stress pattern: non-local control flow with live stack state.
 * setjmp/longjmp inside a loop: a helper with stack locals and a
 * stack argument (the jmp_buf itself lives on main's stack and is
 * passed by pointer) longjmps back into the loop counter context
 * several times; counts and accumulated values are printed.
 */
#include <stdio.h>
#include <setjmp.h>

static unsigned long worker(jmp_buf *jb, unsigned long round, unsigned long seed) {
    unsigned long a[4];
    volatile unsigned long acc = 0;
    int i;

    a[0] = seed;
    a[1] = seed + 1;
    a[2] = seed + 2;
    a[3] = seed + 3;
    for (i = 0; i < 4; i++) {
        acc += a[i] * (unsigned long)(i + (int)round);
    }
    if (round < 3) {
        longjmp(*jb, (int)round + 1);   /* jump back into main's loop context */
    }
    return acc;
}

int main(void) {
    jmp_buf jb;                       /* stack-local jump context */
    volatile unsigned long total = 0; /* volatile: live across longjmp */
    volatile unsigned long rounds = 0;
    volatile unsigned long rseed = 7;  /* stack local; prevents constant folding */
    unsigned long seed = rseed;        /* runtime seed, read from the stack */
    int i;
    int rc;

    for (i = 0; i < 4; i++) {
        rc = setjmp(jb);
        if (rc == 0) {
            total += worker(&jb, (unsigned long)i, seed + (unsigned long)i);
            break;
        } else {
            rounds += 1;
            total += (unsigned long)rc * 1000;
        }
    }
    printf("setjmp_loop: rounds=%lu total=%lu\n", rounds, total);
    return 0;
}
