/*
 * rec_struct.c
 * Stress pattern: recursion with stack-allocated structures.
 * Each frame allocates a local node struct, links it to the caller's
 * frame node (a linked list built entirely on the stack), walks the
 * chain of live ancestor nodes, and sums values on unwind.
 */
#include <stdio.h>

struct node {
    unsigned long v;
    struct node *next;
};

static unsigned long build(struct node *prev, unsigned long v, int depth) {
    struct node cur;
    const struct node *p;
    int len = 0;

    cur.v = v;
    cur.next = prev;               /* link to the caller-frame node */

    if (prev) {
        cur.v += prev->v % 5;      /* read the live caller-frame node */
    }
    for (p = prev; p != 0; p = p->next) {   /* walk the on-stack chain */
        len++;
    }
    cur.v += (unsigned long)len;

    if (depth > 0) {
        unsigned long sub = build(&cur, v * 3 + 1, depth - 1);
        cur.v += sub;              /* sum on unwind */
    }
    return cur.v;
}

int main(void) {
    volatile unsigned long rseed = 70;  /* stack local; prevents constant folding */
    unsigned long seed = rseed % 13 + 1; /* runtime seed, read from the stack */
    unsigned long sum = build(0, seed, 6);
    printf("rec_struct: sum=%lu\n", sum);
    return 0;
}
