#include <stdio.h>

/* STRESS: pointer-chained multi-level stack dereferences.
 * Stack struct S holds a pointer to a stack struct T, which itself holds
 * a pointer to a stack struct U; the chain HEAD is picked at runtime from
 * a loop variable, so the dereference path is not statically constant. */

struct U { long w; };
struct T { int v; struct U *u; };
struct S { struct T *t; };

static long traverse(struct S *sa, struct S *sb, int rounds) {
    long cs = 0;
    for (int i = 0; i < rounds; i++) {
        struct S *s = (i % 2) ? sb : sa; /* runtime-picked chain head */
        struct T *t = s->t;              /* 1st-level deref */
        struct U *u = t->u;              /* 2nd-level deref */
        cs += (long)t->v + u->w;
    }
    return cs;
}

int main(void) {
    struct U u1 = { 1000L }, u2 = { 2000L };
    struct T t1 = { 7, &u1 }, t2 = { 11, &u2 };
    struct S s1 = { &t1 }, s2 = { &t2 };

    long cs = traverse(&s1, &s2, 9); /* 5x chain 1, 4x chain 2 */
    printf("checksum = %ld\n", cs);
    return 0;
}
