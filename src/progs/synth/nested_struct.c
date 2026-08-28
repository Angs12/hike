/*
 * nested_struct.c
 * Stress pattern: deep field access + by-value copies.
 * 4-level nested structs (A -> B -> C -> D) are declared locally,
 * fields are read/written at depth 3-4, and whole structs are copied
 * by value between locals and passed/returned by value.
 */
#include <stdio.h>

struct D { unsigned long v; char c; };
struct C { struct D d; unsigned long x; };
struct B { struct C c; };
struct A { struct B b; };

/* whole-struct argument and whole-struct return (stack copies) */
static struct A transform(struct A in, unsigned long k) {
    struct A out;
    out.b.c.d.v = in.b.c.d.v * k + 1;
    out.b.c.d.c = (char)((unsigned char)in.b.c.d.c + 1);
    out.b.c.x = in.b.c.x ^ k;
    return out;
}

static unsigned long sum_fields(struct A a) {
    struct D d = a.b.c.d;        /* depth-4 field extract, by value */
    struct C c = a.b.c;          /* depth-3 field extract, by value */
    struct B b = a.b;            /* depth-2 field extract, by value */
    unsigned long acc;

    acc = d.v * 3 + (unsigned long)(unsigned char)d.c
        + c.x * 7 + b.c.d.v + (unsigned long)(unsigned char)a.b.c.d.c;
    return acc;
}

int main(void) {
    struct A a;
    struct A a2;
    struct A a3;
    volatile unsigned long rk = 13;  /* stack local; prevents constant folding */
    unsigned long k = rk + 5;        /* runtime k, read from the stack */
    unsigned long ck;

    a.b.c.d.v = k * 3;                           /* depth-4 field write */
    a.b.c.d.c = (char)((unsigned char)(k % 26) + 65);
    a.b.c.x = k + 100;                           /* depth-3 field write */

    a2 = a;                      /* whole-struct by-value copy */
    a3 = transform(a2, k);       /* by-value arg + by-value return */

    ck = sum_fields(a2) * 1000 + sum_fields(a3);
    printf("nested_struct: checksum=%lu\n", ck);
    return 0;
}
