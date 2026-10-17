/* fn_escape.c
 * T4 stress: an address-taken promoted sub whose pointer escapes
 * through memory to a site the VSA cannot resolve.  The handler table
 * is a static array of function pointers (data relocations, T6's
 * rendering class) and the load is indexed by the process's own argc —
 * a value the lift cannot bound — so the site's target denotation is
 * unresolvable: the POINTER call, landing in the memory-convention
 * thunk.  The thunk unpacks the window slots into the promoted body,
 * so the stack-passed arguments survive the unresolvable dispatch. */
#include <stdio.h>

__attribute__((noinline)) static long mul7(long a, long b, long c, long d,
                                           long e, long f, long g, long h) {
    return (a + g) * 7 + (b + h) + c + d + e + f;
}

__attribute__((noinline)) static long add11(long a, long b, long c, long d,
                                            long e, long f, long g, long h) {
    return a + b + c + d + e + f + g + h + 11;
}

static long (*tbl[2])(long, long, long, long, long, long, long, long) = {
    mul7, add11
};

int main(int argc, char **argv) {
    long k = (long)(argc & 1); /* the lift cannot bound argc */
    long s = 0;
    for (long i = 0; i < 4; i++)
        s += tbl[k](i, i + 1, 1, 2, 3, 4, 5, 6);
    printf("fn_escape: s=%ld argc=%d\n", s, argc & 1);
    return 0;
}
