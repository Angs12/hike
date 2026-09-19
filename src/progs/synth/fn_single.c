/* fn_single.c
 * T4 stress: an indirect call the VSA resolves to a SINGLETON.  The
 * handler pointer is forced through a volatile cell (the store/load
 * round trip is real), and the cell holds exactly one stored value,
 * so the site's denotation is a singleton lifted sub: the Resolved
 * Call Site class.  The handler takes eight long arguments, so the
 * resolved direct call goes through the PROMOTED signature — the last
 * two slots arrive as real call arguments at -O0. */
#include <stdio.h>

__attribute__((noinline)) static long add3(long a, long b, long c, long d,
                                           long e, long f, long g, long h) {
    return a + b + c + d + e + f + g * 2 + h * 3 + 3;
}

int main(void) {
    long (*volatile fp)(long, long, long, long, long, long, long, long) = add3;
    long s = 0;
    for (long i = 0; i < 5; i++)
        s += fp(i, 2 * i, 1, 2, 3, 4, 5, 6);
    printf("fn_single: s=%ld\n", s);
    return 0;
}
