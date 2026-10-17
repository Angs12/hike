/* jump_table_sw.c
 * T4 stress: a wide switch that compiles to a JUMP TABLE (the -O2
 * lane builds the .rodata code-address table; the dispatch is an
 * indirect jump through it), with each case calling a DISTINCT
 * handler.  The handlers stay out-of-line (noinline) so the calls are
 * real, and each takes enough arguments to own locals at both -O0 and
 * -O2.  This is the multi-case dispatch class interacting with T6's
 * data-pointer rendering — the lifted table must land the dispatch on
 * handlers whose behavior the harness can observe. */
#include <stdio.h>

__attribute__((noinline)) static long f0(long x) { return x + 1; }
__attribute__((noinline)) static long f1(long x) { return x * 2 + 1; }
__attribute__((noinline)) static long f2(long x) { return x ^ 5; }
__attribute__((noinline)) static long f3(long x) { return x - 3; }
__attribute__((noinline)) static long f4(long x) { return x * x + 2; }
__attribute__((noinline)) static long f5(long x) { return (x + 7) / 2; }
__attribute__((noinline)) static long f6(long x) { return (x * 3) % 11; }
__attribute__((noinline)) static long f7(long x) { return x | 9; }

int main(void) {
    long acc = 0;
    for (long i = 0; i < 24; i++) {
        switch (i % 8) {
        case 0: acc += f0(i); break;
        case 1: acc += f1(i); break;
        case 2: acc += f2(i); break;
        case 3: acc += f3(i); break;
        case 4: acc += f4(i); break;
        case 5: acc += f5(i); break;
        case 6: acc += f6(i); break;
        default: acc += f7(i) * 2; break;
        }
    }
    printf("jump_table_sw: acc=%ld\n", acc);
    return 0;
}
