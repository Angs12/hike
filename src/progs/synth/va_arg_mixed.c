#include <stdio.h>
#include <stdarg.h>
#include <string.h>

/* STRESS: varargs register save area with mixed GPR/XMM args.
 * A variadic function consumes int, double, char*, long, int via va_arg;
 * main feeds it loop-derived values (some in GPRs, some in XMM regs). */

static long consume_mixed(int seed, ...) {
    va_list ap;
    va_start(ap, seed);
    int   i1 = va_arg(ap, int);     /* GPR slot  */
    double d  = va_arg(ap, double); /* XMM slot  */
    char *s  = va_arg(ap, char *);  /* GPR slot  */
    long  l  = va_arg(ap, long);    /* GPR slot  */
    int   i2 = va_arg(ap, int);     /* GPR slot  */
    va_end(ap);

    long sum = (long)i1 + (long)d + (long)strlen(s) + l + i2 + seed;
    printf("mixed: i1=%d d=%.1f s=%s l=%ld i2=%d\n", i1, d, s, l, i2);
    return sum;
}

int main(void) {
    /* Strings live on main's stack; their addresses are the char* varargs */
    char labels[4][8];
    for (int i = 0; i < 4; i++) {
        labels[i][0] = (char)('a' + i);
        labels[i][1] = 'b';
        labels[i][2] = '\0';
    }

    long total = 0;
    for (int i = 0; i < 4; i++) {
        total += consume_mixed(i,                       /* named arg   */
                               i * 10,                  /* int         */
                               (double)(i + 1) * 0.5,   /* double      */
                               labels[i],               /* char*       */
                               (long)i * 1000,          /* long        */
                               i + 7);                  /* int         */
    }
    printf("total = %ld\n", total);
    return 0;
}
