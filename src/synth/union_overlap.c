#include <stdio.h>
#include <string.h>

/* STRESS: overlapping ranges — a local union written through one member
 * and read back through another via memcpy (type-punning through memcpy
 * is well-defined). Several unions on the stack; the member used for the
 * write AND for the read is selected at runtime per element. */

union U {
    int i;
    double d;
    char c[8];
};

static int member_for(int k) {
    return (k * 5 + 1) % 3; /* runtime-selected member (0, 1, or 2) */
}

int main(void) {
    union U u[4];
    int n = 4;

    for (int i = 0; i < n; i++) {
        int m = member_for(i);
        if (m == 0) {
            u[i].i = i * 100 + 1;
            memset(u[i].c + 4, 0, 4);   /* keep all 8 bytes defined */
        } else if (m == 1) {
            u[i].d = (double)(i + 1) * 0.25;
        } else {
            for (int j = 0; j < 8; j++)
                u[i].c[j] = (char)(i * 8 + j);
        }
    }

    long long total = 0;
    for (int i = 0; i < n; i++) {
        int m = member_for(i);
        if (m == 0) {           /* written as int, read as double */
            double d;
            memcpy(&d, &u[i], sizeof d);
            total += (long long)(d * 1e6);
        } else if (m == 1) {    /* written as double, read as int */
            int x;
            memcpy(&x, &u[i], sizeof x);
            total += x;
        } else {                /* written as char[8], read as long */
            long l;
            memcpy(&l, &u[i], sizeof l);
            total += l;
        }
    }
    printf("total = %lld\n", total);
    return 0;
}
