/* data_objects.c
 * T18 prep: multiple DISTINCT .data objects — a scalar int, an array, a
 * double, a struct — accessed at runtime indices, with cross-references:
 * a const initializer pointer INTO one object (the .data.rel.ro shape,
 * a T6-relocated initializer word) and a runtime-stored pointer
 * round-tripped through a stack cell.
 * T18's partition should carve one component per object; the int/long
 * components are typed-on-agreement candidates, the double one stays a
 * byte-array or folds by width; the pointed-to byte range must stay
 * inside some component (the base-map totality rule).
 * Volatile indices keep every access runtime at -O2 (quality envelope). */

#include <stdio.h>
#include <string.h>

static int g_int = 42;
static long g_arr[16] = { 10, 11, 12, 13, 14, 15, 16, 17,
                          18, 19, 20, 21, 22, 23, 24, 25 };
static double g_dbl = 2.5;
static struct { int a; long b; double c; } g_rec = { 7, 700, 0.75 };

/* .data.rel.ro words pointing INTO g_arr */
static long *const g_aliases[3] = { &g_arr[3], &g_arr[12], &g_arr[15] };

static unsigned long bits_of(double d) {
    unsigned long u;
    memcpy(&u, &d, sizeof u);
    return u;
}

int main(void) {
    volatile int k = 3;
    volatile int j = 12;
    unsigned long sum = 0;

    /* runtime-index writes into distinct objects (the dynamic lane) */
    g_arr[k] = 1000 + k;
    g_int += k;
    g_rec.b += k;
    g_rec.c += 0.5;
    g_dbl *= 2.0;

    /* runtime-index reads, folded into one checksum */
    sum += (unsigned long)g_arr[j];
    sum += (unsigned long)(unsigned)g_int;
    sum += (unsigned long)g_rec.a + (unsigned long)g_rec.b;
    sum += bits_of(g_dbl);
    sum += bits_of(g_rec.c);

    /* the .data.rel.ro words: one runtime-indexed read (keeps the
     * relocated table real at -O2) + two constant-index reads */
    volatile unsigned ai = 1;
    sum += (unsigned long)*g_aliases[ai];
    sum += (unsigned long)*g_aliases[0];
    sum += (unsigned long)*g_aliases[2];
    /* the pointer round-trip: a section address stored in memory,
     * reloaded, then dereferenced for write and read */
    long *volatile p = &g_arr[5];
    *p += 77;
    sum += (unsigned long)*p;

    printf("sum=%lu int=%d arr5=%ld arr12=%ld rec_b=%ld\n",
           sum, g_int, g_arr[5], g_arr[12], g_rec.b);
    return 0;
}
