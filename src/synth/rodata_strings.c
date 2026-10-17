/* rodata_strings.c
 * T18 prep: NUL-terminated string literals (each carves as its own
 * byte-array component, extent = the initializer run through the NUL) +
 * a table of string pointers (.data.rel.ro in PIE — the ptr-typed
 * upgrade path: every use is load-and-index, no integer arithmetic) +
 * a bounded index walk over one string (index-dependent membership:
 * the arithmetic propagates the anchor, the component spans the bound).
 * Constant content makes every load foldable — the best constant-prop
 * case for the consumer optimizer. */

#include <stdio.h>
#include <string.h>

static const char s_a[] = "section-values";
static const char s_b[] = "bounded-walk";
static const char s_c[] = "nul-delimited";

/* pointer table into the literals (.data.rel.ro words) */
static const char *const tab[3] = { s_a, s_b, s_c };

int main(void) {
    volatile unsigned bound = 7; /* < strlen(s_b): the walk stays inside */
    volatile unsigned ti = 1;
    unsigned long sum = 0;

    /* full-string scans (constant-address loads: the folding lane) */
    for (const char *p = s_a; *p; ++p)
        sum += (unsigned char)*p;
    for (const char *p = s_c; *p; ++p)
        sum += 31u * (unsigned char)*p;

    /* bounded index walk (runtime bound: the anchored dynamic lane) */
    for (unsigned i = 0; i <= bound; ++i)
        sum += (unsigned char)s_b[i];

    /* constant-offset reads: the byte after the walk bound and the
     * NUL terminator itself */
    sum += (unsigned char)s_b[bound + 1];
    sum += (unsigned char)s_b[12];

    /* the pointer table at runtime and constant indices */
    const char *t = tab[ti];
    sum += (unsigned char)t[0];
    sum += (unsigned char)tab[2][3];

    printf("sum=%lu a_len=%zu walk_last=%c t0=%c t0_len=%zu c3=%c\n",
           sum, strlen(s_a), s_b[bound], t[0], strlen(t), tab[2][3]);
    return 0;
}
