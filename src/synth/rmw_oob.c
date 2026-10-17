#include <stdio.h>

/* P2 (H-R1) semantic test: the bounded-store RMW emission regression.
   The first loop writes through a runtime index (i % 8 < 8) that stays
   IN BOUNDS, so every store takes the ok path (identity write to the
   exact slot) and the second loop's sum reads them back; the result is
   deterministic and byte-comparable with the native binary (sum = 184).

   NOTE (Gate-2 C2): this binary NEVER executes the !ok path at runtime
   (a[i % 8] is always in bounds).  The !ok self-valued write-back is
   verified STRUCTURALLY ONLY: the false-branch clamp index is
   rmin - base -> alloca+0 (in-bounds), and storing the just-loaded
   `old` is a net no-op single-threaded.  Do not read this file as
   exercising !ok. */

int main(void) {
    long a[8];
    for (int i = 0; i < 16; i++)
        a[i % 8] = i * 2;
    long s = 0;
    for (int i = 0; i < 8; i++)
        s += a[i];
    printf("sum = %ld\n", s);
    return 0;
}
