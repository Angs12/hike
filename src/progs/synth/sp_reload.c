/* sp_reload.c
 * Stress: a stack pointer SAVED TO STACK and then REUSED.
 * The address of a local array is stored into a stack cell (the pointer
 * round-trips through memory), reloaded later, and dereferenced — both
 * for writes and reads.  The VSA must tag the reloaded-pointer accesses
 * via channel 2 (the reloaded value is frame-resident and bounded); the
 * typed emitter must route them to the frame cell they name.
 * The volatile qualifier forces the memory round-trip to be real. */

#include <stdio.h>

int main(void) {
    long buf[8];
    long *volatile saved = 0; /* the stack cell that SAVES a stack pointer */
    long sum = 0;

    for (long i = 0; i < 8; i++)
        buf[i] = 100 + i;

    saved = buf; /* SAVE the stack pointer to the stack */
    for (long i = 0; i < 8; i++)
        saved[i] += 1; /* REUSE it: write through the reloaded pointer */

    long *reloaded = saved;
    for (long i = 0; i < 8; i++)
        sum += reloaded[i]; /* read back through the reloaded pointer */

    /* a second save, at a different frame offset */
    saved = &buf[7];
    *saved += 5;
    sum += *saved;

    printf("sum=%ld last=%ld\n", sum, buf[7]);
    return 0;
}
