#include <stdio.h>

/* The class-(b) word: a constant whose raw value lands inside the
   .text span while no relocation names it.  The .text pad makes the
   span reach past 0x10000 structurally; the runtime-indexed read keeps
   the load alive so the initializer's choice is observable. */
__asm__(".section .text\n.rept 131072\n.byte 0x90\n.endr\n.previous\n");

#define PROBE_VALUE 0x10000UL
const unsigned long table[8] = { 1, 2, 3, PROBE_VALUE, 5, 6, 7, 8 };

int main(void) {
    volatile unsigned i = 3;
    unsigned long v = table[i];
    printf("v=%#lx i=%u\n", v, (unsigned)i);
    return 0;
}
