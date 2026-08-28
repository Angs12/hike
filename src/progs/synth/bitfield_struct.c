#include <stdio.h>

/* Bitfield struct with sub-word fields */
struct BitFields {
    int a : 3;   /* 3 bits, range -4..3 */
    int b : 5;   /* 5 bits, range -16..15 */
    int c : 24;  /* 24 bits, fits in 32-bit int */
};

int main(void) {
    struct BitFields bf;

    bf.a = 3;    /* fits in 3 bits signed */
    bf.b = -15;  /* fits in 5 bits signed */
    bf.c = 12345;

    printf("a=%d b=%d c=%d\n", bf.a, bf.b, bf.c);

    /* Check sign extension */
    bf.a = -1;   /* 3-bit signed -1 */
    bf.b = -8;   /* 5-bit signed -8 */
    printf("a=%d b=%d\n", bf.a, bf.b);

    return 0;
}
