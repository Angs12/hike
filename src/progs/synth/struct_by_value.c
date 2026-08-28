#include <stdio.h>

/* ~64 bytes: 16 ints = 64 bytes on x86-64 */
typedef struct {
    int a0, a1, a2, a3, a4, a5, a6, a7;
    int b0, b1, b2, b3, b4, b5, b6, b7;
} BigStruct;

static BigStruct modify_copy(BigStruct s) {
    /* Increment the first and last fields to prove it's a distinct copy */
    s.a0 += 100;
    s.b7 += 999;
    return s;
}

int main(void) {
    BigStruct orig = {
        0, 1, 2, 3, 4, 5, 6, 7,
        8, 9, 10, 11, 12, 13, 14, 15
    };
    BigStruct result = modify_copy(orig);
    printf("orig.a0=%d result.a0=%d result.b7=%d\n",
           orig.a0, result.a0, result.b7);
    return 0;
}
