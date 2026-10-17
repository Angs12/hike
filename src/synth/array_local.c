#include <stdio.h>

int main(void) {
    int a[16];
    int b[32];
    char buf[64];

    /* Write through each array via pointer arithmetic */
    for (int i = 0; i < 16; i++)
        a[i] = i;

    for (int i = 0; i < 32; i++)
        b[i] = i * 10;

    for (int i = 0; i < 64; i++)
        buf[i] = (char)(i + 1);

    /* Read back and sum */
    int sum_a = 0, sum_b = 0, sum_buf = 0;
    for (int i = 0; i < 16; i++)
        sum_a += a[i];
    for (int i = 0; i < 32; i++)
        sum_b += b[i];
    for (int i = 0; i < 64; i++)
        sum_buf += buf[i];

    printf("sum_a=%d sum_b=%d sum_buf=%d\n", sum_a, sum_b, sum_buf);
    return 0;
}
