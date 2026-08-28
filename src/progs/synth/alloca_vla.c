#include <stdio.h>
#include <stdlib.h>
#include <alloca.h>

int main(void) {
    int n = 8;

    /* VLA allocated on the stack */
    int vla[n];
    for (int i = 0; i < n; i++)
        vla[i] = i * 10;

    /* alloca() — runtime-sized stack allocation */
    int *buf = alloca(n * sizeof(int));
    for (int i = 0; i < n; i++)
        buf[i] = i * 100;

    /* Write a marker past both to test dynamic offsets */
    vla[3] = 999;
    buf[3] = 888;

    printf("vla[3]=%d buf[3]=%d vla[0]=%d buf[0]=%d\n",
           vla[3], buf[3], vla[0], buf[0]);
    return 0;
}
