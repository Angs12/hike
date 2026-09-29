#include <stdio.h>
#include <stdlib.h>
#include <alloca.h>

/* argc is TOP in the VSA (a parameter), so [m] is a runtime-sized VLA:
   a static n=8 stays a fixed frame adjust. */
int main(int argc, char **argv) {
    (void)argv;
    int n = 8;

    /* VLA allocated on the stack */
    int vla[n];
    for (int i = 0; i < n; i++)
        vla[i] = i * 10;

    /* alloca() — runtime-sized stack allocation */
    int *buf = alloca(n * sizeof(int));
    for (int i = 0; i < n; i++)
        buf[i] = i * 100;

    /* A runtime-sized VLA: the guarded merge joins two sizes, so the
       VSA cannot collapse [m] to a singleton. */
    int m;
    if (argc > 0)
        m = 4;
    else
        m = 8;
    int rvla[m];
    rvla[2] = 77;

    /* Write a marker past both to test dynamic offsets */
    vla[3] = 999;
    buf[3] = 888;

    printf("vla[3]=%d buf[3]=%d vla[0]=%d buf[0]=%d rvla[2]=%d\n",
           vla[3], buf[3], vla[0], buf[0], rvla[2]);
    return 0;
}
