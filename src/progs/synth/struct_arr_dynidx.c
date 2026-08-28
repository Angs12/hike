#include <stdio.h>

/* STRESS: non-constant GEP index into a stack slot (dynamic-GEP class).
 * Local array of 8 structs on the stack; every access uses an index
 * computed at runtime (via a function call), never a compile-time constant. */

struct P { int a; long b; };

static int runtime_idx(int i) {
    return (i * 7 + 3) % 8;   /* runtime-derived index, not a constant */
}

static long touch(struct P *arr, int n) {
    long sum = 0;
    for (int i = 0; i < n; i++) {
        int k = runtime_idx(i);     /* dynamic index into the stack array */
        arr[k].a += i;              /* write through dynamic index */
        arr[k].b += (long)i * 3;    /* write through dynamic index */
        sum += arr[k].a + arr[k].b; /* read through dynamic index */
    }
    return sum;
}

int main(void) {
    struct P arr[8];
    for (int i = 0; i < 8; i++) {
        arr[i].a = i;
        arr[i].b = (long)i * 100;
    }
    /* More iterations than elements: the runtime index wraps around */
    long cs = touch(arr, 20);
    printf("checksum = %ld\n", cs);
    return 0;
}
