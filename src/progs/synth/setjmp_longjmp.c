#include <stdio.h>
#include <setjmp.h>

static jmp_buf jb;

static void deep_nested(int depth) {
    /* A few locals to grow the frame */
    int local[4] = {depth, depth+1, depth+2, depth+3};
    volatile int sum = local[0] + local[1] + local[2] + local[3];

    if (depth == 0) {
        printf("  deep_nested hit depth 0, longjmp now\n");
        longjmp(jb, 42);
    }
    deep_nested(depth - 1);
    /* Prevent compiler from eliding locals */
    (void)sum;
}

int main(void) {
    printf("before setjmp\n");

    if (setjmp(jb) == 0) {
        /* First return — go deep */
        printf("  setjmp returned 0, entering deep_nested(3)\n");
        deep_nested(3);
        printf("  This line should NOT be reached\n");
    } else {
        /* Longjmp landed here */
        printf("  setjmp returned non-zero after longjmp\n");
    }

    printf("after longjmp — done\n");
    return 0;
}
