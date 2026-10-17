#include <stdio.h>

/* Five levels of nested calls, each with several local variables */

static int level5(int a, int b) {
    int l1 = a + 1;
    int l2 = b + 2;
    int l3 = l1 + l2;
    return l3;
}

static int level4(int a, int b, int c) {
    int x = a * 2;
    int y = b * 3;
    int z = c * 4;
    return level5(x + y, z);
}

static int level3(int a, int b) {
    int p = a + 10;
    int q = b + 20;
    int r = p * q;
    return level4(p, q, r);
}

static int level2(int a) {
    int m = a * 5;
    int n = a + 7;
    return level3(m, n);
}

static int level1(int a) {
    int i = a + 3;
    int j = a * 2;
    return level2(i + j);
}

int main(void) {
    int result = level1(2);
    printf("nested result = %d\n", result);
    return 0;
}
