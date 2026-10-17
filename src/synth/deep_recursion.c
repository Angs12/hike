#include <stdio.h>

/* Recursive fibonacci — depth ~10 for fib(10) */
static int fib(int n) {
    if (n <= 1)
        return n;
    return fib(n - 1) + fib(n - 2);
}

int main(void) {
    int n = 10;
    int result = fib(n);
    printf("fib(%d) = %d\n", n, result);
    return 0;
}
