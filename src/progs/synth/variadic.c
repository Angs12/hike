#include <stdio.h>
#include <stdarg.h>

/* Variadic sum — called with 7 args (6 register + 1 stack spill on x86-64 SysV) */
static int sum_n(int count, ...) {
    va_list ap;
    int total = 0;
    va_start(ap, count);
    for (int i = 0; i < count; i++) {
        total += va_arg(ap, int);
    }
    va_end(ap);
    return total;
}

int main(void) {
    /* 7 arguments: first 6 go in registers, the 7th goes on the stack */
    int result = sum_n(7, 10, 20, 30, 40, 50, 60, 70);
    printf("sum = %d\n", result);
    return 0;
}
