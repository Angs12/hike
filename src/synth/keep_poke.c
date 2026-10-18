#include <stdio.h>
static int *saved;
__attribute__((noinline)) void keep(int *p) { saved = p; }
__attribute__((noinline)) void poke(void) { *saved = 7; }
int main(void) { int x = 1; keep(&x); poke(); printf("%d\n", x); return 0; }
