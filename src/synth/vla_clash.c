#include <stdio.h>
#include <string.h>

/* A multi-page VLA. Built with -fstack-clash-protection, GCC and Clang
   allocate it with a page-probing loop; the plain corpus build uses a
   single subtraction. */
__attribute__((noinline)) long clash(int n) {
  char buf[n];
  memset(buf, 5, n);
  long s = 0;
  for (int i = 0; i < n; i += 4093) s += buf[i] + i;
  return s;
}

int main(int argc, char **argv) {
  (void)argv;
  printf("%ld\n", clash(100000 + argc));
  return 0;
}
