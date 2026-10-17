#include <stdio.h>
#include <string.h>

/* Two live VLAs: the inner one sits below the outer one and is released
   first, so the stack must nest them. */
__attribute__((noinline)) long nested(int n) {
  char outer[n];
  memset(outer, 3, n);
  long s = 0;
  for (int k = 1; k <= 3; k++) {
    char inner[n * k + 1];
    memset(inner, k, n * k + 1);
    s += inner[n * k] + outer[n - 1] + inner[0];
  }
  return s + outer[0];
}

int main(int argc, char **argv) {
  (void)argv;
  printf("%ld\n", nested(argc + 20));
  return 0;
}
