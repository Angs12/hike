#include <stdio.h>
#include <string.h>
__attribute__((noinline)) long big(int n) {
  char buf[n]; memset(buf, 1, n); long s = 0;
  for (int i = 0; i < n; i += 997) s += buf[i] + i;
  return s;
}
int main(int argc, char **argv) { printf("%ld\n", big(300000 + argc)); return 0; }
