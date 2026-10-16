#include <stdio.h>
__attribute__((noinline)) int fill(char *p, int n) { int s = 0; for (int i = 0; i < n; i++) { p[i] = (char)i; s += p[i]; } return s; }
__attribute__((noinline)) int iter(int n) {
  int t = 0;
  for (int k = 1; k <= n; k++) { char buf[k * 3]; t += fill(buf, k * 3); }
  return t;
}
int main(int argc, char **argv) { printf("%d\n", iter(argc + 9)); return 0; }
