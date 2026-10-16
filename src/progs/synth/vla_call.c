#include <stdio.h>
#include <string.h>
__attribute__((noinline)) long many(long a, long b, long c, long d, long e, long f, long g, long h) {
  return a + 2*b + 3*c + 4*d + 5*e + 6*f + 7*g + 8*h;
}
__attribute__((noinline)) long use(int n, long k) {
  char buf[n]; memset(buf, 7, n);
  long r = many(k, buf[0], buf[n-1], 4, 5, 6, k + 1, n);
  printf("%ld\n", r);
  return r + k;
}
int main(int argc, char **argv) { return (int)(use(argc + 16, argc) & 1); }
