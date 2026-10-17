#include <stdio.h>
__attribute__((noinline)) int sumsq(int n) {
  int a[n]; int s = 0;
  for (int i = 0; i < n; i++) a[i] = i * i;
  for (int i = 0; i < n; i++) s += a[i];
  return s;
}
int main(int argc, char **argv) { printf("%d\n", sumsq(argc * 5)); return 0; }
