#include <stdio.h>
__attribute__((noinline)) int trace(int n) {
  int m[n][n]; int t = 0;
  for (int i = 0; i < n; i++) for (int j = 0; j < n; j++) m[i][j] = i + j;
  for (int i = 0; i < n; i++) t += m[i][i];
  return t;
}
int main(int argc, char **argv) { printf("%d\n", trace(argc + 3)); return 0; }
