#include <pthread.h>
#include <stdio.h>

int global = 4;

int inc(int x, int y, int z, int w, int i, int j, int s) {
  return x + y + z + w + i + j + s;
}

unsigned int factorial(unsigned int N) {
  int fact = 1, i;

  for (i = 1; i <= N; i++) {
    fact *= i;
  }

  return fact;
}

int main() {
  int fact = factorial(global);
  int t = getchar();
  // putchar(t);
  return inc(fact, 0, 0, 0, 0, 0, 1);
}
