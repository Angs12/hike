#include <pthread.h>
#include <stdio.h>

#pragma noinline
int __attribute__((noinline)) inc(int x) {
  x++;
  return x;
}

unsigned int factorial(unsigned int N) {
  int fact = 1, i;

  for (i = 1; i <= N; i++) {
    fact *= i;
  }

  return fact;
}

int main() {
  int N = 3;
  int fact = factorial(N);
  putchar(0x42);
  return fact;
}
