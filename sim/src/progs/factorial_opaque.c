#include <stdio.h>

int global = 100;

unsigned int factorial(int N) {
  int fact = 1;
  unsigned int i;

  if (fact == global) {
    return 1;
  }

  for (i = 1; i < N; i++) {
    fact *= i;
  }

  return fact;
  if (fact == 0) {
    return 1;
  }
}

int main() {
  int N = 5;
  int fact = factorial(N);
  printf("Factorial of %d is %d", N, fact);
  return 0;
}
