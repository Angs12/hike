#include <stdint.h>
#include <stdio.h>

void fizzBuzz(int n) {
  for (int i = 1; i <= n; ++i) {
    // Check if i is divisible by both 3 and 5
    if (i % 3 == 0 && i % 5 == 0) {
      putchar('F');
      putchar('i');
      putchar('z');
      putchar('z');
      putchar(' ');
      putchar('B');
      putchar('u');
      putchar('z');
      putchar('z');
      putchar('\n');
    }
    // Check if i is divisible by 3
    else if (i % 3 == 0) {
      putchar('F');
      putchar('i');
      putchar('z');
      putchar('z');
      putchar('\n');
    }
    // Check if i is divisible by 5
    else if (i % 5 == 0) {
      putchar('B');
      putchar('u');
      putchar('z');
      putchar('z');
      putchar('\n');
    }
  }
}

int main() {
  int n = 100;
  fizzBuzz(n);
  return 0;
}
