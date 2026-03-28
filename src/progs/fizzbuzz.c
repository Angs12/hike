#include <stdint.h>
#include <stdio.h>

void fizzBuzz(int n) {
  for (int i = 0; i <= n; ++i) {
    // Check if i is divisible by both 3 and 5
    if (i % 3 == 0 && i % 5 == 0) {
      putchar('F');
      putchar('B');
      putchar('\n');
    }
    // Check if i is divisible by 3
    else if (i % 3 == 0) {
      putchar('F');
      putchar('\n');
    }
    // Check if i is divisible by 5
    else if (i % 5 == 0) {
      putchar('B');
      putchar('\n');
    }
  }
}

int main(int argc, char **argv) {
  fizzBuzz(argc + 10);
  return 0;
}
