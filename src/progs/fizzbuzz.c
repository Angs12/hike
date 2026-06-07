#include <stdint.h>
#include <stdio.h>

const long long int foo = 0;
int bar;

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
  bar = 10;
  fizzBuzz(argc + bar);
  return foo;
}
