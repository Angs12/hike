#include <stdint.h>
#include <stdio.h>

int n = 100;

void fizzBuzz(int n) {
  for (int i = 1; i <= n; ++i) {
    // Check if i is divisible by both 3 and 5
    if (i % 3 == 0 && i % 5 == 0) {
      puts("FizzBuzz\n");
    }
    // Check if i is divisible by 3
    else if (i % 3 == 0) {
      puts("Fizz\n");
    }
    // Check if i is divisible by 5
    else if (i % 5 == 0) {
      puts("Buzz\n");
    }
  }
}

int main(int argc, char **argv) {
  puts("FizzBuzz\n");
  puts("Fizz\n");
  puts("Buzz\n");
  fizzBuzz(argc);
  return 0;
}
