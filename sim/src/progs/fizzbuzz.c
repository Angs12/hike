#include <stdint.h>
#include <stdio.h>

int fizzBuzz(int n) {
  int fizz = 0;
  int buzz = 0;
  int fizzbuzz = 0;
  for (int i = 1; i <= n; ++i) {
    // Check if i is divisible by both 3 and 5
    if (i % 3 == 0 && i % 5 == 0) {
      // Print "FizzBuzz"
      fizzbuzz++;
    }
    // Check if i is divisible by 3
    else if (i % 3 == 0) {
      // Print "Fizz"
      fizz++;
    }
    // Check if i is divisible by 5
    else if (i % 5 == 0) {
      // Print "Buzz"
      buzz++;
    }
  }
  return fizz + buzz + fizzbuzz;
}

int main() {
  int n = 20;
  int f = fizzBuzz(n);
  printf("FizzBuzz: %d\n", f);

  return 0;
}
