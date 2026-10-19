/* A switch on a char argument: GCC -O3 bounds the table index with
 * `cmp al, N` on the low byte only, then re-extracts the byte
 * (`movzx eax, al`) for the table load. */
#include <stdio.h>

__attribute__((noinline)) static int hextobin(char c)
{
  switch (c) {
  case 'A': case 'a': return 10;
  case 'B': case 'b': return 11;
  case 'C': case 'c': return 12;
  case 'D': case 'd': return 13;
  case 'E': case 'e': return 14;
  case 'F': case 'f': return 15;
  default: return c - '0';
  }
}

int main(int argc, char **argv)
{
  const char *s = argc > 1 ? argv[1] : "09afAF";
  int acc = 0;
  for (; *s; s++)
    acc = acc * 16 + hextobin(*s);
  printf("%d\n", acc);
  return 0;
}
