/* A switch on an enum field loaded from memory, no default: GCC -O3
 * bounds the index with `cmp [mem], N; ja`, then reloads the same cell
 * for the table load. */
#include <stdio.h>

enum kind { K_LITERAL, K_RANGE, K_CLASS, K_EQUIV, K_REPEAT };

struct spec {
  enum kind kind;
  int lo, hi;
};

__attribute__((noipa)) static long weight(const struct spec *s, int n)
{
  long acc = 0;
  for (int i = 0; i < n; i++) {
    switch (s[i].kind) {
    case K_LITERAL: acc += 1; break;
    case K_RANGE: acc += s[i].hi - s[i].lo + 1; break;
    case K_CLASS: acc += 26; break;
    case K_EQUIV: acc += 2; break;
    case K_REPEAT: acc += s[i].hi * 3; break;
    }
  }
  return acc;
}

int main(int argc, char **argv)
{
  struct spec s[] = {
    { K_LITERAL, 0, 0 }, { K_RANGE, 'a', 'f' }, { K_CLASS, 0, 0 },
    { K_EQUIV, 0, 0 }, { K_REPEAT, 1, 4 }, { K_LITERAL, 0, 0 },
  };
  printf("%ld\n", weight(s, 5 + (argc > 1)));
  return 0;
}
