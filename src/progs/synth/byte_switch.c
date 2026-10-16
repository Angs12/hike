#include <stdio.h>
static long lines, words, linepos, maxl;
__attribute__((noinline)) int count(const unsigned char *p, const unsigned char *end, int in_word)
{
  while (p < end) {
    if (*p >= 0x80) { p++; continue; }
    switch (*p) {
    case '\n': lines++; /* fallthrough */
    case '\r': case '\f':
      if (linepos > maxl) maxl = linepos;
      words += in_word; in_word = 0; linepos = 0; break;
    case '\t': linepos += 8 - (linepos % 8); words += in_word; in_word = 0; break;
    case ' ': linepos++; /* fallthrough */
    case '\v': words += in_word; in_word = 0; break;
    default:
      if (*p > 32 && *p < 127) { linepos++; in_word = 1; }
      break;
    }
    p++;
  }
  return words + lines + maxl;
}
int main(void)
{
  static const unsigned char text[] = "one two\tthree\nfour\rfive\vsix\fseven  ";
  printf("%d\n", count(text, text + sizeof(text) - 1, 0));
  return 0;
}
