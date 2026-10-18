#include <stdio.h>
struct S { long n; char *p; };
static char heap_buf[16];
__attribute__((noinline)) void redirect(struct S *s) { s->p = heap_buf; s->n = 2; }
void (*volatile fp)(struct S *) = redirect;
int main(void) {
  char local[16] = {0};
  struct S s; s.n = 1; s.p = local;
  __asm__ volatile("" : : "r"(&s), "r"(local) : "memory");
#ifdef ESC_DIRECT
  redirect(&s);
#else
  fp(&s);
#endif
  s.p[0] = 'X';
  __asm__ volatile("" : : "r"(local) : "memory");
  printf("%c %c %ld\n", local[0] ? local[0] : '-', heap_buf[0] ? heap_buf[0] : '-', s.n);
  return 0;
}
