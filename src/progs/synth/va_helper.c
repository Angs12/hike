/* The va_start triangle: the middle sub takes six integer args (every
   SysV GP register, so no incoming stack-arg read forces window
   access); va_start produces the overflow pointer and stores it into
   the va_list inside one straight-line block; &ap escapes by pointer
   to a walker; the caller passes one stack vararg.  The only
   window-class trigger is the overflow-pointer store, whose data is
   SP-derived at the store def itself, never at a block boundary. */

#include <stdarg.h>
#include <stdio.h>

__attribute__((noinline)) static long walk_va(int n, va_list *ap) {
  long sum = 0;
  for (int i = 0; i < n; i++)
    sum += va_arg(*ap, long);
  return sum;
}

__attribute__((noinline)) static long va_middle(int a1, int a2, int a3,
                                                int a4, int a5, int a6, ...) {
  va_list ap;
  long sum;
  va_start(ap, a6);
  sum = a1 + a2 + a3 + a4 + a5 + a6;
  sum += walk_va(1, &ap);
  va_end(ap);
  return sum;
}

int main(void) {
  long r = va_middle(1, 2, 3, 4, 5, 6, 7L);
  printf("va_helper: %ld\n", r);
  return 0;
}
