#include <pthread.h>
#include <stdio.h>
#include <string.h>

/* Each thread grows its own VLA stack; the result must not depend on how
   the threads interleave. */
__attribute__((noinline)) long fill(int n) {
  char buf[n];
  memset(buf, n & 0x7f, n);
  long s = 0;
  for (int i = 0; i < n; i += 61) s += buf[i];
  return s;
}

static long results[2];

static void *worker(void *arg) {
  long k = (long)arg;
  results[k] = fill((int)((k + 1) * 50000));
  return 0;
}

int main(int argc, char **argv) {
  (void)argv;
  pthread_t t1, t2;
  pthread_create(&t1, 0, worker, (void *)0L);
  pthread_create(&t2, 0, worker, (void *)1L);
  pthread_join(t1, 0);
  pthread_join(t2, 0);
  printf("%ld %ld %ld\n", results[0], results[1], fill(argc * 40000));
  return 0;
}
