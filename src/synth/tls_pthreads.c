/* Classic pthreads + TLS: eight threads bump shared atomic counters and
 * a per-thread __thread variable; every increment is a fixed amount, so
 * the totals are deterministic and main prints them after join. */

#include <pthread.h>
#include <stdatomic.h>
#include <stdio.h>

static __thread long tls_ticks = 0;          /* per-thread TLS */
static atomic_long total_ticks = 0;          /* the shared counter */
static atomic_long worker_count = 0;
static pthread_barrier_t start;

static void *worker(void *arg) {
    long id = (long)arg;
    pthread_barrier_wait(&start);
    for (int i = 0; i < 10000; i++) {
        atomic_fetch_add(&total_ticks, id + 1);
        tls_ticks += id + 1;
    }
    atomic_fetch_add(&worker_count, 1);
    return (void *)tls_ticks;
}

int main(void) {
    pthread_t th[8];
    if (pthread_barrier_init(&start, 0, 8)) return 3;
    for (long i = 0; i < 8; i++) {
        if (pthread_create(&th[i], 0, worker, (void *)i) != 0) return 1;
    }
    long per_thread[8];
    for (int i = 0; i < 8; i++) {
        void *ret = 0;
        if (pthread_join(th[i], &ret) != 0) return 2;
        per_thread[i] = (long)ret;
    }
    printf("threads=%ld ticks=%ld tls=",
           (long)atomic_load(&worker_count),
           (long)atomic_load(&total_ticks));
    for (int i = 0; i < 8; i++)
        printf("%ld%c", per_thread[i], i == 7 ? '\n' : ' ');
    pthread_barrier_destroy(&start);
    return 0;
}
