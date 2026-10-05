/* Classic pthreads + TLS: four threads bump shared atomic counters and
 * a per-thread __thread variable; every increment is a fixed amount, so
 * the totals are deterministic and main prints them after join. */

#include <pthread.h>
#include <stdatomic.h>
#include <stdio.h>

static __thread long tls_ticks = 0;          /* per-thread TLS */
static atomic_long total_ticks = 0;          /* the shared counter */
static atomic_long worker_count = 0;

static void *worker(void *arg) {
    long id = (long)arg;
    for (int i = 0; i < 100; i++) {
        atomic_fetch_add(&total_ticks, id + 1);
        tls_ticks += id + 1;
    }
    atomic_fetch_add(&worker_count, 1);
    return (void *)tls_ticks;
}

int main(void) {
    pthread_t th[4];
    for (long i = 0; i < 4; i++) {
        if (pthread_create(&th[i], 0, worker, (void *)i) != 0) return 1;
    }
    long per_thread[4];
    for (int i = 0; i < 4; i++) {
        void *ret = 0;
        if (pthread_join(th[i], &ret) != 0) return 2;
        per_thread[i] = (long)ret;
    }
    printf("threads=%ld ticks=%ld tls=%ld %ld %ld %ld\n",
           (long)atomic_load(&worker_count),
           (long)atomic_load(&total_ticks),
           per_thread[0], per_thread[1], per_thread[2], per_thread[3]);
    return 0;
}
