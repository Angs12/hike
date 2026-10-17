#include <pthread.h>
#include <stdio.h>

static long datum = 37;
static __thread struct {
    unsigned char tag;
    long value;
    long *pointer;
} initialized = { 0xa5, 19, &datum };
static __thread long zero_tail[3];

static void *worker(void *arg) {
    long seed = (long)arg;
    long initial = initialized.tag + initialized.value + *initialized.pointer;
    zero_tail[2] = initial + seed;
    initialized.value += seed;
    return (void *)(zero_tail[2] + initialized.value);
}

int main(void) {
    pthread_t threads[4];
    long values[4];
    for (long i = 0; i < 4; i++)
        if (pthread_create(&threads[i], 0, worker, (void *)i)) return 1;
    for (int i = 0; i < 4; i++) {
        void *value;
        if (pthread_join(threads[i], &value)) return 2;
        values[i] = (long)value;
    }
    printf("initialized=%ld %ld %ld %ld main=%ld zero=%ld\n",
           values[0], values[1], values[2], values[3],
           initialized.value, zero_tail[2]);
    return 0;
}
