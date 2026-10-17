/* The matrix compiles this source with each -ftls-model setting. */
#include <pthread.h>
#include <stdio.h>

__thread long model_value __attribute__((aligned(32))) = 11;
__thread unsigned char model_zero[7];

static void *worker(void *arg) {
    model_value += (long)arg;
    model_zero[6] = 3;
    return (void *)(model_value + model_zero[6]);
}

int main(void) {
    pthread_t thread;
    void *value;
    if (pthread_create(&thread, 0, worker, (void *)5)) return 1;
    if (pthread_join(thread, &value)) return 2;
    printf("model=%ld main=%ld zero=%u\n", (long)value,
           model_value, model_zero[6]);
    return 0;
}
