/* Atomic accesses must use the same native storage as ordinary accesses. */
#include <alloca.h>
#include <stdio.h>
#include <stdlib.h>

static __thread long tls_cell = 11;

int main(int argc, char **argv) {
    (void)argv;
    long local = 13;
    long *heap = malloc(sizeof(long));
    if (!heap) return 1;
    *heap = 17;
    long *dynamic = alloca((argc + 3) * sizeof(long));
    dynamic[argc] = 19;
    long a = __atomic_fetch_add(&local, 3, __ATOMIC_SEQ_CST);
    long b = __atomic_fetch_add(heap, 5, __ATOMIC_SEQ_CST);
    long c = __atomic_fetch_add(&tls_cell, 7, __ATOMIC_SEQ_CST);
    long d = __atomic_fetch_add(&dynamic[argc], 9, __ATOMIC_SEQ_CST);
    printf("local=%ld/%ld heap=%ld/%ld\n", a, local, b, *heap);
    printf("tls=%ld/%ld dynamic=%ld/%ld\n", c, tls_cell, d, dynamic[argc]);
    long *pointer = heap;
    long *old_pointer = __atomic_exchange_n(&pointer, &local, __ATOMIC_SEQ_CST);
    printf("pointer=%d/%d\n", old_pointer == heap, pointer == &local);
    free(heap);
    return 0;
}
