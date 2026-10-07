#include <stdatomic.h>
#include <stdint.h>
#include <stdio.h>

#define CHECK_CAS(T, name)                                      \
    static _Atomic T name = 17;                                 \
    do {                                                       \
        T expected = 17;                                       \
        int success = atomic_compare_exchange_strong(&name, &expected, 29); \
        expected = 17;                                         \
        int failure = atomic_compare_exchange_strong(&name, &expected, 31); \
        printf(#name "=%d/%d/%u/%u\n", success, failure,        \
               (unsigned)expected, (unsigned)atomic_load(&name)); \
    } while (0)

int main(void) {
    CHECK_CAS(uint8_t, byte);
    CHECK_CAS(uint16_t, half);
    CHECK_CAS(uint32_t, word);
    CHECK_CAS(uint64_t, wide);
    atomic_thread_fence(memory_order_seq_cst);
    __asm__ volatile("lfence\nsfence\nmfence" ::: "memory");
    return 0;
}
