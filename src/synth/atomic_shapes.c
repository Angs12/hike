#include <stdatomic.h>
#include <stdint.h>
#include <stdio.h>

#define CHECK_RMW(T, name)                                      \
    static _Atomic T name = 17;                                 \
    do {                                                       \
        T old = atomic_fetch_add(&name, 3);                     \
        atomic_fetch_sub(&name, 2);                             \
        atomic_fetch_and(&name, 31);                            \
        atomic_fetch_or(&name, 64);                             \
        atomic_fetch_xor(&name, 5);                             \
        T swapped = atomic_exchange(&name, 9);                  \
        printf(#name "=%u/%u/%u\n", (unsigned)old,             \
               (unsigned)swapped, (unsigned)atomic_load(&name)); \
    } while (0)

int main(void) {
    CHECK_RMW(uint8_t, byte);
    CHECK_RMW(uint16_t, half);
    CHECK_RMW(uint32_t, word);
    CHECK_RMW(uint64_t, wide);
    return 0;
}
