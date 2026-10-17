#include <stdint.h>
#include <stdio.h>

#define CHECK_FLAGS(T, suffix, name)                             \
    do {                                                        \
        static T name = 255;                                     \
        unsigned char zero, carry;                              \
        __asm__ volatile("lock add" suffix " $1,%2; setz %0; setc %1;" \
                         "lock inc" suffix " %2; lock dec" suffix " %2" \
                         : "=q"(zero), "=q"(carry), "+m"(name)  \
                         : : "cc", "memory");                   \
        printf(#name "=%u/%u/%u\n", zero, carry, (unsigned)name); \
    } while (0)

int main(void) {
    CHECK_FLAGS(uint8_t, "b", byte);
    CHECK_FLAGS(uint16_t, "w", half);
    CHECK_FLAGS(uint32_t, "l", word);
    CHECK_FLAGS(uint64_t, "q", wide);
    return 0;
}
