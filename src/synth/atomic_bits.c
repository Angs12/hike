#include <stdint.h>
#include <stdio.h>

#define CHECK_BITS(T, suffix, name)                              \
    do {                                                        \
        static T name = 5;                                       \
        unsigned char a, b, c;                                   \
        __asm__ volatile("lock bts" suffix " $1,%3; setc %0;"    \
                         "lock btr" suffix " $2,%3; setc %1;"    \
                         "lock btc" suffix " $0,%3; setc %2"     \
                         : "=q"(a), "=q"(b), "=q"(c), "+m"(name) \
                         : : "cc", "memory");                   \
        printf(#name "=%u/%u/%u/%u\n", a, b, c, (unsigned)name); \
    } while (0)

int main(void) {
    CHECK_BITS(uint16_t, "w", half);
    CHECK_BITS(uint32_t, "l", word);
    CHECK_BITS(uint64_t, "q", wide);
    return 0;
}
