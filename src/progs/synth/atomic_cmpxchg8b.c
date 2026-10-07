#include <stdint.h>
#include <stdio.h>

static uint64_t cell = UINT64_C(0x1122334455667788);

static unsigned exchange(uint32_t *low, uint32_t *high) {
    unsigned char success;
    __asm__ volatile("lock cmpxchg8b %1; setz %0"
                     : "=q"(success), "+m"(cell), "+a"(*low), "+d"(*high)
                     : "b"(UINT32_C(0xaabbccdd)), "c"(UINT32_C(0x12345678))
                     : "cc", "memory");
    return success;
}

int main(void) {
    uint32_t low = UINT32_C(0x55667788), high = UINT32_C(0x11223344);
    unsigned success = exchange(&low, &high);
    low = 0; high = 0;
    unsigned failure = exchange(&low, &high);
    printf("cas8b=%u/%u/%08x%08x/%016llx\n", success, failure,
           high, low, (unsigned long long)cell);
    return 0;
}
