/* Captured inputs, carry/borrow, negation, and negative immediates. */
#include <stdint.h>
#include <stdio.h>

int main(void) {
    static uint64_t cell = UINT64_MAX;
    unsigned char carry_add, carry_sub, carry_neg;
    __asm__ volatile("xor %%eax,%%eax; sub $1,%%rax; lock adcq $0,%0; setc %1"
                     : "+m"(cell), "=q"(carry_add) : : "rax", "cc", "memory");
    uint64_t a = cell;
    __asm__ volatile("xor %%eax,%%eax; sub $1,%%rax; lock sbbq $-1,%0; setc %1"
                     : "+m"(cell), "=q"(carry_sub) : : "rax", "cc", "memory");
    uint64_t b = cell;
    cell = 5;
    __asm__ volatile("lock negq %0; setc %1; lock notq %0; lock addq $-2,%0"
                     : "+m"(cell), "=q"(carry_neg) : : "rax", "cc", "memory");
    printf("carry=%u/%u/%u\n", carry_add, carry_sub, carry_neg);
    printf("values=%llu/%llu/%llu\n", (unsigned long long)a,
           (unsigned long long)b, (unsigned long long)cell);
    uint64_t words[2] = {UINT64_MAX, 0};
    long bit = -1;
    unsigned char old_bit;
    __asm__ volatile("lock btrq %2,%1; setc %0"
                     : "=q"(old_bit), "+m"(words[1]) : "r"(bit) : "cc", "memory");
    printf("negative-bit=%u/%llu/%llu\n", old_bit,
           (unsigned long long)words[0], (unsigned long long)words[1]);
    static uint32_t narrow = 7;
    uint64_t accumulator = UINT64_C(0x1234567800000007);
    uint32_t desired = 9;
    __asm__ volatile("lock cmpxchgl %k2,%1" : "+a"(accumulator), "+m"(narrow)
                     : "r"(desired) : "cc", "memory");
    printf("cas-success=%llu/%u\n", (unsigned long long)accumulator, narrow);
    accumulator = UINT64_C(0x1234567800000007);
    __asm__ volatile("lock cmpxchgl %k2,%1" : "+a"(accumulator), "+m"(narrow)
                     : "r"(desired) : "cc", "memory");
    printf("cas-failure=%llu/%u\n", (unsigned long long)accumulator, narrow);
    return 0;
}
