/* A _Complex double return: real and imaginary parts come back in
 * XMM0:XMM1.  The operands ride volatiles so nothing folds at -O2. */

#include <stdio.h>

__attribute__((noinline)) static _Complex double rotate(_Complex double z, double k) {
    return (z * (0.5 + 0.25 * 1.0i)) + k;
}

int main(void) {
    volatile double re = 3.0, im = -2.0, k = 1.5;
    _Complex double z = re + im * 1.0i;
    _Complex double w = rotate(z, k);
    _Complex double v = rotate(w, k);
    printf("w=%.3f,%.3f v=%.3f,%.3f\n", __real__ w, __imag__ w, __real__ v, __imag__ v);
    return 0;
}
