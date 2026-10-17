/* fconvert.c
 * Stress: float<->double conversions (cvtss2sd / cvtsd2ss).
 * Every conversion crosses a volatile boundary so neither direction
 * folds away at -O2: the lift must carry the exact widen (fpext) and
 * the round-to-nearest narrow (fptrunc) natively, not as external
 * soft-float calls. */

#include <stdio.h>

volatile float fin = 2.7f;
volatile double din = -2.7;
volatile double dsmall = 1.0 / 3.0;
volatile float fsmall = 0.1f;

int main(void) {
    double wide = (double)fin;   /* cvtss2sd: exact widen */
    float narrow = (float)din;   /* cvtsd2ss: round-to-nearest */
    double wide2 = (double)fsmall;
    float narrow2 = (float)dsmall;

    /* a chain: float -> double -> float through volatile cells */
    volatile float back = (float)wide;
    volatile double forth = (double)narrow;

    printf("wide=%.6f narrow=%.6f\n", wide, narrow);
    printf("wide2=%.6f narrow2=%.6f\n", wide2, narrow2);
    printf("back=%.6f forth=%.6f\n", back, forth);
    return 0;
}
