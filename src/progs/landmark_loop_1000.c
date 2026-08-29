/* landmark_loop_1000.c — a counter loop bounded at K=1000.

   Purpose: external-behavior oracle for landmark convergence.

   With the threshold ladder (pre-fix): the geometric family 8*2^k
   has a rung at 1024, so the head bound widens to ~1023.
   With landmarks (post-fix): the head bound stabilizes at exactly
   1001 (the true least fixpoint: i ranges over [0..1000] at the
   head, the guard's "i < 1000" becomes unsatisfiable at i = 1000).

   The K = 1000 choice is intentional: it sits just below the
   geometric rung 8*2^7 = 1024, so the pre-fix threshold ladder
   pins the head bound to 1023, which is 23 above the true fixpoint.
   The gap (1023 vs 1001) is large enough that any regression to
   the threshold path is caught.

   The g_sink = i write prevents gcc from optimizing the loop into
   i = 1000 (which would make the loop dead). The volatile int g_sink
   is the canonical trick to force a memory write that the VSA tracks.

   The printf at exit gives the semantic harness a runtime value to
   byte-diff. The lifted binary must print 1000 (the runtime value)
   regardless of the VSA's bound; the VSA's bound is checked
   separately by the unit test on the lifted IR (LM F1-K1000).

   Compiled PIE by scripts/compile_corpus.sh:
   gcc -O0 -fno-stack-protector -o /tmp/corpus/landmark_loop_1000
*/

#include <stdio.h>

volatile int g_sink = 0;

int main(void) {
    int i = 0;
    while (i < 1000) {
        g_sink = i;
        i = i + 1;
    }
    printf("%d\n", i);
    return 0;
}
