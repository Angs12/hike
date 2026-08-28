/* Semantic harness for lifted hike modules (run_semantic.sh pattern).
 *
 * Persisted from the /tmp/sem harness (ora-D closeout action 1; see
 * .slim/deepwork/corpus-expand.md P4-C section).  This is the linker
 * side of the native-vs-lifted stdout diff: it provides main() and the
 * libc wrappers the lifted module needs.
 *
 * The lifted module ABI models the full x86-64 register state:
 * every function takes up to 6 integer args in register order
 * (RDI, RSI, RDX, RCX, R8, R9) and returns {i64,i64} = RAX:RDX.
 * The module's @main is renamed to @hike_main before linking (see
 * run_semantic.sh); the harness's own main calls it with (argc, argv)
 * and returns RAX as the process exit status.
 *
 * printf/putchar wrappers: the lifted code declares these externals
 * with the module ABI (e.g. {i64,i64} @printf(i64 x6)) and calls them
 * with SysV register convention.  The wrappers forward to the real
 * libc implementations without recursion.  The lifted code does not
 * honor the ABI's 16-byte stack alignment, so force re-alignment on
 * entry (this is a documented requirement of the harness pattern).
 */
#include <stdint.h>
#include <stdio.h>
#include <stdarg.h>

struct pair {
    uint64_t rax;
    uint64_t rdx;
};

struct pair hike_main(uint64_t rdi, uint64_t rsi);

/* glibc-private forwards (not in public headers) used by the
 * malloc/free wrappers below so they do not recurse into themselves. */
extern void *__libc_malloc(unsigned long size);
extern void __libc_free(void *p);

int printf(const char *fmt, ...) __attribute__((force_align_arg_pointer));
int putchar(int c) __attribute__((force_align_arg_pointer));
int puts(const char *s) __attribute__((force_align_arg_pointer));
void *malloc(unsigned long size) __attribute__((force_align_arg_pointer));
void free(void *p) __attribute__((force_align_arg_pointer));

int printf(const char *fmt, ...) {
    va_list ap;
    va_start(ap, fmt);
    int n = vfprintf(stdout, fmt, ap);
    va_end(ap);
    return n;
}

int putchar(int c) {
    return fputc(c, stdout);
}

/* puts: forward to fputs + newline (never call puts() here — it would
 * recurse into this wrapper).  Mirrors glibc's semantics: non-negative
 * on success, EOF on error. */
int puts(const char *s) {
    if (fputs(s, stdout) == EOF) return EOF;
    return fputc('\n', stdout) == EOF ? EOF : 0;
}

/* malloc/free: the lifted module calls them with the model ABI (and a
 * stack that may not honor the SysV 16-byte alignment), so forward to
 * glibc's internal __libc_malloc/__libc_free instead of recursing. */
void *malloc(unsigned long size) {
    return __libc_malloc(size);
}

void free(void *p) {
    __libc_free(p);
}

int main(int argc, char **argv) {
    struct pair r = hike_main((uint64_t)argc, (uint64_t)argv);
    return (int)r.rax;
}
