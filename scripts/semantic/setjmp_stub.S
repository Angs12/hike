/* setjmp/longjmp stubs for the lifted setjmp_loop module (run_semantic.sh).
 *
 * Persisted from the /tmp/sem harness (ora-D closeout action 1; see
 * .slim/deepwork/corpus-expand.md P4-C section).  Linked only when the
 * lifted module declares @_setjmp/@longjmp.
 *
 * The lifted module passes MODEL stack addresses (the heritage sp-chain
 * constants) as the jmp_buf pointer, so real glibc __sigsetjmp would
 * dereference an invalid address.  Instead, emulate glibc semantics for
 * the model: _setjmp saves the machine frame + the setjmp continuation
 * (the return address of the call, which is exactly the instruction to
 * resume at) and returns 0 (RAX:RDX=0); longjmp restores the saved frame
 * and transfers to the continuation with RAX = the longjmp value
 * (exactly glibc's semantics).  Layout-independent: no hardcoded
 * addresses.  These definitions override glibc's symbols because they
 * are linked directly as objects (not via a shared library).
 */
.globl _setjmp
.type _setjmp, @function
_setjmp:
    leaq 8(%rsp), %rax          /* call-site RSP (the call pushed the ret) */
    movq %rax, saved_rsp(%rip)
    movq %rbp, saved_rbp(%rip)
    movq 0(%rsp), %rax           /* return address = setjmp continuation */
    movq %rax, saved_cont(%rip)
    xorl %eax, %eax
    xorl %edx, %edx
    ret
.size _setjmp, .-_setjmp

.globl longjmp
.type longjmp, @function
longjmp:
    movq %rsi, %rax              /* longjmp value -> RAX (module ABI arg 2) */
    movq saved_cont(%rip), %r11
    movq saved_rsp(%rip), %rsp
    movq saved_rbp(%rip), %rbp
    jmp *%r11
.size longjmp, .-longjmp

.data
saved_rsp:  .quad 0
saved_rbp:  .quad 0
saved_cont: .quad 0
