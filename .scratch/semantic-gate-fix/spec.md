# Fix Stack-to-Locals Classification and Semantic Corpus Gate — Spec

**Status:** ready-for-agent
**Feature:** fix-stack-to-locals-semantic-gate
**Base branch:** `recover-golden`

## Problem Statement

When running the native-vs-lifted semantic test suite (`run_semantic.sh` and `run_semantic_all.sh`), multiple binaries in the test corpus fail:
- `deep_recursion` fails with a segmentation fault (`rc=139`) instead of producing `fib(10) = 55`.
- `nested_calls` fails with a segmentation fault (`rc=139`) instead of producing `nested result = 8141`.
- `fizzbuzz` exceeds execution timeout (`rc=124`) because loop bounds conditions evaluate incorrectly against uninitialized values.

The root cause is that the `stack_to_locals` transformation pass fails to convert function-local stack slots into local scalar variables. The `is_abi_visible` predicate in `stack_to_locals` incorrectly compares current-RSP relative distances ($k = \text{addr} - \text{RSP}_{\text{current}}$) with $0$. Because all local stack variables reside above the dynamically adjusted $\text{RSP}_{\text{current}}$, $k \ge 0$ holds for all local variables, causing `stack_to_locals` to classify every local variable as an ABI-visible caller argument. Consequently, no local stack slots are converted to variables (`cells` is empty).

Downstream, expressions containing embedded memory operands (such as `cmp [rbp - 20], 1`, `imul eax, [rbp - 8]`, or `sub eax, [rbp - 20]`) retain un-rewritten `Bil.Load` nodes. In precise (region-split) functions where the model frame is erased (`fr.frame = None`), evaluating these nested loads in the LLVM emitter (`create_exp` / `create_load`) falls back to constructing `inttoptr` from erased/poison register values (`%RBP`), resulting in segfaults and corrupted execution state.

## Solution

1. Correct the stack slot classification in `stack_to_locals` so that:
   - Function-local stack accesses (entry-relative offset $lo < 0$) are correctly recognized as internal frame slots and converted into scalar/array local variables.
   - Incoming caller arguments (entry-relative offset $lo \ge 0$) remain classified as ABI-visible memory accesses.
2. Ensure the nested load rewriting pass (`nested_rewrite`) in `stack_to_locals` properly maps all embedded `Bil.Load` sub-expressions to the converted local variables.
3. Ensure the LLVM IR emitter (`bil2llvm.ml`) handles any remaining stack loads in precise frames without generating invalid `inttoptr` operations on erased register values.
4. Verify that `scripts/semantic/run_semantic.sh` and `scripts/semantic/run_semantic_all.sh` achieve 100% pass rate across the full corpus while preserving all structural alloca invariants (`check_allocas.sh`).

## User Stories

1. As a compiler developer, I want `stack_to_locals` to distinguish between incoming caller arguments ($lo \ge 0$) and function-local stack slots ($lo < 0$), so that local stack variables are converted to scalar locals rather than treated as ABI-visible memory.
2. As a compiler developer, I want `stack_to_locals` to populate its `cells` mapping for all convertible local stack ranges, so that subsequent rewriting passes can map memory addresses to local variables.
3. As a compiler developer, I want `nested_rewrite` in `stack_to_locals` to rewrite all `Bil.Load` expressions embedded inside binary, unary, and cast operations to their corresponding local variables, so that expressions do not contain raw memory reads from local stack slots.
4. As a compiler developer, I want recursive function calls (e.g. `fib` in `deep_recursion`) to evaluate comparisons against local variables without dereferencing uninitialized registers, so that recursive functions execute to completion without crashing.
5. As a compiler developer, I want multi-level nested function calls (e.g. `level1` through `level5` in `nested_calls`) to properly load operands from local variables, so that arithmetic computations across nested call frames produce exact native-equivalent results.
6. As a compiler developer, I want loop counter comparisons in counting loops (e.g. `fizzbuzz`) to read termination bounds from converted local variables, so that loop conditions terminate promptly without infinite loops or timeouts.
7. As a compiler developer, I want `is_abi_visible` to classify accesses based on entry-relative VSA offset intervals rather than dynamic RSP-relative offsets, so that frame modifications do not invert variable visibility.
8. As an emission engineer, I want `create_exp` in the LLVM emitter to never construct `inttoptr` from poison or erased registers in precise functions, so that generated LLVM IR is semantically sound and passes verification.
9. As a tester, I want `scripts/semantic/run_semantic.sh` to report 8/8 PASS with byte-identical stdout between native binaries and lifted executables, so that the semantic regression gate is fully green.
10. As a tester, I want `scripts/semantic/run_semantic_all.sh` to report 31/31 PASS across the entire corpus, so that all synthetic and real programs in the corpus maintain native equivalence.
11. As a release engineer, I want `scripts/check_allocas.sh` to continue reporting 124/0 passes, ensuring that frame erasure and per-region alloca shapes remain compliant with ADR 0001 and ADR 0004.
12. As a maintainer, I want all diagnostic and debugging output to remain clean and controllable via environment variables, so that automated CI and test runs produce clean status logs.

## Implementation Decisions

- **Classification Rule:** The `is_abi_visible` check in `stack_to_locals` will use the entry-relative offset ($lo \ge 0$) to identify incoming caller arguments. All accesses with $lo < 0$ inside convertible regions are classified as local stack slots.
- **Nested Load Rewriting:** The second pass of `stack_to_locals` (`nested_rewrite`) traverses all expressions using the BIL expression mapper, rewriting any `Bil.Load` whose address matches a converted cell in `cells` to the corresponding scalar slot or array local.
- **Precise Frame Safety:** For precise functions where the model frame is erased, the emitter will ensure that all local accesses are fully resolved through their allocated `stack_rN` regions or local variables, preventing fallback to raw memory dereferences of uninitialized registers.
- **Preservation of Sound Fallback:** Degraded functions and non-convertible regions continue to use the sound model frame fallback (`%frame = alloca [N x i8]`), preserving full soundness and existing structural invariants.

## Testing Decisions

- **External Behavior Testing:** Tests will assert end-to-end native-vs-lifted equivalence (byte-identical stdout diff and identical return codes) rather than internal AST state.
- **Seams:**
  1. `scripts/semantic/run_semantic.sh` — The primary 8-binary semantic regression gate (including `deep_recursion`, `array_local`, `factorial`, `many_args`, `rmw_oob`, etc.).
  2. `scripts/semantic/run_semantic_all.sh` — The comprehensive 31-binary corpus gate (including `nested_calls`, `fizzbuzz`, `variadic`, `va_arg_mixed`, etc.).
  3. `scripts/check_allocas.sh` — Structural validation ensuring exact 124/0 pass rate on alloca rules (a)-(d).
  4. `dune runtest` — Unit tests for VSA and IR emission.
- **Prior Art:** Existing scripts in `scripts/semantic/` and test runners in `test_cbat/`.

## Out of Scope

- Introducing new widening strategies (landmark-directed widening is specified separately in `landmark-directed-widening/spec.md`).
- Changes to calling convention register sets or BAP soft-float intrinsic models.
- Support for non-PIE binaries (the corpus remains exclusively PIE ET_DYN).

## Further Notes

- The fix directly resolves three open green-gate issues:
  - Issue 04: `04-fix-deep-recursion-threading.md`
  - Issue 05: `05-fix-nested-calls-threading.md`
  - Issue 06: `06-fix-fizzbuzz-widening.md`
- Once implemented and verified, all 31 corpus binaries will pass semantic equivalence tests cleanly.
