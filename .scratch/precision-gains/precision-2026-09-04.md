# Ticket-02 precision gains — verification + mechanism papers (2026-09-04)

Read-only verification of the prior session's ticket-02 report against battery
artifacts. No battery re-run. Worktrees `/tmp/opencode/rr-02` (fb1cb71) and
`/tmp/opencode/rr-ctrl` used as read-only references.

## 0. Method

- Artifacts: `/tmp/opencode/{rr02-probe.txt, ctrl-probe.txt, rr02-watch.txt,
  ctrl-watch.txt, rr02-emissions/, ctrl-emissions/}` (all present; nothing
  marked UNVERIFIED).
- Probe semantics differ by construction (verified in source): ctrl probe runs
  `Relevance.analyze` per sub and denotes tagged defs only (header
  `precision probe (restriction ON)`; `rr-ctrl/test_cbat/precision_probe.ml`
  `Relevance.analyze` at `run_sub`); rr02 probe denotes every def (header
  `gate-free`; `rr-02/.../precision_probe.ml` `let tagged = true`). So the
  probe delta measures the whole restriction-removal effect, not one lane.
- BIN metric (last two columns): `ldstk_exact / (exact+bounded+top+bottom_live)`
  (filtered) and over `+bottom_dead` (full); confirmed in
  `rr-02/test_cbat/precision_probe.ml` `print_bin_line`. Both files share line
  numbering (spot-checked: struct subs at :454–:473 in both).
- Emission-path note (load-bearing for §1): in `rr-02/src/bil2llvm.ml`, the
  `Unbounded` arm (:988, warn at :995) and the non-singleton
  `Range`/`Infinite` arms both fall through to `create_exp` (raw-memory
  fallback). Hence Unbounded→Range/Infinite on a non-convertible access
  changes the warning but emits byte-identical IR. All five top-5 `out_*.ll`
  are byte-identical ctrl-vs-rr02 (`cmp`; only 11/32 binaries differ, none of
  the five); every emission delta below is warning-lines-only.

## 1. Top-5 table (by ldstk-exact gain, BIN lines)

| # | binary | ctrl → rr02 (exact %) | Δ (pp) | primary mechanism | artifact cite | status |
|---|---|---|---|---|---|---|
| 1 | struct | 72.97 → 100.00 | +27.03 | escape lane live | BIN ctrl-probe.txt:474, rr02-probe.txt:474; err_struct.txt ctrl:24, gone in rr02 | VERIFIED |
| 2 | list | 79.64 → 100.00 | +20.36 | escape lane live (+ full denotation) | BIN :232/:232; err_list.txt ctrl:15,34,50, gone in rr02 | VERIFIED |
| 3 | sret_big | 82.50 → 98.51 | +16.01 | escape lane live (residual = genuine escape) | BIN :453/:453; err_sret_big.txt ctrl:2,4, gone in rr02 | VERIFIED |
| 4 | struct_arr_dynidx | 89.47 → 100.00 | +10.53 | escape lane live (+ Channel-2, touch) | BIN :492/:492; err_struct_arr_dynidx.txt ctrl:2,9, gone in rr02 | VERIFIED |
| 5 | struct_by_value | 90.24 → 100.00 | +9.76 | full denotation (call-free sub coverage) | BIN :509/:509; no Unbounded either side | VERIFIED |

All five deltas reproduce the prior-session report (struct +27.0, list +20.4,
sret_big 82.50→98.51, dynidx +10.5, sbv +9.8; anchors rec_struct 96.77→100.00
at BIN :360, ptr_chain +5.17 at BIN :343).

## 2. Per-candidate evidence

### 2.1 struct (+27.03) — escape lane live
- Probe: `main` ctrl-probe.txt:463 `ldstk (27,0,19,0,0)` → rr02-probe.txt:463
  `ldstk (27,0,0,0,0)`: 19 stack tops → 0; `def_exact` 17→30, `def_top` 51→43.
- Emission: `ctrl-emissions/err_struct.txt:24`
  `@print … mem[RBP - 4]` Unbounded — gone in rr02 (warning-only diff; .ll identical).
- Rationale: `src/progs/struct.c` `main` calls malloc/free/puts/print with a
  heap pointer arg. Under restriction the arg-setup defs were untagged → top →
  `escape_ranges = None` → `MemEnv.top` (the pre-image logic now at
  `rr-02/src/cbat_vsa/cbat_ai_representation.ml:311-336`,
  call site `:2509-2520`); the whole caller frame died at every call. rr02
  denotes arg defs → escape reads real (heap) values → frame survives.
  Discriminator: the access was Unbounded (denoted-but-TOP), not unseeded —
  a value-side fix, not a seeding fix.

### 2.2 list (+20.36) — escape lane live, full denotation contributing
- Probe: `list_destroy` ctrl:212 `def_exact` 10→19 (rr02, same layout);
  `list_remove_next` ctrl:220 14→26; `list_next`/`list_node_value` ctrl:218–219
  8→21; BIN ldstk_top 45→0 (ctrl:232 vs rr02:232).
- Emission: three direct `mem[RBP-x]` Unbounded
  (`ctrl-emissions/err_list.txt:15,34,50` — destroy/insert_next/remove_next),
  all gone in rr02; .ll identical.
- Rationale: malloc/free-heavy call graph (`src/progs/list.c`) — same escape
  death as 2.1. The `def_exact` doublings across callees are the full-denotation
  share: previously-skipped producer defs are now denoted so offset chains complete.

### 2.3 sret_big (+16.01) — escape lane live; residual is genuine escape
- Probe: `build` ctrl-probe.txt:441 `ldstk_top` 12→0; `checksum` ctrl:442 top
  1→0; BIN w_big stays 1 and w_max stays 2⁶³−1 both sides (BIN :453).
- Emission: `ctrl-emissions/err_sret_big.txt:2` (`@build mem[RBP-0x14]`) and
  `:4` (`@checksum low:32[RAX]`) Unbounded — both gone; .ll identical.
- Rationale: `main` calls `build` (hidden sret pointer = stack address as arg)
  and `checksum(&a)` (frame address as pointer arg). With the lane live the
  frame survives except the genuinely-escaped cells — the leftover 1.49% /
  w_big = 1 is exactly the escaped sret slot. Matches spec §2.4 prediction 1
  nearly literally.

### 2.4 struct_arr_dynidx (+10.53) — escape lane live + Channel-2 (touch)
- Probe: `touch` `def_exact` 7→21; `main` (ctrl-probe.txt:482) w_max 113→1,
  `ldstk_bounded` 2→0; BIN :492.
- Emission: `ctrl-emissions/err_struct_arr_dynidx.txt:2`
  (`@main mem[RBP-4]`) and `:9` (`@touch low:32[RAX]`) Unbounded — both gone.
- Rationale: `touch` calls `runtime_idx` (int args, no pointer escape) every
  iteration — under restriction the frame died at each call (escape lane).
  The `@touch low:32[RAX]` dynamic-index address additionally needs Channel-2:
  `rewrite_addr` fails on the indexed form, but the denoted address is bounded
  and inside the ±64 KiB neighborhood
  (`rr-02/src/cbat_vsa/cbat_vsa.ml:3031-3032`, `is_seed` at `:3043`), so it
  seeds and classifies `Range`.

### 2.5 struct_by_value (+9.76) — full denotation
- Probe: `modify_copy` (ctrl-probe.txt:501) def buckets byte-identical, but
  tagged b2_3 0→12 — pure coverage gain (rr02 tags every denoted def);
  `main` (ctrl:500) `def_exact` 12→38, `def_top` 21→13 (escape share: main
  calls modify_copy/printf). No Unbounded on either side (verified by grep).
- Rationale: `modify_copy` is call-free (`src/progs/synth/struct_by_value.c`),
  so no escape death is possible inside it — its gain is the deleted
  `denote_def` gate alone (`rr-02/src/cbat_vsa/cbat_vsa.ml:429-431`).

## 3. Aggregate corroboration

- Unbounded 38→2: `grep -o Unbounded | wc -l` gives 38 over 27 ctrl files vs 2
  rr02 files. Residuals: `rr02-emissions/err_union_overlap.txt:4`
  (`RAX := mem[RAX]` — genuinely unbounded base) and
  `rr02-emissions/err_array_local.txt:4` (widened RBP-padded load) — both
  sound fallbacks, correctly unseeded/unbounded.
- Saved-address class closed: `@two_pass low:32[RAX]`
  (ctrl `err_va_arg_vacopy.txt:5`), `@sum_n low:32[RAX]`
  (ctrl `err_variadic.txt:3`), `@touch` (above), `@consume_mixed`
  (ctrl `err_va_arg_mixed.txt:2`) — zero Unbounded in all three rr02 files.
- Watch item (not a failure): `va_arg_mixed` filtered-exact +1.73 but full-ldst
  87.37→78.49 — Channel-2 seeds more accesses (denominator grows) while two
  remain TOP. Expected per spec §2.4.4 (counts rise; conversion is region
  merging's job).

## 4. Per-mechanism papers (primary sources only)

- **M1 escape lane live → WYSINWYX** (Balakrishnan et al., "WYSINWYX: What You
  See Is Not What You eXecute", ACM TOPLAS 2010).
  URL: https://dl.acm.org/doi/10.1145/1749608.1749612 (author PDF:
  https://research.cs.wisc.edu/wpis/papers/wysinwyx.final.pdf).
  Backing: §3, Figs. 9–11 — `MergeAtEndCall`: at a call, esp `(AR_C, s)` maps
  to callee `(AR_X, 0)`≡`(AR_C, s−4)` (Obs. 3.3), ebp is restored from the
  caller (`out[ebp] := in_c[ebp]`), and only the callee's a-locs are refreshed
  — i.e. the caller's AR cells survive a call by default. hike's
  `call_abstraction_frame` (keep cells ≥ call-time RSP outside escaped ranges)
  is this rule coarsened to one frame with an escape set.
- **M2 Channel-1 direct seeding → WYSINWYX §2.1–§2.2** (same paper/URL).
  Backing: §2.1 — every local lives at a fixed `offset(rgn, a)` in its AR
  (e.g. `offset(AR_main, var_40) = −40`); §2.2 (Semi-Naïve) — `[esp+offset]` /
  `[ebp−offset]` forms resolve syntactically. hike's `mentions_frame_var` +
  `rewrite_addr` (`cbat_vsa.ml:296`) is the semantic generalization: any
  address affine over frame-derived registers denotes an AR offset, widened
  or not.
- **M3 Channel-2 reloaded subset → WYSINWYX §4.1 + §3** (same paper/URL).
  Backing: §4.1 "The Problem of Indirect Memory Accesses" — through-pointer
  initialization (`pp` at offset −12, struct at −8) is unresolvable from access
  syntax; it needs the value-set of the pointer register. §3 — value-sets are
  held per a-loc, so a stored frame-derived value IS an offset value-set, and
  `Mem.Key.of_wordset` unification is the paper's region+offset addressing.
  The SUBSET-never-intersection invariant is hike's soundness addition (spec
  §2.2), not the paper's — flagged in §5.
- **M4 full denotation → Balakrishnan & Reps, "Analyzing Memory Accesses in
  x86 Executables", CC 2004, LNCS 2985, pp. 5–23.**
  URL: https://link.springer.com/chapter/10.1007/978-3-540-24723-4_2 (author
  PDF: https://research.cs.wisc.edu/wpis/papers/cc04.pdf).
  Backing: VSA defines abstract transformers for every instruction and runs
  whole-program — there is no slicing pre-pass in the analysis. The removed
  concept is Weiser slicing ("Program Slicing", IEEE TSE 10(4), 1984,
  pp. 352–357; https://doi.org/10.1109/TSE.1984.5010248): a slice preserves
  behavior only w.r.t. the slicing criterion, so restricting denotation to a
  syntactic slice silently drops value flows (here: arg-setup defs, §2.1–2.2).
- **M5 genuine-subset meet → Cousot & Cousot, "Abstract Interpretation: A
  Unified Lattice Model …", POPL 1977, pp. 238–252.**
  URL: https://doi.org/10.1145/512950.512973 (author page:
  https://www.di.ens.fr/~cousot/COUSOTpapers/POPL77.shtml).
  Backing: §§5–7 (program properties form a complete lattice; meet = greatest
  lower bound), §8 (fixpoint construction by monotone iteration) — a meet that
  does not strictly descend equals the current value, so applying it is a
  no-op. The skip-itself is engineering (§5 flag).
- Unchanged infrastructure (not ticket-02 mechanisms, cited for the record):
  Bourdoncle WTO ("Efficient Chaotic Iteration Strategies with Widenings",
  FMPA 1993, LNCS 735, pp. 128–141;
  https://link.springer.com/chapter/10.1007/BFb0039704); Simon & King
  landmarks (APLAS 2006, LNCS 4279 ch. 11 — header verified against worktree
  copy `/tmp/opencode/rr-02/11924661_11.pdf`; DOI 10.1007/11924661_11 per
  Springer convention); Mauborgne & Rival trace partitioning (ESOP 2005, LNCS
  3444, pp. 5–20; https://doi.org/10.1007/978-3-540-31987-0_2); Cousot &
  Halbwachs polyhedral widening (POPL 1978, pp. 84–97;
  https://doi.org/10.1145/512760.512770).

## 5. Engineering-only flags

- **Genuine-subset skip (M5 policy): no paper.** CC'77 backs meet/monotonicity;
  skipping a non-descending meet is implementation (avoids churn), provably a
  no-op by antisymmetry (m ⊑ cur ∧ ¬(m ⊏ cur) ⇒ m = cur). Engineering-only.
- **Channel-2 SUBSET invariant + ±64 KiB neighborhood: no paper.** WYSINWYX
  backs stored-offsets and indirect resolution; the subset-vs-intersection rule
  and the constants are hike's soundness policy (spec §2.2). Engineering-only.
- **Escape scope (written-regs escape set, whole-memory-top fallback): no
  paper.** WYSINWYX backs caller-frame survival; the abstract-call-site
  engineering (which regs are read, singleton-RSP requirement) is hike's.
  Engineering-only.

## 6. Status

Top-5 deltas VERIFIED from artifacts (probe BIN + err-file diffs + .ll
identity). Mechanism attribution is inference from warning shapes (denoted-TOP
⇒ value-side: escape/denotation), call structure of the fixture sources, and
the rr-02 code sites — per-def instrumentation would be needed for proof, but
no artifact is missing, so no candidate is UNVERIFIED. Headline: ticket-02's
gains are dominated by a single mechanism, the escape lane going live
wholesale (spec §2.4.1), with full denotation as the secondary share and
Channel-2 visible in the indexed-address warnings.
