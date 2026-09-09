# T6 — L4: data-section relocation rendering — VERDICT

Branch `tm/t6-reloc`, commit `90916fb` ("T6: relocated data words render
through the code-reference map"). Blind round: no `dune install`, no
`bap` (the shared plugin slot is held elsewhere this wave); the merger
runs the battery.

## The mechanism (what rendered wrong, and why — IR-level proof)

`hike.ml` populated the section globals' initializers (the "pass 2"
loop over data/rodata/got/got.plt/.data.rel.ro) BEFORE calling
`emit_program`. `Bil2llvm.set_section_initializer` renders every 8-byte
word of the section's raw bytes through `Bil2llvm_section.remap_native_addr`,
whose two arms are:

1. `Symtab.find_by_start` → `ptrtoint (ptr @sub)` — the word names a
   lifted sub;
2. the `section_remap` ranges → `ptrtoint (gep @section, word - lo)` —
   the word points into an emitted data section.

At initializer time the module contained NO functions (`emit_program`
defines them), so arm 1 returned `None` for EVERY word and every
function-valued relocated addend (`R_X86_64_RELATIVE` targeting a
lifted sub) fell to the raw-int arm: the emitted data global carried
the INPUT binary's vaddr.

Arm 2 worked even before the emission (the section globals exist from
pass 1), which is why the one data addend that points into `.data`
itself (the `__dso_handle` self-pointer, `.data+8` → `0x4010`) rendered
correctly (`@data = global [2 x i64] [i64 0, i64 ptrtoint (ptr
getelementptr inbounds (i8, ptr @data, i64 8) to i64)]` in the
reference IR) and masked the bug.

**Runtime proof (the 2026-09-09 -O2 corpus, the binary the L4 verdict
was measured on — `/home/tovpr/sp-battery/corpus-test-o2/fptr_table`,
still on disk):** gcc placed tbl slots 0 and 2 (`&fn0` `0x11e0`,
`&fn2` `0x1200`) in `.data.rel.ro` (`0x3dd0..0x3de0`) and built slots 1
and 3 with `lea`s. The lift emitted
`@data.rel.ro = constant [2 x i64] [i64 4576, i64 4608]` — both slots
RAW (arm 1 structurally dead), while the lea'd `&fn1`/`&fn3` rendered
as `ptrtoint (ptr @fn1/@fn3)` (those are `Int` constants materialized
at BODY time, where arm 1 is alive). The program loaded the raw slots
(`movq .data.rel.ro(%rip),%xmm0`), stored them into the stack table,
and called through them: the typed-frame address materialization
(`create_addr_ptr`: `frame + (word − anchor) + 88`, with
`anchor = frame+88`) is an exact modular-arithmetic IDENTITY for any
word — `frame + w − (frame+88) + 88 = w` — so the raw input-world
vaddr became the literal indirect-call target → SIGILL (rc=132).
That closes the chain end-to-end at the IR level: the raw RENDERING
was the sole defect; the call path faithfully jumps to whatever the
data word holds.

## The rule installed (and where it sits)

One ordering rule in `src/hike.ml`: the section-initializer loop moves
AFTER `Bil2llvm.emit_program`. Every 8-byte word of every emitted
section now renders through the SAME map the code references use
(`create_rip_relative_addr`'s Int arm): symtab function starts first,
emitted-section ranges second; a word that names no lifted world keeps
the identity (raw). Total over all sections, all slots, no per-binary
shape tests, no special cases, no gates. `emit_program` reads no
initializer (body emission loads from section bases at runtime; the
compile-time `.text` reads use the stashed bytes), so the reorder is
behavior-preserving except for the initializer contents — which is the
fix. The public seam (`bil2llvm.mli`) is unchanged; `hike.ml` remains
the only caller of `set_section_initializer`.

Identity-arm words on the current corpus (both remain raw, both
harmless — the lifted program never dereferences them): `@got.plt[0]`
(`_DYNAMIC`, a non-emitted section) and `@got.plt[3]` (`printf@plt+6`,
a non-symbol-start text address). Deliberately NOT added, with reasons:

- **Containing-function arm for non-start text words** (`owners`-style
  `@fn + delta`): invents an address with no lifted semantics (the
  lifted instruction layout differs); identity is the sound answer.
- **`create_immidiate` stays symtab-only** (no section-range arm): it
  fires on EVERY `Int` in the program; remapping integers that merely
  fall inside a data section's range would rewrite innocent numeric
  constants. PIE data references arrive as rip-relative accesses
  handled by the full-map path (`create_rip_relative_addr`), so the
  asymmetry is unexercised; recorded here so nobody "completes" it
  blindly.

## What the merger should look for in the battery

Measured over BOTH current corpora (`/tmp/corpus`, `/tmp/corpus_o2`,
33 binaries each) with readelf: **no current corpus binary has a
function-start RELATIVE addend inside an EMITTED section.** The only
function-start addends are the `.init_array`/`.fini_array` entries
(`frame_dummy`, `__do_global_dtors_aux`) and those sections are not
emitted as globals (nothing in the lifted program reads them). The one
addend inside an emitted section (`.data`'s self-pointer) already
remapped through arm 2.

Expected outcomes:

| gate | expectation |
|---|---|
| -O0 emission / semantics | byte-identical emissions; 33/33 PASS (no slot changes on this corpus) |
| check_allocas | unchanged (green) |
| strict opt-safety (-O0) | unchanged — the typed-model regression (nested_struct, struct_by_value) is a different lane (T1), untouched here |
| -O2 emission | rc=0, byte-identical |
| -O2 pinned gate | **no movement expected from this lane** — see below |

**The fptr_table pin entry — known uncertainty, stated plainly.** The
pin's L4 attribution is runtime-proven against the 2026-09-09 -O2
binary, whose fn table was half `.data.rel.ro`. The CURRENT -O2 binary
(rebuilt 2026-09-10 with sp_reload) forms ALL FOUR fn pointers with
rip-relative `lea`s into stack slots — `.data.rel.ro` does not exist in
it, and the lea path already remaps at body time. The L4 data-path
exposure is therefore GONE from that binary's shape: if fptr_table -O2
still fails after this lands, that residual is a DIFFERENT mechanism
(candidate classes: the SSE/lane or callee-side classes from the
attribution verdict) and must be re-attributed with the slot granted —
it is NOT evidence against this fix. This fix fires for every binary
that relocates function pointers into an emitted data section (the
`&fn`-in-`.data.rel.ro`/`.data` class — common at -O2 and -O1 for
static tables); the class is live for arbitrary inputs regardless of
the current corpus's shape.

If the merger's battery does flip fptr_table (i.e. the residual was
still fed by a raw slot I could not see blind): the golden list and
AGENTS.md move in the merger's commit, labeled IMPROVEMENT by the pin —
the designed movement.

## Blind-round validation

| gate | result |
|---|---|
| `dune build` (default) | rc=0 ✅ |
| `dune build --build-dir _build-debug --profile vsa-debug` | rc=0 ✅ |
| `dune runtest` | rc=0; failure set == the pre-existing 8-failure baseline (E2eD-7/8, LM F1-*); clpequiv **2,861,148 checks / 0 mismatches** ✅ |
| instrumentation blocker (`src/check_instrumentation.sh`) | clean ✅ |
| no unit pin added | the defect was the CALLER's ordering (hike.ml); a fixture test that defines the function before initializing cannot fail, and the suite bans tests that cannot fail — the corpus battery is the oracle for this rule |
