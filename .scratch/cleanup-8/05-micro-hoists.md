# Ticket 05 — walk-driver micro-hoists + edge_cond collapse

Status: landed as 8281a8b (2026-09-06). Bundled single ticket (grilled 2026-09-06, 2
rounds): five loop-invariant deletions in the walk driver plus the
single-field `edge_cond` collapse left over from ticket 01. Lands on the
cleanup-8 branch as the fifth commit. `rc_blocks` stays shelved and
independent (different functions).

## Bar (settled)

Reasoning + smoke check + standard battery. No per-item A/B: each item
deletes work whose result already sits in a variable one line up (or a
static lookup recomputed per visit). Smoke check is a REGRESSION check,
not a speedup proof — run `subtimes` on grep `sub_e350` (the C1 reference
sub, ~3.37s producer) before/after and confirm no slowdown; IR
byte-identity 35/35 is the real gate. Expected aggregate: ~0.05–0.15s on
a heavy sub (inside run noise — that is fine and stated upfront).

## Items (all verified present 2026-09-06; line numbers are main+lane)

1. **`def_constraints` takes `~blk_state`** (`cbat_vsa.ml:1296-1300`,
   call site 1442). Verified: `sol`/`blk` appear nowhere in the 1296–1411
   body except the signature and the single `Solution.get`. New shape:
   `def_constraints ~blk_state:AI.t (env : AI.t ref) (d : def term)
   (live : Live.t) (cstr : wordset)`. Internal only (not in the `.mli`,
   single caller) — no fixture fallout.
2. **`List.rev` → `Term.enum ~rev:true`** (`cbat_vsa.ml:1419`, inside
   `reverse_def_walk`): `Term.enum def_t blk |> Seq.to_list |> List.rev`
   materializes and copies the block's def list (~11.6 defs/block ×
   ~276k pops ≈ 3.2M elements per heavy sub) purely to feed `List.iter`.
   `Term.enum ~rev:true def_t blk` yields the reversed sequence directly
   (`bap_ir.ml:1090-1091`, verified present).
3. **Static preds table** (`cbat_vsa.ml:2644`, in `process_vertex`):
   `CFG.Node.preds v cfg |> Seq.to_list` re-derives the static predecessor
   list on every one of ~2,504 visits per sub. Build one
   `Tid.t list Tid.Map.t` (or set map) per run next to `rc_out_edges` in
   `mk_rctx` and read it. The CFG never changes during a run.
4. **`rc_live_in` hoist** (`cbat_vsa.ml:2703`): the
   `Core.Map.find rc.rc_live_in v` sits INSIDE the per-pred loop but
   depends only on the visited block. Hoist above the `List.map preds`.
5. **Guard-first `observe_unsat_var`** (`cbat_landmarks.ml:76-84`):
   currently bitwidth-check → `meet` → bottom-check → `!widening_at_head`
   check. Move the `!widening_at_head = None` early-out above the `meet`
   (keep it below the bitwidth check — nearly free and filters first).
   Safety rests on `meet` being pure: verified — `Cbat_clp_set_composite.meet`
   returns a value consumed only by the `is_bottom` test; all side effects
   (landmark recording) sit below the guard. Outside a cycle the function
   becomes one ref check.
6. **`edge_cond` collapse** (ticket-01 leftover): the type is now
   `{ acc_cond : exp }` only (`cbat_vsa.ml:2112`). Collapse
   `edge_conds_of`'s tables to `exp Tid.Map.t Tid.Map.t`, delete the type,
   update the construction (2132), the read (2304 `ec.acc_cond`), and
   `denote_jump`'s `?edge_conds` param type (2394). All internal
   (not in the `.mli`, no test/probe refs — verified).

## Verification

- `dune build` + `dune build @install` (blocker) + vsa-debug probes build.
- `dune runtest` green (no fixture touches these paths, but the walk
  fixtures F1-*. would catch a semantic slip).
- Smoke: `subtimes` on `/usr/bin/grep sub_e350` before/after — record both
  numbers in the commit message even if inside noise.
- Full battery + IR byte-identity 35/35 vs the lane control.
