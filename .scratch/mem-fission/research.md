# Research: per-region BIL mem vars ("mem fission") for hike

**Question.** Can hike give each stack region its own BIL mem var — rewriting
`mem := mem with [RBP-4] <- x` to `stack_r0 := stack_r0 with [...] <- x` — so
(a) DCE's used-set sweep naturally deletes never-loaded stores, and
(b) the emitter routes each mem var to its alloca without consulting VSA tags?

**Method.** Primary sources only: the installed BAP interface
(`/home/tovpr/.opam/bap-flambda/lib/bap-std/bap.mli`), BAP's shipped implementation
sources (`.../bap-std/types/*.ml`, `.../bap-std/sema/*.ml` — the actual code behind
the `.mli`), and the hike tree at `/home/tovpr/backup/hike-finding1/`. Every claim
carries a file:line. Paths are repo-relative after the first mention.

**Headline answers.** (1) BIL-legal: yes — the mem operand is just a `Mem`-sort
expression, and nothing in the type system, the normal forms, or BAP's own
infrastructure names a canonical var. (2) VSA-transparent: yes — and in the
current pipeline it is *structurally* transparent because the VSA runs BEFORE
stack-to-locals. (3) DCE-enabling: **NOT as-is** — two concrete blockers in
`hike_dce.ml` (the `is_mem` keep clause and the store chain's self-keep), with a
precise minimal fix. (4) Emitter-additive: yes — the emitter never inspects the
mem operand today, so mem-var routing is a purely additive dispatch.

---

## 1. The BIL memory model

**The constructors** (`bap.mli:2001-2002`, inside `Bil.Types`):

```ocaml
| Load    of exp * exp * endian * size (** load from memory *)
| Store   of exp * exp * exp * endian * size (** store to memory  *)
```

with helpers `Bil.load : mem:exp -> addr:exp -> endian -> size -> exp`
(`bap.mli:2286-2287`) and `Bil.store : mem:exp -> addr:exp -> exp -> endian -> size -> exp`
(`bap.mli:2289-2290`). The visitor signatures confirm the field order:
`enter_load : mem:t -> addr:t -> endian -> size -> 'a -> 'a`
(`bap.mli:3589`, implemented at `types/bap_visitor.ml:36-41`) and
`enter_store : mem:t -> addr:t -> exp:t -> endian -> size -> 'a -> 'a`
(`bap.mli:3594`, `types/bap_visitor.ml:29-34`).

**`mem` is just an expression of `Mem` sort.** The exp type is untyped-syntax;
sorts come from `Bil.Types.typ`:

```ocaml
and typ =
  | Imm of int                     (** [Imm n] - n-bit immediate   *)
  | Mem of addr_size * size        (** [Mem (a,t)] memory with a specifed addr_size *)
  | Unk
```

(`bap.mli:2013-2016`). A `Var` carries one of these via `Var.create ... typ`
(`bap.mli:2951`); `Var.typ : t -> typ` (`bap.mli:2957`). Type checking
(`Type.infer`, `bap.mli:2795-2810`) only demands that the mem operand of a
Load/Store be `Mem`-sorted with the matching address width — `Type.bad_mem`
(`bap.mli:2851`) is raised for a non-mem where a mem is expected. There is **no**
restriction to one canonical var anywhere:

- The BNF1 normal form's memory rule says loads "can be only applied to **a
  memory**" and stores are committed "via the assignment operation ... where the
  rhs has type mem_t" — i.e. it constrains the *sort*, and explicitly notes this
  "is effectively the same as make the [Load] constructor to have type
  ([Load (var,exp,endian,size)])" (`bap.mli:4032-4040`). Any `Mem`-typed var
  qualifies; no name is privileged.
- BAP's own `prune_unreferenced` treats physical/virtual vars uniformly by kind,
  not by a mem-name test (`bap.mli:2335-2362`).
- grep for `"RSP"`/`"mem"`-style name tests in hike `src/` finds **zero**
  mem-name checks (the only hit is a comment, `src/hike_vsa_relevance.ml:67`);
  hike's mem-ness test is purely sort-based (§2).

**Multiple mem-typed vars in one sub are legal and exercised.** The fixture
`mk_caller_alias` builds one sub with two distinct mem vars and runs the full
fixpoint over it: `let m = memv "t4_m"` / `let m2 = memv "t4_m2"`
(`test_cbat/test_cbat.ml:1612-1613`), stores into both
(`test_cbat.ml:1651-1662`), and asserts fixpoint facts about them
(`test_cbat.ml:1753-1768`). Same pattern at `test_cbat.ml:1938-1939`
(`t21_n_m`/`t21_n_m2`), `test_cbat.ml:2030-2031` (`t22_m`/`t22_m2`),
`test_cbat.ml:2465` + `2523` (`e2ed_m`/`e2ed_m2`). The VSA carries them as
independent entries (§4).

**Creating a fresh mem-typed var — hike's own helpers:**

```ocaml
let memv (n : string) : var = Var.create ~is_virtual:false ~fresh:false n (Type.Mem (`r64, `r8))
```

(`test_cbat/test_cbat.ml:1422`; same idiom in the probe
`zz_scratch_probe/r6view/probe.ml:13` and ad-hoc at `test_cbat.ml:533`,
`658`, `test_relevance.ml:90` etc.). Production already creates Mem-typed locals
in `src/hike_stack_to_locals.ml`:

```ocaml
let arr_of (lo : int64) (hi : int64) : var =
  Var.create ~is_virtual:false ~fresh:false
    (Printf.sprintf "arr_%Ld_%Ld" lo hi)
    (Type.Mem (Size.addr_of_int_exn 64, Size.of_int_exn 8))
```

(`src/hike_stack_to_locals.ml:60-63`) — and these are used as Load/Store memory
operands and as def lhs (§6), i.e. the exact fission shape already ships.
`convutils.ml`'s `hike_stack_var` (`src/convutils.ml:93-94`) is the same
`Var.create ~is_virtual:false ~fresh:false` idiom with `Type.Imm 64`.

**A caveat worth recording:** the single `mem` var of lifted BIL is a *lifter
convention*, not a language invariant. Everything in hike that looks mem-ish is
sort-based (`Convutils.is_mem`, §2), so a second mem var changes no predicate's
answer except by being `Mem`-sorted too.

---

## 2. hike's `is_mem` and every rule that keys on it

**The definition — sort-based, not name-based** (`src/convutils.ml:103`):

```ocaml
let is_mem var = match Var.typ var with Mem _ -> true | _ -> false
```

**Every use site in `src/`:**

| File:line | What keys on it |
|---|---|
| `src/hike_dce.ml:71` | `is_sp_value_def`: a def whose lhs is mem is never an "SP-value def" (excluded from the precise-path SP erasure set) |
| `src/hike_dce.ml:95` | **`keep`'s unconditional mem-keep**: `Core.Set.mem used lhs \|\| is_ret_reg target lhs \|\| Convutils.is_mem lhs \|\| is_call_reg ... \|\| is_intrinsic_var lhs` — every `Mem`-typed lhs is always kept ("Memory writes ... are always kept", `src/hike_dce.ml:1`) |
| `src/hike.ml:46` | `free_vars`: the sub's free vars are filtered `not @@ is_mem var` before becoming the signature/arg list |
| `src/bil2llvm.ml:797` | `is_plt_trampoline`: the trampoline test filters mem vars out of the free-var list |
| `src/bil2llvm.ml:1779` | **the transfer-phi filter** in `collect_sub_data`: `((not @@ is_mem var) \|\| Var.same var (pc ...)) \|\| sp \|\| fp` — mem vars get no phi lane (§7) |
| `src/hike_stack_to_locals.ml:657` | `frame_value_def`: a mem lhs is not a frame-value def |
| `src/hike_stack_to_locals.ml:1014` | `rewrite_def`'s whole-access test: a def is a candidate rebind iff its lhs `is_mem` |
| `src/hike_model_clean.ml:78, 90, 97, 108, 117, 127, 220, 258` | the push/prologue/epilogue shape predicates (`is_sp_delta8`, `is_store_at_sp`, `is_temp_copy`, `is_load_from_sp_mem`, `is_reg_restore`, `is_leave`, `is_rbp_assign_rsp`, the prologue-skip rule) — all *negative* guards ("lhs is not mem") plus the positive `is_store_at_sp` (line 90) |

Consequences for fission: **all of these keep working unchanged** — they are
sort-based, and a per-region mem var is `Mem`-sorted exactly like `mem`. The two
that *matter* to the design are `hike_dce.ml:95` (blocks the DCE the user wants,
see §3) and `bil2llvm.ml:1779` (already the right behavior: no phis, §7).
`hike_model_clean.ml` runs in `hike-filter`, i.e. *before* any fission could
exist (`src/hike.ml:654-658`), so its mem tests only ever see the lifter's var.

---

## 3. Free-vars / used-set mechanics

**Does `Def.free_vars` include the mem operand of a Load/Store? Yes.**
`Def.free_vars def = Exp.free_vars (rhs def)`
(`types/bap_ir.ml:729`; documented `bap.mli:9001-9004`). `Exp.free_vars` folds a
visitor over the expression, collecting every `Var` node reached
(`types/bap_helpers.ml:1005-1017`), and the base visitor's `visit_load` traverses
`self#visit_exp mem |> self#visit_exp addr` (`types/bap_visitor.ml:38-41`),
`visit_store` traverses mem, addr and data (`types/bap_visitor.ml:31-34`).
So `x := Load(stack0, addr)` has **`stack0` in its free vars** — the mem operand
is an ordinary read of an ordinary variable. (This is also why the relevance
pass had to *exclude* mem-lhs defs from its sp-derived propagation:
`src/hike_vsa_relevance.ml:117-133`, the `is_memory_side_effect` skip.)

**`Blk.free_vars`**: "a set of variables that occurs free in block [blk]. A
variable is free, if it occurs unbound in the expression and there is no
preceding definition of this variable in a block" (`bap.mli:9439-9443`);
implementation `types/bap_ir.ml:1658-1667` — a sequential kill-set fold over
`Ir_def.free_vars -- kill ++ vars`. So a block that only *loads* `stack0` (never
defines it in-block) has `stack0` in its live-in set.

**`Sub.free_vars`**: "computes a set of variables that are free in [sub] ... used
before defined or is not locally bound" (`bap.mli:8776-8782`); implementation is
a liveness fixpoint (`sema/bap_sema_free_vars.ml:126-129` delegating to
`Live.compute`, `bap_sema_free_vars.ml:82-91`, or the SSA fast path at lines
11-14), wired as `Sub.free_vars = FV.free_vars_of_sub` (`sema/bap_sema.ml:48`).
A fissioned var read at the entry before any store would appear here — and is
then *filtered out* of the signature by `src/hike.ml:46`.

**hike's used-set** (`src/hike_dce.ml:38-47`):

```ocaml
let used_of (sub : sub term) : Var.Set.t =
  let v = object
    inherit [Var.Set.t] Term.visitor
    method! visit_def d used = Core.Set.union used (Def.free_vars d)
    method! visit_jmp j used = Core.Set.union used (Jmp.free_vars j)
    method! visit_phi p used = Core.Set.union used (Phi.free_vars p)
  end in v#visit_sub sub Var.Set.empty
```

— a **global syntactic union** over the whole sub; no position, no liveness.

**Consequence for the user's (a): the chain does NOT die naturally — two blockers.**

1. **Self-keep through the store's own rhs.** `stack0 := stack0 with [a] <- x`
   has `stack0` in its own `Def.free_vars` (the Store's mem operand,
   `types/bap_visitor.ml:31-34`). So `stack0 ∈ used_of` **unconditionally** —
   even with zero loads — and the first clause of `keep`
   (`Core.Set.mem used lhs`, `src/hike_dce.ml:95`) keeps every store. A
   store-to-store chain with no loads keeps *itself* alive: each store's rhs reads
   the var the previous store defined.
2. **The `is_mem` keep clause.** `Convutils.is_mem lhs` at `src/hike_dce.ml:95`
   keeps every `Mem`-typed lhs by policy ("Memory writes and ABI registers are
   always kept", `src/hike_dce.ml:1`). A per-region mem var is `Mem`-sorted, so
   every fissioned store is always-kept regardless of the used set.

**The minimal DCE rule that makes (a) work.** Split the used set by *use kind*:
let `load_used` = vars occurring as the **mem operand of a `Load`** (plus any
non-store read — jmps, phis, bare `Var` reads, which BNF1 never produces for mem
vars). A def whose lhs is a fissioned mem var is kept iff `lhs ∈ load_used`; uses
of the var as a **Store's mem operand do not count** (those uses are other stores,
which are themselves only keep-alive-if-load-rooted). Then:

- Chain `s1: stack0 := stack0 with [a] <- x; ...; y := Load(stack0, b)` —
  `stack0 ∈ load_used` ⇒ `s1` kept (and `x`'s def kept through the ordinary
  used set, since `x` is in `s1`'s data free vars). This is exactly the DCE the
  user wants.
- Store-only chain (no loads anywhere): `stack0 ∉ load_used` ⇒ every store of
  `stack0` dies **together** in one sweep round (the fixpoint loop
  `sweep_fixpoint`, `src/hike_dce.ml:104-111`, already re-runs to stability, and
  removing the stores never removes a load-root, so it converges immediately).
- The `is_mem` clause at `hike_dce.ml:95` must be narrowed to keep the
  *non-fissioned* memory (the lifter's `mem` still carries ABI-external traffic
  — see Hazards) — concretely: keep `is_mem lhs` only when the lhs is not one of
  the plan's region mem vars, which requires the fission decision to travel in
  `Convutils.vsa_info` (the `stack_plan` field, `src/convutils.ml:84`, is the
  existing Finding-1 vehicle: one producer, three consumers).

---

## 4. The VSA's memory representation

**Keyed by (mem-var, address), not address alone.** The abstract state is
`{ memories : MemEnv.t; words : WordEnv.t; frame : frame option }`
(`src/cbat_vsa/cbat_ai_representation.ml:196`), with

```ocaml
module MemEnv = MapLattice.Make_indexed_val(VarKey)(Mem)
```

(`cbat_ai_representation.ml:34`) — a **map keyed by the var** (`VarKey` compares
by `Var.same`, `cbat_ai_representation.ml:29-32`), each entry an address-keyed
`Mem.t` interval tree. `AI.find_memory i env v` / `AI.add_memory ~key ~data`
(`cbat_ai_representation.ml:239`, `227-230`) read/write one var's map. Absent var
⇒ `Mem.top` (`cbat_map_lattice.ml:153-158`: absent key reads `L.top idx`; only a
`None` whole-map — the bottom state — reads bottom). So a second mem var starts
at **top, never bottom** — an unsound "path is dead" reading is impossible.

**The denotation DOES read the mem operand.** The Load row
(`src/cbat_vsa/cbat_vsa.ml:459-466`):

```ocaml
| Bil.Load (m, a, e, s) ->
  denote_exp a env >>= val_as_imm >>= fun addr ->
  denote_exp m env >>= val_as_mem >>= fun mv ->
  ... Mem.find (resSize, e) mv k ...
```

and the Store row (`cbat_vsa.ml:467-485`) likewise `denote_exp m env` before
`Mem.add mv ~key ~data`. `denote_exp`'s `Var` arm dispatches on the sort:
`Type.Mem ... -> return_mem @@ AI.find_memory k env v` (`cbat_vsa.ml:447-453`).
So the analysis is **not** mem-var-blind — each var carries its own `Mem.t`.
But a *consistently fissioned* region is a closed system (all its stores and
loads under one var), so the per-var map simply relabels what is today one entry;
and even an *inconsistent* fission is **sound**: a load left on `mem` after its
store moved to `stack_r0` reads `mem`'s map, misses the cell, and gets **top**
(the absent-key default) — imprecise, never wrong.

**The call abstraction handles every mem var.** `AI.call_abstraction_frame`
(`cbat_ai_representation.ml:355-381`) folds **all** `MemEnv` entries:

```ocaml
MemEnv.fold env.memories ~init:env.memories
  ~f:(fun ~key ~data acc ->
      MemEnv.add acc ~key ~data:(Mem.call_keep data ~keep_lo:lo ~escape:ranges))
```

(lines 376-379) — each var's map gets the same frame-keep (cells at/below the
call-time RSP dropped, escape ranges dropped; `Mem.call_keep` itself is
address-keyed within one map, `src/cbat_vsa/cbat_ai_memmap.ml:482-502`). The
whole-memory-top fallback (`| _ -> MemEnv.top`, `cbat_ai_representation.ml:380`)
fires on a non-singleton RSP or an unbounded escape and tops **every** mem var
equally. So a second mem var cannot escape the call-abstraction's modeling:
it receives exactly the treatment `mem` gets today. (The legacy no-frame
abstraction `call_abstraction` also tops all memories: `cbat_ai_representation.ml:351-352`,
pinned by `test_cbat.ml:1820-1823`.)

**Pipeline order makes this moot in production.** The `vsa` pass runs before
`stack-to-locals` (`src/hike.ml:660` relevance → `:666` vsa → `:706`
stack-to-locals → `:722` dce → `:731` convlir), and the tags/regions/plan are
computed on the **pre-rewrite** sub (`src/hike.ml:687-691` — "the per-sub VSA
result INCLUDING the stack model decision ... once, on the PRE-stack-to-locals
sub"). The VSA therefore never sees fissioned BIL if the fission lives in
stack-to-locals — structural transparency. (The `arr_of` locals of today's
stack-to-locals are likewise invisible to the VSA.)

**The relevance pass ignores the mem operand.** `stack_load_store_addr_vars`
visits only the addresses: `visit_load ~mem:_ ~addr ...` /
`visit_store ~mem:_ ~addr ~exp:_ ...` (`src/hike_vsa_relevance.ml:46-56`). Its
`is_memory_side_effect` is sort-based over free vars
(`src/hike_vsa_relevance.ml:70-75`) and exists to *skip* mem-lhs defs in the
sp-derived propagation (`:127`). The backward lane's cell meets also key by the
mem var: `constrain_cell` matches `Bil.Var m` and reads `AI.find_memory k env m`
(`cbat_vsa.ml:1034-1062`), and `constrain_cell_on_trace` the same
(`cbat_vsa.ml:1206-1247`); `edge_constraints`'s `Cell (m, a, s, en, cstr)`
constructor carries the mem expression (`cbat_vsa.ml:2010-2012`). All
per-var-closed; all safe under a consistent fission.

---

## 5. The emitter

**The emitter never inspects the mem operand.** The general expression path:

```ocaml
| Store (_, addr, data, _, _) ->
    let* addr = create_exp llvm_builder blk_tid addr in
    let* data = create_exp llvm_builder blk_tid data in
    create_store llvm_builder (data, addr)
| Load (_, addr, _, size) ->
    let* addr = create_exp llvm_builder blk_tid addr in
    create_load llvm_builder (addr, Size.in_bits size)
```

(`src/bil2llvm.ml:653-659`) — mem is `_` in both. `create_load`
(`src/bil2llvm.ml:474-510`) and `create_store` (`:511-525`) take only the address
(+data) llvalue and emit `inttoptr` + load/store. Every other Load/Store
destructure in the emitter also discards mem: `bil2llvm.ml:955, 959, 962, 968`
(`mem_access_via_ptr`), `:1010, 1024` (`mem_access`'s outgoing/positive arms),
`:1084-1098` (`create_def`'s region-GEP arm), `:1833-1834` (degraded geometry),
`:1395, 1414` (FP-intrinsic width sniffing). The two stack-to-locals-shaped
mapper overrides likewise ignore it: `~mem:_` at `bil2llvm.ml:864, 866, 887, 908`.

**So a rewritten mem var flows through emission with zero change today.** The
routing to storage is decided by the **VSA tag on the def** (`find_def_tag`,
`bil2llvm.ml:760-763`) plus the plan (`mem_access`, `:991-1052`; the split-model
GEP arm keyed on the singleton tag, `:1071-1099`), never by the mem operand.
Emitting a fissioned def today would: (i) fall into `mem_access`/`create_def` as
usual (the def's tid still carries its tag — `Def.with_lhs`/`with_rhs` preserve
the term and its tid, `types/bap_ir.ml:703-715`), and (ii) bind the (void) store
instruction under the fissioned var's name in the block's locals
(`insert_local ctx blk_tid var res`, `bil2llvm.ml:1104`) — a dead binding nobody
reads, exactly like today's `mem` binding. **Mem-var routing is therefore a
purely additive dispatch**: in `mem_access`/`create_def`, when the rhs's memory
operand (or the def's lhs) is one of the plan's region vars, GEP the
corresponding `fr.regions` alloca (`region_of_offset`, `bil2llvm.ml:978-982`, is
the existing span lookup; the regions are built at `:1993-2005`) — no tag
consultation needed for those defs.

One emitter-side nit to keep in mind: the "100% VSA tagging invariant" `failwith`
(`bil2llvm.ml:1046-1052`) fires on an untagged `stack_access` def; fissioned defs
keep their tids so their tags remain found — the invariant is unaffected.

---

## 6. The rewrite vehicle

**BAP's `Exp.mapper` signature** (`bap.mli:3678-3694`):

```ocaml
class mapper : object
  method map_exp : t -> t
  method map_load : mem:t -> addr:t -> endian -> size -> t
  method map_store : mem:t -> addr:t -> exp:t -> endian -> size -> t
  ...
```

(the default implementations map the mem operand through `map_exp`:
`types/bap_visitor.ml:220-226`).

**hike already overrides exactly these hooks** — the Map solution
(`src/hike_stack_to_locals.ml:950-993`):

```ocaml
object
  inherit Exp.mapper
  method! map_load ~mem ~addr e s =
    match local_of_addr addr with
    | Some local -> (... Bil.Load (Bil.Var local, addr, e, s) ...)
    | None -> Bil.Load (mem, addr, e, s)
  method! map_store ~mem ~addr ~exp:data e s =
    match local_of_addr addr with
    | Some local -> (... Bil.Store (Bil.Var local, addr, data, e, s) ...)
    | None -> Bil.Store (mem, addr, data, e, s)
end
```

(`:954-989`, with the read-modify-write splice arm omitted here). The pass also
already **rebinds a def's lhs to a Mem-typed local** — the `Type.Mem` arm of
`rewrite_def`:

```ocaml
| Type.Mem _ -> Def.with_rhs (Def.with_lhs d local) (map_rhs d)
```

(`:1021-1023`), where `local` is an `arr_of` var (`:60-63`) and the mapped rhs is
`Bil.Store (Bil.Var local, ...)` (`:969`). **That is precisely the fission
shape** — a non-`mem` `Mem`-typed var used as both the Store's memory operand and
the def's lhs — and it flows on through DCE (`src/hike.ml:722-729`) and the
emitter (`:731-733`) today. So yes: the same pass can rewrite the mem operand
per-region — one new region-var per convertible region (the `arr_of` recipe),
`map_load`/`map_store` returning `Bil.Load (Bil.Var stack_rN_mem, ...)` for
region-member addresses, and the store defs' lhs rebound with `Def.with_lhs`
for members whose whole rhs is the region's access (`:1012-1019` already
computes that `whole_access` condition with `Convutils.is_mem (Def.lhs d)`).

---

## 7. Block-level threading

**Today `mem` gets no phi threading at all.** The transfer set is filtered in
`collect_sub_data`: `((not @@ is_mem var) || Var.same var (pc ...)) || sp || fp`
(`src/bil2llvm.ml:1778-1785`), so the lifter's `mem` (and any other `Mem`-typed
var) is excluded; the emitter never materializes it (§5). The phi machinery
(`transfer_with_phis` `:1616-1624`, `update_phi` `:1576-1587`,
`build_entry_block` `:1656-1675`) threads only the surviving transfer vars.

**What actually carries cross-block memory state: the address lane.** The
lifter rebinds `mem := mem with [...] <- ...` at each storing block, and BAP's
sequential semantics make a later block's `Load(mem, ...)` read the incoming
binding — `Blk.free_vars` marks the var live-in when used with no preceding
in-block def (`bap.mli:9439-9443`, `types/bap_ir.ml:1658-1667`); `Sub.free_vars`
is a real liveness fixpoint (`sema/bap_sema_free_vars.ml:82-91, 126-129`). But
hike's emitter **ignores the mem var as a value entirely**: every access is
emitted from its *address* through the per-sub `%frame` alloca / the
`stack_rN` allocas (`bil2llvm.ml:991-1102`), and the address is computed from
the phi-threaded RSP/RBP locals (kept at `:1784-1785`; the anchor bound at
`:1683`, fp at `:1688-1694`). The alloca *is* the cross-block state; the store
in block A and the load in block B meet in memory, not in an SSA lane.

**What per-region mems need: nothing new.** Because emission will route by
mem-var *identity* (a compile-time property: which region's alloca) and the
allocas are function-scope values, no runtime threading of the mem vars is
required — the fissioned var never needs a phi, exactly like `mem` today. The
`is_mem` filter at `bil2llvm.ml:1779` already drops fissioned vars from the
transfer set, `hike.ml:46` already drops them from the signature, and the
definedness closure at `:1786-1795` never unions `def_set` into the transfer
set (the NOTE at `:1768-1774`), so a fissioned store's lhs cannot pollute the
phi lanes. The BIL-level dataflow (a load in B reading a def in A) remains
valid BIL for every BAP consumer — `Blk.free_vars`/`Sub.free_vars` see it as an
ordinary inter-block variable — and hike's own consumers of that fact
(`collect_sub_data`'s `blk_free`, `:1723`) are already filtered.

---

## 8. Precedent: existing non-`mem` mem vars in the ecosystem

- **The fixture helper**: `let memv (n : string) : var = Var.create
  ~is_virtual:false ~fresh:false n (Type.Mem (`r64, `r8))`
  (`test_cbat/test_cbat.ml:1422`); dozens of fixtures build subs over such vars.
- **Two mem vars in ONE sub, through the full fixpoint**: `mk_caller_alias`
  (`test_cbat.ml:1606-1692`) — `m = memv "t4_m"`, `m2 = memv "t4_m2"`
  (`:1612-1613`), stores to both, `static_graph_vsa` run at `:1753`, post-call
  assertions at `:1755-1768` (T4-7..12) all reference `fx.ca_m` only but the
  state carries both entries. Also `t21_n_m`/`t21_n_m2` (`:1938-1939`),
  `t22_m`/`t22_m2` (`:2030-2031`), `e2ed_m`/`e2ed_m2` (`:2465`, `:2523`).
- **The unit tests of the call abstraction address memory per-var**:
  `AI.add_memory ~key:m0` then `AI.call_abstraction` ⇒ `AI.find_memory ... m0`
  is topped (`test_cbat.ml:1808-1823`, C1-4).
- **The debug probe**: `memv` at `zz_scratch_probe/r6view/probe.ml:13`, used at
  `:30`.
- **Production**: `arr_of` (`src/hike_stack_to_locals.ml:60-63`) creates
  `Mem`-typed locals that become Load/Store memory operands (`:958`, `:969`) and
  def lhs (`:1023`) — the fission shape, shipped, surviving DCE and emission
  today.

---

## VERDICT

### (a) BIL-legal — YES

`Load`/`Store` take the memory as an ordinary `Mem`-sort expression
(`bap.mli:2001-2002`); the type rules constrain only sorts and widths
(`bap.mli:2795-2852`); BNF1 constrains the form, not the identity
(`bap.mli:4032-4040`); nothing names a canonical var; multiple mem vars per sub
are exercised end-to-end in hike's own fixtures (`test_cbat.ml:1612-1613`) and
in production BIL (`hike_stack_to_locals.ml:60-63` + `:958/:969/:1023`).

### (b) VSA-transparent — YES (structurally, and soundly even if not)

In the current pipeline the VSA runs **before** the rewrite
(`hike.ml:666` vs `:706`), so it never sees fissioned BIL. If it ever did, it is
still sound: memory is keyed by (mem-var, address)
(`cbat_ai_representation.ml:34`), the denotation reads the mem operand
(`cbat_vsa.ml:459-485`), a consistently fissioned region is closed under its own
var, an inconsistent one degrades to **top** (the absent-key default,
`cbat_map_lattice.ml:153-158`) — never bottom, never unsound — and the call
abstraction folds every mem var through the same frame-keep
(`cbat_ai_representation.ml:376-380`). Relevance never looks at the mem operand
(`hike_vsa_relevance.ml:46-56`).

### (c) DCE-enabling — NOT automatic; needs a two-line-rule change in `hike_dce.ml`

Two blockers, both in `src/hike_dce.ml`:
1. `keep`'s unconditional `Convutils.is_mem lhs` (`:95`) keeps every
   `Mem`-typed lhs by policy;
2. `used_of` (`:38-47`) is a global syntactic union, and a store's own mem
   operand puts its lhs in the used set — a store-only chain self-keeps.

Fix: for fissioned mem vars only, (i) narrow the `is_mem` keep clause to
non-fissioned mems, and (ii) count only **Load-side** mem-operand uses as roots
(`load_used`), ignoring Store-side mem-operand uses. Then a chain is kept iff
some Load from the var exists, and load-less store sets die together in one
sweep round. The `is_mem` clause must NOT be removed wholesale: the lifter's
`mem` still carries ABI/external traffic (see hazard 1).

### (d) Emitter-additive — YES

`create_exp`'s Load/Store arms (`bil2llvm.ml:653-659`) and every other emitter
site (`:955-998`, `:1010-1024`, `:1084-1098`) discard the mem operand; a
fissioned var flows through unchanged today (its def-lhs binding at `:1104` is
dead weight, like `mem`'s). Routing by mem var is a new dispatch in
`mem_access`/`create_def` keyed on the plan's region vars → the existing
`fr.regions` allocas (`bil2llvm.ml:1993-2005`, lookup idiom
`region_of_offset` `:978-982`). No phis needed (`bil2llvm.ml:1778-1785` already
excludes `Mem`-sorted vars; the address lane carries the real state).

### Code that would need touching

1. `src/hike_stack_to_locals.ml` — the fission rewrite: one `Mem`-typed var per
   *convertible* region (the `arr_of` recipe, `:60-63`); `map_load`/`map_store`
   (`:954-989`) rewrite the mem operand for region-member addresses;
   `rewrite_def` (`:1012-1059`) rebinds member store defs' lhs
   (`Def.with_lhs`, tid-preserving per `types/bap_ir.ml:703-715`).
2. `src/convutils.ml` + `src/hike_stack_to_locals.ml` (`split_plan`) — carry the
   region→mem-var mapping in `Convutils.vsa_info.stack_plan` (`:84`) so DCE and
   the emitter consume the same decision (Finding 1's one-producer doctrine;
   consumers today: `hike_stack_to_locals`, `hike_dce:86-89`, `bil2llvm`).
3. `src/hike_dce.ml` — `keep` (`:91-96`): exempt fissioned mem lhs from the
   `is_mem` clause; `used_of` (`:38-47`): add the load-rooted set (mem operands
   of `Load`s only, plus jmp/phi reads). `sweep_fixpoint` (`:104-111`) needs no
   change — it already iterates.
4. `src/bil2llvm.ml` — additive dispatch in `mem_access`/`create_def`
   (`:991-1105`): fissioned var ⇒ GEP its region alloca, bypassing
   `find_def_tag` for those defs.
5. NOT the VSA, NOT relevance, NOT `hike_model_clean` (pre-fission by pipeline
   order), NOT `hike.ml:44-47` (the `is_mem` filter already excludes the new
   vars from signatures).
6. Validation: `scripts/check_allocas.sh`'s "one `%frame` alloca per
   memory-touching define" assert may need revisiting for fully-fissioned subs
   whose frame is no longer touched; the semantic harness is the oracle as usual.

### Soundness hazards found in the sources

1. **Callee-read stores (the outgoing-arg cells).** A store the CALLEE reads
   (the pushed 7th-arg class) is never loaded in this sub — a naive
   "never-loaded ⇒ delete" rule kills real ABI traffic. The codebase already
   owns the guard: `is_abi_visible` (`hike_stack_to_locals.ml:560-575`) and
   `has_outgoing_stack_args` (`:327-391`) keep those defs out of the convertible
   set, and the conversion filter requires `not (is_abi_visible d)`
   (`:904-907`). **The fission must reuse exactly these gates**: fission only
   *convertible* regions, so ABI-visible stores stay on `mem` and stay
   always-kept in DCE. Same for `frame_escapes` (`:791-793`), which today blocks
   the whole sub's plan — an escaped frame pointer means a callee can reach any
   slot, so that sub must not fission at all.
2. **The call-abstraction's whole-memory-top fallback.** No escape: it tops
   every `MemEnv` entry equally (`cbat_ai_representation.ml:380`), and the
   frame-keeping fold visits every var (`:376-379`). A fissioned var cannot
   dodge the abstraction. (In production this is moot — the VSA runs
   pre-fission.)
3. **Inconsistent fission in any future VSA-after-fission pipeline.** Sound but
   imprecise: the load reads the wrong var's map ⇒ absent ⇒ top
   (`cbat_map_lattice.ml:153-158`). Never bottom, so the "bottom claims the path
   dead" unsoundness (design principle 3) cannot occur.
4. **The store-chain self-keep is a real liveness question, not a syntactic
   one.** Because `used_of` is a global union, "the whole chain dies when no
   load exists" only holds under the two-tier rule of §3; without it the fission
   yields *no* DCE gain (worse: it silently looks like it should).
5. **Tags remain authoritative for non-fissioned defs.** The emitter's
   untagged-stack-access `failwith` (`bil2llvm.ml:1046-1052`) and the
   `hike: guarded:` Unbounded warn (`:1030-1040`) are keyed on def tids, which
   fission preserves — the mem-var dispatch must be an *alternative* key, not a
   replacement, or the 100%-tagging invariant loses its tripwire.
