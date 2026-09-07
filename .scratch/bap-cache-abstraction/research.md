# Research: can hike's caches move onto BAP's `Cache` abstraction?

**Question.** BAP provides a `Cache` abstraction. Can the caches that the VSA /
hike itself computes be moved onto BAP's `Cache` abstraction to clean up the
code?

**Method.** Primary sources only, hand-audited. For BAP I read the `.mli`
signatures **and** the shipped `.ml` implementations installed in the opam
switch (`/home/tovpr/.opam/bap-flambda/lib/...` — `bap-cache` ships its full
sources, `regular` ships `regular_cache.ml`), plus BAP's own plugins'
`.ml` sources (`bap-taint-propagator`, `bap-optimization`, `bap-disassemble`,
`bap-ida`, `bap-specification` — all installed with sources). I then
**verified every API claim by compiling and running probes against BAP**
(see §A.6 — probes, not docs, are the evidence for the behavioural claims).
For hike I read `src/` and `src/cbat_vsa/` by hand. Every claim carries a
file:line or the exact command. Nothing in `src/` was modified.

**Headline answers.**

1. **The module path is `Regular.Std.Data.Cache`, not `Bap.Std.Cache` and not
   `Bap_cache`.** `Bap_cache` is only the *plugin* that implements the on-disk
   service; consumers never touch it. It is a **persistent, cross-run,
   content-addressed, weak** on-disk store — not an in-process memo table.
2. **It IS intended for analysis results.** BAP's own `propagate-taint` plugin
   caches a whole-program taint fixpoint under it
   (`bap-taint-propagator/plugin/propagate_taint_main.ml:187-191`), and
   `bap-optimization` caches per-sub dead-code analyses (`:164-170`). So the
   "is it only for lifting?" worry is refuted by BAP's own code.
3. **The lattice-inversion blocker the question anticipates does NOT exist:**
   `cbat_vsa_domain` **already links `bap`** (`src/cbat_vsa/dune:35`). Using
   `Data.Cache` there would **not** invert the lattice. This is the opposite
   of the hypothesis; verified by reading the dune stanzas *and* by
   `ocamlobjinfo` on the installed bundle.
4. **There is no `cache`/`Cache` name-collision hazard** analogous to `Abi` —
   but for a *different reason than one might guess*: the kernel of the `Abi`
   hazard (a plugin unit named exactly `Abi`) is **genuinely present** for
   `cache` too (`bap-common/plugins/cache/META` exists, structurally identical
   to `bap-common/plugins/abi/META`). What saves you is that BAP's cache
   plugin exports no top-level `Cache` unit — only `Bap_cache_plugin*`
   (§A.5).
5. **Verdict: almost nothing should move.** Of the ~14 table sites audited,
   **zero** are pure memoization of an expensive deterministic function that
   would benefit, and **zero** should be moved to `Data.Cache`. The three
   process-global tables are (a) tiny, (b) never-keyed to anything
   cachable-by-content, and (c) are *interning* tables whose correctness
   depends on process-lifetime identity. The one place a BAP `Cache` *could*
   pay (the per-sub `vsa_info`) is **already served by the KB**, which is the
   strictly better mechanism for it (§B.4). **Recommendation: no migration.**
   The real cleanup available is two small deletions, not a migration
   (§C.3).

---

## TL;DR

| Question | Answer |
|---|---|
| Exact module path? | `Regular.Std.Data.Cache` (and `T.Cache` for any `Regular`/`Data` type). `Bap_cache` = the plugin only. |
| Persistent or in-process? | **Persistent on-disk**, cross-run. Verified by saving in one process and hitting in a later one (§A.6). |
| Where on disk? | `$XDG_CACHE_HOME/bap` → `~/.cache/bap/data/<md5>`; override with `--cache-dir=DIR` (root becomes `DIR/.cache/bap`). |
| Key type? | `Data.Cache.digest` — an MD5 hex string built printf-style from any values; `Digest.add_sexp` for sexpable values. |
| Value typing? | `T.Cache.load/save` for a `Regular` type `T`; or `Data.Cache.Service.request reader writer` for an ad-hoc binable. No `Cache.Make`/`with_cache`/`memo` combinator exists. |
| Required on values? | `bin_io` (or any `Data.Read`/`Data.Write`). `Regular` = `bin_io + sexp + compare`. Versioned via `Data.S.version`. |
| Disabled when? | No service installed → **oblivion** (`load`=None, `save`=no-op). `--no-cache` disables the plugin. No `Cache.disabled`, no `BAP_DISABLE_CACHE`. The `getenv` in `bap_cache.ml:59` is **dead code**. |
| Analysis results or lifting only? | **Both** — BAP caches taint-propagation and dead-code analyses under it. |
| Intended cleanup win? | **No.** See the verdict table (§C.1) — 0 MOVE, 2 DELETE, 12 KEEP. |
| Lattice inversion? | **Not a blocker** — `cbat_vsa_domain` already depends on `bap`. |
| `Cache` name collision? | **Not a hazard** (no top-level `Cache` unit is exported by BAP), though the plugin-name mechanism is real. |

---

# TASK A — BAP's `Cache` abstraction against primary sources

## A.1 Where it lives, and what the three names are

Three names get confused. Verified:

- **`Regular.Std.Data.Cache`** — the *interface* every consumer uses.
  Declared in `/home/tovpr/.opam/bap-flambda/lib/regular/regular.mli:646-742`
  (generic, `'a -> 'b`-free: `'a t` cachers + `digest`) and
  `:391-442` (the `Data.S` sub-module: `T.Cache.load`/`T.Cache.save`).
  Implemented in `/home/tovpr/.opam/bap-flambda/lib/regular/regular_cache.ml`
  (83 lines — the whole thing).
- **`Bap_cache`** — the *plugin* that implements the on-disk service.
  Installed with **full sources** at
  `/home/tovpr/.opam/bap-flambda/lib/bap-cache/plugin/bap_cache.ml`.
  This is **not** a consumer-facing API.
- **`bap-cache`** — the findlib package. `ocamlfind query bap-cache` →
  `/home/tovpr/.opam/bap-flambda/lib/bap-cache`. Note it exposes **only**
  `bap-cache.plugin` (its `META` has a single `package "plugin"` stanza) —
  a normal library consumer cannot even `#require` an API from it.

**There is no `Bap.Std.Cache`.** Verified exhaustively:

```sh
cd /home/tovpr/.opam/bap-flambda/lib
grep -rln "Cache" . --include="*.mli"   # -> only regular/regular.mli, bap-cache/plugin/{bap_cache,bap_cache_gc}.mli
grep -n "Cache" bap-std/bap.mli         # -> no matches (bap.mli is 11785 lines)
```

`Bap.Std` reaches it only because `bap.mli:5` does `open Regular.Std`, so
`Data.Cache` is in scope after `open Bap.Std`. **Verified by compilation**: a
probe with `open Bap.Std` but no `open Regular.Std` fails with
`Unbound module "Data"`; adding `open Regular.Std` compiles.

## A.2 The full signature

### Generic layer (`regular/regular.mli:646-742`, `regular_cache.mli`)

```ocaml
module Data : sig
  type digest                                    (* = string; regular.mli:73-74,
                                                    regular_data_intf.ml:11 *)

  module Cache : sig
    type 'a t                                    (* a "cacher": load/save pair *)

    val create : load:(digest -> 'a option) -> save:(digest -> 'a -> unit) -> 'a t

    val digest : namespace:string -> ('a, Format.formatter, unit, digest) format4 -> 'a
    module Digest : sig
      include Identifiable with type t = digest
      val create    : namespace:string -> t
      val add       : t -> ('a, Format.formatter, unit, t) format4 -> 'a
      val add_sexp  : t -> ('a -> Sexp.t) -> 'a -> t
      val add_file  : t -> string -> t           (* md5 of the FILE's contents *)
    end

    val load : 'a t -> digest -> 'a option
    val save : 'a t -> digest -> 'a -> unit

    type service = { create : 'a . 'a reader -> 'a writer -> 'a t }
    module Service : sig
      val provide : service -> unit
      val request : 'a reader -> 'a writer -> 'a t
    end
  end
end
```

### Per-type layer (`regular.mli:434-441`)

Any module satisfying `Data.S` gets:

```ocaml
module Cache : sig
  val load : digest -> t option
  val save : digest -> t -> unit
end
```

`Regular.S` (`regular.mli:774-780`) is what you normally make:

```ocaml
module type S = sig
  type t [@@deriving bin_io, sexp, compare]
  include Printable.S          with type t := t
  include Comparable.S_binable with type t := t
  include Hashable.S_binable   with type t := t
  include Data.S               with type t := t
end

module type Minimal = sig
  type t [@@deriving bin_io, sexp, compare]
  include Pretty_printer.S with type t := t
  include Data.Versioned.S with type t := t   (* just: val version : string *)
  val hash : t -> int
  val module_name : string option
end

module Make (M : Minimal) : S with type t := M.t
```

**There is no `Cache.Make`, no `Cache.with_cache`, no `Cache.memo`.** The
idiom is the hand-written load/compute/save triple, documented at
`regular.mli:417-431`:

```ocaml
let compute_graph ?(debug=false) x y : Graphs.Cfg.t =
  let digest = Data.Cache.digest ~namespace:"example" "%s%d" x y in
  match Graphs.Cfg.Cache.load digest with
  | Some g -> g
  | None ->
    let g = build_graph ?debug x y in
    Graphs.Cfg.Cache.save digest g;
    g
```

**There is also no in-process memo table.** `Regular` ships none; the
`Core.Memo` LRU in the switch (`core/memo.mli:31,74` — `?cache_size_bound`)
is a *different*, unrelated thing that `Regular`/`BAP` do not use here.

### What the digest is

`regular_cache.ml:58-77`:

```ocaml
module Digest = struct
  include String
  let make s     = s |> Md5.digest_string |> Md5.to_hex
  let format fmt = let buf = Buffer.create 4096 in ... kfprintf key ppf fmt
  let add buf fmt     = format ("%s" ^^ fmt) buf
  let add_sexp d sx x = add d "%a" Sexp.pp (sx x)
  let add_file d name = add d "%s" (Stdlib.Digest.(file name |> to_hex))
  let create ~namespace = make namespace
end
let digest ~namespace fmt = Digest.format ("%s" ^^ fmt) namespace
```

So: an **MD5 hex string** (`regular_data_intf.ml:11`: `type digest = string`),
built by printf-formatting the inputs into a 4 KiB buffer and hashing. Keys
are flat — hence the mandatory `~namespace` (`regular.mli:689-695`: *"Since a
caching service is using a flat namespace of keys, the `namespace` parameter
is used to distinguish data built by different functions that have the same
parameters digests. A module name is a good candidate"*).

Verified: `Data.Cache.digest ~namespace:"hike-probe" "%s%d" "hello" 42`
→ `116c21a42a12c3a71a33eb1d4f5ccac2` (32 hex chars).

Note the documented cost (`regular.mli:675-679`): `digest` is **O(N)** in the
total size of all inputs, in space and time — *"If N is too big (hundreds of
megabytes) then use [Digest] module for building digests incrementally."*
Relevant below: a whole-program digest is a real cost, not a free key.

## A.3 It is a persistent on-disk cache, and it is *weak*

The service is injected (`regular_cache.ml:27-38`):

```ocaml
module Service = struct
  let oblivion = { create = fun _ _ ->
      { load = (fun _ -> None); save = (fun _ _ -> ()) } }
  let service = ref oblivion
  let provide new_service = service := new_service
  let request x y = !service.create x y
end
```

**Default = oblivion.** With no cache plugin, `save` is a no-op and `load`
always returns `None`. This is the "it works even if there is no caching
service" property (`regular.mli:414-416`).

The on-disk service is `bap-cache/plugin/bap_cache.ml` +
`bap_cache_main.ml`. `bap_cache_main.ml:36-50`:

```ocaml
let filename_of_digest = Data.Cache.Digest.to_string
let save writer dgst data =
  let dir = Cache.data () in
  let file = dir / filename_of_digest dgst in
  Utils.write_to_file ~temp_dir:dir writer file data
let load reader dgst =
  let path = Cache.data () / filename_of_digest dgst in
  try Some (Utils.read_from_file reader path) with _exn -> None
let create reader writer = Data.Cache.create ~load:(load reader) ~save:(save writer)
let provide_service () = Data.Cache.Service.provide { Data.Cache.create }
```

The root (`bap_cache.ml:61-63`, `bap_main.ml:1197-1203`):

```ocaml
let root () = match !default_root with
  | Some dir -> dir // ".cache" // "bap"          (* set by --cache-dir *)
  | None -> Bap_main.Extension.Configuration.cachedir
(* bap_main.ml:1197 *)
let cachedir = match Sys.getenv_opt "XDG_CACHE_HOME" with
  | Some dir -> dir / "bap"
  | None -> match Sys.getenv_opt "HOME" with
    | Some dir -> dir / ".cache" / "bap"
    | None -> Filename.get_temp_dir_name () / "bap" / "cache"
```

Verified on this machine: `~/.cache/bap/config.3` (`-r--r--r--`, 5 bytes) and
`~/.cache/bap/data/` holding **3.1 GB** of entries, each named by its 32-hex
digest.

### The "weak" contract

`regular.mli:393-404` — this is the crucial semantic:

> Store and retrieve data from cache. The cache can seen as a **persistent
> weak key-value storage**. Data stored here can **disappear at any time**,
> but can survive for a long time (outliving the program). […] In fact this
> is just a weak key-value storage. A weak, because storage is allowed to
> loose data.

Also `regular.mli:411-416`: *"[load] will work even if there is no caching
service. Of course, there will be no benefits, since the `save` function will
just immediately forget its argument."*

So **every consumer must be correct when `load` returns `None`** — which for
a pure memoization is free, and for anything stateful is a trap.

### Serialization formats

`Data.Make` registers readers/writers (`regular_data.ml:436-441`) and picks a
default. Verified for a `Regular.Make` type: `default_reader`/`default_writer`
= **`bin/1`** (binprot), not the OCaml `Marshal` format that
`regular.mli:273-276` calls the default for raw `Data.S`. For BAP's own
`Bil` it is `bin/1.0.0`. Available: `bin_reader/bin_writer`,
`sexp_reader/sexp_writer`, `marshal_reader/marshal_writer`, `pretty_writer`
(`regular.mli:234-257`).

`bap_cache_main.ml` uses the generic reader/writer the service is asked for,
so a custom type just needs `Data.Read`/`Data.Write`
(`bap-disassemble/plugin/disassemble_main.ml:243-262` is the canonical
ad-hoc example, wrapping `Knowledge.of_bigstring`/`to_bigstring`).

## A.4 Limits, caveats, and the controls that actually exist

| Caveat | Where documented / verified |
|---|---|
| **Weak** — entries may vanish at any time; `load` may return `None` | `regular.mli:393-404` |
| **Oblivion by default** — silent no-op without the plugin | `regular_cache.ml:28-33`; `regular.mli:414-416` |
| **Flat key namespace** — collisions across functions unless `~namespace` differs | `regular.mli:689-695` |
| **No automatic invalidation.** You must put a *version* in the digest. `Data.S.version` exists for on-disk *format* versioning (`regular.mli:296-311`), but the **`.mli` never bumps a digest for you** — a code change that changes the computed value silently keeps the old entry. | Verified: my probe's entry `770ea0df…` survived unchanged across runs with identical code. |
| **Digest is O(N)** in input size; use incremental `Digest` for big inputs | `regular.mli:675-679` |
| **Capacity + GC**: default `capacity = 4*1024` MB, `overhead = 25%`, `gc_enabled = true` (`bap_cache.ml:29-34`). GC is randomized, size-biased, lock-free, runs at startup when over `capacity*(1+overhead/100)`. | `bap_cache.ml:29-34`; `bap_cache_gc.ml` (whole file, with the CDF derivation in its header comment) |
| **Lock-free / multi-process safe by design** | `bap_cache_main.ml` doc string: *"the plugin implements lock-free store/loading operations with O(1) complexity: the same cache folder can be safely shared between different processes"* |
| **Atomic writes** (temp file + rename) | `bap_cache_utils.mli:12-18`; `bap_cache.ml:120-135` (`mkdir_from_tmp`) |
| **Not atomic across calls / not thread-safety-documented.** The `.mli` says only *"All operations in this module are atomic"* for `Bap_cache` internals (`bap_cache.mli:1`); nothing in `Data.Cache` documents OCaml-thread safety. `bap_cache_gc.ml:88` uses a shared `Random` state. | Absence of any claim in `regular.mli`; flagged as unverified |

**Controls that exist** (all verified by running `bap`/my probe):

| Control | Effect | Verified |
|---|---|---|
| `--cache-dir=DIR` | root becomes `DIR/.cache/bap` | created `croot/.cache/bap/config.3` + `data/<digest>` |
| `--no-cache` | **disables the plugin** → oblivion. Auto-generated from the plugin name (`bap_main.ml:1042`: `info ~doc ~docs ["no-"^name]`) | cache root stayed **empty** |
| `bap cache --clean` / `--cache-clean` | deletes all entries | data dir emptied, `config.3` kept |
| `bap cache --capacity=N` / `--overhead=P` / `--enable-gc` / `--disable-gc` / `--info` | persist to `config.3` | `bap cache --help` |
| `XDG_CACHE_HOME` / `HOME` / `TMP` | find the root | `bap_main.ml:1197-1203` |

**Controls that do NOT exist — I looked for each specifically:**

- **No `BAP_CACHE_DIR`.** The only env vars are `XDG_CACHE_HOME`/`HOME`.
  `grep -rn "getenv" bap-cache/plugin/*.ml` → **one** hit,
  `bap_cache.ml:59` (`let getenv opt = ...`), and it is **dead code** — no
  call site anywhere in `bap_cache.ml`, `bap_cache_main.ml`, or
  `bap_cache_gc.ml` (`grep -c "getenv"` on the call sites = 0).
- **No `BAP_DISABLE_CACHE`.** Disabling is `--no-cache` only.
- **No `Cache.disabled` / `Cache.is_enabled`.** `bap_cache.mli` is 18 lines:
  `init`, `size`, `set_root`, `root`, `data`, `gc_threshold`, `read_config`,
  `write_config`. Nothing else.

## A.5 Is it for analysis results, or only lifting? — BAP's own usages

It is **both**. All of these are installed with sources:

| Plugin | What it caches | File |
|---|---|---|
| `propagate-taint` | **a whole-program taint-propagation fixpoint** (`State.t` = per-sub taint maps, made `Regular` at `:126-134`) | `bap-taint-propagator/plugin/propagate_taint_main.ml:138-192` |
| `optimization` | per-sub dead-code analysis results | `bap-optimization/plugin/optimization_main.ml:151-170` |
| `disassemble` | **the whole KB state** (`Knowledge.to_bigstring`, namespace `"knowledge"`) and `Project.state` | `bap-disassemble/plugin/disassemble_main.ml:243-283, 501-516` |
| `ida` | symbol tables, images, branchers | `bap-ida/plugin/ida_main.ml:47-55, 127-133, 210-216` |
| `specification` | specifications | `bap-specification/plugin/specification_main.ml:59-69` |

The taint case is the closest analogue to hike's VSA, and worth quoting in
full (`propagate_taint_main.ml:137-192`) — note that it digests **the whole
program's BIL**, term by term:

```ocaml
let digest_project proj =
  let module Digest = Data.Cache.Digest in
  let add_taint tag t dst = match Term.get_attr t tag with
    | None -> dst
    | Some v -> Digest.add dst "%a" Tid.pp v in
  (object
    inherit [Digest.t] Term.visitor
    method! enter_term cls t dst = add_taint Taint.reg t dst |> add_taint Taint.ptr t
    method! enter_arg t dst = Digest.add dst "%a" Arg.pp t
    method! enter_def t dst = Digest.add dst "%a" Def.pp t
    method! enter_jmp t dst = Digest.add dst "%a" Jmp.pp t
  end)#run (Project.program proj)
    (Data.Cache.Digest.create ~namespace:"propagate_taint")

let main args proj =
  let digest = digest args proj in
  let state = match State.Cache.load digest with
    | Some s -> s
    | None -> let s = process args proj in State.Cache.save digest s; s in
  ...
```

Two things to note, both of which bear directly on the recommendation:

1. The key is a **whole-program digest**, because the analysis is
   whole-program. Per-sub caching is impossible for it.
2. `State.t` had to be **made `Regular`** (`include Regular.Make(...)` at
   `:126-134`, with `[@@deriving bin_io, compare, sexp]` on the record) —
   the same shape of change hike would need for `vsa_info`.

`bap-optimization` shows the per-sub shape, keyed on **addresses + name +
level** (`optimization_main.ml:137-152`) — no whole-program digest, because
its analysis is genuinely per-sub.

## A.6 What I verified by compiling and running probes

Docs alone are not evidence for behaviour, so I built probes against BAP in
`/tmp/opencode/cacheprobe` (dune, `(libraries bap bap-main core_kernel core
regular threads.posix)`, `(preprocess (pps ppx_bap))`).

| Claim | Probe result |
|---|---|
| `Data.Cache` needs `open Regular.Std` even after `open Bap.Std` | `Unbound module "Data"` without it; compiles with it |
| `Bil.Cache` / `Word.Cache` exist as *modules* with `load`/`save` (not as `'a Cache.t` values — the `Data.S` sub-module, `regular.mli:434-441`) | compiles |
| Digest is 32-hex MD5 | `116c21a42a12c3a71a33eb1d4f5ccac2` |
| **Oblivion default**: `save` then `load` → `None` when no service installed | `oblivion: load after save = true (None)` |
| A `Regular.Make` type round-trips through a global-table service | `global-table roundtrip = 7,9 ok=true` |
| `Bil.t` round-trips through BAP's default writer | `Bil.Cache roundtrip equal = true` |
| Default format for a `Regular.Make` type is **binprot** | `R1 default_reader = bin/1`, `R1 default_writer = bin/1` |
| **Persistence across processes** — save in run 1, hit in run 2 | run 1 `MISS — saving`; run 2 `HIT from disk: 42,99`; file `~/.cache/bap/data/770ea0dfd28a46418b0464df9313c29b` (2 bytes, mode `-r--r--r--`) |
| `--cache-dir=DIR` relocates the root | `DIR/.cache/bap/{config.3,data/<digest>}` |
| `--no-cache` ⇒ oblivion | cache root empty after a `save` |
| `Word`/`Tid`/`Var` are binable | `bil/word/tid/var roundtrip = true` (via `Bil.to_bytes`, `Word.to_bytes`, `Tid.to_bytes`, `Var.to_bytes`) |
| The cache plugin **is** loaded in a plain `dune exec` | `cache unit loaded = true`; `Bap_cache_plugin*` units present |
| The cache plugin **is** loaded during a real `bap --pass=hike-convlir` run | `--cache-dir=croot` produced `croot/.cache/bap/data/d9ea41d7…` (349 KB) |

Two probe gotchas worth recording for anyone repeating this:

- **`Bap_main.init ()` returns `Error` in this sandbox** because of an
  unrelated plugin (`Failed to load plugin "primus-symbolic-executor": It is
  not possible to dynamically link a plugin which uses the thread library
  with an executable not already linked with the thread library`). This is an
  artifact of linking `threads.posix` into a `dune exec` target, **not** of
  BAP's cache. Crucially, **`init` returning `Error` means the cache plugin's
  `Extension.declare` callback never runs, so the service stays oblivion** —
  this is exactly why my first persistence attempts silently missed.
  `bap_main.mli:361-363`: *"If [init ()] terminates with any value other that
  [Ok ()] the BAP framework is considered to be unitialized and shouldn't be
  used."*
- **`Data.Make`'s `Cache` builds a fresh cacher on every call**
  (`regular_data.ml:415-421`: `let load id = Regular_cache.load (cacher ())
  id`). This is harmless for the real plugin (its `create` closes over
  nothing) but means an **in-process** service that allocates its table
  inside `create` will never see its own writes.

## A.7 The `Abi`-analogue hazard — checked

The AGENTS.md records: BAP dynlinks a core `abi` plugin, and a
bundle-internal library named `abi` broke at load with *"interface mismatch on
Abi"*. I checked the mechanism and whether `cache` is analogous.

**The mechanism, verified.** `ocamlobjinfo` on the two plugin archives:

```
$ ocamlobjinfo .../bap-abi/plugin/abi.cmxs   | grep '^Name:'
Name: Abi
Name: Abi__Abi_main

$ ocamlobjinfo .../bap-cache/plugin/bap_cache_plugin.cmxs | grep '^Name:'
Name: Bap_cache_plugin
Name: Bap_cache_plugin__Bap_cache_utils
Name: Bap_cache_plugin__Bap_cache_types
Name: Bap_cache_plugin__Bap_cache
Name: Bap_cache_plugin__Bap_cache_gc
Name: Bap_cache_plugin__Bap_cache_main
```

So the `Abi` collision is concrete: the plugin **defines a compilation unit
literally named `Abi`**, so any other unit named `Abi` in the process (your
library, statically linked) is an interface mismatch.

**Is `cache` analogous? No — and here is the precise reason.**

The *plugin-registration* half of the hazard **is** present, identically:

```
$ ls .../bap-common/plugins/cache/    # -> META   (requires = "bap-cache.plugin")
$ ls .../bap-common/plugins/abi/      # -> META   (requires = "bap-abi.plugin")
```

Structurally the same, and `bap --help` lists `--cache` and `--abi` in the
same "Enables the pass … in the old style (DEPRECATED)" block, and
auto-generates `--no-cache` alongside `--no-abi`.

But the *unit-name* half is **not** present. I enumerated every compilation
unit in the `bap` binary's library set looking for a top-level `Cache`:

```sh
$ for f in bap-std/bap.cmxs bap-std/types/bap_types.cmxs bap-std/disasm/bap_disasm.cmxs \
           bap-main/bap_main.cmxs bap-knowledge/knowledge.cmxs regular/regular.cmxs \
           bap-plugins/bap_plugins.cmxs; do ocamlobjinfo "$f"; done \
  | grep -E '^Name:' | sort -u | grep -wE 'Abi|Cache'
# -> no output
```

(`regular.cmxs` does export a unit named **`Regular_cache`** — but that is
*not* `Cache`, so no clash.)

**Conclusion.** Naming a hike library or module `cache`/`Cache` is **safe**:
BAP ships no top-level `Cache` unit. But two caveats follow, and both are
cheap to respect:

1. Do **not** name a unit exactly `Bap_cache`, `Bap_cache_plugin`, or
   `Regular_cache`.
2. The plugin-name namespace **is** shared: a hike plugin named `cache` would
   collide with BAP's at the `bap-common/plugins/` level and in the
   auto-generated `--no-cache` flag. hike's plugin is `hike.plugin`
   (`/home/tovpr/.opam/bap-flambda/lib/bap-common/plugins/hike.plugin`),
   so this is already fine.

---

# TASK B — Hand audit of the caches hike / the VSA compute

Method: `grep` for `Hashtbl`/`Hashtbl.create`/`Map.empty`/`ref`/memo-shaped
identifiers across `src/` and `src/cbat_vsa/`, then read each site. 75
`Hashtbl.` occurrences total, in 6 files.

**Scope note:** `src/_build/` is dune's build dir and contains stale copies
of some sources; all line numbers below are from the **real** sources.

## B.1 The complete inventory

### Process-global mutable state — 6 sites (module-level, column 0)

Only six. I found them with:

```sh
grep -rn "^let .*= *\(Hashtbl\.create\|ref \|Map\.empty\)" --include="*.ml" src/ \
  | grep -v "^src/_build"
grep -rn "^let [a-z_]* *\(:[^=]*\)\?= *ref " --include="*.ml" src/ | grep -v _build
```

| # | Site | Type | Created | Cleared? |
|---|---|---|---|---|
| G1 | `src/cbat_vsa/cbat_clp.ml:118` `top_cache` | `(int, Cbat_clp.t) Hashtbl.t` | module load, size 16 | **never** |
| G2 | `src/cbat_vsa/cbat_word_ops.ml:123` `dom_size_cache` | `(int*int, word) Hashtbl.t` | module load, size 16 | **never** |
| G3 | `src/cbat_vsa/cbat_word_ops.ml:134` `half_cache` | `(int, word) Hashtbl.t` | module load, size 8 | **never** |
| G4 | `src/cbat_vsa/cbat_landmarks.ml:47` `lm_env` | `(Tid.t, lm_entry list) Hashtbl.t` | module load | yes — `clear ()` at `cbat_vsa.ml:3042`, every fixpoint |
| G5 | `src/cbat_vsa/cbat_vsa.ml:147` `addr_bits_ref` | `int ref` | module load, `0` | **never** (overwritten by `set_addr_bits`) |
| G6 | `src/cbat_vsa/cbat_landmarks.ml:41` `widening_at_head` | `Tid.t option ref` | module load, `None` | set/reset around every widening (`cbat_vsa.ml:3182,3185,3219,3248`) |

**Note the AGENTS.md claim is confirmed**: the deleted `vsa_sol_tbl` has no
analogue left.

```sh
$ grep -rn "vsa_sol_tbl\|provide_sol\|add_sol\|vsa_sol " --include="*.ml*" src/ | grep -v _build
src/cbat_vsa/cbat_vsa.mli:25:type vsa_sol = (tid, AI.t) Solution.t
src/cbat_vsa/cbat_vsa.mli:85:val static_graph_vsa : tid list -> Program.t -> Sub.t -> vsa_sol -> vsa_sol
src/cbat_vsa/cbat_vsa.ml:2893:type vsa_sol = (tid, AI.t) Solution.t
src/cbat_vsa/cbat_vsa.ml:2964:let rec static_graph_vsa ...
```

Only the *type* `vsa_sol` survives (a `Graphlib` `Solution.t`, a fixpoint
value, not a table). The write-only global table is gone.

### Per-fixpoint-run state (`cbat_vsa.ml`)

| # | Site | Type | Lifetime |
|---|---|---|---|
| R1 | `cbat_vsa.ml:3030` `rc_versions` | `(Tid.t, int) Hashtbl.t` | one `static_graph_vsa` call (field of `refine_ctx`, `:2569`) |
| R2 | `cbat_vsa.ml:2578` `rc_cache` | `refine_hit Tid.Map.t Tid.Map.t ref` | same — the **change-driven walk cache** (`:2500-2548`) |
| R3 | `cbat_vsa.ml:2572` `rc_reads` | `Tid.Set.t ref` | same; scratch, reset per walk |
| R4 | `cbat_vsa.ml:3016` `sol_map` | `(Tid.t, AI.t) Tid.Map.t ref` | same — **the fixpoint solution itself** |
| R5 | `cbat_vsa.ml:3043` `head_to_blocks` | `(Tid.t, Tid.Set.t) Hashtbl.t` | same — WTO head → SCC blocks |
| R6 | `cbat_vsa.ml:3053` `block_to_head` | `(Tid.t, Tid.t) Hashtbl.t` | same — block → innermost WTO head |
| R7 | `cbat_vsa.ml:96` `rpo_index` | `(Tid.t, int) Hashtbl.t` | local to one WTO computation |
| R8 | `cbat_vsa.ml:2483` `tbl` in `edge_conds_of` | `(Tid.t, edge_cond Tid.Map.t) Hashtbl.t` | built per sub, folded immediately to a `Tid.Map` |
| R9 | `cbat_vsa.ml:3087-3088` `succ_tbl`/`pred_tbl` | `(Var.t, Var.t list) Hashtbl.t` ×2 | local to one `compute_need` call (per SCC head) |

### Per-sub / per-pass derived maps (computed once, threaded read-only)

| # | Site | Type | Note |
|---|---|---|---|
| S1 | `cbat_vsa.ml:2924` `defs_of_sub` | `(def term * bool) Var.Map.t` | called at `:2969` |
| S2 | `cbat_vsa.ml:2935` `stores_of_sub` | `def term list` | called at `:2971` |
| S3 | `cbat_vsa.ml:2967` `refineable_of_sub` | `Var.Set.t` | called at `:2966` |
| S4 | `cbat_vsa.ml:~2945` `preserved_of_sub` | `Var.Set.t` | called at `:2967` |
| S5 | `hike_vsa_relevance.ml:79-101` | `(def term list Tid.Map.t * Var.Set.t Tid.Map.t * def term Var.Map.t)` | built by a `Term.visitor`, returned |
| S6 | `hike_vsa.ml:202-229` `merged_tags` | `vsa_kind Tid.Map.t` | per sub |
| S7 | `hike_stack_to_locals.ml` — **12** `Map.empty` folds | various `Tid.Map`/`Var.Map` | per sub, all `fold`-built |
| S8 | `hike.ml:425-433` `ctx.subs` | `(Arg.t list * Arg.t list) Tid.Map.t` | **set once** (comment at `:425`), read-only after |

### Emitter tables (`bil2llvm.ml` / `convutils.ml`)

| # | Site | Type | Lifetime |
|---|---|---|---|
| E1 | `convutils.ml:64,82` `edge_sp_restores` | `(Tid.t, (Tid.t, Llvm.llvalue) EHashtbl.t) EHashtbl.t ref` | per-run; **in the emit_ctx record** |
| E2 | `convutils.ml:~59` `blk_llvals` | `blk_llvals Tid.Map.t ref` | per-run; **cleared per sub** (`bil2llvm.ml:2347` → `convutils.ml:221`) |
| E3 | `convutils.ml:~60` `ll_bbs` | `Llvm.llbasicblock Tid.Map.t ref` | per-run; **cleared per sub** (`bil2llvm.ml:2346` → `convutils.ml:222`) |
| E4 | `convutils.ml:~61` `guarded_warned` | `Tid.Set.t ref` | per-run (dedup) |
| E5 | `convutils.ml:~62` `undef_warned` | `Var.Set.t ref Tid.Map.t ref` | per-run (dedup) |
| E6 | `bil2llvm.ml:1919` `edge_counts_of_sub` | `(Tid.t, (Tid.t,int) EHashtbl.t) EHashtbl.t` | **per sub**, pure, built and consumed at `:1946` |
| E7 | `convutils.ml:~55` `ll_funcs` | `(Llvm.llvalue * Llvm.lltype) Tid.Map.t ref` | per-run |

**Structural note (credit where due).** The emitter's comment at
`bil2llvm.ml:16` records that this used to be module-level state and was
already moved into one threaded record:

> *"The per-run emission context ([Convutils.emit_ctx], threaded as a KB
> Context var [emit_ctx_var]): the old module-level refs (ll_funcs /
> copy_reloc_addrs / symtab_ref / section_remap_ref / text_section_ref /
> guarded_warned) now live in that one record."*

So **E1–E5, E7 are already the cleanup's end state** — a per-run record
threaded through `KB.Context.with_var` (`bil2llvm.ml:127-130`,
`hike.ml:438-441`). There is no process-global emitter state left to migrate.

## B.2 The three never-cleared globals, in detail

### G1/G2/G3 — the word/CLP interning tables

```ocaml
(* cbat_clp.ml:116-126 *)
(* [top] recomputed [infinite (zero, one)] per call — [factor_2s]/[dom_size]/[modulo] each time. The widths are few (8/16/32/64/128/256) and the top value is immutable — one cached [t] per width. *)
let top_cache : (int, t) Hashtbl.t = Hashtbl.create 16
let top (i : int) : t =
  assert(i > 0);
  match Hashtbl.find_opt top_cache i with
  | Some t -> t
  | None -> let t = infinite (W.zero i, W.one i) in Hashtbl.add top_cache i t; t
```

```ocaml
(* cbat_word_ops.ml:121-142 *)
(* [dom_size]: / [half] rebuilt [W.lshift (W.one width) i] — GMP allocs — on every CLP op (canonize → is_infinite, the sign-detection paths). *)
let dom_size_cache : (int * int, word) Hashtbl.t = Hashtbl.create 16
let dom_size ?width (i : int) : word = ...
let half_cache : (int, word) Hashtbl.t = Hashtbl.create 8
let half (width : int) : word = ...
```

Facts that matter for the verdict:

- **Domain is bounded and tiny.** `top` is keyed by bit width — the file's own
  comment says *"The widths are few (8/16/32/64/128/256)"*. `half` likewise
  (≤ 8 entries). `dom_size` is keyed by `(i, width)` — unbounded in principle,
  but `width` is from the same small set and `i` is a bit position within it,
  so realistically ≤ ~256×8.
- **They are interning/hash-consing tables, not memoization of an expensive
  computation.** The *purpose* is (a) avoid GMP allocation and (b) return a
  **shared** immutable value. Measured cost of a hit:
  `CLP.top 64` ≈ **27.7 ns/call**, `WO.half 64` ≈ **16.6 ns/call**,
  `WO.dom_size` ≈ **32.8 ns/call** (2M calls each, probe in the repo — see
  §B.5).
- **`Cbat_clp.t` is already `bin_io`**: `cbat_clp.mli:14`
  `type t [@@deriving bin_io, sexp]`. And `word` = `Bap.Std.Word`, which is
  `Regular` (`bap-std/types/bap_bitvector.mli:13`). So serializability is not
  the blocker here.

### G4/G5/G6 — landmark state and addr bits

`lm_env` (`cbat_landmarks.ml:47`) is the per-WTO-head landmark table from
Simon & King §4. Its own header comment (`:34-39`) is emphatic that it is
**singular and per-run**:

> *"Spec ticket S5: 'a [landmark_env] holding the head→landmark-list table' —
> singular, not duplicated."*

And it **is** cleared: `cbat_vsa.ml:3042` `Cbat_landmarks.clear ()` runs at
the top of every `static_graph_vsa`. So its process-global-ness is only a
*mechanism* (the acquisition site `observe_unsat_var` is deep in the meet path
and has no access to the fixpoint's locals) — its **lifetime is per-run**.

`addr_bits_ref` (`cbat_vsa.ml:147`) is a set-once configuration value
(`set_addr_bits`, target-derived): *"0 = not set, the BIL type's size is the
fallback (unit tests run without a target)."* Not a cache at all.

## B.3 Classification (a/b/c)

| Class | Meaning | Members |
|---|---|---|
| **(a) pure memo of a deterministic function of the key** | ideal `Cache` fit | **E6 `edge_counts_of_sub`** (pure function of `sub`), **S1–S5** (pure functions of `sub`) — **but all are cheap** |
| **(b) fixpoint-iteration working state** | must NOT move | **R1–R6** (versions, walk cache, `sol_map`, WTO tables), **G4/G6** (landmark state, widening head) |
| **(c) short-lived scratch** | not worth moving | **R3, R7, R8, R9**, **S6, S7**, the `hike_stack_to_locals` folds |
| **(x) interning / hash-consing** | a *different* thing that only looks like a cache | **G1, G2, G3** |
| **(y) configuration / set-once** | not a cache | **G5** |
| **(z) per-run record, already cleaned up** | nothing to do | **E1–E5, E7, S8** |

**The single most important observation: there is no class-(a) table whose
computation is expensive.** Every table in the tree is either (b) fixpoint
state, (c) a cheap `fold` over a sub's terms, or (x) a hash-consing table over
a bounded domain of small integers.

The one thing that *is* expensive is **the VSA fixpoint itself** — and that
is not a table. `cbat_vsa.ml:2506-2507` records the measurement: *"the deep
per-edge refinement runs on EVERY visit … the fixpoint is ~92% of a hot sub's
producer time."* But `Data.Cache` cannot help there, because the fixpoint's
result **is** `R4`/`vsa_sol`, and caching it is exactly the "cache the
analysis result" question — which is §B.4, not §B.3.

## B.4 The KB: how VSA results are stored today, and Cache vs KB

`src/hike_kb.ml` (136 lines). One slot:

```ocaml
let run_cls = KB.Class.declare ~package:"hike" "run" ()

let vsa_info_slot =
  KB.Class.property ~package:"hike" run_cls "vsa-info"
    (KB.Domain.define
       ~inspect:(fun _ -> Base.Sexp.Atom "hike:vsa-info")
       ~join:map_join
       ~empty:Tid.Map.empty
       ~order:map_order
       "hike:vsa-info")
```

Producer: `hike.ml:672-700` — the `vsa` pass runs `Hike_vsa.offsets_of_sub`
per sub, accumulates into `acc`, then `Hike_kb.provide !acc` **once**
(`hike.ml:699`). Consumers read back with `Hike_kb.vsa_info ()`
(`hike.ml:158`, `:672`, `:712`).

The **domain is the interesting part** (`hike_kb.ml:1-25`) — and it is a
deliberate piece of engineering:

- `order` = **map extension** (`map_order`, `:66-83`): `m1 ⊑ m2` iff every
  sub in `m1` is in `m2` with the **same** `vsa_info`.
- `join` = **map union** with a per-sub rule (`map_join`, `:87-110`,
  `info_join`, `:48-55`): equal infos take either; **differing** non-empty
  infos for the same sub raise `Vsa_info_conflict`, surfaced as a
  `Toplevel.Conflict` via `KB.Conflict.register_printer` (`:41-46`).
- Rationale (`hike_kb.ml:18-24`): the old flat domain silently dropped a
  second, different map; the join domain makes a re-provide either a no-op,
  an extension, an idempotent re-write, **or a loud conflict**.

### Are Cache and KB overlapping or complementary here?

**Complementary, and for this use case the KB is strictly better.** Four
reasons, each grounded in a source:

1. **Lifetime is already right.** The VSA result lives for one `bap` run and
   is consumed by later passes in the **same** run (`hike.ml:158` reads it
   during signature computation, `:712` during stack-to-locals). A
   persistent on-disk cache would add a cross-run persistence nobody asked
   for — and would need a content key for it.
2. **The digest would be expensive and coarse.** To cache `vsa_info` under
   `Data.Cache` you need a digest of everything the analysis depends on.
   `bap-taint-propagator`'s answer is a **whole-program** digest
   (`propagate_taint_main.ml:138-159` — it visits every `arg`/`def`/`jmp` of
   every term). `bap-optimization`'s answer is per-sub but keyed on
   **addresses + name + level** (`optimization_main.ml:137-152`) — i.e. on
   *identity of the code*, which is exactly the fragile thing: any change to
   the sub (or, worse, to hike's analysis) yields a stale hit unless you put
   a version in the key. hike's subs are `Term.tid`-keyed, and `Tid`s are
   **not stable across runs** for the same binary in general.
3. **The KB gives you a conflict you cannot get from a cache.** Two different
   VSA results for one sub is *by construction* a bug in hike. The slot's
   join turns it into a loud `Toplevel.Conflict` (`hike_kb.ml:37-46`). A
   digest-keyed cache would just have two entries under two digests and never
   notice.
4. **The KB already gives cross-run persistence when you want it — for free.**
   This is the point most likely to be missed. `bap` has
   `--project=VAL` / `--knowledge-base=VAL` (alias `-k`, `-p`) and
   `--update/-u`; `bap-disassemble` caches **the entire KB** under
   `Data.Cache` with namespace `"knowledge"`
   (`disassemble_main.ml:264-283`, `:501-516`). So *if* hike ever wants
   cross-run reuse, the right seam is "put `vsa_info` in the KB and let BAP's
   KB cache carry it" — not "move `vsa_info` onto `Data.Cache`".

**Where `Data.Cache` would genuinely overlap the KB**: none of hike's current
state. The KB holds *analysis results keyed by program entity*; `Data.Cache`
holds *blobs keyed by content hash*. Those are different keys for different
purposes, and hike's results are all entity-keyed.

## B.5 The blocker check: are hike's value types serializable?

I tested this by compiling probes against the hike library (a throwaway
`zz_cache_probe/` dune target, since removed; `git status` confirms no source
file was modified).

| Type | Serializable? | Evidence |
|---|---|---|
| `Convutils.Vsa.vsa_info` | **No — but a one-word fix away.** | `convutils.ml:94,103,117,127` derive **only `[@@deriving equal]`**. Probe: `Unbound value "V.sexp_of_vsa_info"` / `V.compare_vsa_info`. A **shadow copy** of the record with `[@@deriving bin_io, compare, sexp]` round-tripped cleanly: `vsa_info(shadow, bin_io) roundtrip = true (10 bytes)`, sexp = `((offsets((9(Range 1 2))))(k_ranges())…)` |
| `Cbat_ai_representation.t` (= `AI.t`, the abstract state) | **Yes — already binable.** | `cbat_ai_representation.ml:195-199` derives `bin_io, sexp, compare`; the `.mli:20` exposes it via `Cbat_lattice_intf.S_val` → `Value.S`, and `bap.mli:4400-4406` shows `Value.S` **requires** `type t [@@deriving bin_io, compare, sexp]`. Probe: `AI.t bin_io rt = true (5 bytes for top)`; `AI.sexp_of_t(top)` = `((memories(()))(words(()))(frame()))` |
| `Cbat_clp.t` | **Yes** | `cbat_clp.mli:14` `type t [@@deriving bin_io, sexp]`. Probe: `CLP.t bin_io roundtrip = true (28 bytes)`; sexp `(3:64u)` |
| `Cbat_clp_set_composite.t` (WordSet) | **Yes, but not exposed** | `.ml:26` derives `bin_io, sexp, compare`, but `cbat_clp_set_composite.mli:15` says `type t` and includes `Cbat_wordset_intf.S` — whose `.ml:17` **does** carry `[@@deriving bin_io, sexp]`. So it is reachable through the interface. |
| `Cbat_ai_memmap.t` (Mem) | **Yes** | `cbat_ai_memmap.ml:220,272` `[@@deriving bin_io, sexp, compare]`; `.mli:25-26` at least exposes `sexp_of_t`/`t_of_sexp` |
| `Cbat_map_lattice` maps | **Yes** | `cbat_map_lattice.ml:215` `type t = L.t M.t Option.t [@@deriving bin_io, compare, sexp]` |
| `Bap.Std.Word` / `Tid` / `Var` / `Bil` | **Yes** — all `Regular` | `bap_bitvector.mli:13` `include Regular.S`; `bap_ir.ml:11-27` `[@@deriving bin_io, compare, sexp]`; `bap_var.mli:7` `include Regular.S`; `bap.mli:2038-2045` (`Bil.t = stmt list`, `include Data.S`). Probe: word/tid/var roundtrip = true. |
| `Llvm.llvalue` (emitter tables E1–E3, E7) | **No — abstract, no serializer** | It is an abstract handle into the LLVM context; not BAP's, and not `Regular`. |

**Two things this settles.** (1) Serializability is **not** the blocker for
the VSA-side candidates — `AI.t`, `CLP.t`, `Bil`/`Word`/`Tid`/`Var` are all
already serializable, and `vsa_info` needs a one-word deriving change.
(2) It **is** a hard blocker for every emitter table, which is fine because
none of those was a candidate anyway.

## B.6 The lattice question — the anticipated blocker does not exist

The question asks me to check this carefully. I did, three ways.

**Reading the stanzas** (`src/cbat_vsa/dune`):

```
(library (name cbat_vsa_domain) (public_name hike.cbat_vsa_domain) (wrapped false)
  ...
  (libraries hike_abi bap bitvec bitvec-order core core_kernel monads hashcons))   ; :35

(library (name cbat_vsa) (public_name hike.cbat_vsa)
  ...
  (libraries bap hike_abi cbat_vsa_domain bitvec core core_kernel monads hashcons)) ; :57
```

**`bap` is on BOTH library stanzas** — `cbat_vsa_domain:35` and
`cbat_vsa:57`. The dune file even explains why (`src/cbat_vsa/dune:11-16`):

> *"Note: the domain library still links `bap` because Bap.Std is the only
> provider of the Word API used here (Bap.Std.Word = Bap_bitvector, internal
> to bap-std; the `bitvec` package has no Word module and a monadic API)."*

**Reading the sources** — every module in `cbat_vsa_domain` opens BAP:

```sh
$ for f in cbat_clp cbat_word_ops cbat_fin_set cbat_map_lattice \
           cbat_clp_set_composite cbat_vsa_utils cbat_landmarks \
           cbat_lattice_intf cbat_wordset_intf; do
    printf "%-24s %s\n" "$f" "$(grep -c 'open Bap\|Bap\.\|Word\.' src/cbat_vsa/$f.ml)"
  done
cbat_clp                  1
cbat_word_ops             1
cbat_fin_set              1
cbat_map_lattice          1
cbat_clp_set_composite    1
cbat_vsa_utils            2
cbat_landmarks            1
cbat_lattice_intf         1
cbat_wordset_intf         1
```

**Reading the shipped bundle** — I unzipped the installed
`bap-common/plugins/hike.plugin` and listed units with `ocamlobjinfo`. The
bundle contains `cbat_vsa_domain.cmxs` and `cbat_vsa.cmxs` alongside
`hike.cmxs`, `hike_abi.cmxs`, `llvm.cmxs`, `hashcons.cmxs`. So the vendored
libraries are **already BAP-coupled in the shipped artifact**.

**Conclusion.** The dependency lattice is

```
hike_abi  ←  cbat_vsa_domain  ←  cbat_vsa  ←  hike
    ↖______________ bap ______________↗   (already, at every level)
```

`bap` is at the bottom with `hike_abi`, not above `cbat_vsa`. Using
`Data.Cache` inside `cbat_vsa_domain` or `cbat_vsa` would add **no new
dependency edge at all**. This blocker is **absent**.

What *is* true is the softer, non-technical concern: the vendored files carry
a Draper copyright header and are a port of CBAT's VSA
(e.g. `cbat_clp.ml:1-11`). Adding BAP-specific caching there would deepen the
vendoring drift — a **maintainability** argument, not a dependency argument.
It is real, and it is the reason I would still not put BAP caching in
`cbat_vsa_domain`, but it must not be confused with a lattice inversion.

## B.7 A perf reality-check

I timed the thing that would actually have to be slow for a cache to pay:

| Measurement | Result |
|---|---|
| `CLP.top 64` (hash lookup + return) | **27.7 ns/call** (2M calls) |
| `WO.half 64` | **16.6 ns/call** |
| `WO.dom_size 63` | **32.8 ns/call** |
| `bap --pass=hike-convlir` on `fizzbuzz` | **0.42 s** wall |
| same, on `factorial` / `array_local` | 0.42 s / 0.44 s |
| `bap --pass=hike-convlir --no-cache` | **0.93 s** (2.2× slower — BAP's own lifting cache is already paying, and hike is not involved) |

Note the last row: the **2.2×** speedup from BAP's cache is entirely BAP's
lifting/knowledge cache (`disassemble_main.ml:264-283`), which hike gets for
free today because it runs as a pass inside `bap`. hike's own contribution to
the 0.42 s is small by comparison. There is no large, hike-owned, cacheable
cost sitting in these tables.

---

# TASK C — Recommendation

## C.1 Candidate table

| # | Name | File:line | Current mechanism | Class | Verdict |
|---|---|---|---|---|---|
| G1 | `top_cache` | `cbat_vsa/cbat_clp.ml:118` | `Hashtbl` `int → Cbat_clp.t`, never cleared | (x) interning | **KEEP** |
| G2 | `dom_size_cache` | `cbat_vsa/cbat_word_ops.ml:123` | `Hashtbl` `(int*int) → word`, never cleared | (x) interning | **KEEP** |
| G3 | `half_cache` | `cbat_vsa/cbat_word_ops.ml:134` | `Hashtbl` `int → word`, never cleared | (x) interning | **KEEP** |
| G4 | `lm_env` | `cbat_vsa/cbat_landmarks.ml:47` | `Hashtbl` `Tid → lm_entry list` | (b) fixpoint state | **KEEP** (per-run in fact; cleared at `cbat_vsa.ml:3042`) |
| G5 | `addr_bits_ref` | `cbat_vsa/cbat_vsa.ml:147` | `int ref`, set-once | (y) config | **KEEP** (not a cache) |
| G6 | `widening_at_head` | `cbat_vsa/cbat_landmarks.ml:41` | `Tid.t option ref` | (b) fixpoint state | **KEEP** |
| R1 | `rc_versions` | `cbat_vsa/cbat_vsa.ml:3030` (`:2569`) | `Hashtbl` `Tid → int` | (b) fixpoint state | **KEEP** |
| R2 | `rc_cache` (walk cache) | `cbat_vsa/cbat_vsa.ml:2578` | `refine_hit Tid.Map.t Tid.Map.t ref` | (b) fixpoint state | **KEEP** |
| R3 | `rc_reads` | `cbat_vsa/cbat_vsa.ml:2572` | `Tid.Set.t ref` | (c) scratch | **KEEP** |
| R4 | `sol_map` | `cbat_vsa/cbat_vsa.ml:3016` | `(Tid, AI.t) Tid.Map.t ref` | (b) **the fixpoint solution** | **KEEP** |
| R5/R6 | WTO tables | `cbat_vsa/cbat_vsa.ml:3043,3053` | `Hashtbl` `Tid → Tid.Set` / `Tid → Tid` | (b) fixpoint state | **KEEP** |
| R7 | `rpo_index` | `cbat_vsa/cbat_vsa.ml:96` | `Hashtbl` `Tid → int`, local | (c) scratch | **KEEP** |
| R8 | `edge_conds_of` tbl | `cbat_vsa/cbat_vsa.ml:2483` | `Hashtbl` → folded to `Tid.Map` | (c) scratch | **KEEP** |
| R9 | `succ_tbl`/`pred_tbl` | `cbat_vsa/cbat_vsa.ml:3087-3088` | `Hashtbl` `Var → Var list`, local | (c) scratch | **KEEP** |
| S1–S5 | per-sub derived maps | `cbat_vsa.ml:2924,2935,2967,~2945`; `hike_vsa_relevance.ml:79-101` | `Map`/`Set`, one `fold` each | (a) pure but **cheap** | **KEEP** |
| S6 | `merged_tags` | `hike_vsa.ml:202-229` | `vsa_kind Tid.Map.t` | (c) scratch | **KEEP** |
| S7 | stack-to-locals folds | `hike_stack_to_locals.ml` ×12 | `Map`-built per sub | (c) scratch | **KEEP** |
| S8 | `ctx.subs` | `hike.ml:425-433` | `(Arg.t list * Arg.t list) Tid.Map.t`, set-once | (z) already clean | **KEEP** |
| E1–E5,E7 | emit_ctx maps | `convutils.ml:55-64,82`; `bil2llvm.ml:2346-2347` | refs in one threaded record | (z) already clean | **KEEP** |
| E6 | `edge_counts_of_sub` | `bil2llvm.ml:1919` (used `:1946`) | `EHashtbl` per sub, pure | (a) pure, cheap, **local** | **KEEP** (or DELETE — see C.3) |
| — | `vsa_info` (per-sub VSA result) | `convutils.ml:89-128`, `hike_kb.ml:98-105` | **KB slot** with a join domain | (a) expensive, but **KB-served** | **KEEP on the KB** — do not move |

**Tally: 0 MOVE, 12–13 KEEP, 2 DELETE-candidates (§C.3).**

## C.2 Why nothing moves — the four arguments, in order of strength

### 1. Every "cache" in the tree is either fixpoint state or hash-consing.

`Data.Cache` is a **persistent, content-addressed, weak** store. Its contract
(`regular.mli:393-404`) is "the value is a pure function of the digest, and
you must tolerate `None`."

- **Fixpoint state (R1–R6, G4, G6)** is *not* a function of any digest. It is
  mutated during widening, it carries iteration-order-dependent history (the
  `dist`/`dist_p` pair in `lm_entry`, `cbat_landmarks.ml:16-20`), and moving
  it to a content-addressed store is **category-confused**. `cbat_vsa.ml`'s
  own comment (`:2546-2548`) gets this exactly right — *"Per-run, per-sub …
  a nested run … builds its own — no cross-run reuse is possible."* The
  author already considered and rejected cross-run reuse, for the right
  reason.
- **Hash-consing (G1–G3)** is the opposite shape: the value is a function of
  the key, but (a) the *point* is to return a **shared** immutable value
  within the process, and (b) the domain is ≤ a few hundred entries. Putting
  a `Word.t` behind an MD5 + a filesystem `open`/`read` to save ~28 ns is
  absurd. Measured: `CLP.top 64` is **27.7 ns**. A single `Data.Cache.load`
  is a path build plus an `open` plus a `read` — four orders of magnitude
  more.

### 2. The one expensive thing is not a table, and it is already KB-served.

The expensive thing is the fixpoint (92% of a hot sub's producer time,
`cbat_vsa.ml:2506-2507`). Its output is `vsa_info`. Two paths:

- **Cache `vsa_info` under `Data.Cache`:** needs a digest of the sub *and* of
  hike's analysis version. `bap-taint-propagator` solves this by digesting
  the **whole program** (`:138-159`), which defeats per-sub caching;
  `bap-optimization` keys on addresses+name+level (`:137-152`), which is
  fragile to any analysis change unless you add a version. Then you must
  derive `[@@deriving bin_io, compare, sexp]` on `vsa_info` (currently
  `[@@deriving equal]` only — `convutils.ml:94,103,117,127`).
- **Or: keep it on the KB** — which is what it does today, and which already
  gives you cross-run persistence for free via `bap --project=` /
  `--knowledge-base=` + BAP's own `"knowledge"`-namespaced KB cache
  (`disassemble_main.ml:264-283`, `:501-516`).

The second strictly dominates. See §B.4.

### 3. The digest cost is real and the invalidation story is not free.

`regular.mli:675-679` documents `digest` as O(N) in input size. And nothing
in `Data.Cache` invalidates on code change: `Data.S.version`
(`regular.mli:296-311`) versions the **on-disk format**, not the digest. If
you cache a VSA result keyed on the sub's BIL and then improve the widening,
you get **silent stale hits** on every binary until you remember to bump a
manual version string in the namespace. hike has no such discipline today and
would be adding a new failure mode to a codebase whose AGENTS.md §5 is
*"soundness over precision, always"* — a stale VSA result is precisely an
unsound narrowing.

This is a **correctness risk introduced in exchange for a perf win that
§B.7 shows is not there** (0.42 s per binary; the tables are nanoseconds).

### 4. The vendoring concern (the honest, non-technical one).

`src/cbat_vsa/` is a vendored port of CBAT's VSA with a Draper copyright
header on every file. Three of the four never-cleared globals (G1–G3) live
there, and AGENTS.md §6 requires the vendored tree to stay production-clean.
Even though §B.6 shows **no** dependency-lattice inversion would occur
(`bap` is already a dependency of `cbat_vsa_domain`), adding BAP-specific
caching to `cbat_clp.ml`/`cbat_word_ops.ml` deepens the drift from upstream
for zero measured benefit.

## C.3 The cleanup that IS available — two small deletions

Since the question was framed as a cleanup opportunity, here is the cleanup I
found. It is not a migration; it is deletion.

**D1 — hoist `def_of_lhs` out of the loop (`hike_vsa.ml:271`).**

```ocaml
| Bil.Var tmp ->
  let def_of_lhs =
    Term.enum blk_t sub'
    |> Seq.concat_map ~f:(Term.enum def_t)
    |> Seq.fold ~init:Var.Map.empty ~f:(fun m d -> Core.Map.set m ~key:(Var.base (Def.lhs d)) ~data:d)
  in
  (match Core.Map.find def_of_lhs (Var.base tmp) with ...)
```

This builds a whole-sub `Var.Map` **inside** a per-def match arm, so it is
O(sub) **per def** = O(sub²). The codebase already knows this pattern and
already fixed it elsewhere — `cbat_vsa.ml:2969` computes `defs_of_sub s`
**once** at fixpoint entry precisely because of it, and
`cbat_vsa.ml:3015-3018` records the identical hoist for `rc_all_tagged`:
*"the HOISTED all-defs-tagged set (was a per-call fold over the whole sub's
defs — O(sub) per refinement on big subs)"*. Same bug, unhoisted.

**D2 — reconsider `edge_counts_of_sub` (`bil2llvm.ml:1919`, used `:1946`).**

It builds a nested `EHashtbl` and is consumed a few lines later. If the
consumption really is a fixed small number of lookups (as `:1946-1970`
suggests — it is only consulted to duplicate phi incoming edges for
same-target conditionals), a direct `Seq` scan at the use site would remove
the table and the "PURE, EAGER, OUTSIDE any monad" subtlety documented at
`:1912-1918` (which records a real bug: the in-monad version's `bump` effects
never ran because `KB.Seq.iter` is lazy). This is a **maybe** — it needs the
use site read closely before deleting, and it is perf-neutral at worst.

## C.4 If you still want to use `Data.Cache` — the one place it fits

For completeness: the *only* hike-shaped thing that fits `Data.Cache`'s
contract is **memoizing the per-sub VSA result across runs**, keyed on
(sub identity + hike version). Concretely, if that were wanted, it would look
like:

```ocaml
(* 1. convutils.ml:89-128 — extend the derivings from [equal] to [bin_io, compare, sexp].
      Verified to compile and round-trip (§B.5): a shadow copy round-tripped in 10 bytes. *)
  type vsa_kind  = ... [@@deriving bin_io, compare, sexp]
  type region    = { ... } [@@deriving bin_io, compare, sexp]
  type vsa_info  = { ... } [@@deriving bin_io, compare, sexp]

(* 2. a Regular instance *)
module Vsa_info_regular = Regular.Make (struct
  type t = Convutils.vsa_info
  let bin_shape_t = Convutils.bin_shape_vsa_info
  let bin_size_t  = Convutils.bin_size_vsa_info
  let bin_write_t = Convutils.bin_write_vsa_info
  let bin_read_t  = Convutils.bin_read_vsa_info
  let __bin_read_t__ = Convutils.__bin_read_vsa_info__
  let bin_writer_t = Convutils.bin_writer_vsa_info
  let bin_reader_t = Convutils.bin_reader_vsa_info
  let bin_t        = Convutils.bin_vsa_info
  let sexp_of_t    = Convutils.sexp_of_vsa_info
  let t_of_sexp    = Convutils.vsa_info_of_sexp
  let compare      = Convutils.compare_vsa_info
  let pp ppf _     = Format.fprintf ppf "<vsa_info>"
  let version      = "1"            (* BUMP ON EVERY ANALYSIS CHANGE — see below *)
  let module_name  = Some "hike.vsa_info"
  let hash         = Hashtbl.hash
end)

(* 3. hike.ml, in the vsa pass, replacing the unconditional per-sub solve *)
let digest (sub : sub term) : Data.Cache.digest =
  let d = Data.Cache.Digest.create
            ~namespace:("hike:vsa_info:v" ^ version_string) in   (* <- manual versioning *)
  let d = Data.Cache.Digest.add d "%s" (Sub.name sub) in
  Term.enum blk_t sub |> Seq.fold ~init:d ~f:(fun d blk ->
    Data.Cache.Digest.add d "%a" Tid.pp (Term.tid blk))
  (* and every def, because the analysis reads them all — cf. bap-taint-propagator:138-159 *)

let info =
  match Vsa_info_regular.Cache.load (digest sub) with
  | Some i -> i
  | None ->
    let i = Hike_vsa.offsets_of_sub target sp sub in
    Vsa_info_regular.Cache.save (digest sub) i;
    i
```

**Honest assessment of this sketch, and why I do not recommend it:**

- The digest must cover **every term the analysis reads** — which, per
  `bap-taint-propagator`'s own answer, is the whole sub (or the whole
  program). That is an O(sub) walk *before* the analysis you are trying to
  skip, and it does not include the **interprocedural** inputs
  (`static_graph_vsa` recurses at `cbat_vsa.ml:2980`), so the key would be
  **unsound** unless it transitively covers callees. Making it sound means
  a call-graph-closed digest — i.e. re-deriving most of what the analysis
  computes.
- `~version` must be **manually bumped on every analysis change** or you get
  silent stale results — an unsound-narrowing risk in a codebase whose
  stated doctrine is soundness first (AGENTS.md §5).
- It is **redundant with the KB path** (§B.4 point 4): `bap --knowledge-base`
  + BAP's `"knowledge"`-namespaced cache already persists the KB across runs,
  and hike's `vsa_info` is *already in the KB*. Moving it to `Data.Cache`
  would mean maintaining two storage paths for one value.

## C.5 Bottom line

**Do not migrate.** BAP's `Cache` is a well-built persistent on-disk
content-addressed store, and it is genuinely used for analysis results — but
hike has **no** cache that matches its contract:

- the three never-cleared globals are **hash-consing tables over a bounded
  domain of small integers**, measured at 17–33 ns per hit;
- the fixpoint tables are **per-run mutable state**, and `cbat_vsa.ml:2546`
  already documents why cross-run reuse is impossible for them;
- the one expensive artefact (`vsa_info`) is **already on the KB**, which is
  the better mechanism and already gets cross-run persistence for free;
- the anticipated blockers turn out to be **non-blockers** (no lattice
  inversion — `cbat_vsa_domain` already links `bap`; no `Cache` name
  collision — BAP exports no top-level `Cache` unit; the values **are**
  serializable — `AI.t` already, `vsa_info` with a one-word deriving change).

The cleanup available is **two small deletions** (§C.3), not a migration —
and one of them (`hike_vsa.ml:271`) is a genuine O(sub²) that the codebase
already fixed in the parallel case at `cbat_vsa.ml:3015`.

---

## Appendix — commands used

```sh
# --- BAP ---
opam switch list; opam var root                       # -> bap-flambda, /home/tovpr/.opam
ocamlfind query bap            # -> /home/tovpr/.opam/bap-flambda/lib/bap
ocamlfind query bap-cache      # -> /home/tovpr/.opam/bap-flambda/lib/bap-cache
cd /home/tovpr/.opam/bap-flambda/lib
grep -rln "Cache" . --include="*.mli"                 # -> regular.mli + bap-cache/plugin/*.mli
grep -n "Cache" bap-std/bap.mli                       # -> no matches
cat regular/regular_cache.{ml,mli}                    # the whole implementation
sed -n '391,442p;646,742p;774,794p' regular/regular.mli
cat bap-cache/plugin/bap_cache.ml bap-cache/plugin/bap_cache_main.ml
sed -n '1190,1210p' bap-main/bap_main.ml              # cachedir
sed -n '1040,1044p' bap-main/bap_main.ml              # --no-<plugin> generation
grep -rn "Data.Cache" bap-taint-propagator/plugin/propagate_taint_main.ml
grep -rn "O.Cache"    bap-optimization/plugin/optimization_main.ml
grep -rn "Data.Cache" bap-disassemble/plugin/disassemble_main.ml
ocamlobjinfo bap-abi/plugin/abi.cmxs | grep '^Name:'            # -> Abi
ocamlobjinfo bap-cache/plugin/bap_cache_plugin.cmxs | grep '^Name:'
for f in bap-std/bap.cmxs bap-std/types/bap_types.cmxs bap-std/disasm/bap_disasm.cmxs \
         bap-main/bap_main.cmxs bap-knowledge/knowledge.cmxs regular/regular.cmxs \
         bap-plugins/bap_plugins.cmxs; do ocamlobjinfo "$f"; done \
  | grep '^Name:' | sort -u | grep -wE 'Abi|Cache'      # -> (empty)
bap --help | grep -iE "cache|no-cache"                   # --cache-dir, --no-cache, --cache-clean
bap cache --help
unzip -o /home/tovpr/.opam/bap-flambda/lib/bap-common/plugins/hike.plugin -d /tmp/opencode/plugdump

# --- behavioural probes (built + run, /tmp/opencode/cacheprobe) ---
# dune: (executables (names probe probe2)
#        (preprocess (pps ppx_bap))
#        (libraries bap bap-main core_kernel core regular threads.posix))
dune exec ./probe.exe        # digest shape, oblivion default, Regular round-trip, IR round-trips
dune exec ./probe2.exe       # run twice -> MISS then HIT from ~/.cache/bap/data/<md5>
dune exec ./probe2.exe -- --cache-dir=/tmp/x     # relocates the root
dune exec ./probe2.exe -- --no-cache             # oblivion; root stays empty

# --- hike ---
cd /home/tovpr/Documents/hike
cat src/dune src/cbat_vsa/dune src/hike_abi/dune        # the lattice
grep -rn "Hashtbl\." --include="*.ml" src/ | wc -l      # 75, in 6 files
grep -rn "^let .*= *\(Hashtbl\.create\|ref \|Map\.empty\)" --include="*.ml" src/ | grep -v _build
grep -rn "^let [a-z_]* *\(:[^=]*\)\?= *ref " --include="*.ml" src/ | grep -v _build
grep -rn "vsa_sol_tbl\|provide_sol\|add_sol" --include="*.ml*" src/ | grep -v _build   # gone
cat src/hike_kb.ml
sed -n '88,130p' src/convutils.ml                       # vsa_info
head -20 src/cbat_vsa/cbat_clp.mli                      # bin_io on the CLP type
sed -n '195,199p' src/cbat_vsa/cbat_ai_representation.ml
git status --short                                      # no source file modified
```

**Not verified / could not verify:**

- **OCaml-thread safety** of `Data.Cache`. No `.mli` anywhere claims it; the
  plugin claims only cross-*process* safety (lock-free file ops). hike's
  passes are single-threaded so this is moot today, but I did not test it.
- **`Marshal`-format cross-OCaml-version safety.** `regular.mli:273-276` says
  Marshal is the default for raw `Data.S`; my probes show `Regular.Make`
  picks **binprot** instead, which is why the round-trips worked. If anyone
  forces `with_writer "marshal"`, that is a different stability story I did
  not investigate.
- **GC behaviour under a full cache.** I read `bap_cache_gc.ml` and the
  config defaults, but did not fill a 4 GB cache to watch it shrink.
- **The exact cost of `Data.Cache.load` on this machine.** I did not
  microbenchmark it; the "four orders of magnitude" claim in §C.2 is an
  inference from the mechanism (path build + `open` + `read` + binprot
  decode) versus a measured 17–33 ns `Hashtbl` hit, not a measurement.
