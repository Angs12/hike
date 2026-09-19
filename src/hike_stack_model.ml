
(* The sections in declaration order (the attribution's vocabulary,
   hosted here — the model is the shared home every lane reads).  A
   range carries its section, so merging across sections is
   impossible. *)
module Vocab = struct
  open! Core

  type sec = Stack | Args | Text | Rodata | Data | Got | Gotplt | Datarelro | Bss
  [@@deriving equal, compare, sexp]

  (* The slim def-carried classification: the def's section with its
     ADDRESS bounds (not the tree's occupied-byte bounds), the
     justified unbounded form, the data-section anchoring, or Dead.
     Absence is the identity.  The constructors live in [Tag] so the
     section constructors stay unshadowed. *)
  module Tag = struct
    type t =
      | Stack of int64 * int64
      | Stack_unbounded
      | Args of int64 * int64
      | Args_unbounded
      | Sec of sec * int64 * int64
      | Dead
    [@@deriving equal, compare, sexp]
  end

  type sec_tag = Tag.t
end

include Vocab

(* Pure stack model: the geometry facts and the shared vocabulary.


   THE MODEL IS THE TAG (ADR 0008): the VSA tags every frame-resident access
   with its proven offset span.  This module merges overlapping spans into
   regions and derives each region's facts from those tags alone — the SP
   Slot anchor makes the partition purely geometric.
   An oversized region joins to Frame with a diagnostic naming it —
   never a gate. *)

open Bap.Std
open Bap.Std.Bil.Types
open Bap_core_theory
module Abi = Hike_abi

(* Stack pointer only: the one register granted stack semantics by fiat
   (ADR 0008).  There is no frame-pointer fact here — fp is an ordinary
   callee-saved GPR whose stack-ness, like any register's, is proven by
   the VSA (its frame term), never by name. *)

(* The Vsa record: the producer/emitter contract point.  The
   producer (hike_vsa) builds it, the KB (hike_kb) stores it, the model
   and the emitter consume it — one home at the contract point. *)
module Vsa = struct
  open Core

  (* The model segment's base (2^62): the ABSOLUTE position of the
     entry RSP on the segment line (the seeded SP is base + offset 0).
     The single representation: tag positions are absolute, so
     every "below/above the entry RSP" question compares against this
     constant, and a frame-relative depth is [base − position]. *)
  let segment_base = Cbat_vsa.WordSet.stack_base

  (* Alias of the kind enum in [Cbat_extraction]. *)
  type vsa_kind = Cbat_vsa.Cbat_extraction.kind =
    | Range of int64 * int64
    | Infinite of int64 * int64
    | Caller of int64 * int64
    | Mixed of int64 * int64
    | Dead
  (* Aliases [equal_kind] for [@@deriving equal]. *)
  let equal_vsa_kind = Cbat_vsa.Cbat_extraction.equal_kind

  (* The fully-infinite span — the kind of a TOP denotation — and the
     fact its consumers key on. *)
  let unbounded_span = Cbat_vsa.Cbat_extraction.unbounded_span
  let is_unbounded_span = Cbat_vsa.Cbat_extraction.is_unbounded_span

  (* One-line contract: the offset set with exactly one element. *)
  let singleton_offset (offs : Cbat_vsa.WordSet.Clp.t) : int64 option =
    let i64 w = match Cbat_word.to_int64 w with Ok v -> Some v | Error _ -> None in
    let open Base.Option in
    Cbat_vsa.WordSet.Clp.min_elem offs >>= i64
    >>= fun lo -> Cbat_vsa.WordSet.Clp.max_elem offs >>= i64
    >>= fun hi -> if Int64.equal lo hi then Some lo else None

  (* One-line contract: the denotation's single stack position
     (absolute, on the segment line), when it denotates to exactly
     one. *)
  let singleton_stack_position (ws : Cbat_vsa.WordSet.t) : int64 option =
    let open Base.Option in
    Cbat_vsa.WordSet.stack_offsets ws >>= singleton_offset
    >>= Cbat_vsa.Cbat_extraction.position_of_offset

  (* One call site's outgoing slot facts: which slot index each of
     the block's outgoing stores feeds.  The structured fact IS the
     provability — presence of slot i in the map = the site's store
     feeds promoted slot i; absence = the store stays on the window
     path (the identity). *)
  type call_site = {
    site_slots : (int * Tid.t) list; (* slot index -> storing def *)
  } [@@deriving equal]

end
include Vsa



let addr_of_rhs (e : exp) : (exp * Size.t) option =
  let vis =
    object
      inherit [ (exp * Size.t) option ] Exp.visitor
      method! visit_load ~mem:_ ~addr _ s acc =
        Base.Option.first_some acc (Some (addr, s))
      method! visit_store ~mem:_ ~addr ~exp:_ _ s acc =
        Base.Option.first_some acc (Some (addr, s))
    end
  in
  vis#visit_exp e None

(* Splits a store rhs into data and cast wrapper using visitor/mapper. *)
let store_data_of_rhs (e : exp) : (exp * (exp -> exp)) option =
  let vis =
    object
      inherit [ exp option ] Exp.visitor
      method! visit_store ~mem:_ ~addr:_ ~exp:data _ _ acc =
        Base.Option.first_some acc (Some data)
    end
  in
  match vis#visit_exp e None with
  | None -> None
  | Some data ->
      let wrap x =
        let mapper =
          object
            inherit Exp.mapper
            method! map_store ~mem:_ ~addr:_ ~exp:_ _ _ = x
          end
        in
        mapper#map_exp e
      in
      Some (data, wrap)

(* One word, in bits: the width of every model-var minter below. *)
let word_bits (word : int) : int = 8 * word

(* The promoted incoming stack-slot parameter of index [i]: the
   callee's own signature fact, minted deterministically so the
   signature and the body agree on the same var. *)
let arg_slot ~(word : int) (i : int) : var =
  Var.create ~is_virtual:false ~fresh:false
    (Printf.sprintf "hike_slot%d" i)
    (Type.Imm (word_bits word))

(* The call-argument temp of slot [i]: the BIR def a call site
   binds the promoted argument to (the promotion rewrite creates it
   right after the site's outgoing store; the call's emission passes its
   bound value).  Deterministically minted like the slots. *)
let call_arg ~(word : int) (i : int) : var =
  Var.create ~is_virtual:false ~fresh:false
    (Printf.sprintf "hike_arg%d" i)
    (Type.Imm (word_bits word))

(* Tests for the call-argument temps (the DCE rule: they survive — they
   are the call's arguments, consumed by the emission). *)
let is_call_arg (v : var) : bool =
  Base.String.is_prefix (Var.name v) ~prefix:"hike_arg"

(* Tests for the promoted slot parameters. *)
let is_arg_slot (v : var) : bool =
  Base.String.is_prefix (Var.name v) ~prefix:"hike_slot"

(* The incoming-window memory var: the rewrite re-points a callee's
   above-entry accesses at it; the emitter materializes them against
   the hike_window parameter (the caller's world), never the callee's
   own residue alloca. *)
let window_mem : var =
  Var.create ~is_virtual:false ~fresh:false "hike_window_mem"
    (mem64_t (Size.of_int_exn 8))

let is_window_mem (v : var) : bool =
  String.equal (Var.name v) "hike_window_mem"

(* The Caller-Window Parameter: the caller-window base, not SP — the
   residual window-base argument of variadic/mixed subs (the bridge) and
   of the memory-convention thunks.  The model owns the var grammar:
   window, slots, and regions all mint here. *)
let hike_window_var ~(word : int) : var =
  Var.create ~is_virtual:false ~fresh:false "hike_window"
    (Type.Imm (word_bits word))

(* Region memory and base vars; the alloca's emitted name. *)
let region_name (id : int) : string = Printf.sprintf "stack_r%d" id

let region_mem (id : int) : var =
  Var.create ~is_virtual:false ~fresh:false
    (region_name id ^ "_mem")
    (mem64_t (Size.of_int_exn 8))

let region_base ~(word : int) (id : int) : var =
  Var.create ~is_virtual:false ~fresh:false
    (region_name id ^ "_base") (Type.Imm (word_bits word))

(* Memory-var test (the BAP var-kind predicate; the var grammar lives
   here with the fission-var tests). *)
let is_mem var = match Var.typ var with Mem _ -> true | _ -> false

(* Tests for fission var names. *)
let is_region_mem (v : var) : bool =
  Base.String.is_prefix (Var.name v) ~prefix:"stack_r"
  && Base.String.is_suffix (Var.name v) ~suffix:"_mem"

(* The region id of a fission var ([stack_rN_mem]). *)
let is_region_base (v : var) : bool =
  Base.String.is_prefix (Var.name v) ~prefix:"stack_r"
  && Base.String.is_suffix (Var.name v) ~suffix:"_base"

(* ------------------------------------------------------------------ *)
(* The section partition.  Sections mirror the stack regions:   *)
(* the attribution pass carves each reserved span into per-object     *)
(* components; the BIL carries the component in the mem var           *)
(* ([sec_comp_N_mem], the fission convention); the emitter routes by  *)
(* name.  A section's native base is a compile-time constant (unlike  *)
(* the stack's runtime anchor), so there is no base var to bind —     *)
(* the address delta is inline arithmetic.                            *)
(* ------------------------------------------------------------------ *)

(* One emitted component: the word range [lo_w, hi_w] of the section
   keyed by its native span, plus the typed-emission decision. *)
type sec_comp = {
  comp_id : int;              (* the N in sec_comp_N (module-wide) *)
  sec_lo : int64;             (* the owning section's native span *)
  sec_hi : int64;
  lo_w : int;                 (* word range within the section *)
  hi_w : int;
  typed_w : int;              (* bytes per element: 8/4/2/1 *)
}

let sec_comp_name (n : int) : string = Printf.sprintf "sec_comp_%d" n

let sec_comp_mem (n : int) : var =
  Var.create ~is_virtual:false ~fresh:false
    (sec_comp_name n ^ "_mem")
    (mem64_t (Size.of_int_exn 8))

(* The gap runs (the residue's byte-exact remainder) continue the same
   numbering; they emit globals but carry no BIL var. *)
let sec_res_name (n : int) : string = Printf.sprintf "sec_res_%d" n

let is_sec_comp_mem (v : var) : bool =
  Base.String.is_prefix (Var.name v) ~prefix:"sec_comp_"
  && Base.String.is_suffix (Var.name v) ~suffix:"_mem"

(* The component id of a fission var ([sec_comp_N_mem]); a var the test
   above rejects parses to no id. *)
(* A word of a section image is string text iff a printable run crosses
   its start boundary: the start byte is printable and every byte back
   to the last NUL (or to the array's start, when none precedes) is
   printable too.  A NUL directly before the word means the run starts
   at the word — no crossing, the word renders as a value. *)
let string_text_word ~(arr : int array) ~(off : int) : bool =
  let printable b = b >= 0x20 && b <= 0x7e in
  let rec crosses i =
    if i < 0 then true
    else if arr.(i) = 0 then i < off - 1
    else if printable arr.(i) then crosses (i - 1)
    else false
  in
  off > 0 && off < Array.length arr && printable arr.(off) && crosses (off - 1)

(* The degraded frame's below-entry depth fact: the deepest literal SP
   decrement in the sub (rsp-sub prologues and VLAs). *)
let deepest_sp_decrement (sub : sub term) ~(abi : Abi.t) : int64 =
  let is_sp v = Abi.is_sp abi (Var.base v) in
  Term.enum blk_t sub
  |> Seq.fold ~init:0L ~f:(fun acc blk ->
         Term.enum def_t blk
         |> Seq.fold ~init:acc ~f:(fun acc d ->
               match Def.rhs d with
               | Bil.BinOp (Bil.MINUS, Bil.Var r, Bil.Int w)
                 when is_sp r ->
                   Int64.max acc (Word.to_int64_exn w)
               | _ -> acc))

(* The capacity of the frame's window extension (the bounded arm: a
   real SysV window never needs more; a wider extent reads past it the
   way an unproven address always has). *)
let caller_window_bytes : int64 = 65536L

(* The directionless stack top's below-entry clamp: a TOP StackOff
   claims [entry − stack_max, entry) — the same practical constant the
   residue's own extent clamps at. *)
let stack_max : int64 = 65536L

(* A call pushes its return address one word below the caller's SP at
   the call — a cell below the lowest SP value the sub reaches, which
   the extent folds never record.  A call with no return continuation
   is the lifted return's epilogue: it pops instead of pushing. *)
let call_pushes (j : jmp term) : bool =
  match Jmp.kind j with
  | Call c -> Option.is_some (Call.return c)
  | _ -> false

let has_call_push (sub : sub term) : bool =
  Term.enum blk_t sub
  |> Seq.exists ~f:(fun blk ->
         Term.enum jmp_t blk |> Seq.exists ~f:call_pushes)

(* The emitter's per-sub inputs are STRUCTURE (the promotion's BIR args /
   arg defs / direct targets, the def-kind slots below) plus this narrow
   LAYOUT fact: the alloca-construction inputs alone (the fallback
   frame's bytes and the split regions' geometry) — no offsets, no
   promotion facts, no kinds. *)

module Sub_layout = struct
  open Core

  (* D3: the fold's product.  [regions] is EVERY alloca of the sub —
     the carved regions and the stack residue (id 0, whose extent
     contains the anchor and the caller window).  [anchor] is the
     entry RSP's runtime position: (region id, byte index inside that
     alloca) — the SP Slot stores ptrtoint of it, so every model
     address integer resolves against one base. *)
  type t = {
    regions : (int * (int64 * int64) * int64) list;
    anchor : (int * int64) option;
    (* The sub reads its incoming window (above-entry positions): its
       direct-call signature carries the hike_window parameter and its
       window accesses materialize against it. *)
    window_param : bool;
  }

  let equal_region (i1, (l1, h1), b1) (i2, (l2, h2), b2) =
    Int.equal i1 i2 && Int64.equal l1 l2 && Int64.equal h1 h2
    && Int64.equal b1 b2

  let compare_region (i1, (l1, h1), b1) (i2, (l2, h2), b2) =
    match Int.compare i1 i2 with
    | 0 -> (
        match Int64.compare l1 l2 with
        | 0 -> (
            match Int64.compare h1 h2 with
            | 0 -> Int64.compare b1 b2
            | c -> c)
        | c -> c)
    | c -> c

  let equal (a : t) (b : t) =
    Base.List.equal equal_region a.regions b.regions
    && Base.Option.equal
         (fun (i1, x1) (i2, x2) -> Int.equal i1 i2 && Int64.equal x1 x2)
         a.anchor b.anchor
    && Bool.equal a.window_param b.window_param

  let compare (a : t) (b : t) : int =
    match Base.List.compare compare_region a.regions b.regions with
    | 0 -> Bool.compare a.window_param b.window_param
    | c -> c

  let pp fmt { regions; anchor; window_param } =
    Format.fprintf fmt "regions=%d;anchor=%s;window=%b"
      (Base.List.length regions)
      (match anchor with
       | Some (i, idx) -> Printf.sprintf "r%d@%Ld" i idx
       | None -> "none")
      window_param

  let empty = { regions = []; anchor = None; window_param = false }

  let sexp_of_t (t : t) : Sexp.t =
    Sexp.List
      (Base.List.map t.regions ~f:(fun (id, (lo, hi), b) ->
           Sexp.Atom (Printf.sprintf "%d:%Ld:%Ld:%Ld" id lo hi b))
       @ (match t.anchor with
          | Some (i, idx) -> [ Sexp.Atom (Printf.sprintf "anchor=%d:%Ld" i idx) ]
          | None -> []
          @ if t.window_param then [ Sexp.Atom "window" ] else []))

  let t_of_sexp (s : Sexp.t) : t =
    match s with
    | Sexp.List items ->
        let regions =
          Base.List.filter_map items ~f:(fun item ->
              match item with
              | Sexp.Atom a when not (Base.String.is_prefix a ~prefix:"anchor=") ->
                  (match Stdlib.String.split_on_char ':' a with
                   | [ id; lo; hi; b ] ->
                       Some
                         ( int_of_string id,
                           (Int64.of_string lo, Int64.of_string hi),
                           Int64.of_string b )
                   | _ -> failwith "hike-layout: bad region sexp")
              | _ -> None)
        in
        let anchor =
          Base.List.find_map items ~f:(fun item ->
              match item with
              | Sexp.Atom a when Base.String.is_prefix a ~prefix:"anchor=" ->
                  (match
                     Stdlib.String.split_on_char ':'
                       (Base.String.drop_prefix a 7)
                   with
                   | [ i; idx ] -> Some (int_of_string i, Int64.of_string idx)
                   | _ -> failwith "hike-layout: bad anchor sexp")
              | _ -> None)
        in
        let window_param =
          Base.List.exists items ~f:(fun item ->
              match item with
              | Sexp.Atom a -> String.equal a "window"
              | _ -> false)
        in
        { regions; anchor; window_param }
    | _ -> failwith "hike-layout: bad sexp"

  module Stringable = struct
    type nonrec t = t
    let to_string t = Base.Sexp.to_string (sexp_of_t t)
    let of_string s = t_of_sexp (Parsexp.Single.parse_string_exn s)
  end

  include Core.Binable.Of_stringable_with_uuid (struct
    include Stringable

    let caller_identity =
      Bin_prot.Shape.Uuid.of_string "hike:hike_stack_model.Sub_layout/2"
  end)
end

(* Top-level aliases (the mli's re-export shape). *)
type sub_layout = Sub_layout.t = {
  regions : (int * (int64 * int64) * int64) list;
  anchor : (int * int64) option;
  window_param : bool;
}



(* The layout rides the SUB TERM (the one tag): the producer computes it
   once; the emitter reads it off the term. *)
let layout_tag : Sub_layout.t Value.Tag.t =
  Value.Tag.register ~package:"hike" ~name:"hike-layout"
    ~uuid:"3f5e1c2a-9b47-4d60-8a15-c4d9e07b2f11"
    (module Sub_layout)

let set_layout (l : Sub_layout.t) (sub : sub term) : sub term =
  Term.set_attr sub layout_tag l


(* Per-def tags ride the DEF'S VALUE: the producer stamps each def with
   its kind (the 100% Tagging Invariant's tag) and the dynamic-allocation
   defs with the dyn-alloc fact; the emitter reads the tags off the
   term — never a per-sub record. *)

module KB = Bap_knowledge.Knowledge

(* The dynamic-allocation fact: the def is a runtime-sized SP
   decrement (the producer's denotation event) and emits a REAL
   runtime-sized alloca.  The storage decision rides the def's value
   beside the kind — the address enum says nothing about storage. *)
let def_dyn_alloc_slot : (Theory.Value.cls, bool) KB.slot =
  let bool_domain =
    KB.Domain.flat
      ~inspect:(fun b -> Base.Sexp.Atom (string_of_bool b))
      ~equal:Bool.equal ~empty:false "hike:dyn-alloc"
  in
  KB.Class.property ~package:"hike" Theory.Value.cls "hike-dyn-alloc"
    bool_domain

let def_is_dyn_alloc (d : def term) : bool =
  KB.Value.get def_dyn_alloc_slot (Def.value d)

(* The window-value fact: the def computes an ADDRESS VALUE that lives
   at/above the entry line — its emitted integer re-bases to the
   hike_window parameter (the caller's world), so derefs of the stored
   pointer stay additive-safe.  The address-expression world rule
   (D4b): values escape in the world their position names. *)
let def_window_value_slot : (Theory.Value.cls, bool) KB.slot =
  KB.Class.property ~package:"hike" Theory.Value.cls "hike-window-value"
    (KB.Domain.flat
       ~inspect:(fun b -> Base.Sexp.Atom (string_of_bool b))
       ~equal:Bool.equal ~empty:false "hike:window-value")

let def_is_window_value (d : def term) : bool =
  KB.Value.get def_window_value_slot (Def.value d)

let stamp_window_values ~(window_values : Tid.Set.t)
    (sub : sub term) : sub term =
  Term.map blk_t sub ~f:(fun blk ->
      Term.map def_t blk ~f:(fun d ->
          if Core.Set.mem window_values (Term.tid d) then
            Def.with_value d
              (KB.Value.put def_window_value_slot (Def.value d) true)
          else d))

(* Stamps the dynamic-allocation fact onto the event defs (the def's
   own slot — it is not a range classification). *)
let stamp_dyn_allocs ~(dynamic_alloc_tids : Tid.Set.t)
    (sub : sub term) : sub term =
  Term.map blk_t sub ~f:(fun blk ->
      Term.map def_t blk ~f:(fun d ->
          if Core.Set.mem dynamic_alloc_tids (Term.tid d) then
            Def.with_value d
              (KB.Value.put def_dyn_alloc_slot (Def.value d) true)
          else d))

(* The slim section tag rides the def's VALUE (the def_kind_slot
   pattern): the producer stamps it; the emitter's dispatch reads it
   off the term. *)

type KB.conflict += Sec_tag_conflict

let () =
  KB.Conflict.register_printer (function
    | Sec_tag_conflict ->
        Some
          "hike: section-tag conflict: two different attributions were stamped for one def"
    | _ -> None)

let sec_tag_domain : sec_tag option KB.Domain.t =
  KB.Domain.optional
    ~inspect:(fun _ -> Base.Sexp.Atom "hike:section-tag")
    ~join:(fun a b -> if Tag.equal a b then Ok a else Error Sec_tag_conflict)
    ~equal:Tag.equal "hike:section-tag"

let sec_tag_slot : (Theory.Value.cls, sec_tag option) KB.slot =
  KB.Class.property ~package:"hike" Theory.Value.cls "hike-section-tag"
    sec_tag_domain

let sec_tag (d : def term) : sec_tag option =
  KB.Value.get sec_tag_slot (Def.value d)

let set_sec_tag (t : sec_tag) (d : def term) : def term =
  Def.with_value d (KB.Value.put sec_tag_slot (Def.value d) (Some t))
