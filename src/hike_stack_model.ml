
(* A range carries its section, so merging across sections is impossible. *)
module Vocab = struct
  open! Core

  type sec = Stack | Args | Text | Rodata | Data | Got | Gotplt | Datarelro | Bss
  [@@deriving equal, compare, sexp]

  (* The def-carried classification: a section with its ADDRESS bounds, the
     justified unbounded form, or Dead.  Absence is the identity.  In [Tag]
     so the [sec] constructors stay unshadowed. *)
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

(* The pure stack model: the VSA tags every frame-resident access with its
   proven offset span; this module merges overlapping spans into regions
   from those tags alone.  An oversized region joins to Frame with a
   diagnostic naming it. *)

open Bap.Std
open Bap.Std.Bil.Types
module Abi = Hike_abi

(* Only [Abi.sp] carries stack semantics; any other register's stack-ness is
   proven by the VSA, never by name. *)

(* The producer builds this record; the model and the emitter consume it. *)
module Vsa = struct
  open Core

  (* The ABSOLUTE position of the entry RSP on the segment line (the seeded
     SP is base + offset 0); a frame-relative depth is [base − position]. *)
  let segment_base = Cbat_vsa.WordSet.stack_base

  (* The base's certified width and the stack band's lower bound: the
     base's low nibble is a fact, and a bounded plain set in
     [stack_band_lo, 2^63) is stack. *)
  let certified_bits = Cbat_vsa.WordSet.certified_bits
  let stack_band_lo = Cbat_vsa.WordSet.stack_band_lo

  (* The clamp and its bounds are shared with the call abstraction. *)
  include Hike_stack_bounds

  let singleton_pair (lo : Cbat_word.t option) (hi : Cbat_word.t option)
      : int64 option =
    match lo, hi with
    | Some lo, Some hi when Cbat_word.equal lo hi -> i64_opt lo
    | _ -> None

  let args_base ~(entry : int64) ~(word : int) : int64 =
    Stdlib.Int64.add entry (Stdlib.Int64.of_int word)

  let stack_top ~(entry : int64) ~(word : int) : int64 =
    Stdlib.Int64.pred (args_base ~entry ~word)

  (* [hi + n - 1] in signed arithmetic, saturating at the ceiling — a
     wrapped short interval would be unsound. *)
  let expand_hi ~(cap : int64) (hi : int64) (n : int) : int64 =
    let w = Stdlib.Int64.of_int (n - 1) in
    let r = Stdlib.Int64.add hi w in
    if Stdlib.Int64.compare r hi < 0 || Stdlib.Int64.compare r cap > 0 then cap else r

  (* [hi + n - 1] in unsigned arithmetic; wrapping saturates at the top. *)
  let expand_hi_unsigned (hi : int64) (n : int) : int64 =
    let w = Stdlib.Int64.of_int (n - 1) in
    let r = Stdlib.Int64.add hi w in
    if Stdlib.Int64.unsigned_compare r hi < 0 then -1L else r

  (* The intersection of [lo, hi] (ordered by [cmp]) with [slo, shi]. *)
  let clip ~(cmp : int64 -> int64 -> int) (lo : int64) (hi : int64)
      (slo : int64) (shi : int64) : (int64 * int64) option =
    let lo = if cmp lo slo >= 0 then lo else slo in
    let hi = if cmp hi shi <= 0 then hi else shi in
    if cmp lo hi <= 0 then Some (lo, hi) else None

  (* The Clp offset hull on the segment line; [None] when not representable. *)
  let hull_positions (offs : Cbat_vsa.WordSet.Clp.t) : (int64 * int64) option =
    let open Base.Option in
    Cbat_vsa.WordSet.Clp.min_elem offs >>= fun lo ->
    Cbat_vsa.WordSet.Clp.max_elem offs >>= position_pair lo

  (* A single known word; a TOP set is deliberately not one. *)
  let singleton_i64 (ws : Cbat_vsa.WordSet.t) : int64 option =
    if Cbat_vsa.WordSet.is_top ws then None
    else singleton_pair (Cbat_vsa.WordSet.min_elem ws) (Cbat_vsa.WordSet.max_elem ws)

  let singleton_offset (offs : Cbat_vsa.WordSet.Clp.t) : int64 option =
    singleton_pair
      (Cbat_vsa.WordSet.Clp.min_elem offs)
      (Cbat_vsa.WordSet.Clp.max_elem offs)

  (* The denotation's single stack position (absolute), when it has
     exactly one. *)
  let singleton_stack_position (ws : Cbat_vsa.WordSet.t) : int64 option =
    let open Base.Option in
    Cbat_vsa.WordSet.stack_offsets ws >>= singleton_offset
    >>= Cbat_vsa.Cbat_extraction.position_of_offset

  (* The return-address fact and its projections: an address that denotes to
     the stack-symbolic singleton at the entry-RSP cell. *)
  let is_return_address (ws : Cbat_vsa.WordSet.t) : bool =
    match singleton_stack_position ws with
    | Some p -> Int64.equal p segment_base
    | None -> false

  (* The same denotation, read off the def's section tag. *)
  let is_return_address_tag (t : sec_tag) : bool =
    match t with
    | Tag.Stack (lo, hi) ->
        Int64.equal lo segment_base && Int64.equal hi segment_base
    | _ -> false

  (* The shape-only projection [mem[SP]], for the consumer that runs before
     any solution exists. *)
  let is_return_address_shape ~(abi : Abi.t) (addr : exp) : bool =
    match addr with
    | Bil.Var v -> Var.same (Var.base v) abi.Hike_abi.sp
    | _ -> false

end
include Vsa



(* A def keeps exactly one inline mem node, so one scan serves every
   consumer. *)
type mem_node =
  [ `Load of exp * exp * Size.t      (* mem, address, width *)
  | `Store of exp * exp * exp * Size.t ]  (* mem, address, data, width *)

let mem_nodes (e : exp) : mem_node list =
  let vis =
    object
      inherit [ mem_node list ] Exp.visitor as super
      method! visit_load ~mem ~addr rest s acc =
        super#visit_load ~mem ~addr rest s (`Load (mem, addr, s) :: acc)
      method! visit_store ~mem ~addr ~exp rest s acc =
        super#visit_store ~mem ~addr ~exp rest s (`Store (mem, addr, exp, s) :: acc)
    end
  in
  List.rev (vis#visit_exp e [])

let mem_node_of (e : exp) : mem_node option =
  match mem_nodes e with n :: _ -> Some n | [] -> None

(* The first node whose mem var satisfies [pred]. *)
let mem_node_where (pred : var -> bool) (e : exp) : mem_node option =
  Base.List.find_map (mem_nodes e) ~f:(fun n ->
      match n with
      | `Load (Bil.Var v, _, _) when pred v -> Some n
      | `Store (Bil.Var v, _, _, _) when pred v -> Some n
      | _ -> None)

let mem_node_count (e : exp) : int = List.length (mem_nodes e)

let reads_mem (e : exp) : bool =
  match mem_node_of e with Some _ -> true | None -> false

(* Free vars of every Load mem in one rhs. *)
let load_mem_vars (rhs : exp) : Var.Set.t =
  Base.List.fold (mem_nodes rhs) ~init:Var.Set.empty
    ~f:(fun (acc : Var.Set.t) n ->
      match n with
      | `Load (mem, _, _) -> Core.Set.union acc (Exp.free_vars mem)
      | _ -> acc)

let addr_of_rhs (e : exp) : (exp * Size.t) option =
  match mem_node_of e with
  | Some (`Load (_, a, s)) | Some (`Store (_, a, _, s)) -> Some (a, s)
  | _ -> None

(* Splits a store rhs into data and cast wrapper using visitor/mapper. *)
let store_data_of_rhs (e : exp) : (exp * (exp -> exp)) option =
  let vis =
    object
      inherit [ exp option ] Exp.visitor
      method! visit_store ~mem:_ ~addr:_ ~exp:data _ _ acc =
        Base.Option.first_some acc (Some data)
    end
  in
  Base.Option.map (vis#visit_exp e None) ~f:(fun data ->
      let wrap x =
        let mapper =
          object
            inherit Exp.mapper
            method! map_store ~mem:_ ~addr:_ ~exp:_ _ _ = x
          end
        in
        mapper#map_exp e
      in
      (data, wrap))

let word_bits (word : int) : int = 8 * word

let is_true_cond (e : exp) : bool =
  match e with Bil.Int w -> Word.equal w (Word.one 1) | _ -> false

(* The producer/emitter signature contract: which subs keep their
   pre-promotion signature — emittable intrinsics and @main. *)
let is_intrinsic (term : sub term) : bool =
  Term.has_attr term Sub.intrinsic

let is_emittable_intrinsic (term : sub term) : bool =
  is_intrinsic term && not (Seq.is_empty (Term.enum blk_t term))

let is_intrinsic_name (s : string) : bool =
  Base.String.is_prefix s ~prefix:"intrinsic:"

let fixed_signature (term : sub term) : bool =
  is_emittable_intrinsic term
  || String.equal (Tid.name (Term.tid term)) "@main"

(* The promoted stack-slot parameter of index [i]; minted deterministically
   so the signature and the body agree on the same var. *)
let arg_slot ~(word : int) (i : int) : var =
  Var.create ~is_virtual:false ~fresh:false
    (Printf.sprintf "hike_slot%d" i)
    (Type.Imm (word_bits word))

(* The call-argument temp of slot [i]; deterministically minted like the
   slots. *)
let call_arg ~(word : int) (i : int) : var =
  Var.create ~is_virtual:false ~fresh:false
    (Printf.sprintf "hike_arg%d" i)
    (Type.Imm (word_bits word))

(* The call-argument temps survive DCE: they are the call's arguments. *)
let is_call_arg (v : var) : bool =
  Base.String.is_prefix (Var.name v) ~prefix:"hike_arg"

let is_arg_slot (v : var) : bool =
  Base.String.is_prefix (Var.name v) ~prefix:"hike_slot"

(* The incoming-window memory var: a callee's above-entry accesses are
   materialized against the caller's window through it. *)
let window_mem : var =
  Var.create ~is_virtual:false ~fresh:false "hike_window_mem"
    (mem64_t (Size.of_int_exn 8))

let is_window_mem (v : var) : bool =
  String.equal (Var.name v) "hike_window_mem"

(* The caller-window base parameter (not SP); the model mints the whole var
   grammar — window, slots, regions — here. *)
let hike_window_var ~(word : int) : var =
  Var.create ~is_virtual:false ~fresh:false "hike_window"
    (Type.Imm (word_bits word))

let is_window_var (v : var) : bool =
  String.equal (Var.name v) "hike_window"

let region_name (id : int) : string = Printf.sprintf "stack_r%d" id

(* The residue is region id 0: the fallback alloca every un-carved
   stack access shares. *)
let residue_id : int = 0

(* Slot geometry: with [entry] the call-time post-push SP (the callee's
   entry line), slot [i] occupies [entry + word + word*i, +word) — the
   return address occupies [entry, entry + word). *)
let slot_offset ~(word : int) (i : int) : int64 =
  Stdlib.Int64.of_int (word * (i + 1))

let slot_index_of_offset ~(word : int) (rel : int64) : int =
  Stdlib.Int64.to_int
    (Stdlib.Int64.div (Stdlib.Int64.sub rel (Stdlib.Int64.of_int word))
       (Stdlib.Int64.of_int word))

let region_mem (id : int) : var =
  Var.create ~is_virtual:false ~fresh:false
    (region_name id ^ "_mem")
    (mem64_t (Size.of_int_exn 8))


let is_mem var = match Var.typ var with Mem _ -> true | _ -> false

let is_region_mem (v : var) : bool =
  Base.String.is_prefix (Var.name v) ~prefix:"stack_r"
  && Base.String.is_suffix (Var.name v) ~suffix:"_mem"

(* The section partition: each reserved span's components are carried in the
   mem var [sec_comp_N_mem] and the emitter routes by name.  A section's
   arithmetic. *)

(* One emitted component: a word range of the section keyed by its native
   span, plus the typed-emission decision. *)
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

(* The gap runs continue the same numbering; they emit globals but carry no
   BIL var. *)
let sec_res_name (n : int) : string = Printf.sprintf "sec_res_%d" n

let is_sec_comp_mem (v : var) : bool =
  Base.String.is_prefix (Var.name v) ~prefix:"sec_comp_"
  && Base.String.is_suffix (Var.name v) ~suffix:"_mem"

(* The tid-name sanitization the symbol-table lookups and the emitted
   names share: a sub's symtab name and its LLVM name stay comparable. *)
let sanitize_tid_name (n : string) : string =
  Base.String.filter n ~f:(fun c ->
      match c with '#' | '.' | '%' | '\\' | '@' -> false | _ -> true)

(* The vars a block reads: its jumps' and phis' free vars. *)
let blk_reads (b : blk term) : Var.Set.t =
  Term.enum jmp_t b
  |> Seq.fold ~init:Var.Set.empty ~f:(fun acc j ->
         Core.Set.union acc (Jmp.free_vars j))
  |> fun acc ->
  Term.enum phi_t b
  |> Seq.fold ~init:acc ~f:(fun acc p -> Core.Set.union acc (Phi.free_vars p))

(* The sub's free register lanes: its free vars minus the memory vars. *)
let free_regs (sub : sub term) : var list =
  Sub.free_vars sub
  |> Core.Set.filter ~f:(fun var -> not @@ is_mem var)
  |> Core.Set.to_list

(* The vars a sub reads: every def's rhs plus each block's reads. *)
let sub_reads (s : sub term) : Var.Set.t =
  Term.enum blk_t s
  |> Seq.fold ~init:Var.Set.empty ~f:(fun acc blk ->
      let acc =
        Term.enum def_t blk
        |> Seq.fold ~init:acc ~f:(fun acc d ->
            Core.Set.union acc (Exp.free_vars (Def.rhs d)))
      in
      Core.Set.union acc (blk_reads blk))

(* A word is string text iff a printable run crosses its start boundary —
   printable back to the last NUL (or the array start); a NUL directly
   before it means the run starts at the word and it renders as a value. *)
let string_text_word ~(arr : Bytes.t) ~(off : int) : bool =
  let byte i = Char.code (Bytes.get arr i) in
  let printable b = b >= 0x20 && b <= 0x7e in
  let rec crosses i =
    if i < 0 then true
    else if byte i = 0 then i < off - 1
    else if printable (byte i) then crosses (i - 1)
    else false
  in
  off > 0 && off < Bytes.length arr && printable (byte off) && crosses (off - 1)

(* The deepest literal SP decrement in the sub (prologues and VLAs). *)
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

(* A machine call pushes its return address one word below the caller's SP;
   a modeled op (an intrinsic rendered inline) pushes nothing. *)
let is_intrinsic_target (t : tid) : bool =
  Base.String.is_prefix (Tid.name t) ~prefix:"intrinsic:"

let machine_call (j : jmp term) : bool =
  match Jmp.kind j with
  | Call c -> (
      match Call.target c with
      | Direct t -> not (is_intrinsic_target t)
      | Indirect _ -> true)
  | _ -> false

let call_pushes (j : jmp term) : bool =
  match Jmp.kind j with
  | Call c -> machine_call j && Option.is_some (Call.return c)
  | _ -> false

let has_call_push (sub : sub term) : bool =
  Term.enum blk_t sub
  |> Seq.exists ~f:(fun blk ->
         Term.enum jmp_t blk |> Seq.exists ~f:call_pushes)

(* The emitter's per-sub inputs are structure (BIR args, direct targets,
   def tags) plus this layout fact: the alloca-construction inputs alone. *)

module Sub_layout = struct
  open Core

  (* [regions] is every alloca of the sub — the carved regions plus the
     stack residue (id 0, whose extent contains the anchor and the caller
     window).  [anchor] is the entry RSP's runtime position (region id, byte
     index inside that alloca), so every model address resolves against one
     base. *)
  type t = {
    regions : (int * (int64 * int64) * int64) list;
    anchor : (int * int64) option;
    (* The sub reads its incoming window: its direct-call signature carries
       the hike_window parameter. *)
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

  (* Required by [Value.Tag.register]. *)
  let pp fmt { regions; anchor; window_param } =
    Format.fprintf fmt "regions=%d;anchor=%s;window=%b"
      (Base.List.length regions)
      (Base.Option.value_map anchor ~default:"none"
         ~f:(fun (i, idx) -> Printf.sprintf "r%d@%Ld" i idx))
      window_param

  let sexp_of_t (t : t) : Sexp.t =
    Sexp.List
      (Base.List.map t.regions ~f:(fun (id, (lo, hi), b) ->
           Sexp.Atom (Printf.sprintf "%d:%Ld:%Ld:%Ld" id lo hi b))
       @ (Base.Option.value_map t.anchor ~default:[]
            ~f:(fun (i, idx) ->
              [ Sexp.Atom (Printf.sprintf "anchor=%d:%Ld" i idx) ]))
       @ if t.window_param then [ Sexp.Atom "window" ] else [])

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

type sub_layout = Sub_layout.t = {
  regions : (int * (int64 * int64) * int64) list;
  anchor : (int * int64) option;
  window_param : bool;
}



(* The layout rides the sub term: the producer computes it once, the emitter
   reads it off the term. *)
let layout_tag : Sub_layout.t Value.Tag.t =
  Value.Tag.register ~package:"hike" ~name:"hike-layout"
    ~uuid:"3f5e1c2a-9b47-4d60-8a15-c4d9e07b2f11"
    (module Sub_layout)

let set_layout (l : Sub_layout.t) (sub : sub term) : sub term =
  Term.set_attr sub layout_tag l

(* The emission signature rides the sub's own [arg] terms: the returns are
   the [Out] intents, the arguments the rest.  One place holds it, and the
   emitter reads it off the sub — no side table. *)
let set_sig (s : sub term) (lanes : Arg.t list) : sub term =
  let s = Term.filter arg_t s ~f:(Fun.const false) in
  Base.List.fold lanes ~init:s ~f:(fun s a -> Term.append arg_t s a)

let is_ret (a : Arg.t) : bool = Arg.intent a = Some Out

let sig_args (s : sub term) : Arg.t list =
  Term.enum arg_t s |> Base.Sequence.to_list
  |> Base.List.filter ~f:(fun a -> not (is_ret a))

let sig_rets (s : sub term) : Arg.t list =
  Term.enum arg_t s |> Base.Sequence.to_list |> Base.List.filter ~f:is_ret

(* The pass is the home of each lane's TYPE: a lane is a pointer (an
   address lane, a by-reference argument, the caller window) or it keeps
   its BIR type.  Stamped on the [arg] term. *)
module Flag = struct
  open Core

  type t = bool [@@deriving compare, equal, sexp]

  let pp fmt b = Format.pp_print_bool fmt b

  module Stringable = struct
    type nonrec t = t

    let to_string = function true -> "true" | false -> "false"
    let of_string = function "true" -> true | _ -> false
  end

  include Core.Binable.Of_stringable_with_uuid (struct
    include Stringable

    let caller_identity =
      Bin_prot.Shape.Uuid.of_string "hike:hike_stack_model.Flag/1"
  end)
end

let arg_ptr_tag : Flag.t Value.Tag.t =
  Value.Tag.register ~package:"hike" ~name:"hike-arg-ptr"
    ~uuid:"7c1d2e3f-0a11-4b22-9c33-44d55e66f704"
    (module Flag)

let is_ptr_arg (a : Arg.t) : bool =
  Base.Option.value (Term.get_attr a arg_ptr_tag) ~default:false

let set_ptr_arg (a : Arg.t) : Arg.t = Term.set_attr a arg_ptr_tag true
