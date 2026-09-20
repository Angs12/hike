
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
open Bap_core_theory
module Abi = Hike_abi

(* Only [Abi.sp] carries stack semantics; any other register's stack-ness is
   proven by the VSA, never by name. *)

(* The producer builds this record; the model and the emitter consume it. *)
module Vsa = struct
  open Core

  (* The ABSOLUTE position of the entry RSP on the segment line (the seeded
     SP is base + offset 0); a frame-relative depth is [base − position]. *)
  let segment_base = Cbat_vsa.WordSet.stack_base


let i64_opt (w : Cbat_word.t) : int64 option =
    match Cbat_word.to_int64 w with Ok v -> Some v | Error _ -> None

  let position_pair (lo : Cbat_word.t) (hi : Cbat_word.t)
      : (int64 * int64) option =
    let open Base.Option in
    i64_opt lo >>= fun lo ->
    i64_opt hi >>= fun hi ->
    Cbat_vsa.Cbat_extraction.position_of_offset lo >>= fun lo ->
    Cbat_vsa.Cbat_extraction.position_of_offset hi >>= fun hi ->
    Some (lo, hi)

  let singleton_pair (lo : Cbat_word.t option) (hi : Cbat_word.t option)
      : int64 option =
    match lo, hi with
    | Some lo, Some hi when Cbat_word.equal lo hi -> i64_opt lo
    | _ -> None

  let stack_floor ~(entry : int64) : int64 = Stdlib.Int64.add entry Stdlib.Int64.min_int
  let args_ceiling : int64 = Stdlib.Int64.max_int

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

  (* A stack-symbolic set's offset extrema on the position line. *)
  let positions_of_offsets (ws : Cbat_vsa.WordSet.t) : (int64 * int64) option =
    Option.bind (Cbat_vsa.WordSet.offset_extrema ws) ~f:(fun (lo, hi) ->
        position_pair lo hi)

  (* A plain set's unsigned extrema; None when not representable. *)
  let unsigned_bounds (ws : Cbat_vsa.WordSet.t) : (int64 * int64) option =
    let open Base.Option in
    Cbat_vsa.WordSet.min_elem ws >>= fun lo ->
    Cbat_vsa.WordSet.max_elem ws >>= fun hi ->
    i64_opt lo >>= fun lo ->
    i64_opt hi >>= fun hi ->
    Some (lo, hi)

  (* An unbounded direction extends to the scope bound; a wrapped or circular
     hull covers the whole scope. *)
  let full_bounds (ws : Cbat_vsa.WordSet.t) ~(flo : int64) ~(cei : int64)
      (lo : int64) (hi : int64) : int64 * int64 =
    if Stdlib.Int64.compare lo hi > 0 then (flo, cei)
    else if Cbat_vsa.WordSet.is_ascending ws then (lo, cei)
    else if Cbat_vsa.WordSet.is_descending ws then (flo, hi)
    else (flo, cei)

  (* The Clp offset hull on the segment line; [None] when not representable. *)
  let hull_positions (offs : Cbat_vsa.WordSet.Clp.t) : (int64 * int64) option =
    let open Base.Option in
    Cbat_vsa.WordSet.Clp.min_elem offs >>= fun lo ->
    Cbat_vsa.WordSet.Clp.max_elem offs >>= position_pair lo

  (* A stack-symbolic value's escape extent: its positions, with the
     unbounded directions reaching the scope bound. *)
  let escape_extent ~(entry : int64) (ws : Cbat_vsa.WordSet.t)
      : (int64 * int64) option =
    match Cbat_vsa.WordSet.stack_offsets ws with
    | None -> None
    | Some _ -> (
        let floor = stack_floor ~entry in
        match positions_of_offsets ws with
        | None -> Some (floor, args_ceiling)
        | Some (lo, hi) ->
            if Cbat_vsa.WordSet.is_infinite ws || Stdlib.Int64.compare lo hi > 0 then
              Some (full_bounds ws ~flo:floor ~cei:args_ceiling lo hi)
            else Some (lo, hi))

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

let region_name (id : int) : string = Printf.sprintf "stack_r%d" id

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
   native base is a compile-time constant, so the address delta is inline
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

(* The window extension's capacity; a real SysV window never needs more. *)
let caller_window_bytes : int64 = 65536L

(* The directionless stack top's below-entry clamp: a TOP stack offset
   claims [entry − stack_max, entry). *)
let stack_max : int64 = 65536L

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


(* Per-def tags ride the def's value: the producer stamps each def, the
   emitter reads the tags off the term. *)

module KB = Bap_knowledge.Knowledge

(* The def is a runtime-sized SP decrement and emits a real runtime-sized
   alloca; the storage fact rides the def's value beside the kind. *)
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

(* The def computes an address value at/above the entry line; its emitted
   integer re-bases to the hike_window parameter. *)
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

(* Stamps the dynamic-allocation fact onto the event defs. *)
let stamp_dyn_allocs ~(dynamic_alloc_tids : Tid.Set.t)
    (sub : sub term) : sub term =
  Term.map blk_t sub ~f:(fun blk ->
      Term.map def_t blk ~f:(fun d ->
          if Core.Set.mem dynamic_alloc_tids (Term.tid d) then
            Def.with_value d
              (KB.Value.put def_dyn_alloc_slot (Def.value d) true)
          else d))

(* The section tag rides the def's value: the producer stamps it, the
   emitter's dispatch reads it off the term. *)

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
