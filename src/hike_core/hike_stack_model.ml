(* The section vocabulary, denotation predicates, and the shared
   stack/var/layout contracts used by the attribution and emitter. *)
module Vocab = struct
  open! Core

  type sec = Hike_section.t =
    | Stack | Args | Text | Rodata | Data | Got | Gotplt | Datarelro | Bss
  [@@deriving equal, compare, sexp]

  let sec_name = Hike_section.name

  (* The def-carried classification: the occupied extent or the
     justified unbounded form.  The RUNTIME ORIGIN is not here — it
     rides the def's origin slot (one carrier); the band rules that
     consumed the kind read the denotation's origin instead.  Absence
     is the identity.  In [Tag] so the [sec] constructors stay
     unshadowed. *)
  module Tag = struct
  type t =
    | Range of int64 * int64
    | Unbounded
  [@@deriving equal, compare, sexp]
  end

  type sec_tag = Tag.t
end

include Vocab

(* One data section's row — the fixed-table facts every consumer (the
   attribution's spans and the emitter's section build) reads.
   [sm_image] is None for the bss region (zeroed, copy-relocated). *)
type sec_meta = {
  sm_type : sec;
  sm_access : Hike_section.access;
  sm_lo : int64;
  sm_hi : int64;
  sm_words : int;
  sm_image : Bytes.t option;
  sm_copy_relocs : (int * string) list;
}

(* The stack-position predicates and frame arithmetic shared by the
   attribution, promotion, and emitter. *)

open Bap.Std
open Bap.Std.Bil.Types
module Abi = Hike_abi

(* Only [Abi.sp] carries stack semantics; any other register's stack-ness is
   proven by the VSA, never by name. *)

module Frame = struct
  open Core

  (* The ABSOLUTE position of the entry RSP on the segment line (the seeded
     SP is base + offset 0); a frame-relative depth is [base − position]. *)
  let segment_base = Cbat_clp_set_composite.stack_base

  (* The clamp and its bounds are shared with the call abstraction. *)
  include Hike_stack_bounds

  let singleton_pair (lo : Cbat_word.t option) (hi : Cbat_word.t option)
      : int64 option =
    match lo, hi with
    | Some lo, Some hi when Cbat_word.equal lo hi -> Cbat_word.to_int64_opt lo
    | _ -> None

  let args_base ~(entry : int64) ~(word : int) : int64 =
    Stdlib.Int64.add entry (Stdlib.Int64.of_int word)

  let stack_top ~(entry : int64) ~(word : int) : int64 =
    Stdlib.Int64.pred (args_base ~entry ~word)

  (* The caller-window denotation: a stack-symbolic set whose positions
     are ordered and entirely at/above the args base — an address in the
     caller's frame.  The ONE rule the promotion's window stamp and the
     pointer-kind storage read. *)
  let is_window_denotation ~(entry : int64) ~(word : int)
      (ws : Cbat_clp_set_composite.t) : bool =
    match Cbat_clp_set_composite.stack_offsets ws with
    | None -> false
    | Some _ -> (
        match positions_of_offsets ws with
        | Some (lo, hi) ->
            let a_base = args_base ~entry ~word in
            Stdlib.Int64.compare lo a_base >= 0
            && Stdlib.Int64.compare hi a_base >= 0
            && Stdlib.Int64.compare lo hi <= 0
        | None -> false)

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

  (* A single known word; a TOP set is deliberately not one. *)
  let singleton_i64 (ws : Cbat_clp_set_composite.t) : int64 option =
    if Cbat_clp_set_composite.is_top ws then None
    else singleton_pair (Cbat_clp_set_composite.min_elem ws) (Cbat_clp_set_composite.max_elem ws)

  let singleton_offset (offs : Cbat_clp_set_composite.Clp.Pieces.t) : int64 option =
    singleton_pair
      (Cbat_clp_set_composite.Clp.Pieces.min_elem offs)
      (Cbat_clp_set_composite.Clp.Pieces.max_elem offs)

  (* The denotation's single position on its stack-origin line. *)
  let singleton_stack_position (ws : Cbat_clp_set_composite.t) : int64 option =
    match Cbat_clp_set_composite.stack_offsets ws with
    | Some _ -> (
        match positions_of_offsets ws with
        | Some (lo, hi) when Int64.equal lo hi -> Some lo
        | _ -> None)
    | None -> None

  (* The return-address fact and its projections: an address that denotes to
     the stack-symbolic singleton at the entry-RSP cell. *)
  let is_return_address (ws : Cbat_clp_set_composite.t) : bool =
    match singleton_stack_position ws with
    | Some p -> Int64.equal p segment_base
    | None -> false

  (* The same denotation, read off the def's section tag. *)
  let is_return_address_tag (t : sec_tag) : bool =
    match t with
    | Tag.Range (lo, hi) ->
        Int64.equal lo segment_base && Int64.equal hi segment_base
    | _ -> false

end
include Frame

(* The storage a ptr-kind value lives in: a region or residue alloca of
   this sub, or the caller frame base (the window). *)
type ptr_storage =
  | Ptr_region of int
  | Ptr_residue
  | Ptr_window

let equal_ptr_storage (a : ptr_storage) (b : ptr_storage) : bool =
  match a, b with
  | Ptr_region x, Ptr_region y -> Int.equal x y
  | Ptr_residue, Ptr_residue | Ptr_window, Ptr_window -> true
  | _ -> false

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

let mem_node_count (e : exp) : int = List.length (mem_nodes e)

let reads_mem (e : exp) : bool = Option.is_some (mem_node_of e)

(* The address and size of the rhs's memory access, if it has one. *)
let addr_of_rhs (e : exp) : (exp * Size.t) option =
  match mem_node_of e with
  | Some (`Load (_, a, s)) | Some (`Store (_, a, _, s)) -> Some (a, s)
  | _ -> None

(* The store's data expression, if the rhs holds a store. *)
let store_data_of_rhs (e : exp) : exp option =
  let vis =
    object
      inherit [ exp option ] Exp.visitor
      method! visit_store ~mem:_ ~addr:_ ~exp:data _ _ acc =
        Base.Option.first_some acc (Some data)
    end
  in
  vis#visit_exp e None

let word_bits (word : int) : int = 8 * word

let is_true_cond (e : exp) : bool =
  match e with Bil.Int w -> Word.equal w (Word.one 1) | _ -> false

(* The one thread-pointer offset rule: whether an address expression
   is the thread pointer plus a byte offset.  The fold is an affine
   analysis in the pointer: [Tp_based (Some o)] — pointer plus the
   constant [o]; [Tp_based None] — pointer plus a dynamic (pointer-free)
   offset; [Tp_nonlinear] — the expression reads the pointer but is not
   pointer-plus-offset (a cast that changes the pointer's width, or a
   non-unit coefficient); [Tp_absent] — the pointer never occurs (a
   bare constant is a summand, never a base). *)
type tp_offset = Tp_absent | Tp_based of int64 option | Tp_nonlinear

(* The affine coefficient of the thread pointer. *)
type tp_coeff = Tp_zero | Tp_one | Tp_non

let tp_is_zero = function Tp_zero -> true | Tp_one | Tp_non -> false

let tp_add_coeff a b =
  match (a, b) with
  | Tp_zero, x | x, Tp_zero -> x
  | Tp_non, _ | _, Tp_non -> Tp_non
  | Tp_one, Tp_one -> Tp_non

let tp_sub_coeff a b =
  match (a, b) with
  | x, Tp_zero -> x
  | Tp_non, _ | _, Tp_non -> Tp_non
  | Tp_one, Tp_one -> Tp_zero
  | Tp_zero, Tp_one -> Tp_non

let tp_bits_of (v : var) : int =
  match Var.typ v with
  | Type.Imm n -> n
  | _ -> invalid_arg "tls_tp_offset: thread pointer is not an immediate"

let tls_tp_offset ~(tp : var) (e : exp) : tp_offset =
  let tp_bits = tp_bits_of tp in
  let rec fold = function
    | Bil.Int w -> (Tp_zero, Some w)
    | Bil.Var v ->
      if Var.same v tp then (Tp_one, Some (Word.zero tp_bits))
      else (Tp_zero, None)
    | Bil.BinOp (op, a, b) ->
      let ca, va = fold a and cb, vb = fold b in
      let coeff = match op with
        | Bil.PLUS -> tp_add_coeff ca cb
        | Bil.MINUS -> tp_sub_coeff ca cb
        | _ -> if tp_is_zero ca && tp_is_zero cb then Tp_zero else Tp_non in
      coeff, Base.Option.map2 va vb ~f:(Bil.Apply.binop op)
    | Bil.Cast (cast, bits, e) ->
      let c, v = fold e in
      if tp_is_zero c then c, Base.Option.map v ~f:(Bil.Apply.cast cast bits)
      else if bits = tp_bits then c, v
      else Tp_non, None
    | Bil.UnOp (op, e) ->
      let c, v = fold e in
      if tp_is_zero c then c, Base.Option.map v ~f:(Bil.Apply.unop op)
      else Tp_non, None
    | Bil.Concat (a, b) ->
      let ca, va = fold a and cb, vb = fold b in
      if tp_is_zero ca && tp_is_zero cb then
        Tp_zero, Base.Option.map2 va vb ~f:Word.concat
      else Tp_non, None
    | Bil.Extract (hi, lo, e) ->
      let c, v = fold e in
      if tp_is_zero c then c, Base.Option.map v ~f:(Word.extract_exn ~hi ~lo)
      else Tp_non, None
    | e ->
      let reads_tp = (object inherit [bool] Exp.visitor
          method! visit_var v found = found || Var.same v tp
        end)#visit_exp e false in
      (if reads_tp then Tp_non else Tp_zero), None in
  match fold e with
  | Tp_non, _ -> Tp_nonlinear
  | Tp_zero, _ -> Tp_absent
  | Tp_one, v ->
    Tp_based (Base.Option.bind v ~f:(fun w ->
        match Word.to_int64 w with Ok off -> Some off | Error _ -> None))

(* The producer/emitter signature contract: which subs keep their
   pre-promotion signature — emittable intrinsics and @main. *)
let is_intrinsic (term : sub term) : bool =
  Term.has_attr term Sub.intrinsic

let is_emittable_intrinsic (term : sub term) : bool =
  is_intrinsic term && not (Seq.is_empty (Term.enum blk_t term))

(* The program's main: stamped by the producer (the address the entry
   passes to the runtime) and exported with the C ABI, so the native
   crt1 calls it directly. *)
let main_role : unit Value.Tag.t =
  Value.Tag.register ~package:"hike" ~name:"hike-main-role"
    ~uuid:"7d3a9c41-2e58-4b0f-9a6d-1c8f5b2e7a10"
    (module Core.Unit)

let fixed_signature (term : sub term) : bool =
  is_emittable_intrinsic term || Term.has_attr term main_role

(* The promoted slot's POINTER: the caller's slot cell, addressed.  The
   parameter IS the address, so a slot access is a real load/store
   through the caller's own storage. *)
let arg_slot ~addr_bits i = Hike_synth.base ~addr_bits (Hike_synth.Slot i)

(* The call-argument temp of slot [i]: the ADDRESS of the caller's slot
   cell (the store the call site made), deterministically minted like
   the slots. *)
let call_arg ~addr_bits i = Hike_synth.base ~addr_bits (Hike_synth.Argument i)

(* The call-argument temps are the call's arguments. *)
let is_call_arg synth v =
  match Hike_synth.classify synth v with
  | Some (Hike_synth.Storage (Hike_synth.Argument _)) -> true
  | _ -> false

(* The FP model's operand temp: [intrinsic:x<N>], width-qualified by the
   fp pass ([intrinsic:x<N>:<width>]); an FP call site's argument.  The
   base name carries no SSA version. *)
let is_fp_operand_temp synth v =
  match Hike_synth.classify synth v with
  | Some (Hike_synth.Fp_lane (Hike_synth.Input, _)) -> true
  | _ -> false

let is_arg_slot synth v =
  match Hike_synth.classify synth v with
  | Some (Hike_synth.Storage (Hike_synth.Slot _)) -> true
  | _ -> false

(* The fission mem vars' type: byte cells addressed at the target's
   address width. *)
let window_mem ~addr_bits = Hike_synth.bytes ~addr_bits Hike_synth.Window

let is_window_mem synth v =
  match Hike_synth.classify synth v with
  | Some (Hike_synth.Bytes Hike_synth.Window) -> true
  | _ -> false

(* The caller-window base parameter. *)
let hike_window_var ~word =
  Hike_synth.base ~addr_bits:(word_bits word) Hike_synth.Window

let is_window_var synth v =
  match Hike_synth.classify synth v with
  | Some (Hike_synth.Storage Hike_synth.Window) -> true
  | _ -> false

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

(* The slot-binding rule shared by attribution, promotion and call
   effects: a start is an argument slot when it is word-aligned above SP. *)
let call_arg_slot ~(word : int) ~(call_sp : int64) ~(start : int64) : int option =
  let rel = Stdlib.Int64.sub start call_sp in
  let word64 = Stdlib.Int64.of_int word in
  if Stdlib.Int64.compare rel word64 >= 0
     && Stdlib.Int64.equal (Stdlib.Int64.rem rel word64) 0L
  then Some (slot_index_of_offset ~word rel)
  else None

(* The slots a stack argument of [bytes] occupies: whole word cells. *)
let arg_cells ~(word : int) (bytes : int) : int = (bytes + word - 1) / word

(* The word cell of an Args span wholly inside one cell at/above the
   args base: its slot index, else [None]. *)
let args_cell_of_span ~(word : int) ~(entry : int64) (lo : int64)
    (hi : int64) : int option =
  let cell pos = slot_index_of_offset ~word (Stdlib.Int64.sub pos entry) in
  if
    Stdlib.Int64.compare lo (args_base ~entry ~word) >= 0
    && Stdlib.Int.equal (cell lo) (cell hi)
  then Some (cell lo)
  else None

let region_mem ~addr_bits id = Hike_synth.bytes ~addr_bits (Hike_synth.Stack id)

(* The storage base family: one Mem-typed value per storage, minted by
   the attribution's rewrite and bound by the emitter to the storage's
   alloca/global (a parameter-backed storage binds nothing).  A
   rewritten address def's value is [base + displacement]. *)
let region_ptr ~addr_bits id = Hike_synth.base ~addr_bits (Hike_synth.Stack id)

let is_region_ptr synth v =
  match Hike_synth.classify synth v with
  | Some (Hike_synth.Storage (Hike_synth.Stack _)) -> true
  | _ -> false

(* The section-component storage base: one var per component id, the
   emitter binds it to the component's global. *)
let sec_comp_ptr ~addr_bits id = Hike_synth.base ~addr_bits (Hike_synth.Global id)

let is_sec_comp_ptr synth v =
  match Hike_synth.classify synth v with
  | Some (Hike_synth.Storage (Hike_synth.Global _)) -> true
  | _ -> false

(* A storage's base value: never renamed, never a lane. *)
let is_storage_base synth (v : var) : bool =
  is_region_ptr synth v || is_sec_comp_ptr synth v

let region_ptr_id_of synth v =
  match Hike_synth.classify synth v with
  | Some (Hike_synth.Storage (Hike_synth.Stack id)) -> Some id
  | _ -> None

let is_mem var = match Var.typ var with Mem _ -> true | _ -> false

(* BAP owns explicit term reads; the ABI adds transfer inputs. *)
let def_reads (d : def term) : Var.Set.t = Def.free_vars d
let phi_reads (p : phi term) : Var.Set.t = Phi.free_vars p

let phi_reads_from (p : phi term) (pred : Tid.t) : Var.Set.t =
  Phi.values p
  |> Seq.fold ~init:Var.Set.empty ~f:(fun reads (src, exp) ->
         if Tid.equal src pred then
           Core.Set.union reads (Exp.free_vars exp)
         else reads)

let jmp_operand_reads (j : jmp term) : Var.Set.t = Jmp.free_vars j

(* A call consumes the containing block's memory: the mem-typed vars the
   block defines — the outgoing stores' storages and the call-argument
   address temps.  The callee reads the state the site built, through the
   slot addresses the site minted. *)
let blk_boundary_reads synth (blk : blk term) : Var.Set.t =
  let is_call j =
    match Jmp.kind j with
    | Call _ when not (Hike_return.is_jmp j) -> true
    | _ -> false
  in
  if not (Term.enum jmp_t blk |> Seq.exists ~f:is_call) then Var.Set.empty
  else
    Term.enum def_t blk
    |> Seq.fold ~init:Var.Set.empty ~f:(fun acc d ->
           let lhs = Def.lhs d in
           if is_mem lhs || is_fp_operand_temp synth lhs then Core.Set.add acc lhs
           else acc)

let def_writes (d : def term) : Var.Set.t = Var.Set.singleton (Def.lhs d)
let phi_writes (p : phi term) : Var.Set.t = Var.Set.singleton (Phi.lhs p)


let is_region_mem synth v =
  match Hike_synth.classify synth v with
  | Some (Hike_synth.Bytes (Hike_synth.Stack _)) -> true
  | _ -> false

type sec_comp = {
  comp_id : int;              (* the N in sec_comp_N (module-wide) *)
  sec_lo : int64;             (* the owning section's native span *)
  sec_hi : int64;
  lo_w : int;                 (* word range within the section *)
  hi_w : int;
  typed_w : int;              (* bytes per element: 8/4/2/1 *)
}

let sec_comp_name (n : int) : string = Printf.sprintf "sec_comp_%d" n

let sec_comp_mem ~addr_bits id = Hike_synth.bytes ~addr_bits (Hike_synth.Global id)

(* The gap runs continue the same numbering; they emit globals but carry no
   BIL var. *)
let sec_res_name (n : int) : string = Printf.sprintf "sec_res_%d" n

let is_sec_comp_mem synth v =
  match Hike_synth.classify synth v with
  | Some (Hike_synth.Bytes (Hike_synth.Global _)) -> true
  | _ -> false

(* A model-owned storage var: a fissioned memory family or a storage
   base. *)
let is_model_storage synth v =
  is_region_mem synth v || is_window_mem synth v || is_sec_comp_mem synth v
  || is_storage_base synth v

let sanitize_tid_name (n : string) : string =
  Base.String.filter n ~f:(fun c ->
      match c with '#' | '.' | '%' | '\\' | '@' -> false | _ -> true)

let sub_operand_reads (s : sub term) : Var.Set.t =
  Term.enum blk_t s
  |> Seq.fold ~init:Var.Set.empty ~f:(fun acc blk ->
      Blk.elts blk
      |> Seq.fold ~init:acc ~f:(fun reads -> function
             | `Def d -> Core.Set.union reads (def_reads d)
             | `Phi p -> Core.Set.union reads (phi_reads p)
             | `Jmp j -> Core.Set.union reads (jmp_operand_reads j)))

(* The deepest literal SP decrement in the sub (prologues), through a
   copy chain. *)
let deepest_sp_decrement (sub : sub term) ~(abi : Abi.t) : int64 =
  let is_sp v = Abi.is_sp abi (Var.base v) in
  (* The literal displacement of [SP - k] through copies defined
     earlier in term order; a cycle through the copy chain stops
     ([seen] carries the visited bases). *)
  let rec disp chain seen rhs =
    match rhs with
    | Bil.BinOp (Bil.MINUS, Bil.Var r, Bil.Int w) when is_sp r ->
      Some (Word.to_int64_exn w)
    | Bil.Var v ->
      let b = Var.base v in
      if Core.Set.mem seen b then None
      else
        Core.Option.bind (Core.Map.find chain b)
          ~f:(fun d -> disp chain (Core.Set.add seen b) (Def.rhs d))
    | _ -> None
  in
  Term.enum blk_t sub
  |> Seq.fold ~init:(0L, Var.Map.empty) ~f:(fun (acc, chain) blk ->
         Seq.fold (Term.enum def_t blk) ~init:(acc, chain)
           ~f:(fun (acc, chain) d ->
             if is_sp (Def.lhs d) then
               let acc =
                 match
                   disp chain (Var.Set.singleton (Var.base (Def.lhs d)))
                     (Def.rhs d)
                 with
                 | Some w -> Int64.max acc w
                 | None -> acc
               in
               (acc, chain)
             else
               (acc, Core.Map.set chain ~key:(Var.base (Def.lhs d)) ~data:d)))
  |> fst

(* A real (non-intrinsic) call, direct or indirect. *)
let machine_call (j : jmp term) : bool =
  match Jmp.kind j with
  | Call c when not (Hike_return.is_jmp j) -> (
      match Call.target c with
      | Direct t -> not (Hike_abi.is_intrinsic_target t)
      | Indirect _ -> true)
  | _ -> false

(* A real call with a continuation pushes its return address. *)
let call_pushes (j : jmp term) : bool =
  match Jmp.kind j with
  | Call c -> machine_call j && Option.is_some (Call.return c)
  | _ -> false

let has_call_push (sub : sub term) : bool =
  Term.enum blk_t sub
  |> Seq.exists ~f:(fun blk ->
         Term.enum jmp_t blk |> Seq.exists ~f:call_pushes)

let ssa_tag : unit Value.Tag.t =
  Value.Tag.register ~package:"hike" ~name:"hike-ssa-processed"
    ~uuid:"d534478d-b5b4-4ca8-b2b9-f28c22da568d" (module Core.Unit)

type call_arg_store = {
  sb_slot : int;
  sb_def : def term;
}

(* The call-site correspondence shared by attribution and promotion: a
   store's singleton aligned start [a] against the block's call-time SP
   [d_sp] is slot [(a - d_sp - word) / word]. *)
(* The emitter's per-sub inputs are structure (BIR args, direct targets,
   def tags) plus this layout fact: the alloca-construction inputs alone. *)

module Sub_layout = struct
  open Core

  (* One alloca of the sub: the region id, the model-address extent it
     covers, and its byte size. *)
  type region = {
    r_id : int;
    r_lo : int64;
    r_hi : int64;
    r_bytes : int64;
  }
  [@@deriving equal, compare, sexp]

  (* [regions] is every alloca of the sub — the carved regions plus the
     stack residue (id 0, whose extent contains the caller window).  Every
     model address resolves against one region's base. *)
  type t = {
    regions : region list;
    (* The sub accesses Args space directly or through a va_list
       overflow pointer, so its signature carries hike_window. *)
    window_param : bool;
    (* The residue's below-entry extent is unbounded or exceeds
       [frame_alloca_max]: its storage is the runtime stack. *)
    runtime_residue : bool;
  }
  [@@deriving equal, compare, sexp]

  (* Required by [Value.Tag.register]. *)
  let pp fmt { regions; window_param; runtime_residue } =
    Format.fprintf fmt "regions=%d;window=%b;runtime=%b"
      (Base.List.length regions)
      window_param runtime_residue

  module Stringable = struct
    type nonrec t = t
    let to_string t = Base.Sexp.to_string (sexp_of_t t)
    let of_string s = t_of_sexp (Parsexp.Single.parse_string_exn s)
  end

  include Core.Binable.Of_stringable_with_uuid (struct
    include Stringable

    let caller_identity =
      Bin_prot.Shape.Uuid.of_string "hike:hike_stack_model.Sub_layout/6"
  end)
end

type sub_layout = Sub_layout.t = {
  regions : Sub_layout.region list;
  window_param : bool;
  runtime_residue : bool;
}

type layout_region = Sub_layout.region = {
  r_id : int;
  r_lo : int64;
  r_hi : int64;
  r_bytes : int64;
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

(* The sub's return lanes: the ABI's return carriers, then any other
   [Out] lane the sub already has. *)
let return_lanes ~target sub =
  let carriers =
    if Abi.is_primary_target target then (Abi.of_target target).Abi.return_regs
    else []
  in
  Base.List.map carriers ~f:(fun reg -> Arg.create ~intent:Out reg (Bil.Var reg))
  @ Base.List.filter (sig_rets sub) ~f:(fun arg ->
      not (Base.List.exists carriers ~f:(Var.same (Arg.lhs arg))))

let call_lanes ~abi ~callee target =
  match Hike_native_fp.native_fp_op (Tid.name target) with
  | Some op ->
    let w = Hike_native_fp.lane_width_of_name
        ~word_bits:(word_bits abi.Abi.word) (Tid.name target) in
    let signature = Hike_native_fp.fp_sig_of op ~w in
    (signature.fp_args, signature.fp_rets)
  | None when Abi.is_intrinsic_name (Tid.name target)
           || Abi.is_interrupt_name (Tid.name target) -> ([], [])
  | None ->
    match callee target with
    | Some sub ->
      (Base.List.map (sig_args sub) ~f:Arg.lhs,
       Base.List.map (sig_rets sub) ~f:Arg.lhs)
    | None ->
      (Core.Set.to_list (Var.Set.of_list (Abi.param_regs abi @ abi.Abi.return_regs)),
       abi.Abi.return_regs)

(* Implicit boundary lanes travel with the jump through SSA and retyping. *)
module Term_effects = struct
  open! Core
  type t = { reads : var list; writes : var list }
  [@@deriving bin_io, compare, sexp]
  let pp ppf t = Sexp.pp ppf (sexp_of_t t)
end

let effects_tag : Term_effects.t Value.Tag.t =
  Value.Tag.register ~package:"hike" ~name:"term-effects"
    ~uuid:"89ddf051-153f-40ac-8940-4260ab3145db" (module Term_effects)

let call_effects ~abi ~callee j =
  match Jmp.kind j with
  | Call c when not (Hike_return.is_jmp j) ->
    let reads, writes = match Call.target c with
      | Direct target -> call_lanes ~abi ~callee target
      | Indirect _ ->
        (Core.Set.to_list (Var.Set.of_list (Abi.param_regs abi @ abi.Abi.return_regs)),
         abi.Abi.return_regs) in
    let machine = match Call.target c with
      | Direct target ->
        not (Abi.is_intrinsic_name (Tid.name target)
             || Abi.is_interrupt_name (Tid.name target))
      | Indirect _ -> true in
    let reads = if machine then abi.Abi.sp :: reads else reads in
    { Term_effects.reads; writes }
  | _ -> { Term_effects.reads = []; writes = [] }

let effects_opt j = Term.get_attr j effects_tag

let effects j =
  match effects_opt j with
  | Some effects -> effects
  | None ->
    let abi = Abi.x86_64_sysv in
    if Hike_return.is_jmp j then
      { Term_effects.reads = abi.return_regs @ [ abi.sp ]; writes = [] }
    else match Jmp.kind j with
      | Ret _ -> { Term_effects.reads = abi.return_regs @ [ abi.sp ]; writes = [] }
      | _ -> call_effects ~abi ~callee:(fun _ -> None) j

(* A boundary's reads precede its writes.  The reads remain on a call
   even when splitting moves it away from its defining block. *)
let boundary_read (blk : blk term) (v : var) : var option =
  Term.enum jmp_t blk
  |> Seq.find_map ~f:(fun j ->
         Base.List.find (effects j).Term_effects.reads ~f:(Var.same v))

let boundary_write (blk : blk term) (v : var) : var option =
  Term.enum jmp_t blk
  |> Seq.fold ~init:None ~f:(fun found j ->
         Base.Option.first_some
           (Base.List.find (effects j).Term_effects.writes ~f:(Var.same v))
           found)

(* Phi outputs precede def outputs; the last local definition wins. *)
let local_output (blk : blk term) (v : var) : var option =
  let phi =
    Term.enum phi_t blk
    |> Seq.find_map ~f:(fun p ->
           let lhs = Phi.lhs p in
           Base.Option.some_if (Var.same lhs v) lhs)
  in
  Term.enum def_t blk
  |> Seq.fold ~init:phi ~f:(fun found d ->
         let lhs = Def.lhs d in
         if Var.same lhs v then Some lhs else found)

let passed_version (blk : blk term) (v : var) : var option =
  if Term.has_attr blk ssa_tag then
    Base.Option.first_some (boundary_read blk v) (local_output blk v)
  else Base.Option.first_some (local_output blk v) (boundary_read blk v)

let version_at_end (blk : blk term) (v : var) : var =
  Base.Option.value (passed_version blk v) ~default:v

let call_stack_arity : int Value.Tag.t =
  Value.Tag.register ~package:"hike" ~name:"hike-call-stack-arity"
    ~uuid:"7a1b9e0e-3c5e-4f06-9d0a-5a4f3a6d2c11" (module Core.Int)

type remote_arg_store = {
  rb_slot : int;
  rb_def : def term;
  rb_blk : Tid.t;
}

(* One call block's stack arguments, found by position. *)
type call_site = {
  cs_own : call_arg_store list;
  cs_remote : remote_arg_store list;
  cs_arity : int;
  cs_window : (int64 * int64) option;
}

let call_sites ~(word : int) ~(sp : var)
    ~(denote : blk:blk term -> ?def:def term -> exp ->
                (Cbat_clp_set_composite.t, Type.error) Result.t)
    (sub : sub term) : call_site Tid.Map.t =
  let singleton_at ?(def : def term option) ~(blk : blk term) (e : exp) :
      int64 option =
    match denote ~blk ?def e with
    | Error _ -> None
    | Ok ws -> singleton_stack_position ws
  in
  (* Every store of the sub with a singleton stack address, once. *)
  let stores =
    Term.enum blk_t sub
    |> Seq.concat_map ~f:(fun blk ->
        Term.enum def_t blk
        |> Seq.filter_map ~f:(fun d ->
            match addr_of_rhs (Def.rhs d), store_data_of_rhs (Def.rhs d) with
            | Some (addr, size), Some _ ->
              Base.Option.map (singleton_at ~def:d ~blk addr) ~f:(fun start ->
                  (Term.tid blk, d, start, Size.in_bytes size))
            | _ -> None))
    |> Seq.to_list
  in
  Term.enum blk_t sub
  |> Seq.fold ~init:Tid.Map.empty ~f:(fun sites blk ->
      let btid = Term.tid blk in
      if not (Term.enum jmp_t blk |> Seq.exists ~f:machine_call) then sites
      else
        let site =
          match singleton_at ~blk (Bil.Var (version_at_end blk sp)) with
          | None -> { cs_own = []; cs_remote = []; cs_arity = 0; cs_window = None }
          | Some call_sp ->
            let slot_of start = call_arg_slot ~word ~call_sp ~start in
            (* The first and last slot a store covers. *)
            let cells start bytes =
              Base.Option.map (slot_of start) ~f:(fun slot ->
                  (slot, slot + arg_cells ~word bytes - 1)) in
            (* The call block's own stores, the last of a slot winning. *)
            let own =
              Base.List.fold stores ~init:Core.Int.Map.empty
                ~f:(fun acc (tid, d, start, _) ->
                    match slot_of start with
                    | Some slot when Tid.equal tid btid ->
                      Core.Map.set acc ~key:slot
                        ~data:{ sb_slot = slot; sb_def = d }
                    | _ -> acc) in
            (* Other blocks' stores of a slot the own stores leave open;
               which of several is named is arbitrary: they write one
               cell. *)
            let remote =
              Base.List.fold stores ~init:Core.Int.Map.empty
                ~f:(fun acc (tid, d, start, _) ->
                    match slot_of start with
                    | Some slot
                      when (not (Tid.equal tid btid))
                        && (not (Core.Map.mem own slot))
                        && not (Core.Map.mem acc slot) ->
                      Core.Map.set acc ~key:slot
                        ~data:{ rb_slot = slot; rb_def = d; rb_blk = tid }
                    | _ -> acc) in
            (* Only the run of slots from 0 that these fill without a gap
               counts: a local stored further up the frame is no
               argument.  A store fills every slot it covers. *)
            let filled =
              Base.List.fold stores ~init:Core.Int.Set.empty
                ~f:(fun acc (_, _, start, bytes) ->
                    match cells start bytes with
                    | Some (first, last) ->
                      Base.List.fold (Base.List.range first (last + 1))
                        ~init:acc ~f:Core.Set.add
                    | None -> acc) in
            let rec run k = if Core.Set.mem filled k then run (k + 1) else k in
            let limit = run 0 in
            let cs_own = Core.Map.data own in
            let cs_remote =
              Base.List.filter (Core.Map.data remote) ~f:(fun b -> b.rb_slot < limit) in
            (* The argument range is the hull of the whole slots the
               argument stores reach. *)
            let arguments =
              Tid.Set.of_list
                (Base.List.map cs_own ~f:(fun b -> Term.tid b.sb_def)
                 @ Base.List.map cs_remote ~f:(fun b -> Term.tid b.rb_def)) in
            let cs_window =
              Base.List.fold stores ~init:None ~f:(fun acc (_, d, start, bytes) ->
                  match cells start bytes with
                  | Some (first, last) when Core.Set.mem arguments (Term.tid d) ->
                    Some (match acc with
                        | None -> (first, last)
                        | Some (lo, hi) -> (Stdlib.min lo first, Stdlib.max hi last))
                  | _ -> acc)
              |> Base.Option.map ~f:(fun (first, last) ->
                  (Stdlib.Int64.add call_sp (slot_offset ~word first),
                   Stdlib.Int64.pred
                     (Stdlib.Int64.add call_sp (slot_offset ~word (last + 1))))) in
            { cs_own; cs_remote; cs_arity = limit; cs_window }
        in
        Core.Map.set sites ~key:btid ~data:site)

let reads = function
  | `Def d -> def_reads d
  | `Phi p -> phi_reads p
  | `Arg a -> Exp.free_vars (Arg.rhs a)
  | `Jmp j ->
    Core.Set.union (jmp_operand_reads j) (Var.Set.of_list (effects j).reads)

let writes = function
  | `Def d -> def_writes d
  | `Phi p -> phi_writes p
  | `Arg a -> Var.Set.singleton (Arg.lhs a)
  | `Jmp j -> Var.Set.of_list (effects j).writes

let map_effects ~read ~write j =
  let effects = effects j in
  Term.set_attr j effects_tag
    { Term_effects.reads = Base.List.map effects.reads ~f:read;
      writes = Base.List.map effects.writes ~f:write }

(* One block's derived lanes.  [outgoing] is the sub-level return lane
   set (the SP plus the signature's return operands); a new block can be
   prepared without touching the rest of the sub. *)
let prepare_block_effects ~synth ~abi ~callee ~outgoing (blk : blk term) :
    blk term =
  let boundary = Core.Set.to_list (blk_boundary_reads synth blk) in
  Term.map jmp_t blk ~f:(fun j ->
      let effects =
        if Hike_return.is_jmp j then
          { Term_effects.reads = outgoing; writes = [] }
        else match Jmp.kind j with
          | Ret _ -> { Term_effects.reads = outgoing; writes = [] }
          | _ -> call_effects ~abi ~callee j in
      let reads = match Jmp.kind j with
        | Call _ -> effects.reads @ boundary
        | _ -> effects.reads in
      Term.set_attr j effects_tag { effects with reads })

let prepare_effects ~synth ~abi ~callee sub =
  let outgoing = abi.Abi.sp :: (sig_rets sub
      |> Base.List.concat_map ~f:(fun arg ->
          Exp.free_vars (Arg.rhs arg) |> Core.Set.to_list)) in
  Term.map blk_t sub
    ~f:(prepare_block_effects ~synth ~abi ~callee ~outgoing)

let sub_reads sub =
  Term.enum blk_t sub |> Seq.fold ~init:Var.Set.empty ~f:(fun acc blk ->
      Blk.elts blk |> Seq.fold ~init:acc ~f:(fun acc term ->
          Core.Set.union acc (reads term)))

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

(* The PLT-trampoline stamp: a self-call stub that reads no non-return,
   non-SP register.  hike-sign computes it from the liveness its
   signature computation already ran, and the emitter reads the stamp.
   Absence is the identity — not a trampoline. *)
let plt_trampoline_tag : Flag.t Value.Tag.t =
  Value.Tag.register ~package:"hike" ~name:"hike-plt-trampoline"
    ~uuid:"8c3e6f1a-92d4-47b5-a083-5e7c1d9b4f62"
    (module Flag)

let is_plt_trampoline_sub (sub : sub term) : bool =
  Base.Option.value (Term.get_attr sub plt_trampoline_tag) ~default:false

(* The self-call stub's shape: a self-targeted direct call, a real call
   jmp, and reads confined to the SP and the return registers — the
   stub's `call next; jmp *[GOT]` idiom, recognized without names.  The
   sign pass stamps what this recognizes; the tag is the carried fact. *)
let is_self_call_shape ~(target : Bap_core_theory.Theory.Target.t)
    (sub : sub term) : bool =
  let abi = Hike_abi.of_target target in
  let self_targeted =
    Term.enum blk_t sub
    |> Seq.exists ~f:(fun blk ->
        Term.enum jmp_t blk
        |> Seq.exists ~f:(fun j ->
            match Jmp.kind j with
            | Call c -> (
                match Call.target c with
                | Direct t ->
                    Tid.equal t (Term.tid sub)
                    || sanitize_tid_name (Tid.name t)
                       = sanitize_tid_name (Tid.name (Term.tid sub))
                | Indirect _ -> false)
            | _ -> false))
  in
  let has_call =
    Term.enum blk_t sub
    |> Seq.exists ~f:(fun blk ->
        Term.enum jmp_t blk
        |> Seq.exists ~f:(fun j ->
            match Jmp.kind j with
            | Call _ -> not (Hike_return.is_jmp j)
            | _ -> false))
  in
  let reads_only_return =
    Core.Set.for_all (sub_operand_reads sub) ~f:(fun reg ->
        Hike_abi.is_sp abi (Var.base reg) || Hike_abi.is_return_reg abi reg)
  in
  self_targeted && has_call && reads_only_return

(* The declaration classification: a sub the module DECLARES but never
   defines.  Evidence accumulates where it is visible — the prune's
   leave census and the sign pass's self-call shape stamp the tag; a
   bodyless sub is a declaration by observation; a sub named by a
   loader relocation is the loader's, named by [reloc_names]. *)
let is_declared ?(reloc_names = Core.String.Set.empty) (sub : sub term) : bool =
  is_plt_trampoline_sub sub
  || Base.Option.is_none (Term.first blk_t sub)
  || Core.Set.mem reloc_names (Hike_abi.strip_at (Tid.name (Term.tid sub)))

let set_plt_trampoline (sub : sub term) : sub term =
  Term.set_attr sub plt_trampoline_tag true
