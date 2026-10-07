(* The section vocabulary, denotation predicates, and the shared
   stack/var/layout contracts used by the attribution and emitter. *)
module Vocab = struct
  open! Core

  type sec = Stack | Args | Vla | Text | Rodata | Data | Got | Gotplt | Datarelro | Bss
  [@@deriving equal, compare, sexp]

  (* The section's ELF name — the one spelling of the name grammar. *)
  let sec_name = function
    | Stack -> "stack"
    | Args -> "args"
    | Vla -> "vla"
    | Data -> "data"
    | Rodata -> "rodata"
    | Bss -> "bss"
    | Got -> "got"
    | Gotplt -> "got.plt"
    | Datarelro -> "data.rel.ro"
    | Text -> "text"

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
  sm_const : bool;
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

(* The producer builds this record; the model and the emitter consume it. *)
module Vsa = struct
  open Core

  (* The ABSOLUTE position of the entry RSP on the segment line (the seeded
     SP is base + offset 0); a frame-relative depth is [base − position]. *)
  let segment_base = Cbat_clp_set_composite.stack_base

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

  let singleton_offset (offs : Cbat_clp_set_composite.Clp.t) : int64 option =
    singleton_pair
      (Cbat_clp_set_composite.Clp.min_elem offs)
      (Cbat_clp_set_composite.Clp.max_elem offs)

  (* The denotation's single stack position (absolute), when it has
     exactly one: the symbolic arm or the in-band plain arm (the band
     holds no real x86-64 address, so a plain word there is stack). *)
  let singleton_stack_position (ws : Cbat_clp_set_composite.t) : int64 option =
    match Cbat_clp_set_composite.stack_offsets ws with
    | Some _ -> (
        match positions_of_offsets ws with
        | Some (lo, hi) when Int64.equal lo hi -> Some lo
        | _ -> None)
    | None ->
        if Cbat_clp_set_composite.in_stack_segment ws then singleton_i64 ws
        else None

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

  (* The shape-only projection [mem[SP]], for the consumer that runs before
     any solution exists. *)
  let is_return_address_shape ~(abi : Abi.t) (addr : exp) : bool =
    match addr with
    | Bil.Var v -> Var.same (Var.base v) abi.Hike_abi.sp
    | _ -> false

end
include Vsa

(* The storage a ptr-kind value lives in: a region or residue alloca of
   this sub, the caller frame base (the window), or a VLA. *)
type ptr_storage =
  | Ptr_region of int
  | Ptr_residue
  | Ptr_window
  | Ptr_vla

let equal_ptr_storage (a : ptr_storage) (b : ptr_storage) : bool =
  match a, b with
  | Ptr_region x, Ptr_region y -> Int.equal x y
  | Ptr_residue, Ptr_residue | Ptr_window, Ptr_window | Ptr_vla, Ptr_vla ->
      true
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

let reads_mem (e : exp) : bool =
  match mem_node_of e with Some _ -> true | None -> false

(* Free vars of every Load mem in one rhs. *)
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
        | _ -> if ca = Tp_zero && cb = Tp_zero then Tp_zero else Tp_non in
      coeff, Base.Option.map2 va vb ~f:(Bil.Apply.binop op)
    | Bil.Cast (cast, bits, e) ->
      let c, v = fold e in
      if c = Tp_zero then c, Base.Option.map v ~f:(Bil.Apply.cast cast bits)
      else if bits = tp_bits then c, v
      else Tp_non, None
    | Bil.UnOp (op, e) ->
      let c, v = fold e in
      if c = Tp_zero then c, Base.Option.map v ~f:(Bil.Apply.unop op)
      else Tp_non, None
    | Bil.Concat (a, b) ->
      let ca, va = fold a and cb, vb = fold b in
      if ca = Tp_zero && cb = Tp_zero then
        Tp_zero, Base.Option.map2 va vb ~f:Word.concat
      else Tp_non, None
    | Bil.Extract (hi, lo, e) ->
      let c, v = fold e in
      if c = Tp_zero then c, Base.Option.map v ~f:(Word.extract_exn ~hi ~lo)
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

(* The call-argument temps survive DCE: they are the call's arguments. *)
let is_call_arg v =
  match Hike_synth.classify Hike_synth.empty v with
  | Some (Hike_synth.Storage (Hike_synth.Argument _)) -> true
  | _ -> false

(* The FP model's operand temp: [intrinsic:x<N>], width-qualified by the
   fp pass ([intrinsic:x<N>:<width>]); an FP call site's argument.  The
   base name carries no SSA version. *)
let is_fp_operand_temp v =
  match Hike_synth.classify Hike_synth.empty v with
  | Some (Hike_synth.Fp_lane (Hike_synth.Input, _)) -> true
  | _ -> false

let is_arg_slot v =
  match Hike_synth.classify Hike_synth.empty v with
  | Some (Hike_synth.Storage (Hike_synth.Slot _)) -> true
  | _ -> false

(* The fission mem vars' type: byte cells addressed at the target's
   address width. *)
let window_mem ~addr_bits = Hike_synth.bytes ~addr_bits Hike_synth.Window

let is_window_mem v =
  match Hike_synth.classify Hike_synth.empty v with
  | Some (Hike_synth.Bytes Hike_synth.Window) -> true
  | _ -> false

(* The caller-window base parameter. *)
let hike_window_var ~word =
  Hike_synth.base ~addr_bits:(word_bits word) Hike_synth.Window

let is_window_var v =
  match Hike_synth.classify Hike_synth.empty v with
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

let is_region_ptr v =
  match Hike_synth.classify Hike_synth.empty v with
  | Some (Hike_synth.Storage (Hike_synth.Stack _)) -> true
  | _ -> false

(* The VLA storage base: one var per allocation, keyed by the
   decrement def's tid — the emitter binds it to that %vla alloca. *)
let vla_ptr ~addr_bits t =
  Hike_synth.base ~addr_bits (Hike_synth.Allocation (Tid.hash t))

let is_vla_ptr v =
  match Hike_synth.classify Hike_synth.empty v with
  | Some (Hike_synth.Storage (Hike_synth.Allocation _)) -> true
  | _ -> false

(* The section-component storage base: one var per component id, the
   emitter binds it to the component's global. *)
let sec_comp_ptr ~addr_bits id = Hike_synth.base ~addr_bits (Hike_synth.Global id)

let is_sec_comp_ptr v =
  match Hike_synth.classify Hike_synth.empty v with
  | Some (Hike_synth.Storage (Hike_synth.Global _)) -> true
  | _ -> false

(* A storage's base value: never renamed, never a lane. *)
let is_storage_base (v : var) : bool =
  is_region_ptr v || is_vla_ptr v || is_sec_comp_ptr v

(* The un-carved global memory state: BAP's own [mem] var, outside the
   fissioned families.  A store into it is observable outside the sub
   (the caller reads the sret buffer through its own pointer) — the
   sweep never kills one. *)
let is_global_mem (v : var) : bool =
  match Hike_synth.classify Hike_synth.empty v with
  | Some (Hike_synth.Bytes (Hike_synth.Global _)) -> true
  | _ -> Core.String.equal (Var.name (Var.base v)) "mem"

let region_ptr_id_of v =
  match Hike_synth.classify Hike_synth.empty v with
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

(* The boundary reads a jmp's kind consumes with no operand naming
   them, split by direction.  The inputs are what the transfer consumes
   from the containing sub: a call's parameter registers.  The outputs
   are what the convention produces at the boundary: the return
   registers (the sub's own at a return edge, the callee's at a call)
   and SP.  Liveness reads the union (an output's producer stays live);
   a sub's input lanes read the inputs only — an output lane with no
   producer is the ABI's undef, not an entry value. *)
let jmp_boundary_inputs ~(abi : Abi.t) (j : jmp term) : Var.Set.t =
  match Jmp.kind j with
  | Call _ when not (Hike_return.is_jmp j) ->
    Core.Set.of_list (module Var) (Abi.param_regs abi)
  | _ -> Var.Set.empty

let jmp_boundary_reads ~(abi : Abi.t) (j : jmp term) : Var.Set.t =
  let fp_ret =
    match abi.vector_return_reg with Some v -> [ v ] | None -> []
  in
  Core.Set.union (jmp_boundary_inputs ~abi j)
    (match Jmp.kind j with
     | Ret _ | Call _ ->
       Core.Set.of_list (module Var)
         (abi.return_regs @ fp_ret @ [ abi.sp ])
     | _ -> Var.Set.empty)

let jmp_reads ~(abi : Abi.t) (j : jmp term) : Var.Set.t =
  Core.Set.union (jmp_operand_reads j) (jmp_boundary_reads ~abi j)

(* The reads that name the containing sub's entry values. *)
let jmp_input_reads ~(abi : Abi.t) (j : jmp term) : Var.Set.t =
  Core.Set.union (jmp_operand_reads j) (jmp_boundary_inputs ~abi j)

(* A call consumes the containing block's memory: the mem-typed vars the
   block defines — the outgoing stores' storages and the call-argument
   address temps.  The callee reads the state the site built, through the
   slot addresses the site minted. *)
let blk_boundary_reads (blk : blk term) : Var.Set.t =
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
           if is_mem lhs || is_fp_operand_temp lhs then Core.Set.add acc lhs
           else acc)

let jmp_target_reads (j : jmp term) : Var.Set.t =
  match Jmp.kind j with
  | Goto (Indirect e) | Ret (Indirect e) -> Exp.free_vars e
  | Call c ->
    let target =
      match Call.target c with
      | Indirect e -> Exp.free_vars e
      | Direct _ -> Var.Set.empty
    in
    let ret =
      match Call.return c with
      | Some (Indirect e) -> Exp.free_vars e
      | Some (Direct _) | None -> Var.Set.empty
    in
    Core.Set.union target ret
  | Goto (Direct _) | Ret (Direct _) | Int _ -> Var.Set.empty

let def_writes (d : def term) : Var.Set.t = Var.Set.singleton (Def.lhs d)
let phi_writes (p : phi term) : Var.Set.t = Var.Set.singleton (Phi.lhs p)

let blk_free_vars (blk : blk term) : Var.Set.t = Blk.free_vars blk

let blk_reads ~(abi : Abi.t) (blk : blk term) : Var.Set.t =
  Blk.elts blk
  |> Seq.fold ~init:Var.Set.empty ~f:(fun reads -> function
         | `Def d -> Core.Set.union reads (def_reads d)
         | `Phi p -> Core.Set.union reads (phi_reads p)
         | `Jmp j -> Core.Set.union reads (jmp_reads ~abi j))

let is_region_mem v =
  match Hike_synth.classify Hike_synth.empty v with
  | Some (Hike_synth.Bytes (Hike_synth.Stack _)) -> true
  | _ -> false

(* The region id a [stack_rN_mem] var names; [None] for any other var. *)
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

let is_sec_comp_mem v =
  match Hike_synth.classify Hike_synth.empty v with
  | Some (Hike_synth.Bytes (Hike_synth.Global _)) -> true
  | _ -> false

(* The component id a [sec_comp_N_mem] var names; [None] for any other
   var. *)
let sanitize_tid_name (n : string) : string =
  Base.String.filter n ~f:(fun c ->
      match c with '#' | '.' | '%' | '\\' | '@' -> false | _ -> true)

(* The program's subs keyed by tid. *)
let sub_map (prog : program term) : sub term Tid.Map.t =
  Term.enum sub_t prog
  |> Seq.fold ~init:Tid.Map.empty ~f:(fun m s ->
      Core.Map.set m ~key:(Term.tid s) ~data:s)

(* The vars a sub reads, including the ABI boundary of each transfer. *)
let sub_reads ~(abi : Abi.t) (s : sub term) : Var.Set.t =
  Term.enum blk_t s
  |> Seq.fold ~init:Var.Set.empty ~f:(fun acc blk ->
      Core.Set.union acc (blk_reads ~abi blk))

let sub_operand_reads (s : sub term) : Var.Set.t =
  Term.enum blk_t s
  |> Seq.fold ~init:Var.Set.empty ~f:(fun acc blk ->
      Blk.elts blk
      |> Seq.fold ~init:acc ~f:(fun reads -> function
             | `Def d -> Core.Set.union reads (def_reads d)
             | `Phi p -> Core.Set.union reads (phi_reads p)
             | `Jmp j -> Core.Set.union reads (jmp_operand_reads j)))

(* The deepest literal SP decrement in the sub (prologues and VLAs),
   through a copy chain as in the dynamic-allocation walk. *)
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

(* The lifted va_list construction: the incoming parameter registers
   stored into the sub's own frame (the reg_save_area) beside a pointer
   at/above the entry args base stored into the frame (the
   overflow_arg_area).  The construction is the proof — a sub that
   merely carries the same registers is not variadic.  The [al] guard
   around the vector spills corroborates and is not required.  Frame
   positions and the register set come from the denotation and [Abi]. *)
let is_variadic_construction ~(abi : Abi.t) ~(entry : int64)
    ~(denote : blk:blk term -> ?def:def term -> exp ->
               (Cbat_clp_set_composite.t, Type.error) Result.t)
    (sub : sub term) : bool =
  let word = abi.Abi.word in
  let a_base = args_base ~entry ~word in
  let params = abi.Abi.int_param_regs @ abi.Abi.vector_param_regs in
  let positions ~blk ~def (e : exp) : (int64 * int64) option =
    match denote ~blk ~def e with
    | Error _ -> None
    | Ok ws -> positions_of_offsets ws
  in
  let in_frame ~blk ~def (e : exp) : bool =
    match positions ~blk ~def e with
    | Some (lo, hi) ->
        Int64.compare lo hi <= 0 && Int64.compare hi (Int64.pred entry) <= 0
    | None -> false
  in
  let stores_overflow ~blk ~def (d : def term) : bool =
    match addr_of_rhs (Def.rhs d) with
    | Some (addr, _) when in_frame ~blk ~def addr -> (
        match store_data_of_rhs (Def.rhs d) with
        | Some data -> (
            match positions ~blk ~def data with
            | Some (dlo, dhi) ->
                Int64.compare dlo a_base >= 0 && Int64.compare dlo dhi <= 0
            | None -> false)
        | None -> false)
    | _ -> false
  in
  let stored_params ~blk ~def (d : def term) : Var.Set.t =
    match addr_of_rhs (Def.rhs d) with
    | Some (addr, _) when in_frame ~blk ~def addr -> (
        match store_data_of_rhs (Def.rhs d) with
        | None -> Var.Set.empty
        | Some data ->
            let free = Exp.free_vars data in
            Base.List.fold params ~init:Var.Set.empty ~f:(fun acc r ->
                if Core.Set.exists free ~f:(fun v -> Var.same v r) then
                  Core.Set.add acc (Var.base r)
                else acc))
    | _ -> Var.Set.empty
  in
  let overflow, regs =
    Term.enum blk_t sub
    |> Seq.fold ~init:(false, Var.Set.empty) ~f:(fun (ov, regs) blk ->
           Term.enum def_t blk
           |> Seq.fold ~init:(ov, regs) ~f:(fun (ov, regs) d ->
                  ( ov || stores_overflow ~blk ~def:d d,
                    Core.Set.union regs (stored_params ~blk ~def:d d) )))
  in
  (* The register-save bound: the reg_save_area saves a majority of the
     integer parameter registers regardless of their individual use,
     where an ordinary sub stores only the args it reads. *)
  overflow
  && Core.Set.length regs > Base.List.length abi.Abi.int_param_regs / 2

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
    (* The sub reads its incoming window: its direct-call signature carries
       the hike_window parameter. *)
    window_param : bool;
  }
  [@@deriving equal, compare, sexp]

  (* Required by [Value.Tag.register]. *)
  let pp fmt { regions; window_param } =
    Format.fprintf fmt "regions=%d;window=%b"
      (Base.List.length regions)
      window_param

  module Stringable = struct
    type nonrec t = t
    let to_string t = Base.Sexp.to_string (sexp_of_t t)
    let of_string s = t_of_sexp (Parsexp.Single.parse_string_exn s)
  end

  include Core.Binable.Of_stringable_with_uuid (struct
    include Stringable

    let caller_identity =
      Bin_prot.Shape.Uuid.of_string "hike:hike_stack_model.Sub_layout/5"
  end)
end

type sub_layout = Sub_layout.t = {
  regions : Sub_layout.region list;
  window_param : bool;
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

(* The SSA pass's block stamp.  [args] holds the versions in effect
   after the block's defs — BEFORE any call-ret minting, so a call
   argument read resolves to the value the machine passes.  [rets]
   holds the call-ret mints — the versions the call's own result
   binds. *)
module Versions = struct
  open! Core

  type t =
    { args : (var * var) list
    ; rets : (var * var) list
    ; entry : (var * var) list
    }
  [@@deriving bin_io, compare, sexp]

  let pp ppf { args; rets; entry } =
    let one ppf (a, b) =
      Format.fprintf ppf "(%a, %a)" Var.pp a Var.pp b
    in
    Format.fprintf ppf "args=[%a] rets=[%a] entry=[%a]"
      (Format.pp_print_list one) args
      (Format.pp_print_list one) rets
      (Format.pp_print_list one) entry
end

let versions_tag : Versions.t Value.Tag.t =
  Value.Tag.register ~package:"hike" ~name:"hike-ssa-versions"
    ~uuid:"1f0d4b8e-52a6-4c11-9f0a-3d7c2b1e8a44"
    (module Versions)

let ssa_tag : unit Value.Tag.t =
  Value.Tag.register ~package:"hike" ~name:"hike-ssa"
    ~uuid:"2c1e5f9a-63b7-4d22-8a1b-4e8d3f2c9b55"
    (module Core.Unit)

let is_ssa (sub : sub term) : bool = Term.has_attr sub ssa_tag

let set_layout (l : Sub_layout.t) (sub : sub term) : sub term =
  Term.set_attr sub layout_tag l

(* The variadic stamp: the sub's body holds the lifted va_list
   construction, so its definition is a real LLVM variadic.  The emitter
   reads it off the term. *)
let variadic_tag : unit Value.Tag.t =
  Value.Tag.register ~package:"hike" ~name:"hike-variadic"
    ~uuid:"7b2d4c9e-1a35-4f80-9c62-5e8d0f3a1b47"
    (module Core.Unit)

let is_variadic (sub : sub term) : bool = Term.has_attr sub variadic_tag

let set_variadic (sub : sub term) : sub term =
  Term.set_attr sub variadic_tag ()

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

(* The lane's value KIND: the lane carries a stack/VLA address.  Distinct
   from [arg_ptr_tag] (the LLVM type of an existing ptr lane); the kind
   pass sets it and the emitter's ptr discipline reads it. *)
let arg_ptr_kind_tag : Flag.t Value.Tag.t =
  Value.Tag.register ~package:"hike" ~name:"hike-arg-ptr-kind"
    ~uuid:"3e5a7c19-8b24-4d6f-a0c1-2f9b8e7d6a33"
    (module Flag)

let is_arg_ptr_kind (a : Arg.t) : bool =
  Base.Option.value (Term.get_attr a arg_ptr_kind_tag) ~default:false

let set_arg_ptr_kind (a : Arg.t) : Arg.t =
  Term.set_attr a arg_ptr_kind_tag true

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
