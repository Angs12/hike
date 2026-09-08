(* Pure stack model: regions and the split plan.

   THE MODEL IS THE TAG (ADR 0008): the VSA tags every frame-resident access
   with its proven offset span, and this module only merges overlapping spans
   into regions and decides conversion.  There is NO shape test for
   stack-ness anywhere in this file — an access is a stack access iff it is
   tagged, and a sub converts a cell iff the cell's tag is owned by the sub
   (a negative offset; a positive offset denotes the caller's frame). *)

open Bap.Std
open Bap.Std.Bil.Types
open Bap_core_theory
module Abi = Hike_abi

(* Stack pointer only: the one register granted stack semantics by fiat
   (ADR 0008).  There is no frame-pointer fact here — fp is an ordinary
   callee-saved GPR whose stack-ness, like any register's, is proven by the
   VSA (its frame term), never by name. *)


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

(* Stored data of a store rhs (no wrapper closure; the model never
   rewrites, only tests). *)
let store_data_exp_of_rhs (e : exp) : exp option =
  let vis =
    object
      inherit [ exp option ] Exp.visitor
      method! visit_store ~mem:_ ~addr:_ ~exp:data _ _ acc =
        Base.Option.first_some acc (Some data)
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

let slot_of (lo : int64) (bits : int) : var =
  Var.create ~is_virtual:false ~fresh:false
    (Printf.sprintf "slot_%Ld" (Int64.abs lo))
    (Type.Imm bits)

(* Region memory and base vars; the alloca's emitted name. *)
let region_name (id : int) : string = Printf.sprintf "stack_r%d" id

let region_mem (id : int) : var =
  Var.create ~is_virtual:false ~fresh:false
    (region_name id ^ "_mem")
    (Type.Mem (Size.addr_of_int_exn 64, Size.of_int_exn 8))

let region_base (id : int) : var =
  Var.create ~is_virtual:false ~fresh:false
    (region_name id ^ "_base") (Type.Imm 64)

(* Tests for fission var names. *)
let is_region_mem (v : var) : bool =
  Base.String.is_prefix (Var.name v) ~prefix:"stack_r"
  && Base.String.is_suffix (Var.name v) ~suffix:"_mem"

let is_region_base (v : var) : bool =
  Base.String.is_prefix (Var.name v) ~prefix:"stack_r"
  && Base.String.is_suffix (Var.name v) ~suffix:"_base"

(* Tests for incoming-arg saves. *)
let saves_incoming_reg (abi : Abi.t) (d : def term) : bool =
  let param_regs = abi.Abi.int_param_regs @ abi.Abi.vector_param_regs in
  match Def.rhs d with
  | Bil.Store (_, _, data, _, _) -> (
      match data with
      | Bil.Var v ->
          Base.List.exists param_regs
            ~f:(fun r -> Var.same r (Var.base v))
      | _ -> false)
  | _ -> false


let is_real_call (j : jmp term) : bool =
  match Jmp.kind j with
  | Call c -> (
      match Call.target c with
      | Direct _ -> true
      | Indirect _ -> Option.is_some (Call.return c))
  | _ -> false

(* Tests whether a frame address escapes. *)

(* Shared walk: per call block, the def list with the last stack def's
   index. Both positional rules below are complements of it. Stack-ness is
   [vsa_info] membership (spec §2.2); callers pass the predicate. *)
let call_block_stack_tails ~(is_stack : def term -> bool) (sub : sub term) :
    (def term list * int option) list =
  Term.enum blk_t sub
  |> Seq.fold ~init:[] ~f:(fun acc blk ->
         if
           Term.enum jmp_t blk
           |> Seq.exists ~f:is_real_call
         then
           let defs = Term.enum def_t blk |> Seq.to_list in
           let last =
             Base.List.foldi defs ~init:None ~f:(fun i acc d ->
                 if is_stack d then Some i else acc)
           in
           (defs, last) :: acc
         else acc)

(* Last stack def per call block. *)
let last_push_tids_of ~(is_stack : def term -> bool) (sub : sub term) :
    Tid.Set.t =
  Base.List.fold_left (call_block_stack_tails ~is_stack sub) ~init:Tid.Set.empty
    ~f:(fun acc (defs, last) ->
      match last with
      | Some i -> Core.Set.add acc (Term.tid (Base.List.nth_exn defs i))
      | None -> acc)

(* Tests for a memory node in rhs (no accumulator games). *)
let is_memory_shape (e : exp) : bool =
  let vis =
    object
      inherit [ bool ] Exp.visitor
      method! visit_load ~mem:_ ~addr:_ _ _ _ = true
      method! visit_store ~mem:_ ~addr:_ ~exp:_ _ _ _ = true
    end
  in
  vis#visit_exp e false

(* Per-def facts, extracted once per pass entry: every consumer below used
   to re-walk the same defs with addr_of_rhs / store_data_of_rhs /
   is_memory_shape / Exp.free_vars (six consumers on one sub). *)
type def_facts = {
  def : def term;
  addr : (exp * Size.t) option;
  store_data : exp option;
  mem_shape : bool;
  free_vars : Var.Set.t;
}

let def_facts_of_sub (sub : sub term) : def_facts Tid.Map.t =
  Term.enum blk_t sub
  |> Seq.fold ~init:Tid.Map.empty ~f:(fun m blk ->
         Term.enum def_t blk
         |> Seq.fold ~init:m ~f:(fun m d ->
                let rhs = Def.rhs d in
                Core.Map.set m ~key:(Term.tid d)
                  ~data:
                    {
                      def = d;
                      addr = addr_of_rhs rhs;
                      store_data = store_data_exp_of_rhs rhs;
                      mem_shape = is_memory_shape rhs;
                      free_vars = Exp.free_vars rhs;
                    }))

(* Frame-escape analysis.  Load-bearing (measured 2026-09-08: deleting it
   lost rec_struct and sret_big — the callee's walk through an escaped
   frame pointer is untaggable IN PRINCIPLE, because the pointer is TOP in
   the callee's sub; the caller is the only sub holding the information).
   Mechanism: the {SP}-seeded syntactic closure over def values, NOT a
   frame-term lookup — terms UNDER-approximate (RAX := RSP - mem[x] has no
   term yet is sp-derived at runtime), and for escape missing an alias is
   the unsound direction, so over-approximating is mandatory.  fp is NOT
   seeded: RBP joins only via its own defs (the -O0 prologue's RBP := RSP);
   a heap-valued RBP escapes nothing (ADR 0008). *)
let sp_escaped (sp : var) (target : Theory.Target.t) (sub : sub term) :
    bool =
  let base_var v = Var.base v in
  let sp_base = base_var sp in
  let derived : Var.Set.t ref = ref (Var.Set.of_list [ sp_base ]) in
  let facts = def_facts_of_sub sub in
  let rec grow () =
    let changed = ref false in
    Core.Map.iter facts ~f:(fun f ->
        let d = f.def in
        if not f.mem_shape then begin
          let uses = f.free_vars in
          if
            Core.Set.exists uses ~f:(fun v ->
                Core.Set.mem !derived (base_var v))
          then begin
            let lhs = base_var (Def.lhs d) in
            if not (Core.Set.mem !derived lhs) then (
              derived := Core.Set.add !derived lhs;
              changed := true)
          end
        end);
    if !changed then grow () else ()
  in
  grow ();
  let arg_regs = lazy (Abi.param_regs target) in
  let rec value_free_vars (e : exp) : Var.Set.t =
    let vis =
      object
        inherit [ Var.Set.t ] Exp.visitor
        method! visit_var v acc = Core.Set.add acc (base_var v)
        method! visit_load ~mem:_ ~addr:_ _ _ acc = acc
        method! visit_store ~mem:_ ~addr:_ ~exp:data _ _ acc =
          Core.Set.union acc (value_free_vars data)
      end
    in
    vis#visit_exp e Var.Set.empty
  in
  let exp_escapes (e : exp) : bool =
    Core.Set.exists (value_free_vars e) ~f:(fun v ->
        Core.Set.mem !derived (base_var v))
  in
  let call_arg_escapes =
    let is_arg_reg (v : var) : bool =
      Base.List.exists (Lazy.force arg_regs)
        ~f:(fun r -> Var.same r (base_var v))
    in
    Term.enum blk_t sub
    |> Seq.exists ~f:(fun blk ->
        let has_call =
          Term.enum jmp_t blk |> Seq.exists ~f:is_real_call
        in
        if not has_call then false
        else
          Term.enum def_t blk
          |> Seq.exists ~f:(fun d ->
              match Core.Map.find facts (Term.tid d) with
              | None -> false
              | Some f ->
                is_arg_reg (Def.lhs d)
                && not f.mem_shape
                && exp_escapes (Def.rhs d))
          || (Term.enum jmp_t blk
              |> Seq.exists ~f:(fun j ->
                  match Jmp.kind j with
                  | Call c -> (
                      match Call.target c with
                      | Indirect e -> exp_escapes e
                      | _ -> false)
                  | _ -> false)))
  in
  let store_data_escapes =
    Term.enum blk_t sub
    |> Seq.exists ~f:(fun blk ->
        Term.enum def_t blk
        |> Seq.exists ~f:(fun d ->
            match Core.Map.find facts (Term.tid d) with
            | None -> false
            | Some f -> (
                match f.store_data with
                | Some data ->
                    if exp_escapes data then
                      match f.addr with
                      | Some (addr, _) ->
                          let bare_sp =
                            match addr with
                            | Bil.Var v -> Var.same (base_var v) sp_base
                            | _ -> false
                          in
                          not bare_sp
                      | None -> false
                    else false
                | None -> false)))
  in
  call_arg_escapes || store_data_escapes

(* Tests for reads through a materialized frame address (the value-closure
   half: a var holding a derived value, and any memory address mentioning
   it — frame_addr_alias).  lhs ∉ derived keeps the -O0 prologue's
   RBP := RSP from counting (RBP is in the closure, so excluded). *)
let frame_addr_alias (sp : var) (target : Theory.Target.t) (sub : sub term)
    (info : Convutils.vsa_info) : bool =
  let facts = def_facts_of_sub sub in
  let derived : Var.Set.t ref =
    ref (Var.Set.of_list [ Var.base sp ])
  in
  let rec grow () =
    let changed = ref false in
    Core.Map.iter facts ~f:(fun f ->
        let d = f.def in
        if not f.mem_shape then begin
          let uses = f.free_vars in
          if
            Core.Set.exists uses ~f:(fun v ->
                Core.Set.mem !derived (Var.base v))
          then begin
            let lhs = Var.base (Def.lhs d) in
            if not (Core.Set.mem !derived lhs) then (
              derived := Core.Set.add !derived lhs;
              changed := true)
          end
        end);
    if !changed then grow () else ()
  in
  grow ();
  (* Frame-value vars: non-memory, non-sp lhs whose rhs mentions a derived
     var — vars that MIGHT hold a frame address.  A read through such a var
     aliases the frame only when that access is UNTAGGED: a TAGGED access
     through a derived base (the -O0 prologue's own [RBP - k] stores — RBP
     is a closure member) is proven frame-resident by the VSA and needs no
     alias protection; an UNTAGGED one ([mem[v]] with v := RSP — the
     bare-copy class) is invisible to the tags and must veto conversion. *)
  let frame_vars =
    Core.Map.filter facts ~f:(fun f ->
        let lhs = Var.base (Def.lhs f.def) in
        (not (Convutils.is_mem (Def.lhs f.def)))
        && not (Var.same lhs (Var.base sp))
        && Core.Set.exists f.free_vars ~f:(fun v ->
              Core.Set.mem !derived (Var.base v)))
    |> Core.Map.fold ~init:Var.Set.empty
         ~f:(fun ~key:_ ~data:f acc ->
           Core.Set.add acc (Var.base (Def.lhs f.def)))
  in
  if Core.Set.is_empty frame_vars then false
  else
    Core.Map.exists facts ~f:(fun f ->
        let untagged =
          match Core.Map.find info.Convutils.offsets (Term.tid f.def) with
          | None -> true
          | Some (Convutils.Range _ | Convutils.Dead) -> false
          | Some (Convutils.Infinite _ | Convutils.Unbounded
                  | Convutils.VLA _) -> true
        in
        untagged
        &&
        (match f.addr with
         | Some (addr, _) ->
             Core.Set.exists (Exp.free_vars addr) ~f:(fun v ->
                 Core.Set.mem frame_vars (Var.base v))
         | None -> false))

(* Tests whether the frame is reachable from outside. *)
let frame_escapes (sp : var) (target : Theory.Target.t) (sub : sub term)
    (info : Convutils.vsa_info) : bool =
  sp_escaped sp target sub || frame_addr_alias sp target sub info

(* SP-mention test: the syntactic sp disjunct only.  (fp is a GPR; an
   untagged fp-based access emits through the real-address lane.) *)
let is_sp_var (sp : var) (v : var) : bool =
  Var.same (Var.base v) (Var.base sp)

let rec exp_contains_sp (sp : var) (e : exp) : bool =
  match e with
  | Bil.Var v -> is_sp_var sp v
  | Bil.BinOp (_, a, b) -> exp_contains_sp sp a || exp_contains_sp sp b
  | Bil.UnOp (_, a) -> exp_contains_sp sp a
  | Bil.Cast (_, _, a) -> exp_contains_sp sp a
  | Bil.Extract (_, _, a) -> exp_contains_sp sp a
  | Bil.Concat (a, b) -> exp_contains_sp sp a || exp_contains_sp sp b
  | Bil.Let (_, a, b) -> exp_contains_sp sp a || exp_contains_sp sp b
  | Bil.Ite (c, a, b) ->
      exp_contains_sp sp c || exp_contains_sp sp a || exp_contains_sp sp b
  | Bil.Load (_, a, _, _) | Bil.Store (_, a, _, _, _) -> exp_contains_sp sp a
  | _ -> false

(* Merges overlapping ranges into regions. *)
let regions_of_sub (sp : var) (target : Theory.Target.t) (sub : sub term)
    (info : Convutils.vsa_info) ~(frame_escaped : bool) :
    Convutils.region list =
  let k_of = info.Convutils.k_ranges in
  let ranges : (int64 * int64) Tid.Map.t =
    Core.Map.filter_map info.Convutils.offsets
      ~f:(fun (kind : Convutils.vsa_kind) ->
        match kind with
        | Convutils.Range (lo, hi) -> Some (lo, hi)
        | Convutils.Infinite _ | Convutils.Unbounded | Convutils.Dead
        | Convutils.VLA _ -> None)
  in
  let abi =
    (* Falls back to x86_64 SysV on unknown targets. *)
    Option.value (Abi.of_target_opt target) ~default:Abi.x86_64_sysv
  in
  (* One walk builds every per-def fact below (the def map, the widths,
     and the member/outgoing re-walks all read it). *)
  let facts = def_facts_of_sub sub in
  let def_of_tid : def term Tid.Map.t =
    Core.Map.map facts ~f:(fun f -> f.def)
  in
  let def_width_of (mtid : tid) : int =
    match Core.Map.find facts mtid with
    | Some { addr = Some (_, s); _ } -> Size.in_bits s
    | _ -> 64
  in
  (* Call-tail defs are the outgoing-arg area. *)
  (* Tests for calls passing stack args. *)
  let outgoing_tail_tids : Tid.Set.t =
    let is_stack (d : def term) : bool =
      Core.Map.mem info.Convutils.offsets (Term.tid d)
    in
    Base.List.fold_left
      (call_block_stack_tails ~is_stack sub)
      ~init:Tid.Set.empty
      ~f:(fun acc (defs, last) ->
        match last with
        | Some i ->
            Base.List.take defs i
            |> Base.List.fold_left ~init:acc ~f:(fun acc d ->
                    Core.Set.add acc (Term.tid d))
        | None -> acc)
  in
   (* Tests for call-tail stack stores. *)
  (* Tests for RSP-relative stores below entry RSP. *)
  let is_outgoing_store (d : def term) : bool =
    match Core.Map.find facts (Term.tid d) with
    | None -> false
    | Some f -> (
      match f.store_data with
      | Some _ -> (
        match f.addr with
        | Some (addr, _) ->
            let rsp_rel =
              Exp.free_vars addr
              |> Core.Set.exists ~f:(Abi.is_sp abi)
            in
            (* lo<0 and k>=0 marks pushed arg cells. *)
            let lo_neg =
              match Core.Map.find ranges (Term.tid d) with
              | Some (lo, _) -> Int64.compare lo 0L < 0
              | None -> false
            in
            let k_pos =
              match Core.Map.find k_of (Term.tid d) with
              | Some (klo, _) -> Int64.compare klo 0L >= 0
              | None -> false
            in
            rsp_rel && lo_neg && k_pos
        | None -> false)
    | None -> false)
  in
  
  (* Exemption applies at conversion time. *)
  let has_outgoing_stack_args : bool lazy_t =
    lazy
      (Term.enum blk_t sub
      |> Seq.exists ~f:(fun blk ->
             if
               Term.enum jmp_t blk
               |> Seq.exists ~f:is_real_call
             then
               Term.enum def_t blk
               |> Seq.exists ~f:(fun d ->
                      Core.Set.mem outgoing_tail_tids (Term.tid d)
                      && is_outgoing_store d)
             else false))
  in
  (* Directness is a TAG fact, not an address shape: a member is direct iff
     its proven offset span is a SINGLETON — the VSA proved the access sits
     at one constant frame offset (any provable base counts, e.g. a
     hand-assembly R12 frame pointer, not just the named SP/FP). *)
  let is_direct_const_addr ~(ranges : (int64 * int64) Tid.Map.t)
      (mtid : tid) : bool =
    match Core.Map.find ranges mtid with
    | Some (lo, hi) -> Int64.equal lo hi
    | None -> false
  in
  (* Connected components of the interval-overlap graph, by sort-and-sweep:
     sort ascending on (lo, hi, tid); a range joins the current component
     when its lo <= the component's max hi — it then overlaps the member
     holding that max (lo_m <= lo_j holds for all earlier members by the
     sort). The (lo, hi, tid) order fixes member and component order. *)
  let merge_components
      (items : (tid * (int64 * int64)) list)
      : (tid * (int64 * int64)) list list =
    let sorted =
      Base.List.sort items
        ~compare:(fun (t1, (lo1, hi1)) (t2, (lo2, hi2)) ->
          let c = Int64.compare lo1 lo2 in
          if c <> 0 then c
          else
            let c = Int64.compare hi1 hi2 in
            if c <> 0 then c else Tid.compare t1 t2)
    in
    let rec sweep cur max_hi rest =
      match rest with
      | [] -> [ Base.List.rev cur ]
      | ((_, (lo, hi)) as x) :: tl ->
          if Int64.compare lo max_hi <= 0 then
            sweep (x :: cur) (if Int64.compare hi max_hi > 0 then hi else max_hi) tl
          else
            Base.List.rev cur :: sweep [ x ] hi tl
    in
    match sorted with
    | [] -> []
    | ((_, (_, hi0)) as x0) :: tl -> sweep [ x0 ] hi0 tl
  in
  let components : (tid * (int64 * int64)) list list =
    merge_components (Core.Map.to_alist ranges)
  in
  Base.List.foldi components ~init:[] ~f:(fun i acc members ->
      let span =
        match members with
        | [] -> (0L, 0L)
        | (_, (lo0, hi0)) :: rest ->
            Base.List.fold_left rest ~init:(lo0, hi0)
              ~f:(fun (l, h) (_, (lo, hi)) ->
                (Int64.min l lo, Int64.max h hi))
      in
      let convertible =
        match members with
        | [] -> false
        | _ ->
            let res = Base.List.for_all members ~f:(fun (mtid, (lo, _)) ->
                Int64.compare lo 0L < 0
                && (match Core.Map.find def_of_tid mtid with
                    | Some md -> not (saves_incoming_reg abi md)
                    | None -> true)
                (* Members sit at proven constant offsets. *)
                && is_direct_const_addr ~ranges mtid) in
#ifdef VSA_DEBUG
            if not res then (
              let lo0, hi0 = span in
              Printf.eprintf "hike: region %d span=(%Ld,%Ld) NOT convertible: members=%d\n" i lo0 hi0 (List.length members);
              Printf.eprintf "hike:   (sub %s)\n" (Sub.name sub);
              Base.List.iter members ~f:(fun (mtid, (lo, hi)) ->
                  let k_str = match Core.Map.find k_of mtid with Some (klo, khi) -> Printf.sprintf "(%Ld,%Ld)" klo khi | None -> "None" in
                  let saves = match Core.Map.find def_of_tid mtid with Some md -> saves_incoming_reg abi md | None -> false in
                  Printf.eprintf "hike:   member %s (%Ld,%Ld) k=%s saves=%b\n" (Tid.name mtid) lo hi k_str saves);
            );
#endif
            res
            && not (Lazy.force has_outgoing_stack_args)
            (* Escape is a per-region rule (load-bearing, see sp_escaped). *)
            && not frame_escaped
      in
      let max_width =
        Base.List.fold_left members ~init:0 ~f:(fun m (mtid, _) ->
            Int.max m (def_width_of mtid))
      in
      {
        Convutils.id = i;
        Convutils.span = span;
        Convutils.members = members;
        Convutils.convertible = convertible;
        Convutils.max_width = max_width;
      }
      :: acc)
  |> Base.List.rev

(* Tests for caller/callee-visible storage. *)
let is_abi_visible ?(last_push_tids = Tid.Set.empty) (sp : var)
    ~(tag_of : Convutils.vsa_kind Tid.Map.t)
    ~(k_of : (int64 * int64) Tid.Map.t) (d : def term) : bool =
  if Core.Set.mem last_push_tids (Term.tid d) then false
  else
  match Core.Map.find tag_of (Term.tid d) with
  | Some (Convutils.Range (lo, _)) when Int64.compare lo 0L >= 0 -> true
  | Some (Convutils.Range (lo, _)) -> (
      match Core.Map.find k_of (Term.tid d) with
      | Some (klo, _) when Int64.compare klo 0L >= 0 -> (
          match addr_of_rhs (Def.rhs d) with
          | Some (addr, _) ->
              Exp.free_vars addr
              |> Core.Set.exists ~f:(fun v ->
                     Var.same (Var.base v) (Var.base sp))
          | None -> false)
      | _ -> false)
  | _ -> false

(* [is_abi_visible] over one sub. *)
let abi_visibility_of (sp : var) (info : Convutils.vsa_info) :
    def term -> bool =
  is_abi_visible sp ~tag_of:info.Convutils.offsets ~k_of:info.Convutils.k_ranges


(* Stack model decision. *)








(* Returns the region alloca size. *)
let region_bytes (r : Convutils.region) : int64 =
  let lo, hi = r.Convutils.span in
  let span_len = Int64.add (Int64.sub hi lo) 1L in
  let raw = Int64.div (Int64.mul span_len (Int64.of_int r.Convutils.max_width)) 8L in
  let raw = if Int64.compare raw 0L <= 0 then 1L else raw in
  let r = Int64.rem raw 16L in
  if Int64.equal r 0L then raw else Int64.add raw (Int64.sub 16L r)

(* Tests the region size guard. *)
let region_size_ok (r : Convutils.region) : bool =
  let b = region_bytes r in
  Int64.compare b 0L > 0 && Int64.compare b 67108864L <= 0

(* Rounds a frame size up to 16-byte alignment. *)
let align16_up n =
  let r = Int64.rem n 16L in
  if Int64.equal r 0L then n else Int64.add n (Int64.sub 16L r)

(* Frame-geometry triple: deepest SP decrement (the granted fact: catches
   rsp-sub prologues and VLAs), and the deepest negative and positive
   access extents.  Extents come from the TAGS (ADR 0008): a tagged
   access's proven offset span IS its extent; an untagged access never
   touches the fallback frame (it emits through the real-address lane). *)
let degraded_geometry (sub : sub term)
    (info : Convutils.vsa_info) : int64 * int64 * int64 * bool =
  let is_sp v = Abi.is_sp Abi.x86_64_sysv (Var.base v) in
  let max_dec =
    Term.enum blk_t sub
    |> Seq.fold ~init:0L ~f:(fun acc blk ->
           Term.enum def_t blk
           |> Seq.fold ~init:acc ~f:(fun acc d ->
                 match Def.rhs d with
                 | Bil.BinOp (Bil.MINUS, Bil.Var r, Bil.Int w)
                   when is_sp r ->
                     Int64.max acc (Word.to_int64_exn w)
                 | _ -> acc))
  in
  (* Tagged extents: Range/Infinite spans, Unbounded = the whole frame. *)
  let max_neg, max_pos, has_unbounded =
    Core.Map.fold info.Convutils.offsets
      ~init:(0L, 0L, false)
      ~f:(fun ~key:_ ~data:(kind : Convutils.vsa_kind) (neg, pos, unb) ->
        match kind with
        | Convutils.Range (lo, hi) | Convutils.Infinite (lo, hi) ->
            let neg =
              if Int64.compare lo 0L < 0 then
                Int64.max neg (Int64.neg (Int64.min lo 0L))
              else neg
            in
            let pos =
              if Int64.compare hi 0L > 0 then Int64.max pos hi else pos
            in
            (neg, pos, unb)
        | Convutils.Unbounded -> (neg, pos, true)
        | Convutils.Dead -> (neg, pos, unb)
        | Convutils.VLA _ -> (neg, pos, true))
  in
  (max_dec, max_neg, max_pos, has_unbounded)

(* Tests whether a VLA overlaps a convertible region. *)
let vla_overlaps_convertible (info : Convutils.vsa_info)
    (convertible : Convutils.region list) : bool =
  
  Core.Map.fold info.Convutils.vla_bounds ~init:false
    ~f:(fun ~key:_ ~data:(_lo, hi) acc ->
      acc
      ||
      let max_size = hi in
      if Int64.compare max_size 0L <= 0 then false
      else
        let vla_lo = Int64.neg max_size in
        let vla_hi = -1L in
        Base.List.exists convertible ~f:(fun r ->
            let rlo, rhi = r.Convutils.span in
            not (Int64.compare vla_hi rlo < 0 || Int64.compare vla_lo rhi > 0)))

(* Unbounded stack accesses force the whole-sub fallback.  Two arms, both
   measured load-bearing (the 2026-09-08 deletion experiment lost
   alloca_vla/rec_struct/sret_big/byte_copy/va_arg_mixed):

   - the TAG arm: a tagged Infinite/Unbounded/VLA access needs fallback
     frame bytes (the VLA's dynamic-RSP traffic writes below the frame);
   - the SP arm: an UNTAGGED access whose address mentions sp writes
     through the model sp lane into the fallback frame — its extent is
     unproven, so the sub must not split.  (fp needs no arm: an untagged
     fp-based access emits through the real-address lane.) *)
let has_unbounded_access (sp : var) (sub : sub term)
    (info : Convutils.vsa_info) : bool =
  Term.enum blk_t sub
  |> Seq.exists ~f:(fun blk ->
      Term.enum def_t blk
      |> Seq.exists ~f:(fun d ->
             let tag_unbounded =
               match Core.Map.find info.Convutils.offsets (Term.tid d) with
               | Some (Convutils.Infinite _) -> true
               | Some Convutils.Unbounded -> true
               | Some (Convutils.VLA _) -> true
               | Some Convutils.Dead -> false
               | Some (Convutils.Range _) -> false
               | None -> false
             in
             (* The SP arm fires only on an UNTAGGED sp-mentioning
                access: a tagged access's fallback needs are decided by
                its tag (the tag arm); an untagged one writes through the
                model sp lane at an unproven extent. *)
             let untagged = function
               | None -> true
               | Some (Convutils.Infinite _ | Convutils.Unbounded
                       | Convutils.VLA _) -> true
               | Some (Convutils.Range _ | Convutils.Dead) -> false
             in
             let sp_lane_unproven =
               untagged
                 (Core.Map.find info.Convutils.offsets (Term.tid d))
               &&
               (match addr_of_rhs (Def.rhs d) with
                | Some (a, _) -> exp_contains_sp sp a
                | None -> false)
             in
             tag_unbounded || sp_lane_unproven))

(* Tests that tags resolve inside convertible regions. *)
let tags_inside_or_disjoint (info : Convutils.vsa_info)
    (convertible : Convutils.region list) : bool =
  Core.Map.for_all info.Convutils.offsets ~f:(fun (kind : Convutils.vsa_kind) ->
      match kind with
      | Convutils.Infinite _ | Convutils.Unbounded -> false
      | Convutils.Dead -> true
      | Convutils.VLA _ -> false
      | Convutils.Range (lo, hi) ->
          let inside =
            Base.List.exists convertible ~f:(fun r ->
                let rlo, rhi = r.Convutils.span in
                Int64.compare lo rlo >= 0 && Int64.compare hi rhi <= 0)
          in
          let disjoint =
            Base.List.for_all convertible ~f:(fun r ->
                let rlo, rhi = r.Convutils.span in
                Int64.compare hi rlo < 0 || Int64.compare lo rhi > 0)
          in
          if Int64.compare lo 0L < 0 then inside else inside || disjoint)

(* Returns split regions, or [[]] for fallback. *)
let split_plan (sp : var) (target : Theory.Target.t) (sub : sub term)
    (info : Convutils.vsa_info) ~(frame_escaped : bool) :
    Convutils.split_plan =
  if info.Convutils.degraded then []
  else if has_unbounded_access sp sub info then []
  else if frame_escaped then []
  else
    let regions = info.Convutils.regions in
    let convertible =
      Base.List.filter regions ~f:(fun r -> r.Convutils.convertible)
    in
    if convertible = [] then []
    else
      let should_degrade_vla =
        vla_overlaps_convertible info convertible
        || (not (Core.Set.is_empty info.Convutils.vla_alloc_tids)
           && Core.Map.is_empty info.Convutils.vla_bounds)
      in
      if should_degrade_vla then []
      else if not (tags_inside_or_disjoint info convertible) then []
      else if not (Base.List.for_all convertible ~f:region_size_ok) then []
      else convertible

(* Tests for the split model. *)
let is_precise (info : Convutils.vsa_info) : bool = info.Convutils.stack_plan <> []


