(* Pure stack model: regions, split plan, and escape rules. *)

open Bap.Std
open Bap.Std.Bil.Types
open Bap_core_theory
module Abi = Hike_abi

(* Derives SP/FP from the target. *)
let fp_of (target : Theory.Target.t) : var option =
  if Theory.Target.is_unknown target then None
  else
    match Abi.fp target with
    | v -> Some v
    | exception _ -> None

let is_sp_or_fp (sp : var) (target : Theory.Target.t) (v : var) : bool =
  Var.same (Var.base v) (Var.base sp)
  ||
  match fp_of target with
  | Some fp -> Var.same (Var.base v) (Var.base fp)
  | None -> false

let addr_of_rhs (e : exp) : (exp * Size.t) option =
  match e with
  | Bil.Load (_, a, _, s) | Bil.Store (_, a, _, _, s) -> Some (a, s)
  | Bil.Cast (_, _, Bil.Load (_, a, _, s))
  | Bil.Cast (_, _, Bil.Store (_, a, _, _, s)) -> Some (a, s)
  | _ -> None

(* Splits a store rhs into data and cast wrapper. *)
let store_data_of_rhs (e : exp) : (exp * (exp -> exp)) option =
  match e with
  | Bil.Store (_, _, data, _, _) -> Some (data, fun x -> x)
  | Bil.Cast (c, w, Bil.Store (_, _, data, _, _)) ->
      Some (data, fun x -> Bil.Cast (c, w, x))
  | _ -> None

let slot_of (lo : int64) (bits : int) : var =
  Var.create ~is_virtual:false ~fresh:false
    (Printf.sprintf "slot_%Ld" (Int64.abs lo))
    (Type.Imm bits)

(* Region memory and base vars. *)
let region_mem (id : int) : var =
  Var.create ~is_virtual:false ~fresh:false
    (Printf.sprintf "stack_r%d_mem" id)
    (Type.Mem (Size.addr_of_int_exn 64, Size.of_int_exn 8))

let region_base (id : int) : var =
  Var.create ~is_virtual:false ~fresh:false
    (Printf.sprintf "stack_r%d_base" id) (Type.Imm 64)

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

let sp_escaped (sp : var) (target : Theory.Target.t) (sub : sub term) :
  bool =
  let base_var v = Var.base v in
  let sp_base = base_var sp in
  let fp_bases =
    match fp_of target with Some fp -> [ base_var fp ] | None -> []
  in
  (* Vars derived via arithmetic, excluding loads. *)
  let derived : Var.Set.t ref =
    ref (Var.Set.of_list (sp_base :: fp_bases))
  in
  let is_memory_shape (e : exp) : bool =
    (* Tests for Load/Store in rhs. *)
    let vis =
      object
        inherit [ bool ] Exp.visitor
        method! visit_load ~mem:_ ~addr:_ _ _ acc = acc || true
        method! visit_store ~mem:_ ~addr:_ ~exp:_ _ _ acc = acc || true
      end
    in
    vis#visit_exp e false
  in
  let rec grow () =
    let changed = ref false in
    Term.enum blk_t sub
    |> Seq.iter ~f:(fun blk ->
        Term.enum def_t blk
        |> Seq.iter ~f:(fun d ->
            let rhs = Def.rhs d in
            if not (is_memory_shape rhs) then begin
              let uses = Exp.free_vars rhs in
              if
                Core.Set.exists uses ~f:(fun v ->
                    Core.Set.mem !derived (base_var v))
              then begin
                let lhs = base_var (Def.lhs d) in
                if not (Core.Set.mem !derived lhs) then (
                  derived := Core.Set.add !derived lhs;
                  changed := true)
              end
            end));
    if !changed then grow () else ()
  in
  grow ();
  (* Derived values escape via call args, stored data, or indirect targets. *)
  (* Free vars of the computed value. *)
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
    (* Only argument-register defs count. *)
    let is_arg_reg (v : var) : bool =
      Base.List.exists (Abi.param_regs target)
        ~f:(fun r -> Var.same r (base_var v))
    in
    Term.enum blk_t sub
    |> Seq.exists ~f:(fun blk ->
        let has_call =
          Term.enum jmp_t blk
          |> Seq.exists ~f:is_real_call
        in
        if not has_call then false
        else
          Term.enum def_t blk
          |> Seq.exists ~f:(fun d ->
              is_arg_reg (Def.lhs d)
              && not (is_memory_shape (Def.rhs d))
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
            match store_data_of_rhs (Def.rhs d) with
            | Some (data, _) ->
                if exp_escapes data then
                  match addr_of_rhs (Def.rhs d) with
                  | Some (addr, _) ->
                      let bare_sp =
                        match addr with
                        | Bil.Var v -> Var.same (base_var v) sp_base
                        | _ -> false
                      in
                      not bare_sp
                  | None -> false
                else false
            | None -> false))
  in
  call_arg_escapes || store_data_escapes

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
  let overlap (lo1 : int64) (hi1 : int64) (lo2 : int64) (hi2 : int64) :
      bool =
    Int64.compare lo1 hi2 <= 0 && Int64.compare lo2 hi1 <= 0
  in
  let ranges_overlap ((lo1, hi1) : int64 * int64)
      ((lo2, hi2) : int64 * int64) : bool =
    overlap lo1 hi1 lo2 hi2
  in
  let def_of_tid : def term Tid.Map.t =
    Term.enum blk_t sub
    |> Seq.fold ~init:Tid.Map.empty ~f:(fun m blk ->
           Term.enum def_t blk
           |> Seq.fold ~init:m ~f:(fun m d ->
                  Core.Map.set m ~key:(Term.tid d) ~data:d))
  in
  let def_width : int Tid.Map.t =
    Term.enum blk_t sub
    |> Seq.fold ~init:Tid.Map.empty ~f:(fun m blk ->
           Term.enum def_t blk
           |> Seq.fold ~init:m ~f:(fun m d ->
                  match addr_of_rhs (Def.rhs d) with
                  | Some (_, s) ->
                      Core.Map.set m ~key:(Term.tid d) ~data:(Size.in_bits s)
                  | None -> m))
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
    match store_data_of_rhs (Def.rhs d) with
    | Some (_data, _) -> (
        match addr_of_rhs (Def.rhs d) with
        | Some (addr, _) ->
            let rsp_rel =
              Exp.free_vars addr
              |> Core.Set.exists ~f:(Abi.is_sp_t target)
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
    | None -> false
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
  (* Escaped frame addresses stay in the model frame. *)
  (* Tests for [sp/fp +- const] addresses. *)
  let rec is_direct_const_addr ~(sp : var) ~(target : Theory.Target.t) (addr : exp) : bool =
    let base_var v = Var.base v in
    let is_base v = is_sp_or_fp sp target (base_var v) in
    match addr with
    | Bil.Int _ -> true
    | Bil.Var v -> is_base v
    | Bil.BinOp ((Bil.PLUS | Bil.MINUS), Bil.Var v, Bil.Int _)
    | Bil.BinOp ((Bil.PLUS | Bil.MINUS), Bil.Int _, Bil.Var v) ->
        is_base v
    | Bil.Cast (_, _, e) -> is_direct_const_addr ~sp ~target e
    | _ -> false
  in
  let components : (tid * (int64 * int64)) list list =
    let items : (tid * (int64 * int64)) list = Core.Map.to_alist ranges in
    (* Merges overlapping components to fixpoint. *)
    let components_overlap (c1 : (tid * (int64 * int64)) list)
        (c2 : (tid * (int64 * int64)) list) : bool =
      Base.List.exists c1 ~f:(fun (_, r1) ->
          Base.List.exists c2 ~f:(fun (_, r2) -> ranges_overlap r1 r2))
    in
    let rec merge_loop comps =
      let n = List.length comps in
      let rec find_pair i =
        if i >= n then None
        else
          let ci = List.nth comps i in
          let rec find_j j =
            if j >= n then find_pair (i + 1)
            else if i = j then find_j (j + 1)
            else
              let cj = List.nth comps j in
              if components_overlap ci cj then Some (i, j) else find_j (j + 1)
          in
          find_j (i + 1)
      in
      match find_pair 0 with
      | None -> comps
      | Some (i, j) ->
          let ci = List.nth comps i and cj = List.nth comps j in
          let merged = ci @ cj in
          let comps' =
            Base.List.filteri comps ~f:(fun k _ -> k <> i && k <> j)
          in
          merge_loop (merged :: comps')
    in
    let init = Base.List.map items ~f:(fun x -> [ x ]) in
    merge_loop init
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
                (* Members use direct-constant addresses. *)
                && (match Core.Map.find def_of_tid mtid with
                    | Some md ->
                        (match addr_of_rhs (Def.rhs md) with
                         | Some (addr, _) ->
                             let ok = is_direct_const_addr ~sp ~target addr in
#ifdef VSA_DEBUG
                             if not ok then
                               Printf.eprintf "hike:   member %s NOT direct: addr=%s\n"
                                 (Tid.name mtid)
                                 (Format.asprintf "%a" Exp.pp addr);
#endif
                             ok
                         | None -> true)
                    | None -> true)) in
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
            (* Escape is a per-region rule. *)
            && not frame_escaped
      in
      let max_width =
        Base.List.fold_left members ~init:0 ~f:(fun m (mtid, _) ->
            Int.max m
              (Option.value ~default:64 (Core.Map.find def_width mtid)))
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

(* Tests for SP/FP-derived memory accesses. *)

(* Tests for SP/FP references. *)
let rec exp_contains_sp (sp : var) (target : Theory.Target.t) (e : exp) :
    bool =
  match e with
  | Bil.Var v -> is_sp_or_fp sp target v
  | Bil.BinOp (_, a, b) ->
      exp_contains_sp sp target a || exp_contains_sp sp target b
  | Bil.UnOp (_, a) -> exp_contains_sp sp target a
  | Bil.Cast (_, _, a) -> exp_contains_sp sp target a
  | Bil.Extract (_, _, a) -> exp_contains_sp sp target a
  | Bil.Concat (a, b) ->
      exp_contains_sp sp target a || exp_contains_sp sp target b
  | Bil.Let (_, a, b) ->
      exp_contains_sp sp target a || exp_contains_sp sp target b
  | Bil.Ite (c, a, b) ->
      exp_contains_sp sp target c
      || exp_contains_sp sp target a
      || exp_contains_sp sp target b
  | Bil.Load (_, a, _, _) | Bil.Store (_, a, _, _, _) ->
      exp_contains_sp sp target a
  | _ -> false

let is_stack_mem (sp : var) (target : Theory.Target.t) (e : exp) : bool =
  match e with
  | Bil.Load (_, a, _, _)
  | Bil.Store (_, a, _, _, _)
  | Bil.Cast (_, _, Bil.Load (_, a, _, _))
  | Bil.Cast (_, _, Bil.Store (_, a, _, _, _)) ->
      exp_contains_sp sp target a
  | _ -> false

let frame_value_def (sp : var) (target : Theory.Target.t) (d : def term) :
    bool =
  let lhs = Def.lhs d in
  (not (Convutils.is_mem lhs))
  && (not (is_sp_or_fp sp target lhs))
  && exp_contains_sp sp target (Def.rhs d)

let rec var_maybe_addr (env : exp Var.Map.t) (sp : var)
    (target : Theory.Target.t) (v : var) (e : exp) : bool =
  match e with
  | Bil.Var w ->
      (is_sp_or_fp sp target w && is_sp_or_fp sp target v)
      || Var.same (Var.base w) (Var.base v)
      ||
      (match Core.Map.find env (Var.base w) with
      | Some e' -> var_maybe_addr env sp target v e'
      | None -> false)
  | Bil.Ite (_, t, f) ->
      var_maybe_addr env sp target v t
      || var_maybe_addr env sp target v f
  | Bil.Let (x, e1, e2) ->
      let env' = Core.Map.set env ~key:x ~data:e1 in
      var_maybe_addr env' sp target v e2
  | Bil.Cast (_, _, e') | Bil.Extract (_, _, e') ->
      var_maybe_addr env sp target v e'
  | _ -> false

(* Tests for reads through a materialized frame pointer. *)
let frame_addr_alias (sp : var) (target : Theory.Target.t) (sub : sub term) :
    bool =
  let defs =
    Term.enum blk_t sub |> Seq.concat_map ~f:(Term.enum def_t) |> Seq.to_list
  in
  Base.List.exists defs ~f:(fun d ->
      frame_value_def sp target d
      &&
      let v = Def.lhs d in
      Base.List.exists defs ~f:(fun d2 ->
          match addr_of_rhs (Def.rhs d2) with
          | Some (addr, _) -> var_maybe_addr Var.Map.empty sp target v addr
          | None -> false))

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

(* Tests for unboundable stack accesses. *)
let has_unbounded_access (sp : var) (target : Theory.Target.t) (sub : sub term)
    (info : Convutils.vsa_info) : bool =
  Term.enum blk_t sub
  |> Seq.exists ~f:(fun blk ->
         Term.enum def_t blk
         |> Seq.exists ~f:(fun d ->
                is_stack_mem sp target (Def.rhs d)
                &&
                match Core.Map.find info.Convutils.offsets (Term.tid d) with
                | None -> true
                | Some (Convutils.Infinite _) -> true
                | Some Convutils.Unbounded -> true
                | Some (Convutils.VLA _) -> true
                | Some Convutils.Dead -> false
                | Some (Convutils.Range _) -> false))

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

(* Tests whether the frame is reachable from outside. *)
let frame_escapes (sp : var) (target : Theory.Target.t) (sub : sub term) :
    bool =
  sp_escaped sp target sub || frame_addr_alias sp target sub

(* Returns split regions, or [[]] for fallback. *)
let split_plan (sp : var) (target : Theory.Target.t) (sub : sub term)
    (info : Convutils.vsa_info) : Convutils.split_plan =
  if info.Convutils.degraded then []
  else if has_unbounded_access sp target sub info then []
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


