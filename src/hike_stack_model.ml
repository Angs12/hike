(* Pure stack model: the overlap partition and the region facts.

   THE MODEL IS THE TAG (ADR 0008): the VSA tags every frame-resident access
   with its proven offset span.  This module merges overlapping spans into
   regions and derives each region's facts from those tags + the producer-side
   escape fact ([vsa_info.frame_escaped]).  The escape analysis (sp_escaped,
   frame_addr_alias, frame_escapes) is restored as private helpers for the
   producer-fix repair: [hike_vsa] computes the field ONCE per sub; downstream
   consumers read it, never recompute.  A region's storage class is the join
   of its members' tag facts (Static/Frame/Dynamic/Dead) AND the escape veto
   (if the frame escapes, ALL regions stay Frame — the callee's access through
   an escaped frame pointer is untaggable in principle).  An oversized region
   joins to Frame with a diagnostic naming it — never a gate. *)

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

(* ---------- Escape analysis (producer-side, ADR 0008) ----------
   Restored for the producer-fix repair: the escape fact is computed ONCE in
   hike_vsa and travels as [vsa_info.frame_escaped].  No STL gate reads it;
   [regions_of_sub] reads the field to veto conversion on escaped frames.

   The callee's access through an escaped frame pointer is untaggable in
   principle (the pointer is TOP in the callee's sub); the caller is the
   only sub holding the information. *)

(* Tests for a memory node in rhs. *)
let is_memory_shape (e : exp) : bool =
  let vis =
    object
      inherit [ bool ] Exp.visitor
      method! visit_load ~mem:_ ~addr:_ _ _ _ = true
      method! visit_store ~mem:_ ~addr:_ ~exp:_ _ _ _ = true
    end
  in
  vis#visit_exp e false

(* Per-def facts, extracted once: escape and alias walkers query these. *)
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

let is_real_call (j : jmp term) : bool =
  match Jmp.kind j with
  | Call c -> (
      match Call.target c with
      | Direct _ -> true
      | Indirect _ -> Option.is_some (Call.return c))
  | _ -> false

(* {SP}-seeded syntactic closure: any non-memory def whose rhs mentions a
   derived var adds its lhs to the closure.  Then test whether a
   frame-derived value escapes through call-arg registers or store data.
   fp is NOT seeded (ADR 0008): RBP joins only via its own defs. *)
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

(* Tag-gated read-through-derived-var test: an UNTAGGED memory access whose
   address mentions a frame-var vetoes conversion; a TAGGED one (the -O0
   prologue's own [RBP - k] stores) is proven frame-resident and needs no
   protection. *)
let frame_addr_alias (sp : var) (_target : Theory.Target.t) (sub : sub term)
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

(* Tests whether a call-tail stack store passes an outgoing stack arg.
   The caller writes pushed arg cells below entry RSP (lo < 0, klo >= 0);
   these denote callee-visible ABI traffic. *)
let has_outgoing_stack_args (sp : var) (target : Theory.Target.t)
    (sub : sub term) (info : Convutils.vsa_info) : bool =
  let abi = Option.value (Abi.of_target_opt target) ~default:Abi.x86_64_sysv in
  let facts = def_facts_of_sub sub in
  let is_stack (d : def term) : bool =
    Core.Map.mem info.Convutils.offsets (Term.tid d)
  in
  let call_tails =
    Term.enum blk_t sub
    |> Seq.fold ~init:[] ~f:(fun acc blk ->
           if Term.enum jmp_t blk |> Seq.exists ~f:is_real_call then
             let defs = Term.enum def_t blk |> Seq.to_list in
             let last =
               Base.List.foldi defs ~init:None ~f:(fun i acc d ->
                   if is_stack d then Some i else acc)
             in
             (defs, last) :: acc
           else acc)
  in
  let outgoing_tail_tids : Tid.Set.t =
    Base.List.fold_left call_tails ~init:Tid.Set.empty
      ~f:(fun acc (defs, last) ->
        match last with
        | Some i ->
            Base.List.take defs i
            |> Base.List.fold_left ~init:acc ~f:(fun acc d ->
                    Core.Set.add acc (Term.tid d))
        | None -> acc)
  in
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
            let lo_neg =
              match Core.Map.find info.Convutils.offsets (Term.tid d) with
              | Some (Convutils.Range (lo, _)) -> Int64.compare lo 0L < 0
              | _ -> false
            in
            let k_pos =
              match Core.Map.find info.Convutils.k_ranges (Term.tid d) with
              | Some (klo, _) -> Int64.compare klo 0L >= 0
              | None -> false
            in
            rsp_rel && lo_neg && k_pos
        | None -> false)
      | None -> false)
  in
  Term.enum blk_t sub
  |> Seq.exists ~f:(fun blk ->
         if Term.enum jmp_t blk |> Seq.exists ~f:is_real_call then
           Term.enum def_t blk
           |> Seq.exists ~f:(fun d ->
                  Core.Set.mem outgoing_tail_tids (Term.tid d)
                  && is_outgoing_store d)
         else false)

(* Tests whether the frame is reachable from outside. *)
let frame_escapes (sp : var) (target : Theory.Target.t) (sub : sub term)
    (info : Convutils.vsa_info) : bool =
  sp_escaped sp target sub
  || frame_addr_alias sp target sub info
  || has_outgoing_stack_args sp target sub info

(* Merges overlapping ranges into regions. *)
let regions_of_sub (sub : sub term) (info : Convutils.vsa_info) :
    Convutils.region list =
  (* The ranges ARE the tags: singleton-span Range members at negative
     offsets are this sub's own proven-constant cells. *)
  let ranges : (int64 * int64) Tid.Map.t =
    Core.Map.filter_map info.Convutils.offsets
      ~f:(fun (kind : Convutils.vsa_kind) ->
        match kind with
        | Convutils.Range (lo, hi) -> Some (lo, hi)
        | Convutils.Infinite _ | Convutils.Unbounded | Convutils.Dead
        | Convutils.VLA _ -> None)
  in
  let facts =
    (* One walk for the widths (the only per-def BIL fact still needed). *)
    Term.enum blk_t sub
    |> Seq.fold ~init:Tid.Map.empty ~f:(fun m blk ->
           Term.enum def_t blk
           |> Seq.fold ~init:m ~f:(fun m d ->
                  match addr_of_rhs (Def.rhs d) with
                  | Some (_, s) ->
                      Core.Map.set m ~key:(Term.tid d)
                        ~data:(Size.in_bits s)
                  | None -> m))
  in
  let def_width_of (mtid : tid) : int =
    match Core.Map.find facts mtid with Some w -> w | None -> 64
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
      (* Storage class, from the tags + the producer-side escape fact:
         - every member at a NEGATIVE offset (this sub owns the cell) and a
           SINGLETON span (the proven offset is constant) → Static;
         - anything else (mixed ownership, a widened span) → Frame.
         The escape veto: if the frame is reachable from outside (a
         frame-derived value passed to a callee), ALL regions stay Frame —
         the callee reads the same physical cell through its own real-stack
         lane, untaggable in principle (ADR 0008, producer-fix repair). *)
      let convertible =
        match members with
        | [] -> false
        | _ ->
            Base.List.for_all members ~f:(fun (_mtid, (lo, hi)) ->
                Int64.compare lo 0L < 0
                && Int64.equal lo hi)
            && not info.Convutils.frame_escaped
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

(* Tests for caller/callee-visible storage: the cross-sub consistency rule.
   [klo >= 0] marks the CALLEE's incoming-arg area — the mirror of the
   [lo >= 0] caller-frame rule — read from the two record facts (offsets +
   k_ranges), per def, never a whole-sub refusal.  The caller writes pushed
   arg cells below its entry RSP (lo < 0, klo >= 0); the callee reads them
   at [RSP + k >= 0] through its own lane: both sides must agree the cell
   is not this sub's to convert. *)
let is_abi_visible ~(tag_of : Convutils.vsa_kind Tid.Map.t)
    ~(k_of : (int64 * int64) Tid.Map.t) (d : def term) : bool =
  match Core.Map.find tag_of (Term.tid d) with
  | Some (Convutils.Range (lo, _)) when Int64.compare lo 0L >= 0 -> true
  | Some (Convutils.Range (lo, _)) -> (
      match Core.Map.find k_of (Term.tid d) with
      | Some (klo, _) when Int64.compare klo 0L >= 0 -> true
      | _ -> false)
  | _ -> false

(* [is_abi_visible] over one sub. *)
let abi_visibility_of (sp : var) (info : Convutils.vsa_info) :
    def term -> bool =
  ignore sp;
  is_abi_visible ~tag_of:info.Convutils.offsets
    ~k_of:info.Convutils.k_ranges


(* Stack model decision. *)

(* Returns the region alloca size. *)
let region_bytes (r : Convutils.region) : int64 =
  let lo, hi = r.Convutils.span in
  let span_len = Int64.add (Int64.sub hi lo) 1L in
  let raw = Int64.div (Int64.mul span_len (Int64.of_int r.Convutils.max_width)) 8L in
  let raw = if Int64.compare raw 0L <= 0 then 1L else raw in
  let r = Int64.rem raw 16L in
  if Int64.equal r 0L then raw else Int64.add raw (Int64.sub 16L r)

(* A region whose alloca would exceed the cap joins to Frame (the sound
   fallback storage — Static ⊔ Frame = Frame, per the storage-class
   lattice); the diagnostic names it.  A rule, never a gate: the OTHER
   regions still convert. *)
let region_max_bytes : int64 = 67108864L

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

(* The emission-shape switch: does this sub split into region allocas
   (plan non-empty) or emit one %frame?  A derived view of the record —
   plan <> [] — consumed by the emitter (region-allocas vs %frame, SP
   erase/keep, call-restore suppression) and DCE's precise sweep. *)
let is_precise (info : Convutils.vsa_info) : bool = info.Convutils.stack_plan <> []

(* The stack plan IS the convertible regions.  No refusals: the plan is the
   partition's Static-class components; a sub with no convertible regions
   has an empty plan and emits one %frame.  An oversized region joins to
   Frame storage with a diagnostic naming it (the sanctioned channel; the
   corpus table greps these). *)
let split_plan (sub : sub term) (info : Convutils.vsa_info) :
    Convutils.split_plan =
  let regions =
    if info.Convutils.regions <> [] then info.Convutils.regions
    else regions_of_sub sub info
  in
  Base.List.filter regions ~f:(fun r ->
      r.Convutils.convertible
      &&
      let b = region_bytes r in
      if Int64.compare b region_max_bytes > 0 then begin
        Hike_diag.warn
          "region: sub %s: region %d span=(%Ld,%Ld) implies %Ld-byte alloca (cap %Ld) — storage Frame"
          (Sub.name sub) r.Convutils.id
          (fst r.Convutils.span) (snd r.Convutils.span)
          b region_max_bytes;
        false
      end
      else true)
