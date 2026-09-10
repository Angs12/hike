(* Computes per-sub VSA tags via the two-channel frame-residency proof
   (spec §2.2); [vsa_info] is the only carrier of stack-access-ness.

   T4: the record also carries the stack-arg promotion facts — the
   callee's proven incoming slots ([prom_slots]/[prom_arity]), the
   Caller-Window Parameter residual ([prom_window]), the dying
   return-address reads ([prom_retaddr]), the per-site outgoing slot
   stores ([prom_sites]), and the singleton resolution of every
   indirect call ([prom_resolved]).  All of it derives from the ONE
   mechanism — the solution's denotations — never a second channel. *)

open Bap.Std
open Bap_core_theory
module Vsa = Cbat_vsa
module Model = Hike_stack_model

(* Forwards the address width into the VSA. *)
let set_addr_bits (n : int) : unit = Vsa.set_addr_bits n

(* [ws] is a single known word. *)
let singleton_i64 (ws : Vsa.WordSet.t) : int64 option =
  if Vsa.WordSet.is_top ws then None
  else
    match Vsa.WordSet.min_elem ws, Vsa.WordSet.max_elem ws with
    | Some lo, Some hi -> (
        match Cbat_word.to_int64 lo, Cbat_word.to_int64 hi with
        | Ok a, Ok b when Int64.equal a b -> Some a
        | _ -> None)
    | _ -> None

(* The segment-relative offset of [e] in [st], when it is a single
   known stack word (the offset-space twin of the denotation). *)
let singleton_stack_offset (e : exp) (st : Vsa.AI.t) : int64 option =
  match Vsa.denote_imm_exp e st with
  | Error _ -> None
  | Ok ws -> (
      match Vsa.Cbat_extraction.relativize_opt ws with
      | Some rel -> singleton_i64 rel
      | None -> None)

(* The def's memory node is a LOAD of (addr, size); stores are not. *)
let load_of_rhs (e : exp) : (exp * Size.t) option =
  match Model.addr_of_rhs e with
  | Some (addr, size) ->
      if Option.is_some (Model.store_data_of_rhs e) then None
      else Some (addr, size)
  | None -> None

(* The SysV slot index of a callee-side incoming offset (the callee's
   slots sit at [entry_rsp + 8 + 8*i]; entry_rsp is the window base the
   caller passes = its SP at the call). *)
let slot_index_of (k : int64) : int option =
  if Int64.compare k 8L >= 0 && Int64.equal (Int64.rem k 8L) 0L then
    Some (Int64.to_int (Int64.div (Int64.sub k 8L) 8L))
  else None

(* The CALLEE side of the promotion: per-def classification of this
   sub's window traffic from its tags and rhs shapes.
   - a LOAD at the singleton offset 0 is the return-address cell — it
     dies with the real LLVM ret and never forces a window parameter;
   - a LOAD at a singleton SysV slot offset, width within the cell,
     promotes to slot [(k-8)/8];
   - a STORE at a singleton slot offset writes the caller's window
     cell: the slot it touches DEMOTES — the parameter is only the
     initialization of a read-only slot, and a read after the write
     must observe the write (T4b) — so every access to that slot takes
     the window;
   - everything else (a spanned or mixed set, a wider read, a storing
     def — writes land in real caller memory) keeps the window. *)
let callee_side ~(offsets : Convutils.vsa_kind Tid.Map.t) (sub : sub term) :
    int Tid.Map.t * int * bool * Tid.Set.t =
  let window = ref false in
  let retaddr = ref Tid.Set.empty in
  let slots = ref Tid.Map.empty in
  let arity = ref 0 in
  let written = ref [] in
  Term.enum blk_t sub
  |> Seq.iter ~f:(fun blk ->
      Term.enum def_t blk
      |> Seq.iter ~f:(fun d ->
          let dtid = Term.tid d in
          match Core.Map.find offsets dtid with
          | Some (Convutils.Caller (lo, hi)) ->
              if not (Int64.equal lo hi) then window := true
              else
                let k = lo in
                (match load_of_rhs (Def.rhs d) with
                | Some (_, size) when Int64.equal k 0L
                                     && Size.in_bits size <= 64 ->
                    (* the return-address slot: dies with the real ret *)
                    retaddr := Core.Set.add !retaddr dtid
                | Some (_, size) -> (
                    match (slot_index_of k, Size.in_bits size) with
                    | Some i, w when w <= 64 ->
                        slots := Core.Map.set !slots ~key:dtid ~data:i;
                        arity := Int.max !arity (i + 1)
                    | _ -> (* a wider read demotes the slot to memory *)
                        window := true)
                | None ->
                    (* a store writes real window memory; every slot
                       cell the store's bytes intersect demotes — a
                       write at a sub-slot offset (the high half of a
                       cell) must be observable by that slot's reads
                       too (T4b) *)
                    window := true;
                    (match Model.addr_of_rhs (Def.rhs d) with
                    | Some (_, size) when Int64.compare k 8L >= 0 ->
                        let bytes = Size.in_bits size / 8 in
                        let first =
                          Int64.to_int Int64.(div (sub k 8L) 8L) in
                        let last =
                          Int64.to_int
                            Int64.(div (add k (of_int (bytes - 1))) 8L) in
                        let rec mark i =
                          if i <= last then
                            (written := i :: !written; mark (i + 1))
                        in
                        mark first
                    | _ -> ()))
          | Some (Convutils.Mixed _) -> window := true
          | _ -> ()));
  (* The written slots leave the promoted map: their reads take the
     window, where the write landed. *)
  let slots =
    Core.Map.filter_map !slots ~f:(fun i ->
        if Base.List.mem !written i ~equal:Int.equal then None else Some i)
  in
  (slots, !arity, !window, !retaddr)

(* The target-resolution predicate (T4): the site's class over the
   target's denotation.  A singleton whose word names a lifted sub
   resolves ([Some tid] — the Resolved Call Site); a bounded
   multi-target set, a foreign singleton, and an unresolvable set all
   take the pointer call ([None]).  [lookup] answers "is this address
   a lifted sub?" (the symtab + the program's name map in
   production). *)
let resolve_target ~(lookup : int64 -> Tid.t option) (ws : Vsa.WordSet.t) :
    Tid.t option = match singleton_i64 ws with
  | None -> None
  | Some v -> lookup v

(* The CALLER side: per-call-block outgoing slot stores, and the
   singleton resolution of each indirect call.  The slot correspondence
   is the SysV-fixed one: a store at relative offset [a] feeds the
   callee slot [k = a - d] where [d] is the SP's offset at the call
   (the window base the site passes = the callee's entry RSP). *)
let caller_side ~(sol : Vsa.vsa_sol) ~(sp : var)
    ~(symtab : Symtab.t option) ~(name_tid : (string * Tid.t) list)
    ~(abi : Hike_abi.t)
    (sub : sub term) :
    Convutils.call_site Tid.Map.t * Tid.t option Tid.Map.t
    * (int64 * int64) list =
  let sites = ref Tid.Map.empty in
  let resolved = ref Tid.Map.empty in
  (* A stack-symbolic value that escapes the sub (a call argument) is
     recorded for the precision decision and the frame sizing: the sub's
     own storage must back every cell another sub reaches through the
     escaped pointer. *)
  let exts = ref [] in
  let note_escape (e : exp) (st : Vsa.AI.t) =
    match Vsa.denote_imm_exp e st with
    | Error _ -> ()
    | Ok ws -> (
        match Vsa.Cbat_extraction.relativize_opt ws with
        | None -> ()
        | Some rel ->
            let ext =
              match singleton_i64 rel with
              | Some v -> (v, v)
              | None -> (
                  match Vsa.WordSet.min_elem rel, Vsa.WordSet.max_elem rel with
                  | Some mn, Some mx -> (
                      match Cbat_word.to_int64 mn, Cbat_word.to_int64 mx with
                      | Ok lo, Ok hi -> (lo, hi)
                      | _ -> (Int64.min_int, Int64.max_int))
                  | _ -> (Int64.min_int, Int64.max_int))
            in
            exts := ext :: !exts)
  in
  let lookup (v : int64) : Tid.t option =
    match symtab with
    | Some symtab -> (
        match Symtab.find_by_start symtab (Word.of_int64 ~width:64 v) with
        | Some (name, _, _) ->
            (* a singleton FOREIGN address resolves to no sub *)
            Base.List.Assoc.find ~equal:String.equal name_tid name
        | None -> None)
    | None -> None
  in
  let resolve_exp (texp : exp) (st : Vsa.AI.t) : Tid.t option =
    match Vsa.denote_imm_exp texp st with
    | Error _ -> None
    | Ok ws -> resolve_target ~lookup ws
  in
  Term.enum blk_t sub
  |> Seq.iter ~f:(fun blk ->
      let btid = Term.tid blk in
      let st0 = Graphlib.Std.Solution.get sol btid in
      let defs = Term.enum def_t blk |> Seq.to_list in
      let st_end =
        Base.List.fold_left defs ~init:st0 ~f:(fun st d -> Vsa.denote_def d st)
      in
      let has_call =
        Term.enum jmp_t blk
        |> Seq.exists ~f:(fun j ->
            match Jmp.kind j with Call _ -> true | _ -> false)
      in
      if has_call then begin
        (* The SP offset at the call = the window base the site passes. *)
        let site_slots =
          match singleton_stack_offset (Bil.Var sp) st_end with
          (* the SP offset at the call is not a single known word: the
             site's outgoing stores stay on the window path (the
             identity) — none of them feeds a promoted slot *)
          | None -> []
          | Some d_sp ->
              let _, slots =
                Base.List.fold_left defs ~init:(st0, [])
                  ~f:(fun (st, acc) d ->
                    let st_before = st in
                    let st = Vsa.denote_def d st in
                    match
                      (Model.addr_of_rhs (Def.rhs d),
                       Model.store_data_of_rhs (Def.rhs d))
                    with
                    | Some (addr, _), Some _ -> (
                        match singleton_stack_offset addr st_before with
                        | Some a -> (
                            (* the store's own slot; later same-slot
                               stores overwrite (last wins) *)
                            match slot_index_of (Int64.sub a d_sp) with
                            | Some i ->
                                ( st,
                                  (i, Term.tid d)
                                  :: Base.List.filter ~f:(fun (j, _) ->
                                         not (Int.equal i j))
                                        acc )
                            | None -> (st, acc))
                        | None -> (st, acc))
                    | _ -> (st, acc))
              in
              slots
        in
        sites := Core.Map.set !sites ~key:btid ~data:{ Convutils.site_slots }
      end;
      (* Resolution of every indirect call at this block's end state,
         and the escaped values (the convention lanes at the call). *)
      Term.enum jmp_t blk
      |> Seq.iter ~f:(fun j ->
          match Jmp.kind j with
          | Call c -> (
              match Call.target c with
              | Indirect texp ->
                  let cls = resolve_exp texp st_end in
                  resolved :=
                    Core.Map.set !resolved ~key:(Term.tid j) ~data:cls
              | Direct _ -> ())
          | _ -> ());
      Core.List.iter
        (abi.Hike_abi.int_param_regs @ abi.Hike_abi.vector_param_regs)
        ~f:(fun v -> note_escape (Bil.Var v) st_end));
  (!sites, !resolved, !exts)

(* Computes [sub]'s offset tags, stack plan, and promotion facts. *)
let offsets_of_sub (target : Theory.Target.t) (sp : var)
    ~(symtab : Symtab.t option) ~(prog : program term)
    (sub : sub term) : Convutils.vsa_info =
  let prog' = Program.create ~subs:[ sub ] () in
  (* VLA detection runs once per sub (spec §2.3), ahead of every arm below:
     even a memory-free sub can carry a dynamic SP decrement the emitter
     must see, and the set travels in [vsa_info.vla_alloc_tids]. *)
  let alloc_tids = Vsa.Cbat_extraction.detect_dynamic_alloc sp sub in
  (* The lifted world's name map: a resolved target address names a sub
     of this program (a singleton foreign address resolves to none). *)
  let name_tid =
    Term.enum sub_t prog
    |> Seq.fold ~init:[] ~f:(fun acc s ->
        (Convutils.sanitize_name (Tid.name (Term.tid s)), Term.tid s) :: acc)
  in
  (* Runs the fixpoint, then extracts tags def by def. *)
  let finish (sol : Vsa.vsa_sol) : Convutils.vsa_info =
    (* Indirect jumps leave the CFG incomplete. *)
    let has_indirect_jumps =
      Term.enum blk_t sub
      |> Seq.exists ~f:(fun blk ->
          Term.enum jmp_t blk
          |> Seq.exists ~f:(fun j ->
              match Jmp.kind j with
              | Goto (Indirect _) | Ret (Indirect _) -> true
              | _ -> false))
    in
    let degraded = has_indirect_jumps in
    (* Extracts tags via [Cbat_extraction]: the per-def offset ranges. *)
    let offsets =
      Vsa.Cbat_extraction.extract
        ~sol ~alloc_tids
        ~dynamic_alloc:(fun d -> Core.Set.mem alloc_tids (Term.tid d))
        sub
    in
    (* The region partition is geometric (T4): the SP Slot anchor makes
       every sub's SP neighborhood private. *)
    let mk = Convutils.mk_vsa_info_maps ~offsets ~degraded
        ~vla_alloc_tids:alloc_tids in
    (* The storage-class lattice (Frame ⊔ anything = Frame): stack
       traffic the regions do not serve keeps the SP-relative lane,
       whose anchor must be the sub's own frame — an unserved sub joins
       to Frame (its regions withdraw, the fallback frame backs every
       access).  Served = the tag is a Range inside a convertible
       region (singleton cells and fissioned ranged regions alike —
       this is what recovers T3c's 21 re-framed subs, whose ranged
       regions now convert); VLA and Dead carry their own lanes; window
       traffic (Caller / the retaddr cell) is served by the promoted
       parameters, the window parameter, or the ret lane without
       touching this sub's storage. *)
    let prom_slots, prom_arity, prom_window, prom_retaddr =
      callee_side ~offsets sub
    in
    let prom_sites, prom_resolved, sp_extents =
      caller_side ~sol ~sp ~symtab ~name_tid
        ~abi:(Hike_abi.of_target target) sub
    in
    let base_info () =
      mk ~prom_sites ~prom_slots ~prom_arity ~prom_window ~prom_retaddr
        ~regions:[] ~stack_plan:[] ()
    in
    let regions = Hike_stack_model.regions_of_sub sub (base_info ()) in
    let region_of_def =
      Base.List.fold regions ~init:Tid.Map.empty ~f:(fun m r ->
          if r.Convutils.convertible then
            Base.List.fold r.Convutils.members ~init:m
              ~f:(fun m (dtid, _) -> Core.Map.set m ~key:dtid ~data:r)
          else m)
    in
    let accesses_served =
      Core.List.for_all
        (Core.Map.to_alist offsets)
        ~f:(fun (dtid, kind) ->
          match kind with
          | Range _ -> Core.Map.mem region_of_def dtid
          | VLA _ | Dead | Caller _ -> true
          | Mixed _ | Infinite _ | Unbounded -> false)
    in
    (* The storage-class closure over escapes: a stack-symbolic value
       that leaves the sub (a call argument — an sret pointer, a cell
       address handed to memcpy, a window base) travels as an
       SP-arithmetic address, and the regions are separate allocas that
       no SP-arithmetic address can name.  The Frame model's anchor is
       the one storage SP-arithmetic addresses stay inside, so any
       escape joins the sub to Frame; a sub with no escaping stack
       values keeps its regions. *)
    let values_served = Base.List.is_empty sp_extents in
    let served = accesses_served && values_served in
    let regions = if served then regions else [] in
    let base =
      mk ~regions ~stack_plan:[] ~prom_slots ~prom_arity ~prom_window
        ~prom_retaddr ~prom_sites ~prom_resolved ~sp_extents ()
    in
    (* The plan IS the convertible regions — no refusals, no recomputation. *)
    { base with
    Convutils.stack_plan = Hike_stack_model.split_plan sub base }
  in
  let probe_res =
    (* Runs the fixpoint; non-convergence degrades to no tags. *)
    match
      try
        Some (Vsa.static_graph_vsa [] prog' sub (Vsa.init_sol sub))
      with Vsa.Fixpoint_not_converged (n, _, _) ->
        (* Partial solutions under-approximate; tags from them are unsound. *)
        Hike_diag.warn
          "vsa: sub %s: fixpoint not converged in %d iterations — degraded (no tags, dynamic stack)"
          (Sub.name sub) n;
        None
    with
    | None ->
      (* Degraded: every memory op is Unbounded (the sound fallback). *)
      let offsets =
        Term.enum blk_t sub
        |> Seq.concat_map ~f:(Term.enum def_t)
        |> Seq.filter ~f:(fun d ->
            Option.is_some
              (Vsa.Cbat_extraction.stack_address_of_rhs (Def.rhs d)))
        |> Seq.fold ~init:Tid.Map.empty ~f:(fun m d ->
            Core.Map.set m ~key:(Term.tid d) ~data:Convutils.Unbounded)
      in
      Convutils.{ empty_vsa_info with offsets; degraded = true;
                  vla_alloc_tids = alloc_tids }
    | Some sol -> finish sol
  in
  probe_res
