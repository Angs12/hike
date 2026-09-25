(* The Stack-Arg promotion: the layout's slots become the sub's
   promoted parameters, call sites bind the stored values, and
   promoted-slot loads read the args. *)

open Bap.Std
open Bap.Std.Bil.Types
module Model = Hike_stack_model
module Vsa = Cbat_vsa
module Tag = Hike_stack_model.Tag
module Sections = Hike_sections

(* The call-site correspondence: a store's singleton aligned start [a]
   against the block's call-time SP [d_sp] is slot
   [(a - d_sp - word) / word]. *)
type site_binding = {
  sb_slot : int;
  sb_def : def term;
  sb_full : bool;
}

let site_bindings_of_sub ~(word : int) ~(abi : Hike_abi.t) ~(sp : var)
    ~(denote : blk:blk term -> ?def:def term -> exp ->
                (Vsa.WordSet.t, Type.error) Result.t)
    (sub : sub term) : site_binding list Tid.Map.t =
  let w64 = Stdlib.Int64.of_int word in
  let singleton_at ?(def : def term option) ~(blk : blk term) (e : exp) :
      int64 option =
    match denote ~blk ?def e with
    | Error _ -> None
    | Ok ws -> (
        match Vsa.WordSet.stack_offsets ws with
        | Some _ -> (
            match Model.positions_of_offsets ws with
            | Some (lo, hi) when Stdlib.Int64.equal lo hi -> Some lo
            | _ -> None)
        | None ->
            if Vsa.WordSet.in_stack_segment ws then Model.singleton_i64 ws
            else None)
  in
  let slot_of_start (a : int64) (d_sp : int64) : int option =
    let rel = Stdlib.Int64.sub a d_sp in
    if
      Stdlib.Int64.compare rel w64 >= 0
      && Stdlib.Int64.equal (Stdlib.Int64.rem rel w64) 0L
    then Some (Model.slot_index_of_offset ~word rel)
    else None
  in
  Term.enum blk_t sub
  |> Seq.fold ~init:Tid.Map.empty ~f:(fun sites blk ->
         let btid = Term.tid blk in
         let has_call =
           Term.enum jmp_t blk
           |> Seq.exists ~f:Hike_stack_model.machine_call
         in
         if not has_call then sites
         else
           match singleton_at ~blk (Bil.Var sp) with
           | None -> Core.Map.set sites ~key:btid ~data:[]
           | Some d_sp ->
               let bindings =
                 Term.enum def_t blk
                 |> Seq.fold ~init:[] ~f:(fun acc d ->
                        match
                          ( Model.addr_of_rhs (Def.rhs d),
                            Model.store_data_of_rhs (Def.rhs d) )
                        with
                        | Some (addr, size), Some _ -> (
                            match singleton_at ~def:d ~blk addr with
                            | Some a -> (
                                match slot_of_start a d_sp with
                                | Some i ->
                                    let cell_lo =
                                      Stdlib.Int64.add d_sp
                                        (Model.slot_offset ~word i)
                                    in
                                    let occ_hi =
                                      Stdlib.Int64.add a
                                        (Stdlib.Int64.of_int
                                           (Size.in_bytes size - 1))
                                    in
                                    let full =
                                      Stdlib.Int64.equal a cell_lo
                                      && Stdlib.Int64.equal occ_hi
                                           (Stdlib.Int64.add cell_lo
                                              (Stdlib.Int64.pred w64))
                                    in
                                    { sb_slot = i; sb_def = d; sb_full = full }
                                    :: Base.List.filter acc ~f:(fun b ->
                                           not (Int.equal b.sb_slot i))
                                | None -> acc)
                            | None -> acc)
                        | _ -> acc)
               in
               Core.Map.set sites ~key:btid
                 ~data:(Base.List.sort bindings ~compare:(fun a b ->
                      Int.compare a.sb_slot b.sb_slot)))

let region_id_of_storage (s : Sections.storage) : int =
  match s with
  | Stack_region n | Data_region n -> n
  | Stack_residue | Arg_slot _ -> Model.residue_id

type conv =
  | Conv_region of int                    (* the region id *)
  | Conv_window                           (* the incoming window: the caller's world *)
  | Conv_slot of int * int                (* slot index, intra-slot byte *)
  | Conv_global of int                    (* the component id *)
  | Keep

(* The rewrite decision reads the attribution's own projection of the
   def (ctx.projections) — the collect path computed it; the rewrite
   cannot disagree with the tree. *)
let conversion_of ~(word : int) ~(entry : int64)
    ~(tree : Sections.sub_tree) ~(data : Sections.data_tree)
    ~(projected : (Sections.Tag.t option * Sections.portion list) option)
    ~(d : def term)
    ~(demoted : int list) : conv * Sections.Tag.t option =
  match Sections.access_of d with
  | None -> (Keep, None)
  | Some (addr, _, _) -> (
      match projected with
      (* A failed attribution query keeps the memory form. *)
      | None -> (Keep, None)
      | Some (tag, portions) ->
          (* An above-entry unbounded address keeps its memory form: its
             storage is the caller's world, which the typed arguments
             carry.  A below-entry unbounded address is a pointer into
             the residue alloca, exactly like a bounded one. *)
          match tag with
          | Some Sections.Tag.Args_unbounded -> (Keep, tag)
          | _ ->
          (* A return-address cell keeps its tag — the emitter's
             return arm. *)
          let retaddr_cell =
            match tag with
            | Some t -> Model.is_return_address_tag t
            | None -> false
          in
          let owned =
            Base.List.filter portions ~f:(fun p ->
                if Sections.is_sub_local p.pt_sec then not retaddr_cell
                else p.pt_elig && Sections.is_const_chain addr)
          in
          match owned with
          | [ p ] -> (
              let owner =
                let space = if Sections.is_sub_local p.pt_sec then tree else data in
                Sections.storage_of_range space (Sections.range p.pt_sec p.pt_lo p.pt_hi)
              in
              match owner with
              | Some rs -> (
                  match (p.pt_sec, rs.storage) with
                  | (Stack, (Stack_region _ | Stack_residue)) ->
                    (Conv_region (region_id_of_storage rs.storage), tag)
                  | (Args, Stack_residue) -> (Conv_window, tag)
                  | Args, Arg_slot i -> (
                      let d_in =
                        Stdlib.Int64.to_int
                          (Stdlib.Int64.rem
                             (Stdlib.Int64.sub p.pt_lo (Model.args_base ~entry ~word))
                             (Stdlib.Int64.of_int word))
                      in
                      if Base.List.mem demoted i ~equal:Int.equal then
                        (Keep, tag)
                      else (Conv_slot (i, d_in), tag))
                  | _, Data_region id -> (Conv_global id, tag)
                  | _ -> (Keep, tag))
              | None -> (Keep, tag))
          | _ -> (Keep, tag))

(* Replaces every Load/Store node of the expression with [dst]. *)
let rewrite_load_node ~(dst : exp) (e : exp) : exp =
  let v =
    object
      inherit Exp.mapper
      method! map_load ~mem:_ ~addr:_ (endian : endian) (size : Size.t) : exp = dst
      method! map_store ~mem:_ ~addr:_ ~exp:_ (endian : endian) (size : Size.t) : exp = dst
    end
  in
  v#map_exp e

(* A read starting [d] bytes into the word cell selects bits
   [8d, 8d+bits) — BIL's little-endian bit numbering. *)
let slot_read ~(word : int) (i : int) (byte_offset : int) (bits : int) : exp =
  let slot = Bil.Var (Model.arg_slot ~word i) in
  let wbits = word * 8 in
  if byte_offset = 0 then
    if Int.equal bits wbits then slot
    else Bil.Cast (Bil.LOW, bits, slot)
  else if Int.equal bits wbits then slot
  else Bil.Extract (8 * byte_offset + bits - 1, 8 * byte_offset, slot)

(* Every memory node of the expression re-points at [mem_var] — a
   converted def keeps no model-memory node.  The override receives
   children unmapped, so it maps the address and store data itself. *)
let repoint_mapper (mem_var : var) =
  object
    inherit Exp.mapper as super
    method! map_load ~mem:_ ~addr rest s =
      Bil.Load (Bil.Var mem_var, super#map_exp addr, rest, s)
    method! map_store ~mem:_ ~addr ~exp rest s =
      Bil.Store
        (Bil.Var mem_var, super#map_exp addr, super#map_exp exp, rest, s)
  end

(* One def's rewrite: re-point to the owning storage's mem var, or
   read the slot parameter's selected bytes. *)
let rewrite_def ~(word : int) ~(conv : conv) ~(bits : int) (d : def term) :
    def term =
  match conv with
  | Keep -> d
  | Conv_region id ->
      let mem_var = Model.region_mem id in
      let d =
        Def.map_exp d ~f:(fun e -> (repoint_mapper mem_var)#map_exp e)
      in
      if Model.is_mem (Def.lhs d) then Def.with_lhs d mem_var else d
  | Conv_window ->
      let mem_var = Model.window_mem in
      let d =
        Def.map_exp d ~f:(fun e -> (repoint_mapper mem_var)#map_exp e)
      in
      if Model.is_mem (Def.lhs d) then Def.with_lhs d mem_var else d
  | Conv_global id ->
      let mem_var = Model.sec_comp_mem id in
      let d =
        Def.map_exp d ~f:(fun e -> (repoint_mapper mem_var)#map_exp e)
      in
      if Model.is_mem (Def.lhs d) then Def.with_lhs d mem_var else d
  | Conv_slot (i, byte_offset) ->
      let read = slot_read ~word i byte_offset bits in
      Def.map_exp d ~f:(fun e -> rewrite_load_node ~dst:read e)

(* Each site's full-cell store gains its [hike_argN] def binding the
   storing def's own value; a partial final store binds nothing (the
   slot is demoted to the window on both sides). *)
let bind_site_args ~(word : int) (bindings : site_binding list)
    (blk : blk term) : blk term =
  Base.List.fold bindings ~init:blk ~f:(fun blk b ->
      if not b.sb_full then blk
      else
        (* The parameter binds the bytes the store wrote — the store's
           data expression, never the def's lhs (a memory-typed model
           var). *)
        let data =
          match Model.store_data_of_rhs (Def.rhs b.sb_def) with
          | Some data -> data
          | None -> Bil.Var (Def.lhs b.sb_def)
        in
        let arg = Def.create (Model.call_arg ~word b.sb_slot) data in
        match Term.next def_t blk (Term.tid b.sb_def) with
        | Some next -> Term.prepend def_t blk ~before:(Term.tid next) arg
        | None -> Term.append def_t blk arg)

(* The promotion's per-sub input facts. *)
type facts = {
  prom_arity : int;
  prom_resolved : Tid.t option Tid.Map.t;
}

(* Resolves each indirect call's target through its denotation: the
   caller-side half of the promotion. *)
let call_resolution ~(denote : blk:blk term -> ?def:def term -> exp ->
                  (Vsa.WordSet.t, Type.error) Result.t)
    ~(lookup : int64 -> Tid.t option)
    (sub : sub term) : Tid.t option Tid.Map.t =
  let resolved = ref Tid.Map.empty in
  Term.enum blk_t sub
  |> Seq.iter ~f:(fun blk ->
      Term.enum jmp_t blk
      |> Seq.iter ~f:(fun j ->
          match Jmp.kind j with
          | Call c -> (
              match Call.target c with
              | Indirect texp -> (
                  match denote ~blk texp with
                  | Error _ ->
                      resolved :=
                        Core.Map.set !resolved ~key:(Term.tid j) ~data:None
                  | Ok ws ->
                      resolved :=
                        Core.Map.set !resolved ~key:(Term.tid j)
                          ~data:(Hike_resolve.resolve_target ~lookup ws))
              | Direct _ -> ())
          | _ -> ()));
  !resolved

(* The promotion rewrite: the sub gains its promoted parameters as
   real BIR args, the sites' outgoing stores gain [hike_argN] defs,
   and singleton-resolved indirect targets become direct.
   Fixed-signature subs (the intrinsics, @main) get no callee-side
   rewrite; the caller side runs for every sub. *)
(* The caller side: a resolved target becomes direct; the jmp keeps
   its tid, guard, and tag. *)
let resolve_targets ~(resolved : Tid.t option Tid.Map.t)
    (sub : sub term) : sub term =
  Term.map blk_t sub ~f:(fun blk ->
      Term.map jmp_t blk ~f:(fun j ->
          match Core.Map.find resolved (Term.tid j) with
          | Some (Some t) -> (
              match Jmp.kind j with
              | Call c -> Jmp.with_kind j (Call (Call.with_target c (Direct t)))
              | _ -> j)
          | _ -> j))

let promote_sub ~(abi : Hike_abi.t) (facts : facts)
    (sub : sub term) : sub term =
  let callee_exempt = Hike_stack_model.fixed_signature sub in
  let word = abi.Hike_abi.word in
  let sub =
    if callee_exempt then sub
    else
      (* Promotion defines the sub's whole argument convention: the
         slots in signature order replace the sub's args. *)
      let slots =
        Base.List.init facts.prom_arity ~f:(fun i ->
            Arg.create ~intent:In (Model.arg_slot ~word i)
              (Bil.Var (Model.arg_slot ~word i)))
      in
      Model.set_sig sub slots
  in
  resolve_targets ~resolved:facts.prom_resolved sub


(* The tree's Arg_slot member defs, minus the demoted slots. *)
let slot_defs_of ~(demoted : int list) (tree : Sections.sub_tree) :
    int Tid.Map.t * int =
  let bindings = Sections.Tree.to_sequence tree |> Seq.to_list in
  let slots, arity =
    Base.List.fold bindings ~init:(Tid.Map.empty, -1) ~f:(fun (m, mx) (_, rs) ->
        match rs.storage with
        | Arg_slot i when not (Base.List.mem demoted i ~equal:Int.equal) ->
            Base.List.fold rs.members ~init:(m, mx) ~f:(fun (m, mx) mm ->
                match mm.m_def with
                | Some dtid -> (Core.Map.set m ~key:dtid ~data:i, Int.max mx i)
                | None -> (m, mx))
        | _ -> (m, mx))
  in
  (slots, if arity < 0 then 0 else arity + 1)

(* The per-sub rewrite: promotion, the storage rewrite, and the layout
   stamp.  [sites]/[resolved] are the call-site and resolution
   products. *)
let rewrite_sub ~(word : int) ~(entry : int64) ~(abi : Hike_abi.t)
    ~(spans : Sections.data_span list)
    ~(denote : blk:blk term -> ?def:def term -> exp ->
                (Vsa.WordSet.t, Type.error) Result.t)
    ~(ctx : Sections.ctx)
    ~(sites : site_binding list Tid.Map.t)
    ~(resolved : Tid.t option Tid.Map.t)
    ~(demoted : int list)
    ~(callee_exempt : bool)
    (sub : sub term) : sub term =
  let tree =
    Core.Map.find ctx.sub_trees (Term.tid sub)
    |> Core.Option.value ~default:Sections.Tree.empty
  in
  let slots, arity = slot_defs_of ~demoted tree in
  let arity = if callee_exempt then 0 else arity in
  let facts = { prom_arity = arity; prom_resolved = resolved } in
  let sub = promote_sub ~abi facts sub in
  (* A non-memory def whose value is bounded stack-symbolic at/above
     the Args base computes an address in the caller's window — the
     emitter re-bases its integer to the window parameter. *)
  let window_values =
    Term.enum blk_t sub
    |> Seq.fold ~init:Tid.Set.empty ~f:(fun acc blk ->
        Term.enum def_t blk
        |> Seq.fold ~init:acc ~f:(fun acc d ->
            if Core.Option.is_some (Model.addr_of_rhs (Def.rhs d)) then acc
            else
              match denote ~blk ~def:d (Def.rhs d) with
              | Error _ -> acc
              | Ok ws -> (
                  match Vsa.WordSet.stack_offsets ws with
                  | None -> acc
                  | Some _ -> (
                      let a_base = Model.args_base ~entry ~word in
                      match Model.positions_of_offsets ws with
                      | Some (lo, hi)
                        when Stdlib.Int64.compare lo a_base >= 0
                             && Stdlib.Int64.compare hi a_base >= 0
                             && Stdlib.Int64.compare lo hi <= 0 ->
                        Core.Set.add acc (Term.tid d)
                      | _ -> acc))))
  in
  let sub = Hike_def_slots.stamp_window_values ~window_values sub in
  let sub =
    Term.map blk_t sub ~f:(fun blk ->
        let blk =
          Term.map def_t blk ~f:(fun d ->
              let bits =
                match Sections.access_of d with
                | Some (_, w, _) -> 8 * w
                | None -> 0
              in
              let conv, _tag =
                conversion_of ~word ~entry ~tree
                  ~data:ctx.data_tree
                  ~projected:(Base.Option.join (Core.Map.find ctx.projections (Term.tid d)))
                  ~d ~demoted
              in
              rewrite_def ~word ~conv ~bits d)
        in
        match Core.Map.find sites (Term.tid blk) with
        | Some bs -> bind_site_args ~word bs blk
        | None -> blk)
  in
  (* The signature carries the window parameter whenever a
     window-value def exists. *)
  let layout = Sections.layout_of_tree ~word ~entry ~abi ~sub tree in
  let layout =
    if Core.Set.is_empty window_values then layout
    else { layout with Hike_stack_model.window_param = true }
  in
  Hike_stack_model.set_layout layout sub

(* The program driver: per-sub sites and resolution, the cross-sub
   demotion, the rewrite. *)
let rewrite_program ~(word : int) ~(entry : int64) ~(facts : Hike_kb.facts)
    ~(spans : Sections.data_span list)
    ~(ctx : Sections.ctx)
    (prog : program term) : program term =
  let abi = facts.abi in
  let denote = facts.denote in
  let sp = abi.Hike_abi.sp in
  let lookup = facts.lookup in
  let callee_exempt = Hike_stack_model.fixed_signature in
  let exempt =
    Term.enum sub_t prog
    |> Seq.fold ~init:Tid.Set.empty ~f:(fun acc s ->
           if callee_exempt s then Core.Set.add acc (Term.tid s) else acc)
  in
  let sides =
    Term.enum sub_t prog
    |> Seq.fold ~init:Tid.Map.empty ~f:(fun acc sub ->
           let sites = site_bindings_of_sub ~word ~abi ~sp ~denote sub in
           let resolved = call_resolution ~denote ~lookup sub in
           Core.Map.set acc ~key:(Term.tid sub) ~data:(sites, resolved))
  in
  (* A slot whose outgoing final store is partial is demoted on both
     sides: the callee's accesses take the window, never the
     parameter. *)
  let demotion =
    Term.enum sub_t prog
    |> Seq.fold ~init:Tid.Map.empty ~f:(fun acc caller ->
        let sites, resolved =
          Core.Map.find sides (Term.tid caller)
          |> Core.Option.value ~default:(Tid.Map.empty, Tid.Map.empty)
        in
        Core.Map.fold sites ~init:acc ~f:(fun ~key:btid ~data:bs acc ->
            let callees =
              match Term.find blk_t caller btid with
              | Some blk ->
                  Term.enum jmp_t blk
                  |> Seq.filter_map ~f:(fun j ->
                         match Core.Map.find resolved (Term.tid j) with
                         | Some (Some t) -> Some t
                         | _ -> None)
                  |> Seq.to_list
              | None -> []
            in
            Base.List.fold callees ~init:acc ~f:(fun acc callee ->
                Base.List.fold bs ~init:acc ~f:(fun acc b ->
                    if b.sb_full then acc
                    else
                      Core.Map.update acc callee ~f:(function
                          | None -> [ b.sb_slot ]
                          | Some ds ->
                              if Base.List.mem ds b.sb_slot ~equal:Int.equal then ds
                              else b.sb_slot :: ds)))))
  in
  Term.map sub_t prog ~f:(fun sub ->
      let sites, resolved =
        Core.Map.find sides (Term.tid sub)
        |> Core.Option.value ~default:(Tid.Map.empty, Tid.Map.empty)
      in
      rewrite_sub ~word ~entry ~abi ~spans ~denote ~ctx ~sites ~resolved
        ~demoted:(Core.Map.find demotion (Term.tid sub)
                  |> Core.Option.value ~default:[])
        ~callee_exempt:(Core.Set.mem exempt (Term.tid sub))
        sub)

