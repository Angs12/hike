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
}

let site_bindings_of_sub_with_blocks ~(word : int) ~(abi : Hike_abi.t) ~(sp : var)
    ~(denote : blk:blk term -> ?def:def term -> exp ->
                (Vsa.WordSet.t, Type.error) Result.t)
    (sub : sub term) : (site_binding list * blk term) Tid.Map.t =
  let w64 = Stdlib.Int64.of_int word in
  let singleton_at ?(def : def term option) ~(blk : blk term) (e : exp) :
      int64 option =
    match denote ~blk ?def e with
    | Error _ -> None
    | Ok ws -> Model.singleton_stack_position ws
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
           | None -> Core.Map.set sites ~key:btid ~data:([], blk)
           | Some d_sp ->
               let bindings =
                 Term.enum def_t blk
                 |> Seq.fold ~init:[] ~f:(fun acc d ->
                        match
                          ( Model.addr_of_rhs (Def.rhs d),
                            Model.store_data_of_rhs (Def.rhs d) )
                        with
                        | Some (addr, _size), Some _ -> (
                            match singleton_at ~def:d ~blk addr with
                            | Some a -> (
                                match slot_of_start a d_sp with
                                | Some i ->
                                    { sb_slot = i; sb_def = d }
                                    :: Base.List.filter acc ~f:(fun b ->
                                           not (Int.equal b.sb_slot i))
                                | None -> acc)
                            | None -> acc)
                        | _ -> acc)
               in
               Core.Map.set sites ~key:btid
                 ~data:
                   ( Base.List.sort bindings ~compare:(fun a b ->
                        Int.compare a.sb_slot b.sb_slot),
                     blk ))

let site_bindings_of_sub ~(word : int) ~(abi : Hike_abi.t) ~(sp : var)
    ~(denote : blk:blk term -> ?def:def term -> exp ->
                (Vsa.WordSet.t, Type.error) Result.t)
    (sub : sub term) : site_binding list Tid.Map.t =
  site_bindings_of_sub_with_blocks ~word ~abi ~sp ~denote sub
  |> Core.Map.map ~f:fst

let region_id_of_storage (s : Sections.storage) : int =
  match s with
  | Stack_region n | Data_region n -> n
  | Stack_residue | Arg_slot -> Model.residue_id

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
    ~(projected : Sections.projection option)
    ~(access : (exp * int * bool) option) : conv * Sections.Tag.t option =
  match access with
  | None -> (Keep, None)
  | Some (addr, _, _) -> (
      match projected with
      (* A failed attribution query keeps the memory form. *)
      | None -> (Keep, None)
      | Some p ->
          (* An unbounded address keeps its memory form: an above-entry
             direction's storage is the caller's world, which the typed
             arguments carry; a below-entry one is a pointer into the
             residue alloca, exactly like a bounded one.  A VLA-origin
             claim keeps its memory form too: the band's real storage is
             the dynamic alloca the pointer chain names. *)
          let tag = p.Sections.tag in
          let portions = p.Sections.portions in
          match (tag, p.Sections.origin) with
          | (Some Sections.Tag.Unbounded, _) -> (Keep, tag)
          | (_, Some (Hike_origin.Vla _)) -> (Keep, tag)
          | _ ->
          (* A return-address cell keeps its tag — the emitter's
             return arm. *)
          let retaddr_cell =
            match tag with
            | Some t -> Model.is_return_address_tag t
            | None -> false
          in
          (* A conversion needs the eligibility proof: an identity
             portion (an escape, a full-span claim, a VLA extent) keeps
             the memory form — the raw lane is its sound answer. *)
          let owned =
            Base.List.filter portions ~f:(fun p ->
                p.pt_elig
                && (if Sections.is_sub_local p.pt_sec then not retaddr_cell
                    else Sections.is_const_chain addr))
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
                  | Args, Arg_slot -> (
                      (* The slot index is the ACCESS's own word cell,
                         never the binding's: a binding may span several
                         cells.  A span outside a single cell is not a
                         slot (the binding's promotability proved one, so
                         this is the defensive identity). *)
                      match
                        Sections.args_cell_of_span ~word ~entry p.pt_lo
                          p.pt_hi
                      with
                      | Some i ->
                        let cell_lo =
                          Stdlib.Int64.add entry (Model.slot_offset ~word i)
                        in
                        ( Conv_slot
                            (i, Stdlib.Int64.to_int (Stdlib.Int64.sub p.pt_lo cell_lo)),
                          tag )
                      | None -> (Keep, tag))
                  | _, Data_region id -> (Conv_global id, tag)
                  | _ -> (Keep, tag))
              | None -> (Keep, tag))
          | _ -> (Keep, tag))

(* ---- The one address map: every address def's value is its storage's
   base plus the storage-relative displacement. ---- *)

(* Every var leaf's kind: [ `Static k ] an address whose offset is
   provably k, [ `Addr ] an address whose offset is not static, [ `Int ]
   a visible non-address (a runtime piece).  A var the denotation cannot
   see is absent — unknown may be a pointer at emission, so it never
   enters a displacement. *)
type leaf = [ `Static of int64 | `Addr | `Int ]

let address_leaves ~(denote : blk:blk term -> ?def:def term -> exp ->
                     (Vsa.WordSet.t, Type.error) Result.t)
    ~(blk : blk term) ~(def : def term) (e : exp) : leaf Var.Map.t =
  (object
     inherit [ leaf Var.Map.t ] Exp.visitor
     method! visit_var v acc =
       match denote ~blk ~def (Bil.Var v) with
       | Ok ws
         when (not (Vsa.WordSet.is_top ws || Vsa.WordSet.is_bottom ws))
              && Vsa.WordSet.in_stack_segment ws ->
             (* A Vla-origin value's offsets are frame-relative —
                read them off the value, never the entry-line hull. *)
             let off =
               match Vsa.WordSet.origin ws with
               | Some (Vsa.WordSet.Origin.Vla _) -> (
                   match Vsa.WordSet.vla_offsets ws with
                   | Some offs -> Model.singleton_offset offs
                   | None -> None)
               | _ -> (
                   match Vsa.WordSet.stack_offsets ws with
                   | Some offs -> Model.singleton_offset offs
                   | None -> None)
             in
             Core.Map.set acc ~key:v
               ~data:(match off with Some k -> `Static k | None -> `Addr)
       | Ok ws
         when not (Vsa.WordSet.is_top ws || Vsa.WordSet.is_bottom ws) ->
           Core.Map.set acc ~key:v ~data:`Int
       | Ok _ | Error _ -> acc
   end)#visit_exp e Var.Map.empty

(* The entry-line arithmetic of an address exp: each address leaf folds
   to its singleton offset, the runtime pieces stay.  [None] when an
   address part is not statically known — the value then composes over
   its operands' own pointers. *)
let offset_of ~(piece_ok : var -> bool) ~(leaves : leaf Var.Map.t)
    (e : exp) : exp option =
  let w64 (k : int64) : exp =
    Bil.Int (Cbat_word.to_word (Cbat_word.of_int64 ~width:64 k))
  in
  Hike_exp_fold.fold
    (fun e child ->
      match e with
      | Bil.Int _ -> Some e
      | Bil.Var v -> (
          match Core.Map.find leaves v with
          | Some (`Static k) -> Some (w64 k)
          | Some `Int when piece_ok v -> Some e
          | Some (`Int | `Addr) | None -> None)
      | Bil.BinOp ((Bil.PLUS | Bil.MINUS) as op, a, b) -> (
          match (child a, child b) with
          | Some a', Some b' -> (
              match (a', b') with
              | Bil.Int x, Bil.Int y -> (
                  match
                    (Cbat_word.to_int64 (Cbat_word.of_word x),
                     Cbat_word.to_int64 (Cbat_word.of_word y))
                  with
                  | Ok x', Ok y' ->
                      Some (w64 ((if op = Bil.PLUS then Stdlib.Int64.add
                                 else Stdlib.Int64.sub)
                                   x' y'))
                  | _ -> Some (Bil.BinOp (op, a', b')))
              | _ -> Some (Bil.BinOp (op, a', b')))
          | _ -> None)
      | Bil.Cast (cast, width, a) ->
          Base.Option.map (child a) ~f:(fun a' -> Bil.Cast (cast, width, a'))
      | Bil.Ite (c, a, b) -> (
          match (child a, child b) with
          | Some a', Some b' -> Some (Bil.Ite (c, a', b'))
          | _ -> None)
      | _ ->
          if
            Core.Set.exists (Exp.free_vars e) ~f:(fun v ->
                match Core.Map.find leaves v with
                | Some `Int when piece_ok v -> false
                | _ -> true)
          then None
          else Some e)
    e

(* [base + (disp − rel)] with the displacement folded: a static
   displacement folds to a constant (the base itself at zero). *)
let base_plus (base : var) ~(rel : int64) (disp : exp) : exp =
  let w64 (k : int64) =
    Bil.Int (Cbat_word.to_word (Cbat_word.of_int64 ~width:64 k))
  in
  match disp with
  | Bil.Int w -> (
      match Cbat_word.to_int64 (Cbat_word.of_word w) with
      | Ok k ->
          let k = Stdlib.Int64.sub k rel in
          if Stdlib.Int64.equal k 0L then Bil.Var base
          else Bil.BinOp (Bil.PLUS, Bil.Var base, w64 k)
      | Error _ -> Bil.BinOp (Bil.PLUS, Bil.Var base, disp))
  | _ ->
      Bil.BinOp
        (Bil.PLUS, Bil.Var base, Bil.BinOp (Bil.MINUS, disp, w64 rel))

(* The stack binding wholly owning [lo, hi]: a value spanning two
   bindings names no one storage. *)
let owning_storage (tree : Sections.sub_tree) (lo : int64) (hi : int64) :
    Sections.storage option =
  Sections.Tree.lookup tree (Sections.point Stack lo)
  |> Seq.find_map ~f:(fun (k, rs) ->
         if
           Stdlib.Int64.compare k.Sections.lo.Sections.p_pos lo <= 0
           && Stdlib.Int64.compare hi k.Sections.hi.Sections.p_pos <= 0
         then Some rs.Sections.storage
         else None)

(* The data binding wholly owning [c]: (component id, its native low
   bound).  A constant spanning bindings names no one storage. *)
let owning_data_binding (tree : Sections.data_tree) (c : int64) :
    (int * int64) option =
  Sections.Tree.lookup tree (Sections.point Rodata c)
  |> Seq.find_map ~f:(fun (k, rs) ->
         if
           Stdlib.Int64.unsigned_compare c k.Sections.lo.Sections.p_pos >= 0
           && Stdlib.Int64.unsigned_compare c k.Sections.hi.Sections.p_pos <= 0
         then (
           match rs.Sections.storage with
           | Sections.Data_region id ->
               Some (id, k.Sections.lo.Sections.p_pos)
           | _ -> None)
         else None)

(* One def's rewrite facts: the access's conversion (the mem re-point)
   plus the storage-relative address forms — a value def's whole rhs,
   an access def's mem-node address. *)
type def_fact = {
  fr_conv : conv;
  fr_bits : int;
  fr_addr : exp option;
  fr_rhs : exp option;
}

let no_fact = { fr_conv = Keep; fr_bits = 0; fr_addr = None; fr_rhs = None }

(* Each storage's geometry: its entry-line offset [rel] and its
   allocated extent (the alloca's own byte range, in positions). *)
type storage_geom = { sg_rel : int64; sg_lo : int64; sg_hi : int64 }

let geoms_of_layout (layout : Hike_stack_model.sub_layout) :
    storage_geom Core.Int.Map.t =
  Base.List.fold layout.Hike_stack_model.regions ~init:Core.Int.Map.empty
    ~f:(fun m { Model.Sub_layout.r_id = id; r_lo = lo; r_hi = hi; _ } ->
        Core.Map.set m ~key:id
          ~data:
            { sg_rel = Stdlib.Int64.sub lo Model.segment_base;
              sg_lo = lo;
              sg_hi = hi })

(* The per-def rewrite facts of one sub: every access keeps its
   conversion; every address def whose value routes to a storage takes
   the base + displacement form. *)
let def_facts ~(word : int) ~(entry : int64) ~(abi : Hike_abi.t)
    ~(tree : Sections.sub_tree) ~(data : Sections.data_tree)
    ~(projections : Sections.projection option Tid.Map.t)
    ~(geoms : storage_geom Core.Int.Map.t)
    ~(window_param : bool) ~(vla_tids : Tid.Set.t)
    ~(spans : Sections.data_span list)
    ~(denote : blk:blk term -> ?def:def term -> exp ->
                (Vsa.WordSet.t, Type.error) Result.t)
    (sub : sub term) : def_fact Tid.Map.t =
#ifdef VSA_DEBUG
  let census key = Cbat_vsa.Cbat_attr_census.bump key in
#else
  let census _ = () in
#endif
  let addr_bits = Model.word_bits word in
  (* The rewrite's admissibility: the address's whole range lies inside
     the storage's allocated extent — a value or access outside it names
     no storage, and the model arithmetic keeps it. *)
  let in_extent id (lo : int64) (hi : int64) =
    match Core.Map.find geoms id with
    | Some g ->
        Stdlib.Int64.compare lo g.sg_lo >= 0
        && Stdlib.Int64.compare hi g.sg_hi <= 0
    | None -> false
  in
  let region_base id disp =
    match Core.Map.find geoms id with
    | Some g ->
        Base.Option.map disp
          ~f:(base_plus (Model.region_ptr ~addr_bits id) ~rel:g.sg_rel)
    | None -> None
  in
  (* The bases whose sort the value join can ptr-ify: a base with any
     address-valued def, plus the ABI lanes (the kind pass proves them
     from callers and callees).  A displacement piece must not ride one
     — its emitted value may be a real pointer, a different world from
     the model offsets. *)
  let ptr_bases =
    Term.enum blk_t sub
    |> Seq.concat_map ~f:(fun blk ->
           Term.enum def_t blk
           |> Seq.filter_map ~f:(fun d ->
                  match denote ~blk ~def:d (Def.rhs d) with
                  | Ok ws when Vsa.WordSet.in_stack_segment ws ->
                      Some (Var.base (Def.lhs d))
                  | _ -> None))
    |> Seq.fold ~init:Var.Set.empty ~f:(fun acc b -> Core.Set.add acc b)
    |> fun defs ->
    Base.List.fold
      (Hike_abi.param_regs abi @ abi.Hike_abi.return_regs)
      ~init:defs ~f:(fun acc v -> Core.Set.add acc (Var.base v))
  in
  let piece_ok (v : var) = not (Core.Set.mem ptr_bases (Var.base v)) in
  Term.enum blk_t sub
  |> Seq.fold ~init:Tid.Map.empty ~f:(fun acc blk ->
         Term.enum def_t blk
         |> Seq.fold ~init:acc ~f:(fun acc d ->
                if
                  Hike_def_slots.def_is_dyn_alloc d
                  || Hike_def_slots.def_is_rip_relative d
                then acc
                else
                  let leaves = address_leaves ~denote ~blk ~def:d (Def.rhs d) in
                  let fact = no_fact in
                  match Sections.access_of d with
                  | Some (addr, w, _) -> (
                      let conv, _tag =
                        conversion_of ~word ~entry ~tree ~data ~projected:
                          (Base.Option.join
                             (Core.Map.find projections (Term.tid d)))
                          ~access:(Sections.access_of d)
                      in
                      let addr_range () =
                        match denote ~blk ~def:d addr with
                        | Ok ws when not (Vsa.WordSet.is_infinite ws) -> (
                            match Model.positions_of_offsets ws with
                            | Some (lo, hi)
                              when Stdlib.Int64.compare lo hi <= 0 ->
                                Some (lo, hi)
                            | _ -> None)
                        | _ -> None
                      in
                      match conv with
                      | Conv_region id when
                          Base.Option.value_map (addr_range ())
                            ~default:false ~f:(fun (lo, hi) ->
                              in_extent id lo hi)
                          -> (
                          let folded = offset_of ~piece_ok ~leaves addr in

                          census
                            (if Int.equal id Model.residue_id then
                               (match folded with
                                | Some _ -> "rw.access.residue.folded"
                                | None -> "rw.access.residue.geom")
                             else
                               (match folded with
                                | Some _ -> "rw.access.region.folded"
                                | None -> "rw.access.region.geom"));
                          let f =
                            match region_base id folded with
                            | Some a -> { fact with fr_addr = Some a }
                            | None -> fact
                          in
                          Core.Map.set acc ~key:(Term.tid d)
                            ~data:{ f with fr_conv = conv; fr_bits = 8 * w })
                      | Conv_region id ->
                          census
                            (if Int.equal id Model.residue_id then
                               "rw.access.residue.outside"
                             else "rw.access.region.outside");
                          Core.Map.set acc ~key:(Term.tid d)
                            ~data:{ fact with fr_conv = conv; fr_bits = 8 * w }
                      | Conv_window ->
                          census "rw.access.window";
                          (* The window's base is the parameter; its
                             coordinate IS the entry-relative offset. *)
                          let f =
                            match
                              Base.Option.map
                                (offset_of ~piece_ok ~leaves addr)
                                ~f:(base_plus (Model.hike_window_var ~word)
                                       ~rel:0L)
                            with
                            | Some a -> { fact with fr_addr = Some a }
                            | None -> fact
                          in
                          Core.Map.set acc ~key:(Term.tid d)
                            ~data:{ f with fr_conv = conv; fr_bits = 8 * w }
                      | Conv_global _ ->
                          census "rw.access.section";
                          Core.Map.set acc ~key:(Term.tid d)
                            ~data:{ fact with fr_conv = conv; fr_bits = 8 * w }
                      | _ ->
                          census "rw.access.keep";
                          Core.Map.set acc ~key:(Term.tid d)
                            ~data:
                              { fact with fr_conv = conv;
                                fr_bits = 8 * w })
                  | None -> (
                      let v = Def.lhs d in
                      if
                        Model.is_mem v
                        || Hike_abi.is_sp abi (Var.base v)
                        || not
                             (match Var.typ v with
                              | Type.Imm n -> Int.equal n addr_bits
                              | _ -> false)
                      then acc
                      else
                        match denote ~blk ~def:d (Def.rhs d) with
                        | Error _ -> acc
                        | Ok ws
                          when not (Vsa.WordSet.in_stack_segment ws)
                               && not (Vsa.WordSet.is_top ws)
                               && not (Vsa.WordSet.is_bottom ws) -> (
                            (* A plain constant address routes to its
                               component's base: the binding wholly
                               owning it, minus the component's own low
                               bound.  A constant at a copy-relocated
                               slot is externally owned — it keeps the
                               raw lane. *)
                            match Model.singleton_i64 ws with
                            | None -> census "rw.value.raw"; acc
                            | Some c -> (
                                let at_slot =
                                  Base.List.exists spans ~f:(fun sp ->
                                      Sections.equal_sec sp.Sections.ds_sec
                                        (Sections.point Rodata c).p_sec
                                      && Base.List.exists sp.Sections.ds_slots
                                           ~f:(fun sl ->
                                             Stdlib.Int64.equal sl c))
                                in
                                match
                                  (at_slot,
                                   owning_data_binding data c)
                                with
                                | false, Some (id, comp_lo) -> (
                                    (* A pure constant address materializes
                                       at this def: the component's pointer
                                       base plus its own constant.  A value
                                       with var leaves composes over its
                                       operands' own pointers — the address
                                       defs carrying it already render the
                                       real bits, so a re-base here would
                                       materialize the address twice. *)
                                    match
                                      offset_of ~piece_ok ~leaves (Def.rhs d)
                                    with
                                    | Some (Bil.Int w) ->
                                        census "rw.value.section";
                                        let rhs =
                                          match
                                            Cbat_word.to_int64
                                              (Cbat_word.of_word w)
                                          with
                                          | Ok k
                                            when Stdlib.Int64.equal k c ->
                                              base_plus
                                                (Model.sec_comp_ptr
                                                   ~addr_bits id)
                                                ~rel:comp_lo (Bil.Int w)
                                          | _ ->
                                              Bil.BinOp
                                                ( Bil.PLUS,
                                                  Bil.Var
                                                    (Model.sec_comp_ptr
                                                       ~addr_bits id),
                                                  Bil.BinOp
                                                    ( Bil.MINUS,
                                                      Bil.Int w,
                                                      Bil.Int
                                                        (Cbat_word.to_word
                                                           (Cbat_word
                                                              .of_int64
                                                              ~width:64
                                                              comp_lo))
                                                    ) )
                                        in
                                        Core.Map.set acc ~key:(Term.tid d)
                                          ~data:
                                            { fact with fr_rhs = Some rhs }
                                    | _ ->
                                        census "rw.value.section.carried";
                                        acc)
                                | _ -> census "rw.value.raw"; acc))
                        | Ok ws when Core.Map.is_empty leaves -> (
                            (* A pure constant is a machine constant, not
                               a synthesized address: the model's stack
                               line sits at 2^62, and a double's bits can
                               land inside it — only a value with var
                               leaves (an SP-derived address) routes to
                               the frame's storages. *)
                            census "rw.value.raw";
                            acc)
                        | Ok ws -> (
                            (* The routing of an address value: at/above
                               the args base it names the caller's window
                               (the parameter is the base); below the
                               entry line the tree's binding owns its
                               whole range. *)
                            match Vsa.WordSet.origin ws with
                            | Some (Vsa.WordSet.Origin.Vla tid)
                              when (not (Vsa.WordSet.is_infinite ws))
                                   && Core.Set.mem vla_tids tid -> (
                                (* The offsets are frame-relative: the
                                   allocation's base is byte zero, no
                                   position arithmetic applies. *)
                                match
                                  Base.Option.map
                                    (offset_of ~piece_ok ~leaves (Def.rhs d))
                                    ~f:(base_plus (Model.vla_ptr ~addr_bits tid)
                                         ~rel:0L)
                                with
                                | Some rhs ->
                                    census "rw.value.vla";
                                    Core.Map.set acc ~key:(Term.tid d)
                                      ~data:{ fact with fr_rhs = Some rhs }
                                | None ->
                                    census "rw.value.vla.unfoldable"; acc)
                            | Some (Vsa.WordSet.Origin.Vla _) ->
                                census "rw.value.vla"; acc
                            | _ -> (
                                let a_base = Model.args_base ~entry ~word in
                                match
                                  (not (Vsa.WordSet.is_infinite ws),
                                   Model.positions_of_offsets ws)
                                with
                                | true, Some (lo, hi)
                                  when Stdlib.Int64.compare lo hi <= 0
                                       && Stdlib.Int64.compare lo a_base >= 0
                                       && window_param -> (
                                    match
                                      Base.Option.map
                                        (offset_of ~piece_ok ~leaves
                                           (Def.rhs d))
                                        ~f:(base_plus
                                              (Model.hike_window_var ~word)
                                              ~rel:0L)
                                    with
                                    | Some rhs ->
                                        census "rw.value.window";
                                        Core.Map.set acc ~key:(Term.tid d)
                                          ~data:{ fact with fr_rhs = Some rhs }
                                    | None ->
                                        census "rw.value.window.unfoldable";
                                        acc)
                                | true, Some (lo, hi)
                                  when Stdlib.Int64.compare lo hi <= 0 -> (
                                    match owning_storage tree lo hi with
                                    | Some
                                        ((Stack_region _ | Stack_residue) as
                                        st)
                                      when in_extent
                                             (region_id_of_storage st) lo hi
                                      -> (
                                        match
                                          region_base (region_id_of_storage st)
                                            (offset_of ~piece_ok ~leaves
                                               (Def.rhs d))
                                        with
                                        | Some rhs ->
                                            census "rw.value.region";
                                            Core.Map.set acc
                                              ~key:(Term.tid d)
                                              ~data:{ fact with fr_rhs = Some rhs }
                                        | None ->
                                            census "rw.value.region.unfoldable";
                                            acc)
                                    | Some _ -> census "rw.value.window"; acc
                                    | None -> census "rw.value.raw"; acc)
                                | _ -> census "rw.value.raw"; acc)))))

(* Every memory node of the expression re-points at [mem_var] — a
   converted def keeps no model-memory node — and takes [addr] as its
   address when the rewrite computed the storage-relative form.  The
   override receives children unmapped, so it maps the address and
   store data itself. *)
let repoint_mapper ?(addr : exp option) (mem_var : var) =
  object
    inherit Exp.mapper as super
    method! map_load ~mem:_ ~addr:a rest s =
      Bil.Load
        ( Bil.Var mem_var,
          (match addr with Some e -> e | None -> super#map_exp a),
          rest, s )
    method! map_store ~mem:_ ~addr:a ~exp rest s =
      Bil.Store
        ( Bil.Var mem_var,
          (match addr with Some e -> e | None -> super#map_exp a),
          super#map_exp exp, rest, s )
  end

(* A slot access keeps its memory node and takes [addr] as its address:
   the load/store is real, through the caller's slot pointer. *)
let slot_addr_mapper (addr : exp) =
  object
    inherit Exp.mapper as super
    method! map_load ~mem ~addr:_ endian size =
      Bil.Load (mem, addr, endian, size)
    method! map_store ~mem ~addr:_ ~exp endian size =
      Bil.Store (mem, addr, super#map_exp exp, endian, size)
  end

(* One def's rewrite: re-point to the owning storage's mem var at the
   storage-relative address, or address its memory node at the caller's
   slot. *)
let rewrite_def ~(addr_bits : int) ~(conv : conv) ~(bits : int)
    ?(addr : exp option) (d : def term) : def term =
  match conv with
  | Keep -> d
  | Conv_region id ->
      let mem_var = Model.region_mem ~addr_bits:bits id in

      let d =
        Def.map_exp d ~f:(fun e -> (repoint_mapper ?addr mem_var)#map_exp e)
      in

      if Model.is_mem (Def.lhs d) then Def.with_lhs d mem_var else d
  | Conv_window ->
      let mem_var = Model.window_mem ~addr_bits:bits in
      let d =
        Def.map_exp d ~f:(fun e -> (repoint_mapper ?addr mem_var)#map_exp e)
      in
      if Model.is_mem (Def.lhs d) then Def.with_lhs d mem_var else d
  | Conv_global id ->
      let mem_var = Model.sec_comp_mem ~addr_bits:bits id in
      let d =
        Def.map_exp d ~f:(fun e -> (repoint_mapper mem_var)#map_exp e)
      in
      if Model.is_mem (Def.lhs d) then Def.with_lhs d mem_var else d
  | Conv_slot (i, byte_offset) ->
      let slot = Model.arg_slot ~addr_bits i in
      let addr =
        base_plus slot ~rel:0L
          (Bil.Int
             (Cbat_word.to_word
                (Cbat_word.of_int64 ~width:addr_bits
                   (Stdlib.Int64.of_int byte_offset))))
      in
      Def.map_exp d ~f:(fun e -> (slot_addr_mapper addr)#map_exp e)

(* Each call site's stored slot gains its [hike_argN] def binding the
   caller's own slot ADDRESS: the store's address, which the rewrite
   above already re-pointed at the caller's storage.  A partial store
   passes its address too — the callee reads and writes the exact
   bytes. *)
let bind_site_args ~(addr_bits : int) (bindings : site_binding list)
    (blk : blk term) : blk term =
  Base.List.fold bindings ~init:blk ~f:(fun blk b ->
      (* [b.sb_def] is the PRE-rewrite term; its address is read off the
         rewritten block, whose mapper has already run. *)
      let addr =
        match Term.find def_t blk (Term.tid b.sb_def) with
        | Some d -> (
            match Model.addr_of_rhs (Def.rhs d) with
            | Some (a, _) -> a
            | None ->
                failwith
                  ("hike-promote: call-arg binding: slot "
                  ^ Int.to_string b.sb_slot
                  ^ "'s store address is not readable after the rewrite"))
        | None ->
            failwith
              ("hike-promote: call-arg binding: slot "
             ^ Int.to_string b.sb_slot
             ^ "'s storing def is not in its block")
      in
      let arg = Def.create (Model.call_arg ~addr_bits b.sb_slot) addr in
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

let promote_sub ~(addr_bits : int) (facts : facts)
    (sub : sub term) : sub term =
  let with_signature sub =
    if Hike_stack_model.fixed_signature sub then sub
    else
      (* Promotion defines the sub's whole argument convention: the
         slots in signature order replace the sub's args.  A slot is the
         caller's cell ADDRESS, so the parameter is a pointer. *)
      let slots =
        Base.List.init facts.prom_arity ~f:(fun i ->
            Arg.create ~intent:In (Model.arg_slot ~addr_bits i)
              (Bil.Var (Model.arg_slot ~addr_bits i)))
      in
      Model.set_sig sub slots
  in
  resolve_targets ~resolved:facts.prom_resolved (with_signature sub)


(* The promoted slots' arity: one per word cell the tree's Arg_slot
   members name, derived from each member's own address — the binding is
   never the unit. *)
let slot_arity ~(word : int) ~(entry : int64) (tree : Sections.sub_tree) : int =
  let arity =
    Sections.Tree.to_sequence tree
    |> Seq.fold ~init:None ~f:(fun mx (_, rs) ->
           match rs.storage with
           | Arg_slot ->
               Base.List.fold rs.members ~init:mx ~f:(fun mx mm ->
                   match Sections.args_member_cell ~word ~entry mm with
                   | Some i -> (
                       match mx with
                       | Some n -> Some (Int.max n i)
                       | None -> Some i)
                   | None -> mx)
           | _ -> mx)
  in
  match arity with Some i -> i + 1 | None -> 0

(* The per-sub rewrite: promotion, the storage rewrite, and the layout
   stamp.  [sites]/[resolved] are the call-site and resolution
   products. *)
let rewrite_sub ~(word : int) ~(entry : int64) ~(addr_bits : int)
    ~(abi : Hike_abi.t)
    ~(spans : Sections.data_span list)
    ~(denote : blk:blk term -> ?def:def term -> exp ->
                (Vsa.WordSet.t, Type.error) Result.t)
    ~(ctx : Sections.ctx)
    ~(sites : (site_binding list * blk term) Tid.Map.t)
    ~(resolved : Tid.t option Tid.Map.t)
    ~(vla_tids : Tid.Set.t)
    ~(callee_exempt : bool)
    (sub : sub term) : sub term =
  (* A fixed-signature sub (@main, an emittable intrinsic) carries a
     convention of its own, never the ABI's, so it is not a variadic
     definition however its body is built. *)
  let variadic =
    (not callee_exempt)
    && Model.is_variadic_construction ~abi ~entry ~denote sub
  in
  let tree =
    Core.Map.find ctx.sub_trees (Term.tid sub)
    |> Core.Option.value ~default:Sections.Tree.empty
  in
  let arity = slot_arity ~word ~entry tree in
  let arity = if callee_exempt then 0 else arity in
  let facts = { prom_arity = arity; prom_resolved = resolved } in
  let sub = promote_sub ~addr_bits facts sub in
  (* A non-memory def whose value is a caller-window address — the
     model's one window denotation — is stamped; the emitter re-bases
     its integer to the window parameter. *)
  let window_values =
    Term.enum blk_t sub
    |> Seq.fold ~init:Tid.Set.empty ~f:(fun acc blk ->
        Term.enum def_t blk
        |> Seq.fold ~init:acc ~f:(fun acc d ->
            if Core.Option.is_some (Model.addr_of_rhs (Def.rhs d)) then acc
            else
              match denote ~blk ~def:d (Def.rhs d) with
              | Error _ -> acc
              | Ok ws ->
                  if Model.is_window_denotation ~entry ~word ws then
                    Core.Set.add acc (Term.tid d)
                  else acc))
  in
  let sub = Hike_def_slots.stamp_window_values ~window_values sub in
  (* The layout precedes the rewrite: each storage's base offset [rel]
     reads off it, and the rewrite's value forms must not perturb the
     region geometry the layout measures. *)
  let layout = Sections.layout_of_tree ~word ~entry ~abi ~sub tree in
  let geoms = geoms_of_layout layout in
  (* The window forms need the signature's window parameter: a
     fixed-signature sub (@main, the intrinsics) never carries it.  A
     window-VALUE def forces the parameter (the layout is stamped with it
     below), so the forms are available for it too. *)
  let window_ok =
    (layout.Hike_stack_model.window_param
    || not (Core.Set.is_empty window_values))
    && not callee_exempt
  in
  let facts =
    def_facts ~word ~entry ~abi ~tree ~data:ctx.data_tree
      ~projections:ctx.projections ~geoms ~window_param:window_ok
      ~vla_tids ~spans ~denote sub
  in
  (* The second pass: one general [Term.mapper] over the sub.  Every def
     (and phi) the attribution proved is rewritten to its owning
     storage — no ad-hoc def filtering. *)
  let rewrite =
    object
      inherit Term.mapper as super

      method! map_def d =
        let d = super#map_def d in
        match Core.Map.find facts (Term.tid d) with
        | None -> d
        | Some f -> (
            match f.fr_rhs with
            | Some rhs -> Def.with_rhs d rhs
            | None ->
                let d =
                  rewrite_def ~addr_bits ~conv:f.fr_conv ~bits:f.fr_bits
                    ?addr:f.fr_addr d
                in
                (* The conversion names the address's own alloca; carry
                   it on the def so the emitter materializes into that
                   region, never the operand's. *)
                match f.fr_conv with
                | Conv_region id ->
                    Hike_def_slots.stamp_ptr_storage (Model.Ptr_region id) d
                | Conv_window ->
                    Hike_def_slots.stamp_ptr_storage Model.Ptr_window d
                | Conv_slot _ | Conv_global _ | Keep -> d)

      method! map_blk blk =
        let blk = super#map_blk blk in
        match Core.Map.find sites (Term.tid blk) with
        | Some (bs, _) -> bind_site_args ~addr_bits bs blk
        | None -> blk
    end
  in
  let sub = rewrite#map_sub sub in
  (* The signature carries the window parameter whenever a
     window-value def exists. *)
  let layout =
    if Core.Set.is_empty window_values then layout
    else { layout with Hike_stack_model.window_param = true }
  in
  let sub = Hike_stack_model.set_layout layout sub in
  if variadic then Hike_stack_model.set_variadic sub else sub

(* The program driver: per-sub sites and resolution, the rewrite. *)
let rewrite_program ~(word : int) ~(entry : int64) ~(facts : Hike_kb.facts)
    ~(spans : Sections.data_span list)
    ~(ctx : Sections.ctx)
    (prog : program term) : program term =
  let abi = facts.abi in
  let denote = facts.denote in
  let sp = abi.Hike_abi.sp in
  let lookup = facts.lookup in
  (* The slot vars are address lanes: the run's target address width,
     the same fact the emitter threads. *)
  let addr_bits = Bap_core_theory.Theory.Target.bits facts.target in
  let callee_exempt = Hike_stack_model.fixed_signature in
  let exempt =
    Term.enum sub_t prog
    |> Seq.fold ~init:Tid.Set.empty ~f:(fun acc s ->
           if callee_exempt s then Core.Set.add acc (Term.tid s) else acc)
  in
  let sides =
    Term.enum sub_t prog
    |> Seq.fold ~init:Tid.Map.empty ~f:(fun acc sub ->
           let sites =
             site_bindings_of_sub_with_blocks ~word ~abi ~sp ~denote sub
           in
           let resolved = call_resolution ~denote ~lookup sub in
           Core.Map.set acc ~key:(Term.tid sub) ~data:(sites, resolved))
  in
  Term.map sub_t prog ~f:(fun sub ->
      let sites, resolved =
        Core.Map.find sides (Term.tid sub)
        |> Core.Option.value ~default:(Tid.Map.empty, Tid.Map.empty)
      in
      rewrite_sub ~word ~entry ~addr_bits ~abi ~spans ~denote ~ctx ~sites
        ~resolved
        ~vla_tids:(Core.Map.key_set facts.Hike_kb.vla_extents)
        ~callee_exempt:(Core.Set.mem exempt (Term.tid sub))
        sub)
