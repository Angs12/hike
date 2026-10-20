(* The node-fission pass: every def keeps exactly one memory node
   inline; the later nodes of a multi-node rhs become fresh synthetic
   load defs before it, reading the same mem-var state (nested loads
   see pre-store memory either way).  The per-def tag is then the
   complete proof of the def's only memory node. *)

open Bap.Std

(* The first memory node stays inline (the one the VSA's
   classification describes); every distinct later load becomes a
   fresh synthetic def; equal later nodes share one def. *)
let split_def ~(synth : Hike_synth.table ref) (d : def term) : def term list =
  let rhs = Def.rhs d in
  if Hike_stack_model.mem_node_count rhs <= 1 then [ d ]
  else
    let later = ref ([] : (exp * var) list) in
    let seen = ref 0 in
    let fresh_node ~bits node =
      match Base.List.Assoc.find ~equal:Exp.equal !later node with
      | Some v -> v
      | None ->
        let v =
          Hike_synth.record synth
            (Hike_synth.mint_fresh ~bits:(Size.in_bits bits) Hike_synth.Load)
        in
        later := (node, v) :: !later;
        v
    in
    let m =
      object
        inherit Exp.mapper as super
        method! map_load ~mem ~addr e s =
          incr seen;
          if !seen = 1 then super#map_load ~mem ~addr e s
          else Bil.Var (fresh_node ~bits:s (Bil.Load (mem, addr, e, s)))
        method! map_store ~mem ~addr ~exp:e rest s =
          (* The first (pre-order) store node is the def's own write —
             the def defines the mem var; a later (nested or second)
             store hoists like a load: one node per def, always. *)
          incr seen;
          if !seen = 1 then super#map_store ~mem ~addr ~exp:e rest s
          else Bil.Var (fresh_node ~bits:s (Bil.Store (mem, addr, e, rest, s)))
      end
    in
    let rhs' = m#map_exp rhs in
    let hoists =
      Base.List.rev !later
      |> Base.List.map ~f:(fun (node, v) -> Def.create v node)
    in
    hoists @ [ Def.with_rhs d rhs' ]

(* One block's rewrite: identity unless a def needs splitting. *)
let split_block ~(synth : Hike_synth.table ref) (blk : blk term) : blk term =
  let bad =
    Term.enum def_t blk
    |> Seq.exists ~f:(fun d -> Hike_stack_model.mem_node_count (Def.rhs d) > 1)
  in
  if not bad then blk
  else Term.concat_map def_t blk ~f:(split_def ~synth)

(* Identity unless a def needs splitting. *)
let split_sub ~(synth : Hike_synth.table ref) (sub : sub term) : sub term =
  (* One traversal decides; the map pass re-checks only the blocks it
     visits after the cheap whole-sub reject. *)
  let offending =
    Term.enum blk_t sub
    |> Seq.filter_map ~f:(fun blk ->
        let bad =
          Term.enum def_t blk
          |> Seq.exists ~f:(fun d -> Hike_stack_model.mem_node_count (Def.rhs d) > 1) in
        if bad then Some (Term.tid blk) else None)
    |> Seq.to_list
  in
  if Base.List.is_empty offending then sub
  else
    let offending = Tid.Set.of_list offending in
    Term.map blk_t sub ~f:(fun blk ->
        if Core.Set.mem offending (Term.tid blk) then
          split_block ~synth blk
        else blk)

let normalize ~(synth : Hike_synth.table) (prog : program term) :
    Hike_synth.table * program term =
  let cell = ref synth in
  let prog = Term.map sub_t prog ~f:(split_sub ~synth:cell) in
  (!cell, prog)
