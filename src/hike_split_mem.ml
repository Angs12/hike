(* The node-fission pass: every def keeps exactly one memory node
   inline; the later nodes of a multi-node rhs become fresh virtual
   load defs before it, reading the same mem-var state (nested loads
   see pre-store memory either way).  The per-def tag is then the
   complete proof of the def's only memory node. *)

open Bap.Std

let mem_count (e : exp) : int = Hike_stack_model.mem_node_count e

(* The first memory node stays inline (the one the VSA's
   classification describes); every distinct later load becomes a
   fresh virtual def; equal later nodes share one def. *)
let split_def (d : def term) : def term list =
  let rhs = Def.rhs d in
  if mem_count rhs <= 1 then [ d ]
  else
    let later = ref ([] : (exp * var) list) in
    let seen = ref 0 in
    let fresh_node ~bits node =
      match Base.List.Assoc.find ~equal:Exp.equal !later node with
      | Some v -> v
      | None ->
        let v =
          Var.create ~is_virtual:true ~fresh:true "hike_ld"
            (Type.Imm (Size.in_bits bits))
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

(* Identity unless a def needs splitting. *)
let split_sub (sub : sub term) : sub term =
  let needs =
    Term.enum blk_t sub
    |> Seq.exists ~f:(fun blk ->
        Term.enum def_t blk |> Seq.exists ~f:(fun d -> mem_count (Def.rhs d) > 1))
  in
  if not needs then sub
  else
    Term.map blk_t sub ~f:(fun blk ->
        let defs = Term.enum def_t blk |> Seq.to_list in
        if Base.List.for_all defs ~f:(fun d -> mem_count (Def.rhs d) <= 1) then
          blk
        else Term.concat_map def_t blk ~f:split_def)

let normalize (prog : program term) : program term =
  Term.map sub_t prog ~f:split_sub
