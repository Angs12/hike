(* Sweeps dead defs; region mems survive iff loaded. *)
open Bap.Std
open Bap.Std.Bil.Types
module Abi = Hike_abi

(* Registers read implicitly by calls. *)
let is_call_reg ~(abi : Abi.t) (v : var) : bool =
  let regs = Abi.param_regs abi @ abi.Abi.return_regs in
  Base.List.exists regs ~f:(fun r -> Var.same r (Var.base v))

(* The sweep census: contributor counts behind [used]/[roots].  Jmp/phi
   mentions are permanent (only defs are ever removed); [cnt]/[rcnt] count
   SURVIVING defs mentioning each var, so a var leaves its set exactly when
   its count hits zero outside [perm] and the cascade re-checks precisely the
   defs whose [keep] verdict could have flipped. *)
type sweep_census = {
  defs : def term Tid.Map.t;
  (* Defs whose lhs is the key var (re-check set when the var leaves). *)
  by_lhs : Tid.Set.t Var.Map.t;
  (* Rhs free vars per def (contributor counts for [used]). *)
  fvs : Var.Set.t Tid.Map.t;
  (* Load-mem free vars per def (contributor counts for [roots]). *)
  lms : Var.Set.t Tid.Map.t;
  cnt : int Var.Map.t;
  rcnt : int Var.Map.t;
  perm : Var.Set.t;
}

let load_mem_vars (rhs : exp) : Var.Set.t =
  Hike_stack_model.load_mem_vars rhs

let sweep_census_of (sub : sub term) : sweep_census =
  let bump m v =
    Core.Map.update m v ~f:(function None -> 1 | Some n -> n + 1)
  in
  let bump_all m vs = Core.Set.fold vs ~init:m ~f:(fun m v -> bump m v) in
  let init =
    {
      defs = Tid.Map.empty;
      by_lhs = Var.Map.empty;
      fvs = Tid.Map.empty;
      lms = Tid.Map.empty;
      cnt = Var.Map.empty;
      rcnt = Var.Map.empty;
      perm = Var.Set.empty;
    }
  in
  let census_blk acc blk =
    let acc =
      Term.enum def_t blk
      |> Seq.fold ~init:acc ~f:(fun acc d ->
          let tid = Term.tid d in
          let lhs = Def.lhs d in
          let fvs = Exp.free_vars (Def.rhs d) in
          let lms = load_mem_vars (Def.rhs d) in
          let by_lhs =
            Core.Map.update acc.by_lhs lhs ~f:(function
              | None -> Tid.Set.singleton tid
              | Some s -> Core.Set.add s tid)
          in
          {
            acc with
            defs = Core.Map.set acc.defs ~key:tid ~data:d;
            by_lhs;
            fvs = Core.Map.set acc.fvs ~key:tid ~data:fvs;
            lms = Core.Map.set acc.lms ~key:tid ~data:lms;
            cnt = bump_all acc.cnt fvs;
            rcnt = bump_all acc.rcnt lms;
          })
    in
    let perm =
      Term.enum jmp_t blk
      |> Seq.fold ~init:acc.perm ~f:(fun s j ->
          Core.Set.union s (Jmp.free_vars j))
    in
    let perm =
      Term.enum phi_t blk
      |> Seq.fold ~init:perm ~f:(fun s p ->
          Core.Set.union s (Phi.free_vars p))
    in
    { acc with perm }
  in
  Term.enum blk_t sub |> Seq.fold ~init ~f:census_blk

let is_intrinsic_var (v : var) : bool =
  Hike_stack_model.is_intrinsic_name (Var.name (Var.base v))

(* Region and section-component mems survive iff loaded; call-arg defs
   survive (they ARE the call's arguments — the emission consumes them at
   the call); [mem] always survives.  SP needs no special case: the SP local
   binds to the sub's SP Slot, so SP-derived address defs stay live by the
   plain used rule. *)
let keep ?(load_roots=Var.Set.empty)
    ~(abi : Abi.t) (d : def term) (used : Var.Set.t) : bool =
  let lhs = Def.lhs d in
  if Hike_stack_model.is_window_mem lhs then
    (* The incoming window's stores are the call's outgoing arguments —
       their reader is the callee, never a def of this sub. *)
    true
  else if Hike_stack_model.is_region_mem lhs
  || Hike_stack_model.is_sec_comp_mem lhs then
    Core.Set.mem load_roots lhs
  else
    Core.Set.mem used lhs || Abi.is_return_reg abi (Var.base lhs)
    || Hike_stack_model.is_mem lhs
    || Hike_stack_model.is_call_arg lhs
    || is_call_reg ~abi lhs || is_intrinsic_var lhs

(* Incremental sweep: [used] and [load_roots] start exact and stay exact (a
   var leaves only when its last contributor is removed), so each [keep]
   verdict is final. *)
let sweep_worklist ~(abi : Abi.t) ~(roots : Var.Set.t) (sub : sub term) :
    sub term =
  let census = sweep_census_of sub in
  let dom m =
    Core.Map.fold m ~init:Var.Set.empty ~f:(fun ~key:v ~data:_ acc ->
        Core.Set.add acc v)
  in
  let used = ref (Core.Set.union census.perm (dom census.cnt)) in
  let load_roots =
    ref
      (Core.Set.union roots (Core.Set.union census.perm (dom census.rcnt)))
  in
  let cnt = ref census.cnt in
  let rcnt = ref census.rcnt in
  let removed = ref Tid.Set.empty in
  (* A contributor leaving can only flip defs whose lhs it is. *)
  let readers_of v =
    Core.Map.find census.by_lhs v |> Option.value ~default:Tid.Set.empty
  in
  let leave counts v =
    match Core.Map.find !counts v with
    | Some n when n > 1 ->
        counts := Core.Map.set !counts ~key:v ~data:(n - 1);
        false
    | _ ->
        counts := Core.Map.remove !counts v;
        true
  in
  let rec drain = function
    | [] -> ()
    | tid :: rest -> (
        match Core.Map.find census.defs tid with
        | None -> drain rest
        | Some d ->
            if
              Core.Set.mem !removed tid
              || keep ~load_roots:!load_roots ~abi d !used
            then drain rest
            else begin
              removed := Core.Set.add !removed tid;
              let unuse counts set v q =
                if leave counts v && not (Core.Set.mem census.perm v) then begin
                  set := Core.Set.remove !set v;
                  Core.Set.fold (readers_of v) ~init:q ~f:(fun q t ->
                      t :: q)
                end
                else q
              in
              let rest =
                Core.Set.fold
                  (Core.Map.find census.fvs tid
                  |> Option.value ~default:Var.Set.empty)
                  ~init:rest
                  ~f:(fun q v -> unuse cnt used v q)
              in
              let rest =
                Core.Set.fold
                  (Core.Map.find census.lms tid
                  |> Option.value ~default:Var.Set.empty)
                  ~init:rest
                  ~f:(fun q m -> unuse rcnt load_roots m q)
              in
              drain rest
            end)
  in
  drain (Core.Map.keys census.defs);
  if Core.Set.is_empty !removed then sub
  else
    Term.map blk_t sub ~f:(fun blk ->
        if
          Term.enum def_t blk
          |> Seq.exists ~f:(fun d -> Core.Set.mem !removed (Term.tid d))
        then
          Term.filter def_t blk ~f:(fun d ->
              not (Core.Set.mem !removed (Term.tid d)))
        else blk)

(* A return-less call never consumes its target; rendering it Unknown frees
   the def that produced it. *)
let ret_replacement ~(word_bits : int) (j : jmp term) : jmp term =
  match Jmp.kind j with
  | Call c -> (
      match (Call.target c, Call.return c) with
      | Indirect (Bil.Var _), None ->
        Jmp.with_kind j
          (Call
             (Call.with_target c
                (Indirect (Bil.Unknown ("hike-dce-ret", Type.Imm word_bits)))))
      | _ -> j)
  | _ -> j

(* [roots] names the storage mem vars whose bytes escape this sub — their
   stores' reader lives outside it.  Intrinsics pass through. *)
let dce ?(roots = Var.Set.empty) ~target (sub : sub term) : sub term =
  if Term.has_attr sub Sub.intrinsic then sub
  else
    let abi = Abi.of_target target in
    let word_bits = 8 * abi.Abi.word in
    let sub =
      Term.map blk_t sub
        ~f:(Blk.map_elts ~jmp:(ret_replacement ~word_bits))
    in
    sweep_worklist ~abi ~roots sub
