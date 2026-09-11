(* Sweeps dead defs; region mems survive iff loaded. *)

open Bap.Std
open Bap.Std.Bil.Types
module Abi = Hike_abi

(* Registers read implicitly by calls. *)
let is_call_reg ~(abi : Abi.t) (v : var) : bool =
  let regs = abi.Abi.int_param_regs @ abi.Abi.vector_param_regs @ abi.Abi.return_regs in
  Base.List.exists regs ~f:(fun r -> Var.same r (Var.base v))

(* Rewrites the return epilogue to a var-free target. *)
let ret_replacement (j : jmp term) : jmp term =
  match Jmp.kind j with
  | Call c -> (
      match (Call.target c, Call.return c) with
      | Indirect (Bil.Var _), None ->
          Jmp.create ~tid:(Term.tid j) ~cond:(Jmp.cond j)
            (Call
               (Call.create
                  ~target:
                    (Indirect (Bil.Unknown ("hike-dce-ret", Type.Imm 64)))
                  ()))
      | _ -> j)
  | _ -> j

(* One-pass sweep census: the def index, the lhs reader map, and the
   contributor counts behind [used]/[roots]. Jmp/phi mentions are
   permanent (only defs are ever removed). [cnt]/[rcnt] count SURVIVING
   defs mentioning each var, so a var leaves its set exactly when its
   count hits zero outside [perm] — the cascade below then re-checks
   precisely the defs whose [keep] verdict could have flipped. *)
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

(* Free vars of every Load mem in one rhs. *)
let load_mem_vars (rhs : exp) : Var.Set.t =
  let v =
    object
      inherit [Var.Set.t] Exp.visitor
      method! visit_load ~mem ~addr:_ _ _ acc =
        Core.Set.union acc (Exp.free_vars mem)
    end
  in
  v#visit_exp rhs Var.Set.empty

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

(* Tests for intrinsic interface vars. *)
let is_intrinsic_var (v : var) : bool =
  Bil2llvm_env.is_intrinsic_name (Var.name (Var.base v))

(* Region mems survive iff loaded; the promotion's call-arg defs survive
   (they ARE the call's arguments — the emission consumes them at the
   call); [mem] always survives.  (T3 deleted the precise-lane SP
   erasure: the uniform materialization READS the SP-derived address
   arithmetic — since T4 the SP local binds to the sub's own SP Slot at
   entry, so those defs are defined and their liveness is the plain
   used-based rule.) *)
let keep ?(load_roots=Var.Set.empty)
    ~(abi : Abi.t) (d : def term) (used : Var.Set.t) : bool =
  let lhs = Def.lhs d in
  if Hike_stack_model.is_region_mem lhs then
    Core.Set.mem load_roots lhs
  else
    Core.Set.mem used lhs || Abi.is_return_reg abi (Var.base lhs)
    || Hike_stack_model.is_mem lhs
    || Hike_stack_model.is_call_arg lhs
    || is_call_reg ~abi lhs || is_intrinsic_var lhs

(* Incremental sweep: one census walk, then a removal cascade. [used] and
   [load_roots] start exact (permanent mentions plus every counted var)
   and stay exact (a var leaves only when its last contributor is
   removed), so each [keep] verdict equals the round version's verdict at
   convergence — and each def is decided at most a handful of times
   instead of once per round. Blocks that lose nothing keep their
   physical block (no rebuild). *)
let sweep_worklist ~(abi : Abi.t) (sub : sub term) : sub term =
  let census = sweep_census_of sub in
  let dom m =
    Core.Map.fold m ~init:Var.Set.empty ~f:(fun ~key:v ~data:_ acc ->
        Core.Set.add acc v)
  in
  let used = ref (Core.Set.union census.perm (dom census.cnt)) in
  let load_roots = ref (Core.Set.union census.perm (dom census.rcnt)) in
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

(* Rewrites returns, then sweeps. Intrinsics pass through. *)
let dce ~target (sub : sub term) : sub term =
  if Term.has_attr sub Sub.intrinsic then sub
  else
    let mapper =
      object
        inherit Term.mapper
        method! map_jmp j = ret_replacement j
      end
    in
    let abi = Abi.of_target target in
    mapper#map_sub sub |> sweep_worklist ~abi
