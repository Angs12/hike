(* The analysis closure: the run's facts as ONE value, built by
   [build] at the discover boundary and threaded through every
   consumer as a parameter.  The KB value slots (sec-tag, dyn-alloc,
   window) stay the term-carried half; the module has no read API for
   the closure — [install]/[facts] move the record across the pass
   boundary, one fetch per pass entry. *)

open Bap.Std

(* One KB computation, evaluated through a fresh toplevel var. *)
let eval (x : 'a Bap_core_theory.KB.t) : 'a =
  let v = Toplevel.var "hike-kb-eval" in
  Toplevel.put v x;
  Toplevel.get v

(* The denotation seam: [exp] in the before-env of [def], or the
   block's postcondition with no [def]. *)
type denote =
  blk:blk term -> ?def:def term -> exp ->
  (Cbat_vsa.WordSet.t, Type.error) Result.t

type facts = {
  (* One (pre, post) pair per block tid; [post] answers no-def queries
     and [pre] feeds the VSA_DEBUG differential's replay.  Absence
     means the sub's analysis did not converge; [denote] answers
     [AI.top]. *)
  envs : (Cbat_vsa.AI.t * Cbat_vsa.AI.t) Tid.Map.t;
  (* An address to the tid of the block whose extent contains it.
     An empty map keeps every dispatch foreign. *)
  block_addrs : Tid.t Addr.Map.t;
  sub_addrs : Tid.t Addr.Map.t;
  images : Cbat_vsa.section_image list;
  foreign_slots : Core.Int64.Set.t;
  target : Bap_core_theory.Theory.Target.t;
  abi : Hike_abi.t;
  (* [e] denotes in the before-env of [def] — the def's Env Tag — or,
     with no [def], in the block's postcondition (the state a jmp
     reads).  A def with no tag (minted after the boundary) answers
     [AI.top]. *)
  denote : denote;
  (* The run's resolution lookup: one name table for the program,
     built at the discover boundary beside the other facts. *)
  lookup : int64 -> Tid.t option;
  (* The emitter's section spec, installed by the attribution pass in
     the same run that built [envs]; [None] = no attribution ran and
     the sections emit with no components. *)
  spec : Hike_spec.section_spec option;
  (* The SSA definition index: every version VSA solved, with the def or
     phi that defines it. *)
  defs : [ `Def of def term | `Phi of phi term ] Var.Map.t;
  (* The run's synthetic vars with their kinds: each pass that creates
     one records it here, and a var absent from the table is not
     synthetic. *)
  synth : Hike_synth.table;
  (* The user's signatures, as matched against this binary's imports:
     the emitter declares and calls the externals they describe
     exactly. *)
  signatures : Hike_signatures.t;
}

(* The definition index of one solved sub / program.  A version has one
   definition; a duplicate later definition replaces the earlier one, as
   the SSA passes keep only the live version. *)
let defs_of_sub (sub : sub term) : [ `Def of def term | `Phi of phi term ] Var.Map.t =
  Term.enum blk_t sub
  |> Seq.fold ~init:Var.Map.empty ~f:(fun acc blk ->
      let acc =
        Term.enum phi_t blk
        |> Seq.fold ~init:acc ~f:(fun acc p ->
            Core.Map.set acc ~key:(Phi.lhs p) ~data:(`Phi p)) in
      Term.enum def_t blk
      |> Seq.fold ~init:acc ~f:(fun acc d ->
          Core.Map.set acc ~key:(Def.lhs d) ~data:(`Def d)))

let defs_of_program (prog : program term) : [ `Def of def term | `Phi of phi term ] Var.Map.t =
  Term.enum sub_t prog
  |> Seq.fold ~init:Var.Map.empty ~f:(fun acc sub ->
      Core.Map.fold (defs_of_sub sub) ~init:acc ~f:(fun ~key ~data acc ->
          Core.Map.set acc ~key ~data))

let build ~(block_envs : (Cbat_vsa.AI.t * Cbat_vsa.AI.t) Tid.Map.t)
    ~(lookup : int64 -> Tid.t option)
    ~(block_addrs : Tid.t Addr.Map.t)
    ~(target : Bap_core_theory.Theory.Target.t)
    ~(defs : [ `Def of def term | `Phi of phi term ] Var.Map.t) : facts =
  let abi = Hike_abi.of_target target in
  let synth =
    Base.List.fold abi.Hike_abi.env_regs ~init:Hike_synth.empty
      ~f:Hike_synth.add_environment
    |> fun synth ->
    Hike_synth.add_window synth ~addr_bits:(Hike_abi.word_bits abi)
  in
  let denote ~synth ~blk ?def e =
    let pre, post =
      Option.value (Core.Map.find block_envs (Term.tid blk))
        ~default:(Cbat_vsa.AI.top, Cbat_vsa.AI.top)
    in
    Cbat_vsa.denote_exp_at ~synth ~pre ~post ~blk ?def e
  in
  { envs = block_envs;
    block_addrs;
    sub_addrs = Addr.Map.empty;
    images = [];
    foreign_slots = Core.Int64.Set.empty;
    target;
    abi;
    lookup;
    denote = denote ~synth;
    spec = None;
    defs;
    synth;
    signatures =
      Hike_signatures.create ~target Hike_signatures.empty
        ~imports:(fun _ -> None) }

(* The run's record, installed once at the discover boundary. *)
let run : facts option ref = ref None

let install (f : facts) = run := Some f

let facts () =
  match !run with
  | Some f -> f
  | None -> failwith "hike: no analysis facts installed (discover did not run)"

(* The optional read for passes that also run on fixtures (no analysis). *)
let facts_opt () : facts option = !run

let with_synth (f : facts) (synth : Hike_synth.table) : facts =
  let denote ~blk ?def e =
    let pre, post =
      Option.value (Core.Map.find f.envs (Term.tid blk))
        ~default:(Cbat_vsa.AI.top, Cbat_vsa.AI.top)
    in
    Cbat_vsa.denote_exp_at ~synth ~pre ~post ~blk ?def e
  in
  { f with synth; denote }

(* The attribution pass adds the emitter spec to the installed record. *)
let with_attribution (f : facts) ~(spec : Hike_spec.section_spec) : facts =
  { f with spec = Some spec }
