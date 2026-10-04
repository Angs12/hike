(* T15 C0 spike: the drive loop's four open questions, answered over
   BAP's own sub-resolution machinery.  Probe-only forensics; no
   production change.

   Per binary, ROUNDS of the loop (decode -> solve -> facts -> decode):
   A. the primary project (BAP's own scan: state, subroutines, program)
      plus the already_scanned short-circuit measurement;
   B. the jumps the primary left unresolved and their destination
      labels (the addr channel's subjects; label identity by KB oid);
   C. per round: the resolutions (the production chain to the VSA pass
      over the CURRENT program terms; the bounded word sets of every
      surviving indirect transfer; main by denotation);
   D. per round: the feedback facts -- is_subroutine on the discovered
      entries, Label.addr on an unresolved destination label (call-class
      words ride is_subroutine; goto-class words ride the dest label
      when one exists, else fall back to is_subroutine -- the
      over-provisioning measurement);
   E. per round: the re-scan (a fresh Driver.scan under the file's own
      package, unit, and theory -- one decode context) and the partition
      (Subroutines.update);
   F. per round: adoption -- each discovered entry's cfg closure lifts
      into a sub term of the working program (split_def + coerce_block
      + the FP normalization), so the next round's solve sees it;
   G. the FP A/B: the loop's decode of the FP idioms vs the primary's. *)

open Bap.Std
open Bap_core_theory
module Kb = Bap_core_theory.KB
module Driver = Disasm.Driver
module Subs = Disasm.Subroutines
module Cfg = Graphs.Cfg

open Probe_common

let hex a = Printf.sprintf "%Lx" (Word.to_int64_exn a)

let flush_all () = flush stdout; flush stderr

(* A plain recursive fold over the knowledge monad (the KB.List/KB.Seq
   combinators are not in the public interface). *)
let rec kb_fold (f : 'a -> 'x -> 'a Kb.t) (acc : 'a) (xs : 'x list) : 'a Kb.t =
  let open Kb.Syntax in
  match xs with
  | [] -> !!acc
  | x :: xs -> f acc x >>= fun acc -> kb_fold f acc xs

(* ------------------------------------------------------------------ *)
(* B. the jumps and their dest labels *)

type label_row = {
  lid : Core.Int63.t;
  lnull : bool;
  laddr : Bitvec.t option;
  lname : string option;
}

let dests_of (site : Addr.t) : Theory.Label.t list Kb.t =
  let open Kb.Syntax in
  Theory.Label.for_addr (Word.to_bitvec site) >>= fun code ->
  Kb.collect Theory.Semantics.slot code >>| fun sema ->
  match Kb.Value.get Insn.Slot.dests sema with
  | None -> []
  | Some ds -> Core.Set.to_list ds

let label_row (l : Theory.Label.t) : label_row Kb.t =
  let open Kb.Syntax in
  Kb.collect Theory.Label.addr l >>= fun a ->
  Kb.collect Theory.Label.name l >>| fun n ->
  { lid = Kb.Object.id l; lnull = Kb.Object.is_null l; laddr = a; lname = n }

let row_string (r : label_row) =
  Printf.sprintf "id=%s null=%b addr=%s name=%s"
    (Core.Int63.to_string r.lid) r.lnull
    (match r.laddr with Some a -> Bitvec.to_string a | None -> "none")
    (match r.lname with Some n -> n | None -> "-")

let jumps_of (s : Driver.state) : (Addr.t * Driver.jump) list =
  Core.Set.to_list (Driver.blocks s)
  |> Base.List.filter_map ~f:(fun a ->
      Base.Option.map (Driver.jump s a) ~f:(fun j -> (a, j)))

let unresolved_jumps (s : Driver.state) : Addr.t list =
  jumps_of s
  |> Base.List.filter_map ~f:(fun (a, j) ->
      Base.Option.some_if
        (Core.Set.is_empty (Driver.destinations j) && not (Driver.is_barrier j))
        a)

let state_line what (s : Driver.state) =
  Printf.printf "STATE %s: blocks=%d funs=%d jumps=%d\n%!" what
    (Core.Set.length (Driver.blocks s))
    (Core.Set.length (Driver.subroutines s))
    (Base.List.length (jumps_of s))

(* The dest labels of every site, read under the file's own package
   (the labels are interned per package; outside it the read would
   mint fresh objects and see nothing). *)
let read_dest_labels (bin : string) (sites : Addr.t list)
    : (Addr.t * (Theory.Label.t * label_row) list) list =
  if Base.List.is_empty sites then []
  else
    let v : (Addr.t * (Theory.Label.t * label_row) list) list option
        Toplevel.var = Toplevel.var "drive-loop-dest-labels" in
    Toplevel.put v
      (Kb.Symbol.in_package bin @@ fun () ->
       let open Kb.Syntax in
       kb_fold (fun acc site ->
           dests_of site >>= fun labels ->
           kb_fold (fun rows l ->
               label_row l >>| fun row -> (l, row) :: rows)
             [] labels
           >>| fun rows -> (site, Base.List.rev rows) :: acc)
         [] sites
       >>| fun xs -> Some xs);
    match Toplevel.get v with
    | Some xs -> Base.List.rev xs
    | None -> []

(* ------------------------------------------------------------------ *)
(* C. the resolutions: the production chain to the VSA pass *)

type resolution = {
  r_sub : string;                 (* dispatching sub's name *)
  r_owner : Addr.t option;        (* its entry address *)
  r_site : Addr.t option;         (* dispatching block's address *)
  r_call : bool;
  r_words : int64 list;
}

(* The production seam's decode, verbatim in shape (src/hike.ml seam_cfg
   + lift_at): a region view from the word, the unit promise, the
   project's theory instance.  Used only to GET the resolutions. *)
let make_lift_at proj =
  let seam_cfg (view : mem) : Cfg.t option =
    let run : Disasm_expert.Recursive.t option Toplevel.var =
      Toplevel.var "drive-loop-seam-cfg" in
    Toplevel.put run
      (let open Kb.Syntax in
       let lower = Word.to_bitvec (Memory.min_addr view) in
       let upper = Word.to_bitvec (Memory.max_addr view) in
       Theory.Unit.for_region ~lower ~upper >>= fun unit ->
       Kb.provide Theory.Unit.target unit (Project.target proj)
       >>= fun () ->
       Theory.instance () >>= fun theory ->
       Theory.with_current theory @@ fun () ->
       Kb.promising Theory.Label.unit
         ~promise:(fun _ -> !!(Some unit))
         (fun () ->
            Disasm_expert.Recursive.run_in_scope (Project.arch proj) view
            >>| Result.to_option));
    match Toplevel.get run with
    | Some rec_t -> Some (Disasm_expert.Recursive.cfg rec_t)
    | None -> None
  in
  fun ~(block_addrs : Tid.t Addr.Map.t) (a : Addr.t) : blk term list option ->
    match Seq.to_list (Memmap.lookup (Project.memory proj) a) with
    | [] -> None
    | (seg, _) :: _ -> (
        let view = Memory.view_exn ~from:a seg in
        match seam_cfg view with
        | None -> None
        | Some cfg ->
          let root =
            Cfg.nodes cfg |> Seq.find ~f:(fun b -> Addr.equal (Block.addr b) a)
          in
          Base.Option.map root ~f:(fun root ->
              let nodes =
                Graphlib.Std.Graphlib.fold_reachable (module Cfg) cfg ~init:[]
                  ~f:(fun acc n -> n :: acc) root
              in
              let others =
                Base.List.filter nodes ~f:(fun n ->
                    not (Addr.equal (Block.addr n) a))
              in
              let others =
                Base.List.filter others ~f:(fun n ->
                    not (Core.Map.mem block_addrs (Block.addr n)))
              in
              Base.List.concat_map (root :: others) ~f:(Blk.lift cfg)))

let blk_addr (b : blk term) : Addr.t option = Term.get_attr b address

let bounded_words (ws : Cbat_vsa.WordSet.t) : int64 list option =
  if Cbat_vsa.WordSet.is_top ws || Cbat_vsa.WordSet.is_bottom ws
     || Cbat_vsa.WordSet.is_infinite ws
  then None
  else
    match Cbat_word.to_int64 (Cbat_vsa.WordSet.cardinality ws) with
    | Error _ -> None
    | Ok n when n <= 0L || n > 64L -> None
    | Ok _ ->
      Some
        (Base.List.filter_map (Cbat_vsa.WordSet.iter ws)
           ~f:(fun w -> Result.to_option (Cbat_word.to_int64 w)))

(* One round's harvest over the CURRENT program terms. *)
let harvest proj program =
  let target = Project.target proj in
  let block_addrs0 =
    Term.enum sub_t program
    |> Seq.concat_map ~f:(Term.enum blk_t)
    |> Seq.filter_map ~f:(fun b ->
        Base.Option.map (blk_addr b) ~f:(fun a -> (a, Term.tid b)))
    |> Seq.to_list
    |> Core.Map.of_alist_exn (module Addr)
  in
  let images = section_images proj in
  let written =
    Hike.Vsa.kill_summaries ~abi:(Hike.Abi.of_target target) program
  in
  let entry_addrs =
    Term.enum sub_t program
    |> Seq.fold ~init:Core.Int64.Map.empty ~f:(fun m s ->
        match match Term.first blk_t s with
          | Some b -> blk_addr b
          | None -> None
        with
        | Some a -> Core.Map.set m ~key:(Word.to_int64_exn a) ~data:(Term.tid s)
        | None -> m)
  in
  let lookup =
    let named =
      Hike.Resolve.symtab_lookup ~symtab:(Some (Project.symbols proj))
        ~table:(Hike.Resolve.name_table_of program)
        ~addr_bits:(Hike.Abi.addr_size_bits target)
    in
    fun v ->
      match named v with
      | Some t -> Some t
      | None -> Core.Map.find entry_addrs v
  in
  let sub_addrs0 =
    Core.Map.fold block_addrs0 ~init:Addr.Map.empty
      ~f:(fun ~key:addr ~data:_ m ->
          match lookup (Word.to_int64_exn addr) with
          | Some sub -> Core.Map.set m ~key:addr ~data:sub
          | None -> m)
  in
  let subs = Term.enum sub_t program |> Seq.to_list in
  let subs_acc, stamped =
    Base.List.fold subs ~init:(Tid.Map.empty, [])
      ~f:(fun (acc, st) sub ->
          let envs, sub', _ba', _facts =
            Hike.Vsa.fixpoint target ~lookup ~sub_addrs:sub_addrs0 ~images
              ~written ~foreign_slots:Core.Int64.Set.empty
              ~block_addrs:block_addrs0 sub
          in
          (Core.Map.set acc ~key:(Term.tid sub) ~data:envs,
           (Term.tid sub, sub') :: st))
  in
  (* main by denotation: the entry's call block passes main's address. *)
  let main_addr =
    let entry =
      Base.List.find subs ~f:(fun s -> Term.has_attr s Sub.entry_point) in
    match entry with
    | None -> None
    | Some entry -> (
        match Core.Map.find subs_acc (Term.tid entry) with
        | None -> None
        | Some envs ->
          let arg0 = Hike.Abi.argc_argv_regs (Hike.Abi.of_target target) |> fst in
          Term.enum blk_t entry
          |> Seq.filter_map ~f:(fun blk ->
              let has_call =
                Term.enum jmp_t blk
                |> Seq.exists ~f:(fun j ->
                    match Jmp.kind j with Call _ -> true | _ -> false)
              in
              if not has_call then None
              else
                Core.Map.find envs (Term.tid blk)
                |> Base.Option.bind ~f:(fun (_, post) ->
                    match
                      Cbat_vsa.denote_exp_at ~pre:post ~post ~blk (Bil.Var arg0)
                    with
                    | Error _ -> None
                    | Ok ws -> (
                        match
                          Cbat_word.to_int64 (Cbat_vsa.WordSet.cardinality ws)
                        with
                        | Ok 1L ->
                          Base.Option.bind (Cbat_vsa.WordSet.min_elem ws)
                            ~f:(fun w -> Result.to_option (Cbat_word.to_int64 w))
                        | _ -> None)))
          |> Seq.hd)
  in
  (* The resolutions: every surviving indirect transfer's bounded word
     set, denotated at the state its block reads (the completion's own
     bounded-words rule, probe-side). *)
  let resolutions =
    Base.List.concat_map subs ~f:(fun s ->
        let envs =
          match Core.Map.find subs_acc (Term.tid s) with
          | Some e -> e
          | None -> Tid.Map.empty in
        let owner = Base.Option.bind (Term.first blk_t s) ~f:blk_addr in
        Term.enum blk_t s |> Seq.to_list
        |> Base.List.concat_map ~f:(fun blk ->
            match Core.Map.find envs (Term.tid blk) with
            | None -> []
            | Some (pre, post) ->
              Term.enum jmp_t blk |> Seq.to_list
              |> Base.List.filter_map ~f:(fun j ->
                  let call, e =
                    match Jmp.kind j with
                    | Goto (Indirect e) -> (false, Some e)
                    | Call c -> (
                        match Call.target c with
                        | Indirect e -> (true, Some e)
                        | _ -> (true, None))
                    | _ -> (false, None)
                  in
                  match e with
                  | None | Some (Bil.Int _) -> None
                  | Some e -> (
                      match Cbat_vsa.denote_exp_at ~pre ~post ~blk e with
                      | Error _ ->
                        if Base.String.is_prefix ~prefix:"loop_sub_"
                            (Sub.name s) then
                          Printf.printf "  DENOTE %s @%s: error\n%!"
                            (Sub.name s)
                            (match blk_addr blk with
                             | Some a -> hex a | None -> "?");
                        None
                      | Ok ws ->
                        (match bounded_words ws with
                         | None ->
                           if Base.String.is_prefix ~prefix:"loop_sub_"
                               (Sub.name s) then
                             Printf.printf
                               "  DENOTE %s @%s: unbounded (top=%b \
                                bot=%b inf=%b)\n%!"
                               (Sub.name s)
                               (match blk_addr blk with
                                | Some a -> hex a | None -> "?")
                               (Cbat_vsa.WordSet.is_top ws)
                               (Cbat_vsa.WordSet.is_bottom ws)
                               (Cbat_vsa.WordSet.is_infinite ws)
                         | Some _ -> ());
                        Base.Option.map (bounded_words ws) ~f:(fun words ->
                            { r_sub = Sub.name s;
                              r_owner = owner;
                              r_site = blk_addr blk;
                              r_call = call;
                              r_words = words })))))
  in
  let dis = Project.State.disassembly (Project.state proj) in
  let known_word w =
    Core.Map.mem entry_addrs w || Driver.is_subroutine dis (Addr.of_int64 w)
  in
  let main_root =
    match main_addr with
    | Some w when not (known_word w) -> [ w ]
    | _ -> []
  in
  let call_words =
    resolutions
    |> Base.List.filter_map ~f:(fun r ->
        Base.Option.some_if r.r_call r.r_words)
    |> Base.List.concat
    |> Base.List.dedup_and_sort ~compare:Int64.compare in
  let roots =
    Base.List.append main_root
      (Base.List.filter call_words ~f:(fun w -> not (known_word w)))
    |> Base.List.dedup_and_sort ~compare:Int64.compare
  in
  (resolutions, roots, main_addr, stamped)

(* ------------------------------------------------------------------ *)
(* E. the re-scan *)

(* Disasm_expert.Recursive.global_cfg's shape, over exposed pieces. *)
let cfg_of_state (state : Driver.state) : Cfg.t Kb.t =
  let open Kb.Syntax in
  let follows_after m1 m2 =
    Addr.equal (Addr.succ (Memory.max_addr m1)) (Memory.min_addr m2) in
  let has_conditional_jump blk =
    let insn = Block.terminator blk in
    Insn.is Insn.jump insn && Insn.is Insn.conditional insn in
  Driver.explore state
    ~init:Cfg.empty
    ~block:(fun mem insns ->
        Driver.execution_order insns >>=
        Kb.List.filter_map ~f:(fun label ->
            Kb.collect Disasm_expert.Basic.Insn.slot label >>= fun basic ->
            Kb.collect Theory.Semantics.slot label >>= fun s ->
            Kb.collect Memory.slot label >>| function
            | None -> None
            | Some mem ->
              let insn = match basic with
                | Some b -> Insn.with_basic s b
                | None -> s in
              Some (mem, insn)) >>|
        Block.create mem)
    ~node:(fun node cfg -> Kb.return (Cfg.Node.insert node cfg))
    ~edge:(fun src dst g ->
        let k =
          if follows_after (Block.memory src) (Block.memory dst)
          then `Fall
          else if has_conditional_jump src then `Cond
          else `Jump in
        Kb.return (Cfg.Edge.insert (Cfg.Edge.create src dst k) g))

let code_mems (proj : Project.t) : mem list =
  Memmap.to_sequence (Project.memory proj)
  |> Seq.filter ~f:(fun (_, v) ->
      Option.is_some (Value.get Image.code_region v))
  |> Seq.map ~f:fst
  |> Seq.to_list

type loop_out = {
  grown : Driver.state;
  gcfg : Cfg.t;
  gsubs : Subs.t;
}

(* The re-scan: one decode context (the file's package, unit, and
   theory), the entry promise over the discovered roots, a FRESH
   Driver state (the project's own state short-circuits on
   already_scanned).  [table] feeds the BRANCHER: the dests channel
   the backend lacks for x86 indirect jumps.  The brancher sees
   UNBIASED addresses (the context subtracts the unit's bias), so the
   table's keys and words are converted with the same bias. *)
let drive_loop proj ~bin ~roots ~table : loop_out =
  let width = Theory.Target.code_addr_size (Project.target proj) in
  let roots_set =
    Core.Set.of_list (module Addr) (Base.List.map roots ~f:Addr.of_int64) in
  let entry_promise label =
    let open Kb.Syntax in
    Kb.collect Theory.Label.addr label >>= function
    | Some a ->
      let w = Word.create a width in
      !!(Base.Option.some_if (Core.Set.mem roots_set w) true)
    | None -> !!(None)
  in
  let out : loop_out option Toplevel.var = Toplevel.var "drive-loop-rescan" in
  Toplevel.put out
    (let open Kb.Syntax in
     Theory.instance () >>= fun theory ->
     Theory.with_current theory @@ fun () ->
     Theory.Unit.for_file bin >>= fun unit ->
     Kb.collect Theory.Unit.bias unit >>= fun bias ->
     let unbi w =
       match bias with
       | Some b -> Int64.sub w (Bitvec.to_int64 b)
       | None -> w in
     let table =
       Core.Map.map table ~f:(Base.List.map ~f:unbi) in
     let brancher =
       Brancher.create (fun mem _insn ->
           match
             Core.Map.find table (Word.to_int64_exn (Memory.min_addr mem))
           with
           | Some ws ->
             Base.List.map ws ~f:(fun w -> (Some (Addr.of_int64 w), `Jump))
           | None -> [])
       in
     kb_fold (fun () a ->
         Theory.Label.for_addr (Word.to_bitvec (Addr.of_int64 a))
         >>= fun l ->
         Kb.provide Theory.Label.is_subroutine l (Some true))
       () roots
     >>= fun () ->
     Kb.Symbol.in_package bin @@ fun () ->
     Kb.promising Theory.Label.unit ~promise:(fun _ -> !!(Some unit)) @@
     fun () ->
     Kb.promising Theory.Label.is_subroutine ~promise:entry_promise @@ fun () ->
     Brancher.providing brancher @@ fun () ->
     let mems = code_mems proj |> List.rev in
     kb_fold (fun s mem -> Driver.scan mem s) Driver.init mems
     >>= fun grown ->
     cfg_of_state grown >>= fun gcfg ->
     Subs.update Subs.empty grown >>| fun gsubs ->
     Some { grown; gcfg; gsubs });
  match Toplevel.get out with
  | Some o -> o
  | None -> failwith "drive-loop: the re-scan produced nothing"

(* F. adoption: the entry's cfg closure lifts into a sub term. *)
let adopt (gcfg : Cfg.t) ~(root : Addr.t) ~(claimed : Addr.Set.t)
    ~(program_addrs : Addr.Set.t) : sub term * Addr.Set.t =
  let node =
    match
      Cfg.nodes gcfg |> Seq.find ~f:(fun b -> Addr.equal (Block.addr b) root)
    with
    | Some n -> n
    | None -> failwith (Printf.sprintf "adopt: no cfg block at %s" (hex root))
  in
  let nodes =
    Graphlib.Std.Graphlib.fold_reachable (module Cfg) gcfg ~init:[]
      ~f:(fun acc n -> n :: acc) node
  in
  let blks =
    Base.List.concat_map nodes ~f:(Blk.lift gcfg)
    |> Base.List.filter ~f:(fun b ->
        match blk_addr b with
        | Some a ->
          not (Core.Set.mem claimed a) && not (Core.Set.mem program_addrs a)
        | None -> true)
  in
  let claimed =
    Base.List.fold blks ~init:claimed ~f:(fun c b ->
        match blk_addr b with
        | Some a -> Core.Set.add c a
        | None -> c)
  in
  let sb =
    Sub.Builder.create ~tid:(Tid.for_name (Printf.sprintf "loop_sub_%s"
                                (hex root)))
      ~name:(Printf.sprintf "loop_sub_%s" (hex root)) ()
  in
  Base.List.iter blks ~f:(fun b ->
      let b = Term.concat_map def_t b ~f:Hike.Split_mem.split_def in
      Sub.Builder.add_blk sb (Hike.Coerce.coerce_block b));
  let sub = Sub.Builder.result sb in
  let sub =
    Term.enum sub_t (Hike.Fp.run_program (Program.create ~subs:[ sub ] ()))
    |> Seq.hd_exn
  in
  (sub, claimed)

(* G. the FP A/B *)

let fp_names =
  [ "cvtsi2sd"; "cvtsi2ss"; "cvtss2sd"; "cvtsd2si"; "cvttsd2si"; "movsd";
    "movss"; "addsd"; "subsd"; "mulsd"; "divsd"; "movapd"; "movaps";
    "movdqa"; "movdqu"; "movupd"; "movups"; "ucomisd"; "comisd"; "pxor";
    "xorpd"; "xorps"; "cvtsd2ss"; "cvttsd2sil" ]

let is_fp_name n =
  let n = String.uppercase_ascii n in
  Base.List.exists fp_names ~f:(fun p ->
      Base.String.is_substring n ~substring:(String.uppercase_ascii p))

let insn_form (_, i) =
  Format.asprintf "%s %s ops=[%s] bil=%a"
    (Insn.name i) (Insn.asm i)
    (Array.map (fun (o : Op.t) ->
         match o with
         | Op.Reg r -> "reg:" ^ Reg.name r
         | Op.Imm x -> Printf.sprintf "imm:%Ld" (Imm.to_int64 x)
         | Op.Fmm _ -> "fmm")
        (Insn.ops i)
     |> Array.to_list |> String.concat ";")
    Bil.pp (Insn.bil i)

let fp_insns (cfg : Cfg.t) : (Addr.t * string) list =
  Cfg.nodes cfg
  |> Seq.to_list
  |> Base.List.concat_map ~f:(fun b ->
      Block.insns b
      |> Base.List.filter_map ~f:(fun (mem, i) ->
          if is_fp_name (Insn.name i)
          then Some (Memory.min_addr mem, insn_form (mem, i))
          else None))
  |> Base.List.dedup_and_sort ~compare:(fun (a, _) (b, _) -> Addr.compare a b)

(* The seam's decode of one address (src/hike.ml seam_cfg's shape: a
   region view from the address, the unit promise, the project's theory
   instance); the insn form the region context produces. *)
let seam_form (proj : Project.t) (a : Addr.t) : string option =
  match Seq.to_list (Memmap.lookup (Project.memory proj) a) with
  | [] -> None
  | (seg, _) :: _ ->
    let view = Memory.view_exn ~from:a seg in
    let run : Disasm_expert.Recursive.t option Toplevel.var =
      Toplevel.var "drive-loop-seam-form" in
    Toplevel.put run
      (let open Kb.Syntax in
       let lower = Word.to_bitvec (Memory.min_addr view) in
       let upper = Word.to_bitvec (Memory.max_addr view) in
       Theory.Unit.for_region ~lower ~upper >>= fun unit ->
       Kb.provide Theory.Unit.target unit (Project.target proj)
       >>= fun () ->
       Theory.instance () >>= fun theory ->
       Theory.with_current theory @@ fun () ->
       Kb.promising Theory.Label.unit
         ~promise:(fun _ -> !!(Some unit))
         (fun () ->
            Disasm_expert.Recursive.run_in_scope (Project.arch proj) view
            >>| Result.to_option));
    match Base.Option.map (Toplevel.get run)
             ~f:Disasm_expert.Recursive.cfg with
    | Some cfg ->
      Cfg.nodes cfg
      |> Seq.filter_map ~f:(fun b ->
          Base.List.find_map (Block.insns b) ~f:(fun (mem, i) ->
              Base.Option.some_if (Addr.equal (Memory.min_addr mem) a)
                (insn_form (mem, i))))
      |> Seq.hd
    | _ -> None

let fp_ab proj (gcfg : Cfg.t) =
  let pcfg = Disasm.cfg (Project.disasm proj) in
  let prim = fp_insns pcfg in
  let loop = fp_insns gcfg in
  if Base.List.is_empty prim && Base.List.is_empty loop then
    Printf.printf "G. FP-A/B: no FP idioms decoded on either side\n%!"
  else begin
    let mprim = Core.Map.of_alist_exn (module Addr) prim in
    let mloop = Core.Map.of_alist_exn (module Addr) loop in
    Printf.printf "G. FP-A/B: primary=%d loop=%d FP insns\n%!"
      (Base.List.length prim) (Base.List.length loop);
    Base.List.iter prim ~f:(fun (a, form) ->
        match Core.Map.find mloop a with
        | None ->
          Printf.printf "  FP @%s\n    PRIMARY %s\n    LOOP    <missing>\n%!"
            (hex a) form
        | Some lform ->
          if String.equal form lform then
            Printf.printf "  FP @%s IDENTICAL\n    %s\n%!" (hex a) form
          else
            Printf.printf "  FP @%s DIFFER\n    PRIMARY %s\n    LOOP    %s\n%!"
              (hex a) form lform);
    Base.List.iter loop ~f:(fun (a, form) ->
        if Base.Option.is_none (Core.Map.find mprim a) then begin
          match seam_form proj a with
          | None ->
            Printf.printf "  FP @%s LOOP-ONLY (seam: no insn)\n    %s\n%!"
              (hex a) form
          | Some sform ->
            if String.equal form sform then
              Printf.printf "  FP @%s LOOP=SEAM\n    %s\n%!" (hex a) form
            else
              Printf.printf
                "  FP @%s DIFFER\n    LOOP %s\n    SEAM %s\n%!"
                (hex a) form sform
        end)
  end

(* ------------------------------------------------------------------ *)

(* The term dump (probe evidence): blocks with addresses and jmp shapes. *)
let dump_sub what (s : sub term) =
  Printf.printf "  === %s\n%!" what;
  Term.enum blk_t s |> Seq.iter ~f:(fun b ->
      let addr =
        match blk_addr b with
        | Some a -> "@" ^ hex a
        | None -> "@none" in
      Printf.printf "    blk %s %s\n%!" (Tid.name (Term.tid b)) addr;
      Term.enum jmp_t b |> Seq.iter ~f:(fun j ->
          Printf.printf "      %s\n" (jmp_to_string j)))

let max_rounds = 4

let run_bin bin =
  Printf.printf "\n==== DRIVE-LOOP %s\n%!" bin;
  let t0 = Unix.gettimeofday () in
  let proj = load_project bin in
  let dis = Project.State.disassembly (Project.state proj) in
  Printf.printf "A. primary: program subs=%d\n%!"
    (Term.enum sub_t (Project.program proj) |> Seq.to_list
     |> Base.List.length);
  state_line "primary" dis;
  (* The already_scanned short-circuit: scanning the project's own code
     memory through the grown state changes nothing. *)
  (match code_mems proj with
   | mem0 :: _ ->
     let short : Driver.state option Toplevel.var = Toplevel.var "dl-short" in
     Toplevel.put short
       (let open Kb.Syntax in
        Driver.scan mem0 dis >>| fun s -> Some s);
     (match Toplevel.get short with
      | Some s ->
        Printf.printf "A0. Driver.scan on the primary's mem via the grown \
                       state: %s\n%!"
          (if Driver.equal s dis
           then "short-circuited (state unchanged)"
           else "state CHANGED (no short-circuit)")
      | None -> print_endline "A0. scan failed")
   | [] -> failwith "no code region");
  (* B. the primary's unresolved jumps and their dest labels. *)
  let sites0 = unresolved_jumps dis in
  Printf.printf "B. primary unresolved jumps: %d\n%!" (Base.List.length sites0);
  Base.List.iter (read_dest_labels bin sites0) ~f:(fun (site, rows) ->
      Printf.printf "  JMP @%s\n%!" (hex site);
      Base.List.iter rows ~f:(fun (_, r) ->
          Printf.printf "    dest-label %s\n%!" (row_string r)));
  Hike.Vsa.set_addr_bits (Hike.Abi.addr_size_bits (Project.target proj));
  (* The HAND-FACTS (C0's sanctioned stand-in for the completion's
     output): jump_table_sw's dispatch at 0x107a resolves to the eight
     case entries -- written here by hand so the brancher channel gets
     exercised end to end. *)
  let dispatch_table = ref (Core.Int64.Map.empty) in
  if Base.String.is_substring bin ~substring:"jump_table_sw" then begin
    let site = 0x107aL in
    let ws =
      [ 0x1080L; 0x1090L; 0x10a0L; 0x10b0L; 0x10c0L; 0x10d0L; 0x10e0L;
        0x10f1L ] in
    dispatch_table := Core.Map.set !dispatch_table ~key:site ~data:ws;
    Printf.printf "D0. HAND-FACTS: dispatch @%Lx := [%s]\n%!" site
      (String.concat ","
         (Base.List.map ws ~f:(fun w -> Printf.sprintf "%Lx" w)))
  end;
  (* The loop. *)
  let program = ref (production_input proj) in
  let adopted : sub term list ref = ref [] in
  let claimed : Addr.Set.t ref = ref (Core.Set.empty (module Addr)) in
  let seen_roots : int64 list ref = ref [] in
  let main_addr_ref : int64 option ref = ref None in
  let last_out = ref None in
  let stop = ref false in
  for _round = 1 to max_rounds do
    if !stop then ()
    else

    Printf.printf "\n-- ROUND %d\n%!" _round;
    let resolutions, roots, main_addr, stamped = harvest proj !program in
    if Base.Option.is_none !main_addr_ref then main_addr_ref := main_addr;
    Printf.printf "C. resolutions=%d main_addr=%s roots=[%s]\n%!"
      (Base.List.length resolutions)
      (match main_addr with Some a -> Printf.sprintf "%Lx" a | None -> "none")
      (String.concat ","
         (Base.List.map roots ~f:(fun w -> Printf.sprintf "%Lx" w)));
    Base.List.iter resolutions ~f:(fun r ->
        Printf.printf "  RES sub=%s @%s %s words=[%s]\n%!"
          r.r_sub
          (match r.r_site with Some a -> hex a | None -> "?")
          (if r.r_call then "call" else "goto")
          (String.concat ","
             (Base.List.map r.r_words ~f:(fun w ->
                  Printf.sprintf "%Lx" w))));
    (* The adopted subs' post-solve shapes: what the completion made
       of the indirect transfers. *)
    Base.List.iter stamped ~f:(fun (_, s') ->
        if Base.String.is_prefix ~prefix:"loop_sub_" (Sub.name s') then begin
          let nind = ref 0 in
          Term.enum blk_t s' |> Seq.iter ~f:(fun b ->
              Term.enum jmp_t b |> Seq.iter ~f:(fun j ->
                  match Jmp.kind j with
                  | Goto (Indirect _) -> incr nind
                  | Call c -> (
                      match Call.target c with
                      | Indirect _ -> incr nind
                      | _ -> ())
                  | _ -> ()));
          Printf.printf "  SOLVED %s: blocks=%d indirect-left=%d\n%!"
            (Sub.name s')
            (Term.enum blk_t s' |> Seq.to_list |> Base.List.length) !nind;
          dump_sub (Printf.sprintf "post-solve %s" (Sub.name s')) s'
        end);
        Printf.printf "D. roots=[%s]\n%!"
      (String.concat ","
         (Base.List.map roots ~f:(fun w -> Printf.sprintf "%Lx" w)));
    let new_roots =
      Base.List.filter roots ~f:(fun w ->
          not (Base.List.mem !seen_roots w ~equal:Int64.equal)) in
    (* The fact policy: call-class words and main are function starts
       (is_subroutine); goto-class resolutions ride the BRANCHER (the
       dests channel -- the backend mints no dest label for an x86
       indirect jump, so there is nothing to provide addr on). *)
    let goto_facts =
      Base.List.filter_map resolutions ~f:(fun r ->
          match r.r_site, r.r_call with
          | Some site, false when not (Base.List.is_empty r.r_words) ->
            Some (site, r.r_words)
          | _ -> None) in
    let fresh_goto =
      Base.List.filter goto_facts ~f:(fun (site, _) ->
          not (Core.Map.mem !dispatch_table (Word.to_int64_exn site))) in
    Base.List.iter fresh_goto ~f:(fun (site, ws) ->
        Printf.printf "  FACT @%s: brancher dests [%s]\n%!" (hex site)
          (String.concat ","
             (Base.List.map ws ~f:(fun w -> Printf.sprintf "%Lx" w)));
        dispatch_table :=
          Core.Map.set !dispatch_table
            ~key:(Word.to_int64_exn site) ~data:ws);
    if Base.List.is_empty new_roots && Base.List.is_empty fresh_goto then
      (Printf.printf "-- loop fixpoint: nothing new\n%!";
       stop := true)
    else begin
      seen_roots := !seen_roots @ new_roots;
      let t1 = Unix.gettimeofday () in
      let out = drive_loop proj ~bin ~roots:!seen_roots
          ~table:!dispatch_table in
      last_out := Some out;
      Printf.printf "E. re-scan wall=%.1fs\n%!" (Unix.gettimeofday () -. t1);
      state_line "grown" out.grown;
      Base.List.iter (jumps_of out.grown) ~f:(fun (a, j) ->
          let dsts = Driver.destinations j in
          if not (Core.Set.is_empty dsts) then
            Printf.printf "  JUMP @%s -> [%s]\n%!" (hex a)
              (String.concat ","
                 (Base.List.map (Core.Set.to_list dsts) ~f:hex)));
      let unres = unresolved_jumps out.grown in
      Base.List.iter unres ~f:(fun a ->
          Printf.printf "  JUMP @%s -> UNRESOLVED\n%!" (hex a));
      Base.List.iter (read_dest_labels bin unres) ~f:(fun (site, rows) ->
          Base.List.iter rows ~f:(fun (_, r) ->
              Printf.printf "    dest-label @%s %s\n%!" (hex site)
                (row_string r)));
      let entries = Subs.entries out.gsubs in
      Printf.printf "E2. partition entries (%d): [%s]\n%!"
        (Core.Set.length entries)
        (String.concat ","
           (Base.List.map (Core.Set.to_list entries) ~f:hex));
      (* The resolved sites' evidence. *)
      Base.List.iter resolutions ~f:(fun r ->
          match r.r_site with
          | None -> ()
          | Some site -> (
              match Driver.jump out.grown site with
              | None -> ()
              | Some j ->
                Printf.printf "  SITE @%s: resolved=[%s] wanted=[%s]\n%!"
                  (hex site)
                  (String.concat ","
                     (Base.List.map
                        (Core.Set.to_list (Driver.destinations j)) ~f:hex))
                  (String.concat ","
                     (Base.List.map r.r_words ~f:(fun w ->
                          Printf.sprintf "%Lx" w)))));
      (* F. adoption. *)
      Base.List.iter new_roots ~f:(fun w ->
          let a = Addr.of_int64 w in
          let already =
            Core.Map.mem
              (Term.enum sub_t !program
               |> Seq.fold ~init:Core.Int64.Map.empty ~f:(fun m s ->
                   match match Term.first blk_t s with
                     | Some b -> blk_addr b
                     | None -> None
                   with
                   | Some x ->
                     Core.Map.set m ~key:(Word.to_int64_exn x) ~data:()
                     | None -> m))
              w
          in
          if already then
            Printf.printf "  ADOPT %Lx: already a program sub entry\n%!" w
          else
            try
              let program_addrs =
                Term.enum sub_t !program
                |> Seq.concat_map ~f:(Term.enum blk_t)
                |> Seq.filter_map ~f:(fun b ->
                    Base.Option.map (blk_addr b) ~f:(fun a -> (a, ())))
                |> Seq.to_list
                |> Base.List.map ~f:fst
                |> Core.Set.of_list (module Addr)
              in
              let sub, claimed' =
                adopt out.gcfg ~root:a ~claimed:!claimed
                  ~program_addrs in
              claimed := claimed';
              adopted := !adopted @ [ sub ];
              program :=
                Term.append sub_t !program sub;
              Printf.printf "  ADOPT %Lx: %d blocks\n%!" w
                (Term.enum blk_t sub |> Seq.to_list |> Base.List.length);
              dump_sub (Printf.sprintf "adopted %Lx (pre-solve)" w) sub
            with e ->
              Printf.printf "  ADOPT %Lx: failed: %s\n%!" w
                (Printexc.to_string e))
    end
  done;
  (* G. the partition ownership of the resolutions + the FP A/B. *)
  (match !last_out with
   | None -> ()
   | Some out ->
     let entries = Subs.entries out.gsubs in
     Printf.printf "\nF. final partition: %d entries\n%!"
       (Core.Set.length entries);
     Base.List.iter !seen_roots ~f:(fun w ->
         Printf.printf "  ROOT %Lx: is-own-entry=%b\n%!" w
           (Core.Set.mem entries (Addr.of_int64 w)));
     let main_entry =
       match !main_addr_ref with Some w -> w | None -> 0L in
     Base.List.iter (Core.Map.to_alist !dispatch_table)
       ~f:(fun (site, ws) ->
         match Driver.jump out.grown (Addr.of_int64 site) with
         | None ->
           Printf.printf "  BRANCH @%Lx: not a jump record in the grown \
                          state\n%!" site
         | Some j ->
           Printf.printf "  BRANCH @%Lx: resolved=[%s]\n%!" site
             (String.concat ","
                (Base.List.map (Core.Set.to_list (Driver.destinations j))
                   ~f:hex));
           Base.List.iter ws ~f:(fun w ->
               Printf.printf "    word %Lx: is_block=%b in-main=%b\n%!" w
                 (Driver.is_block out.grown (Addr.of_int64 w))
                 (Subs.belongs out.gsubs ~entry:(Addr.of_int64 main_entry)
                    (Addr.of_int64 w))));
     fp_ab proj out.gcfg);
  Printf.printf "==== done %s wall=%.1fs\n%!" bin
    (Unix.gettimeofday () -. t0);
  flush_all ()

let () =
  init ();
  let bins =
    match Base.Array.to_list Sys.argv with
    | _ :: bins -> bins
    | [] -> []
  in
  if Base.List.is_empty bins then begin
    Printf.eprintf "usage: %s <binary> [<binary> ...]\n" Sys.argv.(0);
    exit 2
  end;
  Base.List.iter bins ~f:run_bin
