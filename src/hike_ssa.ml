(* Every incoming register value has a block-local phi, including on
   single-predecessor edges. Memory keeps its model storage identity.
   Machine-call SP operands restore the pushed return-address word. *)

open Bap.Std
open Bap_core_theory

module Model = Hike_stack_model
module Abi = Hike_abi

let ssa_tag = Model.ssa_tag

let entry_tag : unit Value.Tag.t =
  Value.Tag.register ~package:"hike" ~name:"hike-ssa-entry"
    ~uuid:"1072b3e1-a039-4a5b-b340-d052dded07cd" (module Core.Unit)

module High_water = struct
  open! Core
  type t = (var * int) list [@@deriving bin_io, compare, sexp]
  let pp ppf xs = Format.fprintf ppf "%d variables" (Base.List.length xs)
end

let high_water_tag : High_water.t Value.Tag.t =
  Value.Tag.register ~package:"hike" ~name:"hike-ssa-high-water"
    ~uuid:"543d89dd-dfc1-4bf7-b84f-fb93932026c3" (module High_water)

let high_water sub =
  Base.Option.value (Term.get_attr sub high_water_tag) ~default:[]

(* Every non-interrupt, non-halt call jmp mints its ret lanes. *)
let call_of_jmp (j : jmp term) : Call.t option =
  match Jmp.kind j with
  | Call c -> (
      match Call.target c with
      | Direct target ->
          if Hike_abi.is_interrupt_name (Tid.name target) then None
          else
            (match Hike_native_fp.native_fp_op (Tid.name target) with
             | Some Hike_native_fp.FHLT -> None
             | _ -> Some c)
      | Indirect _ -> Some c)
  | _ -> None

(* The machine calls: a mapped intrinsic is a soft-float helper, not a
   call — no return address is pushed, so no SP restore rides it.  An
   unmapped intrinsic target (the atomic family's marker stubs) is a
   fact about one instruction, not code — the model's own rule. *)
let machine_call (j : jmp term) : bool =
  match Jmp.kind j with
  | Call c -> (
      match Call.target c with
      | Direct target ->
        Base.Option.is_none (Hike_native_fp.native_fp_op (Tid.name target))
        && not (Hike_abi.is_intrinsic_name (Tid.name target))
      | Indirect _ -> true)
  | _ -> false

let restore_word ~(abi : Abi.t) : exp =
  Bil.Int
    (Cbat_word.to_word
       (Cbat_word.of_int ~width:(Model.word_bits abi.Abi.word) abi.Abi.word))

#ifdef VSA_DEBUG
let debug_graph g =
  Graphs.Tid.nodes g
  |> Seq.iter ~f:(fun n ->
         Format.eprintf "SSA-DBG %s -> [%s]@." (Tid.name n)
           (String.concat ","
              (Graphs.Tid.Node.succs n g |> Seq.to_list
              |> Base.List.map ~f:Tid.name)))

#endif

(* The phis of [needs] in the blocks [only] accepts. *)
let place_phis ~preds_of ~only (needs : Var.Set.t Tid.Map.t) (sub : sub term) :
    sub term =
  let insert_phi ~(preds : Tid.t list) (blk : blk term) (v : var) =
    if
      Term.enum phi_t blk |> Seq.exists ~f:(fun p -> Var.same (Phi.lhs p) v)
    then blk
    else Term.append phi_t blk (Phi.of_list v (Base.List.map preds ~f:(fun p -> (p, Bil.Var v))))
  in
  Core.Map.fold needs ~init:sub ~f:(fun ~key:tid ~data:vs sub ->
      if not (only tid) then sub
      else
        match Term.find blk_t sub tid with
        | None -> sub
        | Some blk ->
            Term.update blk_t sub
              (Core.Set.fold vs ~init:blk
                 ~f:(insert_phi ~preds:(preds_of tid))))

(* [Full] names a new block. [Stable] keeps old term outputs and names
   only newly added outputs; [Reread] resolves changed jump reads. *)
type mode = Fixed | Reread | Stable | Full

(* Block-local renaming.  A block's incoming names are its phi lhs
   values; its defs and call results take fresh versions.  A second pass
   wires every phi operand from the predecessor's end-of-block names.
   No dominator order is needed: a value crossing a block boundary is a
   phi (or an index-0 boundary input), so a block's local names cover
   every renamable read. *)
let rename_versions ?(mode = fun _ -> Full) ?(floor = Var.Map.empty)
    ?preds_of ?(preserve_phi = fun _ _ -> false)
    ?(preserve_def = fun _ _ -> false)
    ?(preserve_write = fun _ _ _ -> false)
    ~abi ~sp ~renamable ~machine_blk_tids (sub : sub term) : sub term =
  let nums : int Var.Table.t = Core.Hashtbl.create (module Var) in
  Base.List.iter (high_water sub) ~f:(fun (key, data) ->
      Core.Hashtbl.set nums ~key ~data);
  Core.Map.iteri floor ~f:(fun ~key ~data ->
      Core.Hashtbl.update nums key ~f:(fun previous ->
          max data (Base.Option.value previous ~default:0)));
  let new_name x =
    Core.Hashtbl.change nums x ~f:(function
      | None -> Some 1
      | Some k -> Some (k + 1));
    Var.with_index x (Core.Hashtbl.find_exn nums x)
  in
  (* The block's current name per base var: its phis, then its defs,
     then its call results (the last write wins). *)
  let names : var Var.Map.t ref = ref Var.Map.empty in
  let set_name v = names := Core.Map.set !names ~key:(Var.base v) ~data:v in
  let lookup v =
    if Var.index v = 0 then
      Base.Option.value (Core.Map.find !names (Var.base v)) ~default:v
    else v
  in
  let substitute =
    (object
      inherit Exp.mapper
      method! map_sym z = lookup z
    end)#map_exp
  in
  let outputs : var Var.Map.t Tid.Map.t ref = ref Tid.Map.empty in
  let record tid = outputs := Core.Map.set !outputs ~key:tid ~data:!names in
  let kept_blk blk =
    names := Var.Map.empty;
    Term.enum phi_t blk |> Seq.iter ~f:(fun p -> set_name (Phi.lhs p));
    Term.enum def_t blk
    |> Seq.iter ~f:(fun d ->
           let v = Def.lhs d in
           if Var.index v > 0 then set_name v);
    Term.enum jmp_t blk |> Seq.iter ~f:(fun j ->
        Base.List.iter (Model.effects j).Model.Term_effects.writes ~f:set_name);
    blk
  in
  let full_blk blk =
    names := Var.Map.empty;
    let blk =
      Term.map phi_t blk ~f:(fun phi ->
          let lhs = new_name (Phi.lhs phi) in
          set_name lhs;
          Phi.with_lhs phi lhs)
    in
    let blk =
      Term.map def_t blk ~f:(fun d ->
          let d = Def.with_rhs d (substitute (Def.rhs d)) in
          (* The name-routed lanes (slots, call args, the window) keep
             their base name: readers find them by name. *)
          if renamable (Def.lhs d) then begin
            let lhs = new_name (Def.lhs d) in
            set_name lhs;
            Def.with_lhs d lhs
          end
          else d)
    in
    let blk =
      Term.map jmp_t blk ~f:(fun j ->
          Jmp.map_exp ~f:substitute j
          |> Model.map_effects ~read:lookup ~write:Fun.id)
    in
    let blk =
      Term.map jmp_t blk ~f:(fun j ->
          Model.map_effects ~read:Fun.id ~write:(fun v ->
              let version = new_name v in
              set_name version;
              version) j)
    in
    Term.set_attr blk ssa_tag ()
  in
  let sub =
    Term.map blk_t sub ~f:(fun blk ->
        let tid = Term.tid blk in
        let blk =
          match mode tid with
          | Full -> full_blk blk
          | Fixed -> kept_blk blk
          | Reread ->
              let blk = kept_blk blk in
              Term.map jmp_t blk ~f:(fun j ->
                  Jmp.map_exp ~f:substitute j
                  |> Model.map_effects ~read:lookup ~write:Fun.id)
          | Stable ->
              names := Var.Map.empty;
              let blk = Term.map phi_t blk ~f:(fun p ->
                  let v = Phi.lhs p in
                  if Var.index v = 0 && renamable v
                     && not (preserve_phi tid (Term.tid p)) then begin
                    let v = new_name v in
                    set_name v;
                    Phi.with_lhs p v
                  end else (set_name v; p)) in
              let blk = Term.map def_t blk ~f:(fun d ->
                  let d = Def.with_rhs d (substitute (Def.rhs d)) in
                  let v = Def.lhs d in
                  if Var.index v = 0 && renamable v
                     && not (preserve_def tid (Term.tid d)) then begin
                    let lhs = new_name v in
                    set_name lhs;
                    Def.with_lhs d lhs
                  end else (
                    if Var.index v > 0 || preserve_def tid (Term.tid d)
                    then set_name v;
                    d)) in
              let blk = Term.map jmp_t blk ~f:(fun j ->
                  Jmp.map_exp ~f:substitute j
                  |> Model.map_effects ~read:lookup ~write:Fun.id) in
              let blk = Term.map jmp_t blk ~f:(fun j ->
                  Model.map_effects ~read:Fun.id ~write:(fun v ->
                      if Var.index v = 0 && renamable v
                         && not (preserve_write tid (Term.tid j) v) then begin
                        let v = new_name v in set_name v; v
                      end else (set_name v; v)) j) in
              Term.set_attr blk ssa_tag ()
        in
        record tid;
        blk)
  in
  (* The wiring pass: each phi operand is the predecessor's end name
     for that base, base itself when the predecessor does not name it.
     The SP incoming from a call block carries the pushed word. *)
  let wired_blk blk =
      Term.map phi_t blk ~f:(fun phi ->
          let base = Var.base (Phi.lhs phi) in
          let values =
            let sources = match preds_of with
              | None -> Phi.values phi |> Seq.to_list |> Base.List.map ~f:fst
              | Some preds -> preds (Term.tid blk) in
            Base.List.map sources ~f:(fun src ->
                   let name =
                     match Core.Map.find !outputs src with
                     | Some names ->
                       Base.Option.value (Core.Map.find names base)
                         ~default:base
                     | None -> base
                   in
                   let exp =
                     if
                       Var.same base sp
                       && Core.Set.mem machine_blk_tids src
                     then
                       Bil.BinOp
                         (Bil.PLUS, Bil.Var name, restore_word ~abi)
                     else Bil.Var name
                   in
                   (src, exp))
          in
          let old_values = Phi.values phi |> Seq.to_list in
          if Base.List.equal (fun (a, x) (b, y) ->
                 Tid.equal a b && Exp.equal x y) old_values values
          then phi
          else Phi.of_list (Phi.lhs phi) values)
  in
  let sub = Term.map blk_t sub ~f:wired_blk in
  let sub = Term.set_attr sub high_water_tag (Core.Hashtbl.to_alist nums) in
  sub

let is_real tid =
  not (Tid.equal tid Graphs.Tid.start) && not (Tid.equal tid Graphs.Tid.exit)

(* A backedge to the first block needs a separate initial incoming edge.
   Keep its identity stable across fresh construction and updates; an
   update reuses the old entry's attrs, so rebuilding it is not a change. *)
let with_entry ?old sub =
  match Term.first blk_t sub with
  | None -> sub
  | Some first ->
    let g = Sub.to_graph sub in
    if Graphs.Tid.Node.preds (Term.tid first) g |> Seq.exists ~f:is_real then
      let tid = Tid.for_name ~package:"hike" ("ssa-entry-" ^ Tid.to_string (Term.tid sub)) in
      let entry = Blk.create ~tid ~jmps:[Jmp.create (Goto (Direct (Term.tid first)))] ()
        |> fun b -> Term.set_attr b entry_tag () in
      let entry =
        match old with
        | Some old ->
          (match Term.find blk_t old tid with
           | Some previous when Term.has_attr previous entry_tag ->
             Term.with_attrs entry (Term.attrs previous)
           | _ -> entry)
        | None -> entry
      in
      Term.prepend blk_t sub entry
    else sub

(* What phi placement and renaming share for one pre-SSA sub: its CFG,
   the call edges, and the blocks' phi needs. *)
type ctx = {
  abi : Abi.t;
  sp : var;
  renamable : var -> bool;
  succs_of : Tid.t -> Tid.t list;
  preds_of : Tid.t -> Tid.t list;
  machine_blk_tids : Tid.Set.t;
  sub : sub term;
  needs : Var.Set.t Tid.Map.t;
}

let analyze ~(synth : Hike_synth.table)
    ~(target : Bap_core_theory.Theory.Target.t) (sub : sub term) : ctx =
    let abi = Abi.of_target target in
    let pc = Abi.pc target in
    (* The sub's own SP var: the retype gave it the pointer sort, and the
       phi must keep that sort (a fresh [Abi.sp] would
       reintroduce an integer SP beside the pointer one). *)
    let sp =
      Term.enum blk_t sub
      |> Seq.concat_map ~f:(fun b -> Term.enum def_t b)
      |> Seq.find_map ~f:(fun d ->
             let v = Def.lhs d in
             if Abi.is_sp abi (Var.base v) then Some v else None)
      |> Base.Option.value ~default:(Abi.sp target)
    in
    let window = Model.hike_window_var ~word:abi.Abi.word in
    (* The memory state stays one un-renamed variable: no Mem-typed var
       (the model's memory or an address value) takes versions. *)
    let renamable (v : var) =
      not (Model.is_mem v)
      && not (Model.is_model_storage synth v)
      && not (Hike_synth.is_address_var synth v)
      && not (Var.same v pc)
      && not (Var.same v window)
      && not (Model.is_arg_slot synth (Var.base v))
      && not (Model.is_call_arg synth (Var.base v))
    in
    (* The sub's CFG, straight from the BIR (every edge is an explicit
       jmp: the completion writes the guards' fallthroughs).  The
       [start]/[exit] pseudo-nodes are dropped for the block relations. *)
    let g = Sub.to_graph sub in
    let succs_of tid =
      Graphs.Tid.Node.succs tid g |> Seq.to_list |> Base.List.filter ~f:is_real
    in
    let preds_of tid =
      Graphs.Tid.Node.preds tid g |> Seq.to_list |> Base.List.filter ~f:is_real
    in
    let machine_blk_tids =
      Term.enum blk_t sub
      |> Seq.filter ~f:(fun blk ->
             Term.enum jmp_t blk |> Seq.exists ~f:machine_call)
      |> Seq.map ~f:Term.tid
      |> Seq.to_list
      |> Core.Set.of_list (module Tid)
    in
#ifdef VSA_DEBUG
    debug_graph g;
#endif
    (* Block live-in over the terms' own reads and writes. *)
    let live_in =
      let live =
        Hike_bir_flow.liveness ~graph:g ~sub
          ~initial:(Tid.Map.singleton Graphs.Tid.exit Var.Set.empty)
          ~def:(fun d -> (Model.writes (`Def d), Model.reads (`Def d)))
          ~phi:(fun p -> (Model.writes (`Phi p), Model.reads (`Phi p)))
          ~jmp:(fun j -> (Model.writes (`Jmp j), Model.reads (`Jmp j)))
      in
      fun tid ->
        Base.Option.value (Core.Map.find live.Hike_bir_flow.before tid)
          ~default:Var.Set.empty
    in
    (* Incoming values are block parameters even with one predecessor:
       each edge's refinement belongs to the destination's own name. *)
    let needs =
      Term.enum blk_t sub
      |> Seq.fold ~init:Tid.Map.empty ~f:(fun needs blk ->
          let tid = Term.tid blk in
          if Base.List.is_empty (preds_of tid) then needs
          else
            let inputs = Core.Set.filter (live_in tid) ~f:renamable in
            let inputs =
              if Base.List.exists (preds_of tid) ~f:(Core.Set.mem machine_blk_tids)
              then Core.Set.add inputs sp else inputs in
            Core.Map.set needs ~key:tid ~data:inputs)
    in
    { abi; sp; renamable; succs_of; preds_of; machine_blk_tids; sub;
      needs }

(* The construction on a sub whose jmp effects are prepared. *)
let construct ~(synth : Hike_synth.table)
    ~(target : Bap_core_theory.Theory.Target.t) (sub : sub term) : sub term =
  if Seq.is_empty (Term.enum blk_t sub) then sub
  else
    let c = analyze ~synth ~target (with_entry sub) in
    let sub =
      place_phis ~preds_of:c.preds_of ~only:(Fun.const true) c.needs c.sub
    in
    let sub =
      rename_versions ~abi:c.abi ~sp:c.sp
        ~renamable:c.renamable
        ~machine_blk_tids:c.machine_blk_tids sub
    in
    sub

(* The block back in its pre-SSA form: base names and no phis. *)
let unssa_blk (blk : blk term) : blk term =
  let base_exp =
    (object
      inherit Exp.mapper
      method! map_sym z = Var.base z
    end)#map_exp
  in
  blk
  |> Term.filter phi_t ~f:(Fun.const false)
  |> Term.map def_t ~f:(fun d ->
         Def.with_lhs (Def.with_rhs d (base_exp (Def.rhs d)))
           (Var.base (Def.lhs d)))
  |> Term.map jmp_t ~f:(fun j ->
         Jmp.map_exp ~f:base_exp j
         |> Model.map_effects ~read:Var.base ~write:Var.base)
  |> fun b -> Term.del_attr b ssa_tag

let unssa_sub (sub : sub term) : sub term =
  Term.map blk_t sub ~f:unssa_blk

(* Up to a consistent renaming of versions per base var: each version is
   renumbered by first occurrence, then the terms are printed without
   their own tids. *)
let canonical (sub : sub term) : string =
  let seen : var Var.Table.t = Core.Hashtbl.create (module Var) in
  let counts : int Var.Table.t = Core.Hashtbl.create (module Var) in
  let name v =
    if Var.index v = 0 then v
    else
      match Core.Hashtbl.find seen v with
      | Some w -> w
      | None ->
          let b = Var.base v in
          let n = 1 + Base.Option.value (Core.Hashtbl.find counts b) ~default:0 in
          Core.Hashtbl.set counts ~key:b ~data:n;
          let w = Var.with_index b n in
          Core.Hashtbl.set seen ~key:v ~data:w;
          w
  in
  let exp =
    (object
      inherit Exp.mapper
      method! map_sym z = name z
    end)#map_exp
  in
  let vars l =
    String.concat "," (Base.List.map l ~f:(fun v -> Var.to_string (name v)))
  in
  let label = function
    | Direct t -> Tid.name t
    | Indirect e -> Exp.to_string (exp e)
  in
  let buf = Buffer.create 4096 in
  let line fmt = Printf.bprintf buf (fmt ^^ "\n") in
  Term.enum blk_t sub
  |> Seq.iter ~f:(fun blk ->
         line "blk %s" (Tid.name (Term.tid blk));
         Term.enum phi_t blk |> Seq.to_list
         |> Base.List.sort ~compare:(fun p q ->
                Var.compare (Var.base (Phi.lhs p)) (Var.base (Phi.lhs q)))
         |> Base.List.iter ~f:(fun p ->
                let lhs = name (Phi.lhs p) in
                let ins =
                  Phi.values p |> Seq.to_list
                  |> Base.List.sort ~compare:(fun (a, _) (b, _) ->
                         Tid.compare a b)
                  |> Base.List.map ~f:(fun (s, e) ->
                         Tid.name s ^ ":" ^ Exp.to_string (exp e))
                in
                line "phi %s = %s" (Var.to_string lhs) (String.concat ";" ins));
         Term.enum def_t blk
         |> Seq.iter ~f:(fun d ->
                let rhs = exp (Def.rhs d) in
                line "def %s = %s" (Var.to_string (name (Def.lhs d)))
                  (Exp.to_string rhs));
         Term.enum jmp_t blk
         |> Seq.iter ~f:(fun j ->
                let cond = exp (Jmp.cond j) in
                let kind =
                  match Jmp.kind j with
                  | Goto l -> "goto " ^ label l
                  | Ret l -> "ret " ^ label l
                  | Int (n, t) -> Printf.sprintf "int %d %s" n (Tid.name t)
                  | Call c ->
                      Printf.sprintf "call %s -> %s" (label (Call.target c))
                        (Base.Option.value_map (Call.return c) ~default:"-"
                           ~f:label)
                in
                let eff = Model.effects j in
                line "jmp when %s %s r[%s] w[%s]" (Exp.to_string cond) kind
                  (vars eff.Model.Term_effects.reads)
                  (vars eff.Model.Term_effects.writes)));
  Buffer.contents buf

let equivalent (a : sub term) (b : sub term) : bool =
  String.equal (canonical a) (canonical b)

(* CFG changes affect VSA facts independently of SSA identity. New blocks
   are named once; existing blocks retain names while their phi operands
   are rewired and their reachable dependents are woken. *)
let update_sub_woken_analyzed ~(old : sub term) ~(c : ctx)
    (sub : sub term) : sub term * Tid.Set.t =
  if Seq.is_empty (Term.enum blk_t sub) then (sub, Tid.Set.empty)
  else
    let old_g = Sub.to_graph old in
    let old_preds tid =
      Graphs.Tid.Node.preds tid old_g |> Seq.to_list
      |> Base.List.filter ~f:is_real |> Tid.Set.of_list
    in
    let tids f b = Seq.to_list (Seq.map (f b) ~f:Term.tid) in
    let phi_bases b =
      Term.enum phi_t b |> Seq.to_list
      |> Base.List.map ~f:(fun p -> Var.base (Phi.lhs p))
      |> Var.Set.of_list
    in
    (* A block whose only change is new pure jmps keeps its names; the
       jmps' reads are resolved in place. *)
    let kind b =
      let tid = Term.tid b in
      let needed =
        Base.Option.value (Core.Map.find c.needs tid) ~default:Var.Set.empty
      in
      match Term.find blk_t old tid with
      | None -> Full
      | Some ob when not (Term.has_attr ob ssa_tag) ->
          failwith "Hike_ssa.update_sub: existing block lacks SSA marker"
      | Some ob ->
          let changed_jmps = tids (Term.enum jmp_t) ob <> tids (Term.enum jmp_t) b in
          let pure j =
            Core.Set.is_empty (Model.writes (`Jmp j))
            && Base.Option.is_none (call_of_jmp j)
          in
          let differing x y =
            Term.enum jmp_t x
            |> Seq.filter ~f:(fun j -> Base.Option.is_none (Term.find jmp_t y (Term.tid j)))
          in
          if
            not (Core.Set.equal (old_preds tid) (Tid.Set.of_list (c.preds_of tid)))
            || not (Base.List.equal (fun a b ->
                      Tid.equal (Term.tid a) (Term.tid b)
                      && Var.equal (Def.lhs a) (Def.lhs b)
                      && Exp.equal (Def.rhs a) (Def.rhs b))
                      (Term.enum def_t ob |> Seq.to_list)
                      (Term.enum def_t b |> Seq.to_list))
            || Seq.exists (Term.enum jmp_t b) ~f:(fun j ->
                 match Term.find jmp_t ob (Term.tid j) with
                 | None -> false
                 | Some oj ->
                   not (Core.Set.equal (Model.reads (`Jmp oj)) (Model.reads (`Jmp j)))
                   || not (Core.Set.equal (Model.writes (`Jmp oj)) (Model.writes (`Jmp j)))
                   || not (Exp.equal (Jmp.cond oj) (Jmp.cond j))
                   || Jmp.kind oj <> Jmp.kind j)
            || not (Core.Set.equal needed (phi_bases b))
          then Stable
          else if changed_jmps then
            if Seq.for_all (differing b ob) ~f:pure
               && Seq.for_all (differing ob b) ~f:pure
            then Reread
            else Stable
          else Fixed
    in
    let kinds =
      Term.enum blk_t sub |> Seq.to_list
      |> Base.List.fold ~init:Tid.Map.empty ~f:(fun m b ->
             Core.Map.set m ~key:(Term.tid b) ~data:(kind b))
    in
    let roots =
      Core.Map.fold kinds ~init:[] ~f:(fun ~key ~data acc ->
          if data <> Fixed then key :: acc else acc)
    in
    let rec close seen = function
      | [] -> seen
      | t :: rest ->
          if Core.Set.mem seen t then close seen rest
          else close (Core.Set.add seen t) (c.succs_of t @ rest)
    in
    let affected = close Tid.Set.empty roots in
    let mode tid =
      match Term.find blk_t old tid with
      | None -> Full
      | Some _ -> Base.Option.value (Core.Map.find kinds tid) ~default:Fixed
    in
    (* Fresh versions continue above every index ever used. *)
    let floor =
      let note acc v =
        if Var.index v = 0 then acc
        else
          Core.Map.update acc (Var.base v) ~f:(function
            | Some k when k >= Var.index v -> k
            | _ -> Var.index v)
      in
      let scan acc s =
        Term.enum blk_t s
        |> Seq.fold ~init:acc ~f:(fun acc blk ->
               Blk.elts blk
               |> Seq.fold ~init:acc ~f:(fun acc t ->
                      Core.Set.fold (Model.writes t)
                        ~init:
                          (Core.Set.fold (Model.reads t) ~init:acc ~f:note)
                        ~f:note))
      in
      let history = Core.Map.of_alist_exn (module Var) (high_water old) in
      let current = scan (scan Var.Map.empty old) sub in
      Core.Map.merge history current ~f:(fun ~key:_ -> function
          | `Left k | `Right k -> Some k
          | `Both (a, b) -> Some (max a b))
    in
    let base =
      Term.map blk_t sub ~f:(fun b ->
          match Term.find blk_t old (Term.tid b) with
          | None -> Base.Option.value (Term.find blk_t c.sub (Term.tid b)) ~default:b
          | Some ob when Base.Option.value (Core.Map.find kinds (Term.tid b))
                            ~default:Fixed = Fixed -> ob
          | Some ob ->
              let b = Term.filter phi_t b ~f:(Fun.const false) in
              let needed = Base.Option.value (Core.Map.find c.needs (Term.tid b))
                  ~default:Var.Set.empty in
              let b = Term.enum phi_t ob
                  |> Seq.filter ~f:(fun p ->
                         Core.Set.mem needed (Var.base (Phi.lhs p)))
                  |> Seq.fold ~init:b ~f:(Term.append phi_t) in
              let b = Term.map def_t b ~f:(fun d ->
                  match Term.find def_t ob (Term.tid d) with
                  | None -> d
                  | Some previous -> Def.with_lhs d (Def.lhs previous)) in
              let b = Term.map jmp_t b ~f:(fun j ->
                  match Term.find jmp_t ob (Term.tid j) with
                  | None -> j
                  | Some previous ->
                      let writes = (Model.effects previous).Model.Term_effects.writes in
                      Model.map_effects ~read:Fun.id ~write:(fun v ->
                          Base.Option.value
                            (Base.List.find writes ~f:(Var.same v)) ~default:v) j) in
              Term.set_attr b ssa_tag ())
    in
    let base =
      place_phis ~preds_of:c.preds_of ~only:(Fun.const true) c.needs base
    in
    let result =
      let preserve_phi block phi =
        match Term.find blk_t old block with
        | None -> false
        | Some previous -> Option.is_some (Term.find phi_t previous phi)
      in
      let preserve_def block def =
        match Term.find blk_t old block with
        | None -> false
        | Some previous -> Option.is_some (Term.find def_t previous def)
      in
      let preserve_write block jmp v =
        match Term.find blk_t old block with
        | None -> false
        | Some previous ->
            (match Term.find jmp_t previous jmp with
             | None -> false
             | Some j ->
                 (* Only a versioned write is an identity worth keeping;
                    a version-0 name is a pre-SSA lane, not a definition. *)
                 Base.List.exists
                   (Model.effects j).Model.Term_effects.writes
                   ~f:(fun w -> Var.equal v w && Var.index w > 0))
      in
      rename_versions ~mode ~floor ~preds_of:c.preds_of ~abi:c.abi
        ~preserve_phi ~preserve_def ~preserve_write
        ~sp:c.sp ~renamable:c.renamable
        ~machine_blk_tids:c.machine_blk_tids base
    in
(* The update preserves existing read/write identities by design, so it
   is not textually equal to a fresh construction; the property
   verifier (tests, vsa-debug) is its oracle. *)
    let woken = affected in
    (result, woken)

let update_sub_woken ~(synth : Hike_synth.table)
    ~(target : Bap_core_theory.Theory.Target.t) ~(old : sub term)
    (sub : sub term) : sub term * Tid.Set.t =
  if Seq.is_empty (Term.enum blk_t sub) then (sub, Tid.Set.empty)
  else
    let sub = with_entry ~old sub in
    let c = analyze ~synth ~target (unssa_sub sub) in
    update_sub_woken_analyzed ~old ~c sub

let update_sub ~synth ~target ~old sub =
  fst (update_sub_woken ~synth ~target ~old sub)

(* Under SSA the sub's input lanes are its index-0 reads: every
   versioned read is dominated by its def.  The model's memory vars and
   storage bases are not lanes; a Mem-typed pointer value is. *)
let free_regs_ssa ~(synth : Hike_synth.table) ~(abi : Abi.t) (sub : sub term) :
    var list =
  Term.enum blk_t sub
  |> Seq.fold ~init:Var.Set.empty ~f:(fun acc blk ->
      Blk.elts blk |> Seq.fold ~init:acc ~f:(fun acc term ->
          Core.Set.union acc (Model.reads term
              |> Core.Set.filter ~f:(fun v -> Var.index v = 0))))
  |> Core.Set.filter ~f:(fun v ->
         not
           (Model.is_model_storage synth v
          || Model.is_window_var synth v || Abi.is_sp abi (Var.base v)
          || Hike_synth.is_address_var synth v))
  |> Core.Set.to_list

(* The highest version index each base variable reaches in the sub. *)
let version_ceiling (sub : sub term) : int Var.Map.t =
  let note acc v =
    Core.Map.update acc (Var.base v) ~f:(function
      | Some k when k >= Var.index v -> k
      | _ -> Var.index v)
  in
  Term.enum blk_t sub
  |> Seq.fold ~init:(Core.Map.of_alist_exn (module Var) (high_water sub)) ~f:(fun acc blk ->
      Blk.elts blk
      |> Seq.fold ~init:acc ~f:(fun acc t ->
          Core.Set.fold (Model.writes t) ~f:note
            ~init:(Core.Set.fold (Model.reads t) ~f:note ~init:acc)))

(* Derived views may mint versions too; the canonical body reserves them
   even though its claims and matching warm solution stay unchanged. *)
let retain_history ~from sub =
  let versions = Core.Map.merge (version_ceiling from) (version_ceiling sub)
      ~f:(fun ~key:_ -> function
          | `Left n | `Right n -> Some n
          | `Both (a, b) -> Some (max a b)) in
  Term.set_attr sub high_water_tag (Core.Map.to_alist versions)

let is_call_jmp (j : jmp term) : bool =
  match Jmp.kind j with
  | Call _ -> not (Hike_return.is_jmp j)
  | _ -> false

(* Refresh selected call effects. Existing reads and writes retain their
   exact versions; a gained read comes from the block's local outputs. *)
let refresh_calls ~(synth : Hike_synth.table) ~(abi : Abi.t)
    ~(callee : Tid.t -> sub term option) ~(select : jmp term -> bool)
    (sub : sub term) : sub term =
  if
    not
      (Term.enum blk_t sub
       |> Seq.exists ~f:(fun blk -> Term.enum jmp_t blk |> Seq.exists ~f:select))
  then sub
  else
    let derived = Model.prepare_effects ~synth ~abi ~callee sub in
    let ceiling = ref (version_ceiling sub) in
    let fresh w =
      let b = Var.base w in
      let k = 1 + Core.Option.value (Core.Map.find !ceiling b) ~default:0 in
      ceiling := Core.Map.set !ceiling ~key:b ~data:k;
      Var.with_index b k
    in
    let assoc_base lanes v = Base.List.find lanes ~f:(Var.same v) in
    Term.map blk_t sub ~f:(fun blk ->
        if not (Term.enum jmp_t blk |> Seq.exists ~f:select) then blk
        else
        let prepared = Term.find_exn blk_t derived (Term.tid blk) in
        Term.map jmp_t blk ~f:(fun j ->
              if not (select j) then j
              else
                let old = Model.effects j in
                let read r =
                  match assoc_base old.Model.Term_effects.reads r with
                  | Some v -> v
                  | None ->
                      Base.Option.value (Model.local_output blk r) ~default:r
                in
                let write w =
                  let v =
                    match assoc_base old.Model.Term_effects.writes w with
                    | Some v -> v
                    | None -> fresh w
                  in
                  v
                in
                Term.find_exn jmp_t prepared (Term.tid j)
                |> Model.map_effects ~read ~write))

(* Read-only lane narrowing leaves register definitions and their VSA facts
   intact. A gained live merge or changed result needs a real SSA update. *)
let relane_sub ~synth ~target ~callee sub =
  if Seq.is_empty (Term.enum blk_t sub) then sub else
  let abi = Abi.of_target target in
  let refreshed = refresh_calls ~synth ~abi ~callee ~select:is_call_jmp sub in
  let changed_writes = Term.enum blk_t refreshed |> Seq.exists ~f:(fun b ->
      Term.enum jmp_t b |> Seq.exists ~f:(fun j ->
          let before = Term.find_exn blk_t sub (Term.tid b)
            |> fun b -> Term.find_exn jmp_t b (Term.tid j) in
          not (Core.Set.equal (Model.writes (`Jmp before)) (Model.writes (`Jmp j))))) in
  let sub' = with_entry ~old:sub refreshed in
  let c = analyze ~synth ~target (unssa_sub sub') in
  let needed b = Base.Option.value (Core.Map.find c.needs (Term.tid b))
      ~default:Var.Set.empty in
  let missing = Term.enum blk_t sub' |> Seq.exists ~f:(fun b ->
      let existing = Term.enum phi_t b |> Seq.map ~f:(fun p -> Var.base (Phi.lhs p))
        |> Seq.to_list |> Var.Set.of_list in
      not (Core.Set.is_subset (needed b) ~of_:existing)) in
  if changed_writes || missing then
    fst (update_sub_woken_analyzed ~old:sub ~c sub')
  else
    Term.map blk_t refreshed ~f:(fun b ->
        Term.filter phi_t b ~f:(fun p ->
            Core.Set.mem (needed b) (Var.base (Phi.lhs p))))

(* The SSA edit session: a mutable builder over an SSA sub.  A pass that
   restructures the BIR after construction calls these primitives instead
   of rebuilding terms by hand; [finish] derives the new calls' lanes and
   commits the whole edit through the update once.  [split_block] gives
   every call its own block and rewires the successor phis per piece. *)
module Edit = struct
  type t = {
    synth : Hike_synth.table;
    target : Bap_core_theory.Theory.Target.t;
    callee : Tid.t -> sub term option;
    original : sub term;
    mutable current : sub term;
    (* New or retargeted call jmps: their lanes are derived at finish. *)
    mutable derive : Tid.Set.t;
    (* Moved call jmps that had no effects: derive only if still bare. *)
    mutable bare : Tid.Set.t;
    (* A block with a new renamable definition needs the update. *)
    mutable mint : bool;
  }

  let start ~synth ~target ~callee sub =
    { synth;
      target;
      callee;
      original = sub;
      current = sub;
      derive = Tid.Set.empty;
      bare = Tid.Set.empty;
      mint = false }

  let view t = t.current

  let update_blk t tid f =
    match Term.find blk_t t.current tid with
    | None ->
        failwith
          (Printf.sprintf "Hike_ssa.Edit: no block %s" (Tid.name tid))
    | Some b ->
        t.current <- Term.update blk_t t.current (f b);
        t

  let append_jmp t blk j =
    (match Jmp.kind j with
     | Call _ -> t.derive <- Core.Set.add t.derive (Term.tid j)
     | _ -> ());
    update_blk t blk (fun b -> Term.append jmp_t b j)

  let replace_jmp t (old : jmp term) (j : jmp term) =
    let old_tid = Term.tid old in
    let found = ref false in
    t.current <-
      Term.map blk_t t.current ~f:(fun b ->
          if Base.Option.is_none (Term.find jmp_t b old_tid) then b
          else begin
            found := true;
            Term.map jmp_t b ~f:(fun x ->
                if Tid.equal (Term.tid x) old_tid then j else x)
          end);
    if not !found then
      failwith
        (Printf.sprintf "Hike_ssa.Edit: no jmp %s" (Tid.name old_tid));
    (match Jmp.kind j with
     | Call _ -> t.derive <- Core.Set.add t.derive (Term.tid j)
     | _ -> ());
    t

  let remove_jmp t tid =
    t.current <-
      Term.map blk_t t.current ~f:(fun b ->
          Term.filter jmp_t b ~f:(fun j -> not (Tid.equal (Term.tid j) tid)));
    t

  (* Replace a block's jmp series.  Every call in the new series is a
     derived lane set: its target may be new, so its effects are not
     trusted. *)
  let set_jmps t blk js =
    Base.List.iter js ~f:(fun j ->
        match Jmp.kind j with
        | Call _ -> t.derive <- Core.Set.add t.derive (Term.tid j)
        | _ -> ());
    update_blk t blk (fun b ->
        Base.List.fold js
          ~init:(Term.filter jmp_t b ~f:(Fun.const false))
          ~f:(Term.append jmp_t))

  (* Add a local definition (a dispatch-base binding).  It is a new
     renamable value, so the commit must version it. *)
  let add_def t ~blk ?before d =
    t.mint <- true;
    update_blk t blk (fun b ->
        match before with
        | Some before -> Term.prepend def_t ~before b d
        | None -> Term.append def_t b d)

  let add_block t b =
    let call_arg d = Model.is_call_arg t.synth (Def.lhs d) in
    if (Term.enum phi_t b |> Seq.is_empty |> not)
       || (Term.enum def_t b |> Seq.exists ~f:(fun d -> not (call_arg d)))
    then t.mint <- true;
    t.current <- Term.append blk_t t.current b;
    t

  let remove_block t tid =
    t.current <-
      Term.filter blk_t t.current ~f:(fun b ->
          not (Tid.equal (Term.tid b) tid));
    t

  let tids_of js = Core.Set.of_list (module Tid) (Base.List.map js ~f:Term.tid)

  (* The pieces and, per original edge, the block that now holds it:
     every jmp must be a direct goto or a direct call.  The first piece
     keeps the tid, phis and defs; a call moves into its own action block
     with the call-arg defs.  Successor phi edges from the original block
     are duplicated per holder. *)
  let split_block t blk_tid groups =
    match Term.find blk_t t.current blk_tid with
    | None ->
        failwith
          (Printf.sprintf "Hike_ssa.Edit: no block %s" (Tid.name blk_tid))
    | Some blk ->
      let jmps = Term.enum jmp_t blk |> Seq.to_list in
      let flat = Base.List.concat groups in
      if not (Core.Set.equal (tids_of flat) (tids_of jmps)) then
        failwith
          (Printf.sprintf
             "Hike_ssa.Edit: split of block %s does not cover its jmps"
             (Tid.name blk_tid));
      let edge_of j =
        match Jmp.kind j with
        | Goto (Direct target) -> `Goto target
        | Call c -> (
            match Call.return c with
            | Some (Direct return) -> `Call return
            | None -> `No_edge
            | Some _ ->
                failwith
                  (Printf.sprintf
                     "Hike_ssa.Edit: split of block %s: call %s has no \
                      direct return"
                     (Tid.name blk_tid) (Tid.name (Term.tid j))))
        | _ ->
            failwith
              (Printf.sprintf
                 "Hike_ssa.Edit: split of block %s: jmp %s is not a direct \
                  goto or call"
                 (Tid.name blk_tid) (Tid.name (Term.tid j)))
      in
      let ssa = Term.has_attr blk Model.ssa_tag in
      let tag b = if ssa then Term.set_attr b Model.ssa_tag () else b in
      let call_args =
        Term.enum def_t blk
        |> Seq.filter ~f:(fun d -> Model.is_call_arg t.synth (Def.lhs d))
        |> Seq.to_list
      in
      let has_actions =
        Base.List.exists flat ~f:(fun j ->
            match Jmp.kind j with Call _ -> true | _ -> false)
      in
      let built =
        Base.List.map groups ~f:(fun group ->
            Base.List.map group ~f:(fun j ->
                let edge = edge_of j in
                match Jmp.kind j with
                | Call _ ->
                    let action =
                      Blk.create ~defs:call_args
                        ~jmps:[ Jmp.with_cond j (Bil.Int (Word.one 1)) ]
                        ()
                      |> tag
                    in
                    ( Jmp.create ~cond:(Jmp.cond j)
                        (Goto (Direct (Term.tid action))),
                      Some action,
                      edge )
                | _ -> (j, None, edge)))
      in
      let piece_tids =
        Term.tid blk
        :: Base.List.map (Base.List.tl_exn groups) ~f:(fun _ -> Tid.create ())
      in
      let pieces =
        Base.List.mapi built ~f:(fun i group ->
            let selectors = Base.List.map group ~f:(fun (j, _, _) -> j) in
            let piece =
              if Int.equal i 0 then
                Term.filter jmp_t blk ~f:(Fun.const false)
                |> Term.filter def_t ~f:(fun d ->
                       (not has_actions)
                       || not (Model.is_call_arg t.synth (Def.lhs d)))
                |> fun b ->
                Base.List.fold selectors ~init:b ~f:(Term.append jmp_t)
                |> tag
              else
                Blk.create ~tid:(Base.List.nth_exn piece_tids i)
                  ~jmps:selectors ()
                |> tag
            in
            if i + 1 < Base.List.length built then
              Term.append jmp_t piece
                (Jmp.create
                   (Goto
                      (Direct
                         (Base.List.nth_exn piece_tids (i + 1)))))
            else piece)
      in
      let actions =
        Base.List.concat_map built ~f:(fun group ->
            Base.List.filter_map group ~f:(fun (_, action, _) -> action))
      in
      let holders =
        Base.List.concat
          (Base.List.mapi built ~f:(fun i group ->
               Base.List.filter_map group ~f:(fun (_, action, edge) ->
                   match edge with
                   | `Call return ->
                       Some
                         (return, Term.tid (Base.Option.value_exn action))
                   | `Goto target ->
                       Some (target, Base.List.nth_exn piece_tids i)
                   | `No_edge -> None)))
      in
      let base =
        Term.filter blk_t t.current ~f:(fun b ->
            not (Tid.equal (Term.tid b) blk_tid))
      in
      let current =
        Base.List.fold (pieces @ actions) ~init:base ~f:(Term.append blk_t)
      in
      let current =
        Term.map blk_t current ~f:(fun dst ->
            let dst_tid = Term.tid dst in
            let sources =
              Base.List.filter_map holders
                ~f:(fun (succ, holder) ->
                    Base.Option.some_if (Tid.equal succ dst_tid) holder)
              |> Base.List.dedup_and_sort ~compare:Tid.compare
            in
            Term.map phi_t dst ~f:(fun phi ->
                let values =
                  Phi.values phi |> Seq.to_list
                  |> Base.List.concat_map ~f:(fun (src, e) ->
                         if Tid.equal src blk_tid then
                           Base.List.map sources ~f:(fun holder -> (holder, e))
                         else [ (src, e) ])
                in
                Phi.of_list (Phi.lhs phi) values))
      in
      t.current <- current;
      Base.List.iter actions ~f:(fun b ->
          Term.enum jmp_t b
          |> Seq.iter ~f:(fun j ->
                 if Base.Option.is_none (Model.effects_opt j) then
                   t.bare <- Core.Set.add t.bare (Term.tid j)));
      t

  let finish t =
    if Base.phys_equal t.current t.original then (t.original, Tid.Set.empty)
    else if (not t.mint) && Core.Set.is_empty t.derive
            && Core.Set.is_empty t.bare
    then (t.current, Tid.Set.empty)
    else
      let current =
        if Core.Set.is_empty t.derive && Core.Set.is_empty t.bare then
          t.current
        else
          let abi = Abi.of_target t.target in
          let derived =
            Model.prepare_effects ~synth:t.synth ~abi ~callee:t.callee t.current
          in
          Term.map blk_t t.current ~f:(fun b ->
              let db = Term.find_exn blk_t derived (Term.tid b) in
              Term.map jmp_t b ~f:(fun j ->
                  let tid = Term.tid j in
                  let want =
                    Core.Set.mem t.derive tid
                    || (Core.Set.mem t.bare tid
                        && Base.Option.is_none (Model.effects_opt j))
                  in
                  if want then
                    Base.Option.value (Term.find jmp_t db tid) ~default:j
                  else j))
      in
      update_sub_woken ~synth:t.synth ~target:t.target ~old:t.original current
end

(* The SSA of a lifted sub: its calls read and write the machine
   convention and its returns the ABI's return lanes. *)
let prepare_sub ~(synth : Hike_synth.table)
    ~(target : Bap_core_theory.Theory.Target.t) (sub : sub term) : sub term =
  let abi = Abi.of_target target in
  let lanes = Term.enum arg_t sub |> Seq.to_list in
  (if Model.is_emittable_intrinsic sub then sub
   else Model.set_sig sub (Model.return_lanes ~target sub @ Model.sig_args sub))
  |> Model.prepare_effects ~synth ~abi ~callee:(fun _ -> None)
  |> (fun sub -> Model.set_sig sub lanes)

let ssa_sub ~synth ~target sub =
  prepare_sub ~synth ~target sub |> construct ~synth ~target

let ssa_program ~(synth : Hike_synth.table)
    ~(target : Bap_core_theory.Theory.Target.t)
    (prog : program term) : program term =
  Term.map sub_t prog ~f:(ssa_sub ~synth ~target)
