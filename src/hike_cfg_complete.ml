(* The CFG completion, fused into the solver's own loop: per phase,
   bounding dispatches grow the extra edges and split their mid-block
   case entries; at drain the materialization lands once. *)

open Bap.Std
module Vsa = Cbat_vsa
module Model = Hike_stack_model

(* The solve's own denotation: [e] denotes in [blk] (in the target
   def's before-env when [~def] is given), replayed from the phase's
   solution state by the solve's own replay. *)
type denote = Hike_kb.denote

let denote_of_sol (sol : Vsa.vsa_sol) : denote =
  fun ~blk ?def e ->
    Vsa.solve_denote
      ~pre:(Graphlib.Std.Solution.get sol (Term.tid blk)) ~blk ?def e

(* A load of at most one word; its address, if so. *)
let load_addr_of (word_bits : int) (d : def term) : exp option =
  match Model.addr_of_rhs (Def.rhs d) with
  | Some (addr, size) when Size.in_bits size <= word_bits ->
      if Option.is_none (Model.store_data_of_rhs (Def.rhs d)) then Some addr
      else None
  | _ -> None

(* The defs whose load address denotates, in the def's own before-env,
   to the stack-symbolic entry-RSP cell.  One replay per block: the
   fold carries each def's before-env, so the per-def address
   denotations ride the block's single pass. *)
let retaddr_defs ~(abi : Hike_abi.t) ~(sol : Vsa.vsa_sol)
    (sub : sub term) : Tid.Set.t =
  let word_bits = Hike_abi.word_bits abi in
  Term.enum blk_t sub
  |> Seq.fold ~init:Tid.Set.empty ~f:(fun acc blk ->
         fst
           (Vsa.fold_block_states ~sol blk ~init:acc
              ~f:(fun before _after d acc ->
                  match load_addr_of word_bits d with
                  | Some addr -> (
                      match Vsa.denote_imm_exp addr before with
                      | Ok ws when Model.is_return_address ws ->
                        Core.Set.add acc (Term.tid d)
                      | _ -> acc)
                  | None -> acc)))

(* A target variable whose reaching def reads the return-address cell:
   a return, never a dispatch candidate. *)
let retaddr_read ~(last_defs : def term Var.Map.t) ~(retaddr : Tid.Set.t)
    (v : var) : bool =
  Base.Option.value_map (Core.Map.find last_defs v |> Option.map Term.tid)
    ~default:false
    ~f:(fun dtid -> Core.Set.mem retaddr dtid)

(* The dispatch resolution's debug trace; compiled out of production. *)
let option_if_debug msg =
#ifdef VSA_DEBUG
  Printf.eprintf "hike-dbg-dispatch: %s\n%!" msg
#else
  ignore msg
#endif

(* The jmp's indirect target when it is not a retaddr read: the ret
   epilogue's target is the stack-symbolic cell, never a dispatch. *)
let dispatch_target ~(last_defs : def term Var.Map.t) ~(retaddr : Tid.Set.t)
    (j : jmp term) : exp option =
  let target =
    match Jmp.kind j with
    | Call c -> (match Call.target c with Indirect e -> Some e | _ -> None)
    | Goto (Indirect e) -> Some e
    | _ -> None
  in
  match target with
  | Some (Bil.Var v) when retaddr_read ~last_defs ~retaddr v -> None
  | t -> t

(* The run's block-address entries restricted to this sub — the block
   extents' bounds; cross-sub entries never contain a split. *)
(* The sub's block tids. *)
let sub_tids (sub : sub term) : Tid.Set.t =
  Core.Set.of_list (module Tid)
    (Base.List.map (Seq.to_list (Term.enum blk_t sub)) ~f:Term.tid)

let addressed_starts ~(block_addrs : Tid.t Addr.Map.t) (sub : sub term) :
    (Addr.t * tid) list =

  block_addrs
  |> Core.Map.to_alist
  |> Base.List.filter ~f:(fun (_, t) -> Core.Set.mem (sub_tids sub) t)

(* The dispatch's case words: a bounded plain set no larger than the
   run's block count — the words a resolution may target or split at. *)
let bounded_words ~(denote : denote) ~(block_addrs : Tid.t Addr.Map.t)
    ~(blk : blk term) ?def
    (texp : exp) : Cbat_word.t list option =
  let blocks = block_addrs in
  if Core.Map.is_empty blocks then None
  else
    Base.Option.bind (Base.Result.ok (denote ~blk ?def texp)) ~f:(fun ws ->
        if Vsa.WordSet.is_top ws || Vsa.WordSet.is_infinite ws
           || Vsa.WordSet.is_bottom ws
        then (
          option_if_debug
            (Printf.sprintf "bounded_words: the target denotation is %s"
               (if Vsa.WordSet.is_top ws then "TOP"
                else if Vsa.WordSet.is_infinite ws then "INFINITE"
                else "BOTTOM"));
          None)
        else
          (match Vsa.WordSet.enumerate ~cap:(Core.Map.length blocks) ws with
           | Some ws -> Some ws
           | None ->
             option_if_debug
               (Printf.sprintf
                  "bounded_words: card exceeds the map's %d blocks"
                  (Core.Map.length blocks));
             None))

(* Rewrite a lifted term's direct targets through [f]; indirect targets
   stay the resolution's own. *)
let remap_label f = function
  | Direct t -> Direct (f t)
  | Indirect e -> Indirect e

let remap_jmp f (j : jmp term) : jmp term =
  let kind =
    match Jmp.kind j with
    | Goto l -> Goto (remap_label f l)
    | Ret l -> Ret (remap_label f l)
    | Int (n, t) -> Int (n, f t)
    | Call c ->
      Call
        (Call.create ~target:(remap_label f (Call.target c))
           ?return:(Base.Option.map (Call.return c) ~f:(remap_label f))
           ())
  in
  Jmp.create ~tid:(Term.tid j) ~cond:(Jmp.cond j) kind

(* A dispatch word can name an address the lift never made a block: a
   jump-table case body BAP never disassembled.  [lift_at] re-decodes
   and lifts it; the lifted blocks are spliced in like any other block
   and their addresses join the run's map.  A lifted block that only
   repeats a block already present (its address or tid is known) is not
   added twice — references to it are retargeted to that block. *)
let materialize_block ~(lift_at : Addr.t -> blk term list option)
    ~(block_addrs : Tid.t Addr.Map.t) (sub : sub term) (a : Addr.t) :
    (sub term * tid * (Addr.t * tid) list) option =
  match lift_at a with
  | None | Some [] -> None
  | Some blks ->
    let addr_of b = Term.get_attr b address in
    let duplicate b =
      match addr_of b with
      | Some addr -> Core.Map.mem block_addrs addr
      | None -> false
    in
    (* A lifted direct target is address-derived; an address that already
       names a block resolves to that block's tid. *)
    let existing =
      Core.Map.fold block_addrs ~init:Tid.Map.empty
        ~f:(fun ~key:addr ~data:t m ->
          Core.Map.set m ~key:(Tid.for_addr addr) ~data:t)
    in
    let retarget t =
      Base.Option.value (Core.Map.find existing t) ~default:t
    in
    let present =
      Term.enum blk_t sub
      |> Seq.fold ~init:Tid.Set.empty ~f:(fun s b ->
             Core.Set.add s (Term.tid b))
    in
    let kept =
      Base.List.filter_map blks ~f:(fun b ->
          if duplicate b || Core.Set.mem present (Term.tid b) then None
          else Some (Term.map jmp_t b ~f:(remap_jmp retarget)))
    in
    let entries =
      Base.List.filter_map kept ~f:(fun b ->
          Base.Option.map (addr_of b) ~f:(fun addr -> (addr, Term.tid b)))
    in
    let sub' =
      Base.List.fold kept ~init:sub ~f:(fun s b -> Term.append blk_t s b)
    in
    Some (sub', retarget (Term.tid (Base.List.hd_exn blks)), entries)

(* One mid-block case entry: the prefix keeps the block's tid (its
   incoming edges) and falls through to the fresh entry block, which
   takes the address; sound only when the prefix is transparent.  A word
   in no block at all materializes its case body instead. *)
let split_entry ~(starts : (Addr.t * tid) list)
    ~(lift_at : Addr.t -> blk term list option)
    ~(block_addrs : Tid.t Addr.Map.t) (a : Addr.t) (sub : sub term) :
    sub term * tid * (Addr.t * tid) list =
  let container =
    Base.List.fold starts ~init:None ~f:(fun best (sa, t) ->
        if Word.compare sa a < 0 then
          match best with
          | Some (sa', _) when Word.compare sa' sa >= 0 -> best
          | _ -> Some (sa, t)
        else best)
  in
  match container with
  | None ->
      failwith
        (Printf.sprintf
           "hike-cfg-complete: dispatch word %s names no block in the run's block-address map"
           (Word.to_string a))
  | Some (sa, ctid) ->
    let c =
      Term.enum blk_t sub
      |> Seq.find_exn ~f:(fun b -> Tid.equal (Term.tid b) ctid)
    in
    let defs = Seq.to_list (Term.enum def_t c) in
    let pivot =
      Base.List.find defs ~f:(fun d ->
          match Term.get_attr d address with
          | Some da -> Word.equal da a
          | None -> false)
    in
    match pivot with
    | None -> (
        match materialize_block ~lift_at ~block_addrs sub a with
        | Some (sub', t, entries) -> (sub', t, entries)
        | None ->
          failwith
            (Printf.sprintf
               "hike-cfg-complete: dispatch word %s falls inside the block at %s (%s) with no entry instruction to split at"
               (Word.to_string a) (Word.to_string sa) (Tid.name ctid)))
    | Some pivot ->
        let b1, b2 = Blk.split_before c pivot in
        let b2 = Term.set_attr b2 address a in
        let b2_free = Blk.free_vars b2 in
        let repair_needed =
          Term.enum def_t b1 |> Seq.exists ~f:(fun d ->
              Core.Set.mem b2_free (Def.lhs d))
          || (Term.enum phi_t b1 |> Seq.exists ~f:(fun p ->
                 Core.Set.mem b2_free (Phi.lhs p)))
        in
        (* A prefix nothing targets is dead code and drops; a prefix
           something jumps into stays, and needs phi repair if a
           prefix-defined value is read past the split (loud). *)
        let entry = Term.first blk_t sub |> Base.Option.value_exn in
        let targets tid blk =
          Term.enum jmp_t blk
          |> Seq.exists ~f:(fun j ->
                 match Jmp.kind j with
                 | Goto (Direct t) -> Tid.equal t tid
                 | Call c -> (
                     match Call.return c with
                     | Some (Direct t) -> Tid.equal t tid
                     | _ -> false)
                 | _ -> false)
        in
        let reachable =
          Tid.equal ctid (Term.tid entry)
          || Seq.exists (Term.enum blk_t sub) ~f:(fun b ->
                 not (Tid.equal (Term.tid b) ctid)
                 && targets (Term.tid b1) b)
        in
        if reachable then (
          if not (Tid.equal (Term.tid b1) ctid) then
            failwith
              "hike-cfg-complete: the split's prefix lost the container's tid";
          if repair_needed then
            failwith
              (Printf.sprintf
                 "hike-cfg-complete: the split of the block at %s at %s needs phi repair"
                 (Word.to_string sa) (Word.to_string a));
          let sub' =
            Term.concat_map blk_t sub ~f:(fun b ->
                if Tid.equal (Term.tid b) ctid then [ b1; b2 ] else [ b ])
          in
          (sub', Term.tid b2, []))
        else
          let sub' =
            Term.concat_map blk_t sub ~f:(fun b ->
                if Tid.equal (Term.tid b) ctid then [ b2 ] else [ b ])
          in
          (sub', Term.tid b2, [])

(* The dispatch's case words, denotated at the state the jump reads;
   a bare-variable target's words come from its reaching definition's
   before-env, never the noreturn-poisoned post-transfer state. *)
let dispatch_words ~(denote : denote) ~(block_addrs : Tid.t Addr.Map.t)
    ~(last_defs : def term Var.Map.t)
    ~(blk : blk term) (texp : exp) : Cbat_word.t list option =
  match texp with
  | Bil.BinOp (Bil.PLUS, _, _) -> bounded_words ~denote ~block_addrs ~blk texp
  | Bil.Var v ->
    Base.Option.bind (Core.Map.find last_defs v) ~f:(fun add_def ->
        bounded_words ~denote ~block_addrs ~blk ~def:add_def (Def.rhs add_def))
  | _ -> None

(* The dispatch's guard subject and base: of the target's top-level
   summands, one denotates to a singleton (the base) and the other
   carries the table's delta and is the guard's subject. *)

(* The resolution's preparation walk: every resolvable dispatch's case
   words land on the run's map (mid-block entries through the block
   split).  A cross-sub word stays foreign; a word in no block is a
   loud analysis loss.  One split per walk, so the walks terminate. *)
let rec prepare_dispatches ~(denote : denote) ~(retaddr : Tid.Set.t)
    ~(fresh : Tid.Set.t ref)
    ~(lift_at : Addr.t -> blk term list option)
    ~(block_addrs : Tid.t Addr.Map.t)
    (sub : sub term) : sub term * Tid.t Addr.Map.t =
  let starts = addressed_starts ~block_addrs sub in
  let dispatch_word blk =
    let last_defs = Vsa.last_defs blk in
    Base.List.find_map (Term.enum jmp_t blk |> Seq.to_list) ~f:(fun j ->
        match dispatch_target ~last_defs ~retaddr j with
        | None -> None
        | Some texp ->
          Base.Option.bind
            ~f:(dispatch_words ~denote ~block_addrs ~last_defs ~blk) (Some texp)
          |> Base.Option.bind ~f:(fun words ->
                 Base.List.find_map words ~f:(fun w ->
                     let a = Cbat_word.to_word w in
                     match Core.Map.find block_addrs a with
                     | Some _ -> None
                     | None -> Some a)))
  in
  match
    Term.enum blk_t sub
    |> Seq.filter_map ~f:(fun blk ->
           match dispatch_word blk with
           | None -> None
           | Some a ->
               let sub', t, entries =
                 split_entry ~starts ~lift_at ~block_addrs a sub
               in
               Some (a, sub', t, entries))
    |> Seq.to_list
    |> Base.List.hd
  with
  | None ->
      option_if_debug "prepare: no missing word, done";
      (sub, block_addrs)
  | Some (a, sub', t, entries) ->
      option_if_debug
        (Printf.sprintf "prepare: split at %s -> tid %s"
           (Word.to_string a) (Tid.name t));
      let block_addrs' =
        Base.List.fold entries
          ~init:(Core.Map.set block_addrs ~key:a ~data:t)
          ~f:(fun m (addr, tid) -> Core.Map.set m ~key:addr ~data:tid)
      in
      fresh := Core.Set.add !fresh t;
      prepare_dispatches ~denote ~retaddr ~fresh ~lift_at
        ~block_addrs:block_addrs' sub'

let delta_subject ~(denote : denote) ~(last_defs : def term Var.Map.t)
    ~(blk : blk term) (texp : exp) : (exp * exp * Int64.t) option =
  let singleton_value ?def e =
    match Result.to_option (denote ~blk ?def e) with
    | Some ws ->
      (match Cbat_word.to_int64 (Vsa.WordSet.cardinality ws) with
       | Ok 1L ->
         Base.Option.bind (Vsa.WordSet.min_elem ws)
           ~f:(fun w -> Result.to_option (Cbat_word.to_int64 w))
       | _ -> None)
    | None -> None
  in
  let pick ?def x y =
    match singleton_value ?def x with
    | Some bval -> Some (y, x, bval)
    | None -> Base.Option.map (singleton_value ?def y) ~f:(fun bval -> (x, y, bval))
  in
  let reaching_sum v =
    Base.Option.bind (Core.Map.find last_defs v) ~f:(fun add_def ->
        match Def.rhs add_def with
        | Bil.BinOp (Bil.PLUS, x, y) -> pick ~def:add_def x y
        | _ -> None)
  in
  match texp with
  | Bil.BinOp (Bil.PLUS, x, y) -> pick x y
  | Bil.Var v -> reaching_sum v
  | _ -> None

(* The dispatch's case pairs off the target's denotation: a bounded
   set, every word naming an in-sub block.  The pairs are
   BASE-RELATIVE — the guard word is the delta [w - base] — so the
   runtime comparison never depends on where the table was linked. *)
let resolved_pairs_of ~(denote : denote) ~(last_defs : def term Var.Map.t)
    ~(sub_tids : Tid.Set.t) ~(block_addrs : Tid.t Addr.Map.t)
    ~(blk : blk term) (texp : exp) :
    (exp * (word * tid) list * Int64.t) option =
  let blocks = block_addrs in
  match dispatch_words ~denote ~block_addrs ~last_defs ~blk texp with
  | None -> None
  | Some ws ->
    if Base.List.length ws > Core.Map.length blocks then None
    else
        match delta_subject ~denote ~last_defs ~blk texp with
        | None -> None
        | Some (delta_exp, base_exp, bval) ->
          let subject =
            match texp with
            | Bil.BinOp (Bil.PLUS, _, _) -> delta_exp
            | _ -> Bil.BinOp (Bil.MINUS, texp, base_exp)
          in
          let case (w : Cbat_word.t) : (word * tid) option =
            let a = Cbat_word.to_word w in
            match Core.Map.find block_addrs a with
            | Some t when Core.Set.mem sub_tids t ->
              Some (Addr.of_int64 (Int64.sub (Word.to_int64_exn a) bval), t)
            | Some _ -> None
            | None ->
                failwith
                  (Printf.sprintf
                     "hike-cfg-complete: dispatch word %s names no block in the run's block-address map"
                     (Word.to_string a))
          in
          let pairs = Base.List.map ws ~f:case in
          if Base.List.exists pairs ~f:Option.is_none then None
          else Some (subject, Base.List.filter_map pairs ~f:(fun p -> p), bval)

(* The eq chain of one target's words: [sel = w1 || sel = w2 || ...].
   The words share the selector's width, so the comparisons typecheck. *)
let guarded_cond (sel : exp) (ws : word list) : exp =
  let eq w = Bil.BinOp (Bil.EQ, sel, Bil.Int w) in
  match ws with
  | [] -> Bil.Int (Word.one 1)
  | w :: rest ->
      Base.List.fold rest ~init:(eq w)
        ~f:(fun acc w -> Bil.BinOp (Bil.OR, acc, eq w))

(* The dispatch jmp's own guard narrows every case and the default
   alike. *)
let true_cond : exp = Bil.Int (Word.one 1)

let guard_of (j : jmp term) : exp option =
  match Jmp.cond j with c when Model.is_true_cond c -> None | c -> Some c

let and_guard (guard : exp option) (cond : exp) : exp =
  Base.Option.fold guard ~init:cond ~f:(fun cond g -> Bil.BinOp (Bil.AND, g, cond))

(* The dispatch's successor series: one conditional goto per distinct
   case target (its words OR-merge into one guard).  A call dispatch's
   continuation is the series' terminal; a goto dispatch has none —
   under the completeness premise its guards are exhaustive. *)
let dispatch_jmps (j : jmp term) (sel : exp)
    (pairs : (word * tid) list) (cont : tid option) :
    jmp term list option =
  let by_target =
    Base.List.fold pairs ~init:[] ~f:(fun acc (w, t) ->
        match Base.List.Assoc.find acc t ~equal:Tid.equal with
        | Some ws -> Base.List.Assoc.add acc t (w :: ws) ~equal:Tid.equal
        | None -> (t, [ w ]) :: acc)
  in
  (* Groups in ascending first-word order. *)
  let ascending = List.rev by_target in
  let guard = guard_of j in
  let guarded (t, ws) =
    Jmp.create ~cond:(and_guard guard (guarded_cond sel ws))
      (Goto (Direct t))
  in
  match cont with
  | Some t ->
    let groups =
      Base.List.filter ascending ~f:(fun (g, _) -> not (Tid.equal g t)) in
    if Base.List.is_empty groups then None
    else
      Some
        (Base.List.map groups ~f:guarded
         @ [ Jmp.create
               ~cond:(Base.Option.value guard ~default:true_cond)
               (Goto (Direct t)) ])
  | None ->
    if Base.List.length ascending < 2 then None
    else Some (Base.List.map ascending ~f:guarded)

(* The return epilogue's replacement: the canonical [Ret] shape — a
   return-less call the emitter renders as a return; the var-free
   target leaves the retaddr load unread, so the sweep kills it. *)
let ret_jmp ~(word_bits : int) : jmp term =
  Jmp.create
    (Call
       (Call.create
          ~target:(Indirect (Hike_stack_model.canonical_ret_target ~word_bits))
          ()))

(* The [bits]-bit word of an image's byte array at [off], in [endian]. *)
let image_word_at (bytes : Bytes.t) (off : int) ~(endian : endian)
    ~(bits : int) : int64 option =
  let n = bits / 8 in
  if off < 0 || off + n > Bytes.length bytes then None
  else
    let byte i = Int64.of_int (Char.code (Bytes.get bytes (off + i))) in
    let w =
      match endian with
      | LittleEndian ->
        Base.List.fold (Base.List.init n ~f:(fun i -> i)) ~init:0L
          ~f:(fun acc i -> Int64.logor acc (Int64.shift_left (byte i) (8 * i)))
      | BigEndian ->
        Base.List.fold (Base.List.init n ~f:(fun i -> i)) ~init:0L
          ~f:(fun acc i -> Int64.logor (Int64.shift_left acc 8) (byte i))
    in
    Some w

(* The completeness premise: the enumerated words cover every value
   the dispatch's source may produce; a memory-read value only when
   every address the table load may read is bounded and each slot's
   image word is one of the case addresses.  Any doubt is incomplete. *)
let table_covered ~(denote : denote) ~(last_defs : def term Var.Map.t)
    ~(blk : blk term) ~(base : Int64.t) ~(pairs : (word * tid) list)
    ~(images : Vsa.section_image list)
    (texp : exp) : bool =
  let enumerated =
    Core.Set.of_list (module Core.Int64)
      (Base.List.map pairs ~f:(fun (w, _) ->
           Int64.add (Word.to_int64_exn w) base))
  in
  let value_var =
    let singleton e =
      Base.Option.value_map (Base.Result.ok (denote ~blk e))
        ~default:false ~f:(fun ws ->
          Cbat_word.is_one (Vsa.WordSet.cardinality ws))
    in
    match texp with
    | Bil.Var _ -> Some texp
    | Bil.BinOp (Bil.PLUS, x, y) ->
      if singleton x then Some y
      else if singleton y then Some x
      else None
    | _ -> None
  in
  let load =
    Base.Option.bind value_var ~f:(fun e ->
        match e with
        | Bil.Var v -> Core.Map.find last_defs v
        | _ -> None)
  in
  (* One enumerated address: inside some image, and its slot's image
     word is one of the enumerated case addresses. *)
  let slot_covered ~(endian : endian) ~(bits : int) (a : Cbat_word.t) : bool
      =
    match Cbat_word.to_int64 a with
    | Error _ -> false
    | Ok a ->
      Base.List.find_map images ~f:(fun img ->
          if Stdlib.Int64.unsigned_compare a img.img_lo >= 0
             && Stdlib.Int64.unsigned_compare
                  (Int64.add a (Int64.of_int (bits / 8 - 1)))
                  img.img_hi <= 0
          then Some img
          else None)
      |> Base.Option.bind ~f:(fun img ->
          let off =
            Stdlib.Int64.to_int (Stdlib.Int64.sub a img.img_lo) in
          Base.Option.map
            (image_word_at img.img_bytes off ~endian ~bits)
            ~f:(Core.Set.mem enumerated))
      |> Base.Option.value ~default:false
  in
  Base.Option.bind load ~f:(fun d ->
      match Def.rhs d with
      | Bil.Load (_, addr_exp, endian, size) ->
        Some (d, addr_exp, endian, Size.in_bits size)
      | _ -> None)
  |> Base.Option.map ~f:(fun (d, addr_exp, endian, bits) ->
      match Base.Result.ok (denote ~blk ~def:d addr_exp) with
      | Some addrs
        when (not (Vsa.WordSet.is_top addrs))
             && (not (Vsa.WordSet.is_infinite addrs))
             && (not (Vsa.WordSet.is_bottom addrs))
             && not (Cbat_word.gt_int (Vsa.WordSet.cardinality addrs) 64)
        -> Base.List.for_all (Vsa.WordSet.iter addrs)
             ~f:(slot_covered ~endian ~bits)
      | _ -> false)
  |> Base.Option.value ~default:true

(* One jmp's rewrite decision: the return epilogue (a noreturn call
   whose target var's reaching def is the retaddr read) becomes the
   canonical return; a fully-resolving, completely-enumerating
   dispatch becomes the guarded-goto series; else it stays. *)
let rewritten_jmps ~(denote : denote) ~(retaddr : Tid.Set.t)
    ~(word_bits : int) ~(sub_tids : Tid.Set.t)
    ~(block_addrs : Tid.t Addr.Map.t)
    ~(last_defs : def term Var.Map.t) ~(images : Vsa.section_image list)
    ~(blk : blk term) (j : jmp term) :
    jmp term list option =
  let series texp cont =
    Base.Option.bind
      (resolved_pairs_of ~denote ~last_defs ~sub_tids ~block_addrs ~blk texp)
      ~f:(fun (subject, pairs, base) ->
          if
            table_covered ~denote ~last_defs ~blk ~base ~pairs ~images texp
          then dispatch_jmps j subject pairs cont
          else None)
  in
  match Jmp.kind j with
  | Call c -> (
      match (Call.return c, Call.target c) with
      | None, Indirect (Bil.Var v) when retaddr_read ~last_defs ~retaddr v ->
          Some [ ret_jmp ~word_bits ]
      | _, Indirect texp ->
          let cont =
            match Call.return c with
            | Some (Direct t) -> Some t
            | Some (Indirect _) | None -> None
          in
          series texp cont
      | _ -> None)
  | Goto (Indirect (Bil.Var v)) when retaddr_read ~last_defs ~retaddr v ->
      Some [ ret_jmp ~word_bits ]
  | Goto (Indirect texp) -> series texp None
  | _ -> None

(* Rebuilds [blk] with exactly [js'] as its jmps. *)
let with_jmps (blk : blk term) (js' : jmp term list) : blk term =
  let b = Blk.Builder.init ~copy_phis:true ~copy_defs:true blk in
  Base.List.iter js' ~f:(Blk.Builder.add_jmp b);
  Term.with_attrs (Blk.Builder.result b) (Term.attrs blk)

(* The fresh blocks a surviving indirect transfer may still denote:
   [go] does not follow indirect edges, so an unresolved transfer whose
   target denotation names a split entry keeps it live.  A transfer
   whose denotation cannot be bounded keeps every fresh block. *)
let indirect_live ~(denote : denote) ~(retaddr : Tid.Set.t)
    ~(block_addrs : Tid.t Addr.Map.t) ~(fresh : Tid.Set.t)
    (sub : sub term) : Tid.Set.t =
  if Core.Set.is_empty fresh then Tid.Set.empty
  else
    let add_target acc blk texp =
      let last_defs = Vsa.last_defs blk in
      match texp with
      | Bil.Var v when retaddr_read ~last_defs ~retaddr v -> acc
      | _ -> (
          match dispatch_words ~denote ~block_addrs ~last_defs ~blk texp with
          | None -> Core.Set.union acc fresh
          | Some ws ->
            Base.List.fold ws ~init:acc ~f:(fun acc w ->
                let a = Cbat_word.to_word w in
                match Core.Map.find block_addrs a with
                | Some t when Core.Set.mem fresh t -> Core.Set.add acc t
                | _ -> acc))
    in
    Term.enum blk_t sub
    |> Seq.fold ~init:Tid.Set.empty ~f:(fun acc blk ->
        Term.enum jmp_t blk
        |> Seq.fold ~init:acc ~f:(fun acc j ->
            match Jmp.kind j with
            | Goto (Indirect texp) -> add_target acc blk texp
            | Call c -> (
                match Call.target c with
                | Indirect texp -> add_target acc blk texp
                | _ -> acc)
            | _ -> acc))

(* The split retraction: a fresh entry block nothing reaches — no
   transfer names it, no jmp-less block's fallthrough (the next block
   in term order) reaches it, no surviving indirect transfer denotes
   it ([live]) — drops.  Only fresh blocks are prunable: a block behind
   an unresolved indirect transfer is live. *)
let prune_unreachable ~(fresh : Tid.Set.t) ~(live : Tid.Set.t)
    (sub : sub term) : sub term =
  if Core.Set.is_empty fresh then sub
  else
    let entry = Base.Option.value_exn (Term.first blk_t sub) in
    let blocks = Seq.to_list (Term.enum blk_t sub) in
    let rec nexts = function
      | [] -> []
      | b :: tl -> (
          let nx = match tl with b2 :: _ -> Some (Term.tid b2) | [] -> None in
          (Term.tid b, nx) :: nexts tl)
    in
    let fall_tbl = Core.Map.of_alist_exn (module Tid) (nexts blocks) in
    let rec go seen blk =
      if Core.Set.mem seen (Term.tid blk) then seen
      else
        let seen = Core.Set.add seen (Term.tid blk) in
        let js = Seq.to_list (Term.enum jmp_t blk) in
        let seen =
          Base.List.fold js ~init:seen ~f:(fun seen j ->
              let targets =
                match Jmp.kind j with
                | Goto (Direct t) -> [ t ]
                | Call c -> (
                    match Call.return c with
                    | Some (Direct t) -> [ t ]
                    | _ -> [])
                | _ -> []
              in
              Base.List.fold targets ~init:seen ~f:(fun seen t ->
                  match
                    Base.List.find blocks ~f:(fun b ->
                        Tid.equal (Term.tid b) t)
                  with
                  | Some b -> go seen b
                  | None -> seen))
        in
        if Base.List.is_empty js then
          match Core.Map.find fall_tbl (Term.tid blk) with
          | Some (Some t) -> (
              match
                Base.List.find blocks ~f:(fun b ->
                    Tid.equal (Term.tid b) t)
              with
              | Some b -> go seen b
              | None -> seen)
          | _ -> seen
        else seen
    in
    let reachable = go Tid.Set.empty entry in
    let reachable =
      Core.Set.fold live ~init:reachable ~f:(fun seen t ->
          match
            Base.List.find blocks ~f:(fun b -> Tid.equal (Term.tid b) t)
          with
          | Some b -> go seen b
          | None -> seen)
    in
    Term.filter_map blk_t sub ~f:(fun b ->
        if (not (Core.Set.mem fresh (Term.tid b)))
           || Core.Set.mem reachable (Term.tid b)
        then Some b
        else None)

(* The exit rewrite, once at drain; a sub with no decision comes back
   unchanged. *)
let rewrite_jmps_once ~(denote : denote) ~(retaddr : Tid.Set.t)
    ~(word_bits : int) ~(block_addrs : Tid.t Addr.Map.t)
    ~(images : Vsa.section_image list)
    (sub : sub term) : sub term =

  let reblock (blk : blk term) : blk term =
    let js = Seq.to_list (Term.enum jmp_t blk) in
    let last_defs = Vsa.last_defs blk in
    let decided =
      Base.List.filter_map js ~f:(fun j ->
          rewritten_jmps ~denote ~retaddr ~word_bits ~sub_tids:(sub_tids sub)
            ~block_addrs
            ~last_defs
            ~images ~blk j
          |> Base.Option.map ~f:(fun js' -> (Term.tid j, js')))
    in
    match decided with
    | [] -> blk
    | _ ->
        let rewr = Core.Map.of_alist_exn (module Tid) decided in
        let spliced =
          Base.List.concat_map js ~f:(fun j ->
              match Core.Map.find rewr (Term.tid j) with
              | Some js' -> js'
              | None -> [ j ])
        in
        with_jmps blk spliced
  in
  Term.map blk_t sub ~f:reblock

(* One resolution event pass on the phase's own solution: the case
   words land on the run's map and resolved dispatches contribute
   their target sets to the extra edges.  The split is the only BIR
   change and it is additive. *)
let resolve_phase ~(abi : Hike_abi.t) ~(sol : Vsa.vsa_sol)
    ~(images : Vsa.section_image list)
    ~(lift_at : Addr.t -> blk term list option)
    ~(block_addrs : Tid.t Addr.Map.t)
    (sub : sub term) (resolved : Tid.Set.t Tid.Map.t) :
    sub term * Tid.Set.t Tid.Map.t * Tid.Set.t * Tid.t Addr.Map.t * bool =
  let denote = denote_of_sol sol in
  let retaddr = retaddr_defs ~abi ~sol sub in
  let sub_tids = sub_tids sub in
  let fresh = ref Tid.Set.empty in
  Vsa.with_images images (fun () ->
      let sub, block_addrs' =
        prepare_dispatches ~denote ~retaddr ~fresh ~lift_at ~block_addrs sub
      in

      let grew = ref false in
      let resolved' =
        Term.enum blk_t sub
        |> Seq.fold ~init:resolved ~f:(fun acc blk ->
            let last_defs = Vsa.last_defs blk in
            Term.enum jmp_t blk
            |> Seq.fold ~init:acc ~f:(fun acc j ->
                match dispatch_target ~last_defs ~retaddr j with
                | None -> acc
                | Some texp -> (
                    match resolved_pairs_of ~denote ~last_defs ~sub_tids
                            ~block_addrs:block_addrs' ~blk texp with
                    | None -> acc
                    | Some (_, pairs, _) ->
                      let ts =
                        Core.Set.of_list (module Tid)
                          (Base.List.map pairs ~f:snd) in
                      match Core.Map.find acc (Term.tid j) with
                      | Some old when Core.Set.equal old ts -> acc
                      | Some old ->
                        grew := true;
                        Core.Map.set acc ~key:(Term.tid j)
                          ~data:(Core.Set.union old ts)
                      | None ->
                        grew := true;
                        Core.Map.set acc ~key:(Term.tid j) ~data:ts)))
      in
      (sub, resolved', !fresh, block_addrs',
       not (Core.Set.is_empty !fresh) || !grew))

(* The exit materialization at drain: the rewrites land once and the
   prune retracts the split structure the materialization didn't
   claim; the denotations run with the section images armed. *)
let materialize ~(abi : Hike_abi.t) ~(sol : Vsa.vsa_sol)
    ~(images : Vsa.section_image list) ~(block_addrs : Tid.t Addr.Map.t)
    ~(fresh : Tid.Set.t)
    (sub : sub term) : sub term =
  let retaddr = retaddr_defs ~abi ~sol sub in
  let word_bits = Hike_abi.word_bits abi in
  let sub, live =
    Vsa.with_images images (fun () ->
        let live =
          indirect_live ~denote:(denote_of_sol sol) ~retaddr ~block_addrs
            ~fresh sub
        in
        let sub =
          rewrite_jmps_once ~denote:(denote_of_sol sol) ~retaddr ~word_bits
            ~block_addrs ~images sub
        in
        (sub, live))
  in
  prune_unreachable ~fresh ~live sub
