(* The canary-strip pass's pins: the four-fact composition (the TLS
   read, the same-cell store/reload, the not-equal edge to a
   symtab-resolved __stack_chk_fail) is removed — the equality edge
   continues unconditionally, the orphaned fail block dies, the join
   keeps its arity — and every residual shape the census recorded stays
   the identity. *)

open Bap.Std
open Bap_core_theory
open Hike_test.Harness
open Hike_test.Common
open Hike_test.Fixtures

let tp = Hike_abi.x86_64_sysv.Hike_abi.thread_pointer
let m = memv "sc_m"
let rsp = v64 "RSP"
let rbp = v64 "RBP"
let rax = v64 "RAX"
let rdx = v64 "RDX"
let rcx = v64 "RCX"
let rbx = v64 "RBX"
let zf = v1 "ZF"

let tls_load = Bil.Load (Bil.Var m, Bil.Var tp, LittleEndian, `r64)

let cell_addr off =
  Bil.BinOp (Bil.MINUS, Bil.Var rbp, Bil.Int (Cbat_word.to_word (w64 off)))

let cell_load off = Bil.Load (Bil.Var m, cell_addr off, LittleEndian, `r64)
let cell_store off data = Bil.Store (Bil.Var m, cell_addr off, data, LittleEndian, `r64)
let def v rhs = Def.create v rhs
let one = Bil.Int (Word.one 1)
let zero64 = Bil.Int (Cbat_word.to_word (w64 0))

let names_of prog =
  Term.enum sub_t prog
  |> Seq.fold ~init:Tid.Map.empty ~f:(fun mm s ->
      Core.Map.set mm ~key:(Term.tid s) ~data:(Sub.name s))

let strip ?(facts : Hike.Kb.facts option) prog fixture =
  Hike.Strip_canaries.strip_sub
    ~facts:(match facts with Some f -> f | None -> top_facts)
    ~names:(names_of prog)
    fixture

(* The production chain up to the strip: the jump compiler, then the
   VSA run whose stamped block environments the seam's cell identities
   read (the pass's only VSA input).  The stamped fixture comes back
   for the strip to read its defs' Env Tags. *)
let run_to_strip (fixture : sub term) (stub : sub term) :
    sub term * program term * Hike.Kb.facts =
  let fixture = Hike.Jump.compile_sub jump_target fixture in
  let prog = Program.create ~subs:[ fixture; stub ] () in
  let facts, fixture = fixture_facts_sub fixture in
  (fixture, prog, facts)

(* Term lookups on a sub. *)
let blk_of sub btid =
  Base.List.find_exn (Term.enum blk_t sub |> Seq.to_list)
    ~f:(fun b -> Tid.equal (Term.tid b) btid)

let has_block sub btid =
  Term.enum blk_t sub |> Seq.exists ~f:(fun b -> Tid.equal (Term.tid b) btid)

let has_def sub dtid =
  Term.enum blk_t sub
  |> Seq.exists ~f:(fun b ->
      Term.enum def_t b |> Seq.exists ~f:(fun d -> Tid.equal (Term.tid d) dtid))

let has_jmp sub jtid =
  Term.enum blk_t sub
  |> Seq.exists ~f:(fun b ->
      Term.enum jmp_t b |> Seq.exists ~f:(fun j -> Tid.equal (Term.tid j) jtid))

let jmp_of sub jtid =
  Term.enum blk_t sub
  |> Seq.find_map ~f:(fun b ->
      Term.enum jmp_t b
      |> Seq.find_map ~f:(fun j ->
          if Tid.equal (Term.tid j) jtid then Some j else None))

let nth_def sub btid i =
  Base.List.nth_exn (Term.enum def_t (blk_of sub btid) |> Seq.to_list) i

let jmps_of sub btid = Term.enum jmp_t (blk_of sub btid) |> Seq.to_list

let cond_is_true j = Exp.equal (Jmp.cond j) one

(* The canary idiom at cell [off]: read -> store in the entry; reload ->
   subtract -> flag compare in the compare block; the equality edge to
   a ret; the not-equal fallthrough to [fail_jmp].  [extra_entry]
   carries pin-specific defs. *)
let build_idiom ~off ~store_data ~extra_entry ~(fail_jmp : jmp term) :
    sub term * tid array =
  let fixture, tids =
    sub_of "sc_idiom"
      [ [ def rbp (Bil.Var rsp);
          def rax tls_load;
          def m (cell_store off store_data) ] @ extra_entry,
        [ (1, mk_goto) ];
        [ def rdx (cell_load off);
          def rdx (Bil.BinOp (Bil.MINUS, Bil.Var rdx, tls_load));
          def zf (Bil.BinOp (Bil.EQ, zero64, Bil.Var rdx)) ],
        [ (2, fun t -> mk_jmp_to t (Bil.Var zf));
          (3, fun t -> mk_jmp_to t one) ];
        [], [ (0, mk_ret) ];
        [], [] ]
  in
  let fail_b = blk_of fixture tids.(3) in
  let fail_b = with_jmps fail_b [ fail_jmp ] in
  let fixture =
    Term.map blk_t fixture ~f:(fun b ->
        if Tid.equal (Term.tid b) tids.(3) then fail_b else b)
  in
  (fixture, tids)

(* The eq jmp: the compare block's jmp whose target is the eq block. *)
let eq_jmp_of fixture tids =
  Base.List.find_exn (jmps_of fixture tids.(1)) ~f:(fun j ->
      match Jmp.kind j with
      | Goto (Direct t) -> Tid.equal t tids.(2)
      | _ -> false)

(* The symtab-resolved stub and its non-equal edge call. *)
let mk_stub () : sub term = fst (sub_of "__stack_chk_fail" [ [], [] ])

let tests : unit Alcotest.test list =
  [
    (* SC1: the full composition is removed — the read, the store, the
       reload, the compare family, the not-equal edge; the equality
       edge continues unconditionally; the fail block is gone; the
       entry's other defs survive. *)
    pin "SC-01"
      "the proven canary composition deletes (read, store, reload, compare \
       family, not-equal edge); the fail block dies; the equality edge runs \
       unconditionally"
      (fun () ->
        let stub = mk_stub () in
        let fail_jmp () =
          Jmp.create (Call (Call.create ~target:(Label.direct (Term.tid stub)) ()))
        in
        let fixture, tids =
          build_idiom ~off:8 ~store_data:(Bil.Var rax) ~extra_entry:[]
            ~fail_jmp:(fail_jmp ())
        in
        let fixture, prog, facts = run_to_strip fixture stub in
        let eq_j = eq_jmp_of fixture tids in
        let fail_j =
          Base.List.find_exn (jmps_of fixture tids.(1)) ~f:(fun j ->
              not (Tid.equal (Term.tid j) (Term.tid eq_j)))
        in
        let read = nth_def fixture tids.(0) 1 in
        let store = nth_def fixture tids.(0) 2 in
        let reload = nth_def fixture tids.(1) 0 in
        let subtract = nth_def fixture tids.(1) 1 in
        let rbp_def = nth_def fixture tids.(0) 0 in
        let stripped = strip ~facts prog fixture in
        check "SC-01"
          ((not (has_def stripped (Term.tid read)))
          && not (has_def stripped (Term.tid store))
          && not (has_def stripped (Term.tid reload))
          && not (has_def stripped (Term.tid subtract))
          && not (has_jmp stripped (Term.tid fail_j))
          && not (has_block stripped tids.(3))
          && has_block stripped tids.(2)
          && has_def stripped (Term.tid rbp_def)
          && Option.is_some
               (Base.Option.filter (jmp_of stripped (Term.tid eq_j)) ~f:cond_is_true)));

    (* SC2 (census: no-RELOAD, 120 corpus-wide): the compare reads the
       read value directly, the cell has no reload — the identity. *)
    pin "SC-02"
      "no same-cell reload — the identity (the canary stays, the fail edge \
       stays)"
      (fun () ->
        let stub = mk_stub () in
        let fail_jmp () =
          Jmp.create (Call (Call.create ~target:(Label.direct (Term.tid stub)) ()))
        in
        let fixture, tids =
          build_idiom ~off:8 ~store_data:(Bil.Var rax) ~extra_entry:[]
            ~fail_jmp:(fail_jmp ())
        in
        (* Drop the reload def: rebuild the compare block without it. *)
        let cmp = blk_of fixture tids.(1) in
        let cmp =
          Term.filter def_t cmp ~f:(fun d -> not (Exp.equal (Def.rhs d) (cell_load 8)))
        in
        let fixture =
          Term.map blk_t fixture ~f:(fun b ->
              if Tid.equal (Term.tid b) tids.(1) then cmp else b)
        in
        let fixture, prog, facts = run_to_strip fixture stub in
        let subtract =
          Base.List.nth_exn (Term.enum def_t (blk_of fixture tids.(1)) |> Seq.to_list) 0
        in
        let stripped = strip ~facts prog fixture in
        check "SC-02"
          (has_def stripped (Term.tid subtract)
          && has_block stripped tids.(3)
          && has_block stripped tids.(2)));

    (* SC3 (census: no-fail-edge, 16 corpus-wide): the not-equal edge
       reaches no __stack_chk_fail — the identity. *)
    pin "SC-03"
      "the not-equal edge reaches no fail call — the identity"
      (fun () ->
        let stub = mk_stub () in
        let fixture, tids =
          build_idiom ~off:8 ~store_data:(Bil.Var rax) ~extra_entry:[]
            ~fail_jmp:(mk_ret (Tid.create ()))
        in
        let fixture, prog, facts = run_to_strip fixture stub in
        let read = nth_def fixture tids.(0) 1 in
        let store = nth_def fixture tids.(0) 2 in
        let reload = nth_def fixture tids.(1) 0 in
        let stripped = strip ~facts prog fixture in
        check "SC-03"
          (has_def stripped (Term.tid read)
          && has_def stripped (Term.tid store)
          && has_def stripped (Term.tid reload)
          && has_block stripped tids.(3)));

    (* SC4 (the census's register-alias false-fire shape): a second TLS
       read into RDX whose value a byte store's ADDRESS mentions —
       name-matching stored that store as the canary store; the
       def/value tie removes only the true composition and the alias
       store survives. *)
    pin "SC-04"
      "the alias byte-store through the read register does not become the \
       canary store — the true composition removes, the alias store and its \
       read survive"
      (fun () ->
        let stub = mk_stub () in
        let fail_jmp () =
          Jmp.create (Call (Call.create ~target:(Label.direct (Term.tid stub)) ()))
        in
        let alias_store =
          Bil.Store
            ( Bil.Var m,
              Bil.Var rdx,
              Bil.Int (Word.of_int ~width:8 0x41),
              LittleEndian,
              `r8 )
        in
        let fixture, tids =
          build_idiom ~off:0x18 ~store_data:(Bil.Var rax)
            ~extra_entry:[ def rdx tls_load; def m alias_store ]
            ~fail_jmp:(fail_jmp ())
        in
        let fixture, prog, facts = run_to_strip fixture stub in
        let read = nth_def fixture tids.(0) 1 in
        let store = nth_def fixture tids.(0) 2 in
        let alias_read = nth_def fixture tids.(0) 3 in
        let alias_st = nth_def fixture tids.(0) 4 in
        let reload = nth_def fixture tids.(1) 0 in
        let stripped = strip ~facts prog fixture in
        check "SC-04"
          ((not (has_def stripped (Term.tid read)))
          && not (has_def stripped (Term.tid store))
          && not (has_def stripped (Term.tid reload))
          && not (has_block stripped tids.(3))
          && has_def stripped (Term.tid alias_read)
          && has_def stripped (Term.tid alias_st)));

    (* SC5: the store/reload/compare/fail shape on one cell whose
       stored value is a LOCAL, not the TLS read (a decoy read is
       present) — the value tie refuses the composition. *)
    pin "SC-05"
      "a local stored to the cell is not the canary — the identity, decoy TLS \
       read notwithstanding"
      (fun () ->
        let stub = mk_stub () in
        let fail_jmp () =
          Jmp.create (Call (Call.create ~target:(Label.direct (Term.tid stub)) ()))
        in
        let fixture, tids =
          build_idiom ~off:0x20 ~store_data:(Bil.Var rbx)
            ~extra_entry:[ def rbx zero64 ]
            ~fail_jmp:(fail_jmp ())
        in
        let fixture, prog, facts = run_to_strip fixture stub in
        let read = nth_def fixture tids.(0) 1 in
        let store = nth_def fixture tids.(0) 2 in
        let reload = nth_def fixture tids.(1) 0 in
        let stripped = strip ~facts prog fixture in
        check "SC-05"
          (has_def stripped (Term.tid read)
          && has_def stripped (Term.tid store)
          && has_def stripped (Term.tid reload)
          && has_block stripped tids.(3)));

    (* SC6: two checks share one cell and one fail block (the phi
       carries an entry per pred).  A runtime selector dispatches the
       entry to both check blocks, so both compositions are proven.
       Both remove together, the fail block dies with its phi, both
       equality edges run unconditionally. *)
    pin "SC-06"
      "two checks on one cell remove together; the shared fail block and its \
       phi die; both equality edges continue unconditionally"
      (fun () ->
        let stub = mk_stub () in
        let fail_jmp () =
          Jmp.create (Call (Call.create ~target:(Label.direct (Term.tid stub)) ()))
        in
        let fixture, tids =
          sub_of "sc6"
            [ [ def rbp (Bil.Var rsp);
                def rax tls_load;
                def m (cell_store 8 (Bil.Var rax)) ],
              [ (1, mk_goto) ];
              [ def rcx (cell_load 16) ],
              [ (2, fun t -> mk_jmp_to t (Bil.BinOp (Bil.EQ, zero64, Bil.Var rcx)));
                (3, fun t -> mk_jmp_to t (Bil.BinOp (Bil.NEQ, zero64, Bil.Var rcx))) ];
              [ def rdx (cell_load 8);
                def rdx (Bil.BinOp (Bil.MINUS, Bil.Var rdx, tls_load));
                def zf (Bil.BinOp (Bil.EQ, zero64, Bil.Var rdx)) ],
              [ (4, fun t -> mk_jmp_to t (Bil.Var zf));
                (5, fun t -> mk_jmp_to t one) ];
              [ def rdx (cell_load 8);
                def rdx (Bil.BinOp (Bil.MINUS, Bil.Var rdx, tls_load));
                def zf (Bil.BinOp (Bil.EQ, zero64, Bil.Var rdx)) ],
              [ (4, fun t -> mk_jmp_to t (Bil.Var zf));
                (5, fun t -> mk_jmp_to t one) ];
              [], [ (0, mk_ret) ];
              [], [] ]
        in
        (* The shared fail block: one phi entry per check block, the fail
           call. *)
        let phi =
          Phi.of_list (v64 "sc6_phi")
            [ (tids.(2), zero64); (tids.(3), one) ]
        in
        let fail_b = blk_of fixture tids.(5) in
        let bb = Blk.Builder.init ~copy_phis:true ~copy_defs:true fail_b in
        Blk.Builder.add_phi bb phi;
        Blk.Builder.add_jmp bb (fail_jmp ());
        let fail_b = Blk.Builder.result bb in
        let fixture =
          Term.map blk_t fixture ~f:(fun b ->
              if Tid.equal (Term.tid b) tids.(5) then fail_b else b)
        in
        let facts, fixture = fixture_facts_sub fixture in
        let prog = Program.create ~subs:[ fixture; stub ] () in
        let eq1 =
          Base.List.find_exn (jmps_of fixture tids.(2)) ~f:(fun j ->
              match Jmp.kind j with
              | Goto (Direct t) -> Tid.equal t tids.(4)
              | _ -> false)
        in
        let eq2 =
          Base.List.find_exn (jmps_of fixture tids.(3)) ~f:(fun j ->
              match Jmp.kind j with
              | Goto (Direct t) -> Tid.equal t tids.(4)
              | _ -> false)
        in
        let stripped = strip ~facts prog fixture in
        check "SC-06"
          ((not (has_block stripped tids.(5)))
          && Option.is_some
               (Base.Option.filter (jmp_of stripped (Term.tid eq1)) ~f:cond_is_true)
          && Option.is_some
               (Base.Option.filter (jmp_of stripped (Term.tid eq2)) ~f:cond_is_true)
          && has_block stripped tids.(4)
          && not (has_def stripped (Term.tid (nth_def fixture tids.(2) 0)))
          && not (has_def stripped (Term.tid (nth_def fixture tids.(3) 0)))));
  ]

let () = run "strip_canaries" tests
