(* Stack-arg promotion pins: the promotion-fact derivation through the REAL
   fixpoint ([Hike.Vsa.fixpoint] / [fixture_ctx]), the promotion as a BIR
   rewrite ([Hike.Promote.promote_sub] / [rewrite_program]), and the
   promotion's emitted shape.  One Alcotest group per pin; each pin builds
   its own fixture, so no state crosses pins. *)

open Bap.Std
open Bap_core_theory
open Hike_test.Harness
open Hike_test.Common
open Hike_test.Fixtures

(* [sp + off] — the caller-window address shape (entry RSP = segment base,
   so the BIL offset IS the SysV slot space). *)
let plus_addr sp (off : int64) : exp =
  Bil.BinOp (Bil.PLUS, Bil.Var sp, Bil.Int (Cbat_word.to_word (w64 (Int64.to_int off))))

(* The fixture stamps the producer's facts onto the terms, then runs the
   promotion as a BIR rewrite — what the pipeline's vsa pass does. *)
let stamp (facts : Hike.Promote.facts) (sub : sub term) : sub term =
  let sub =
    Ds.stamp_dyn_allocs
      ~dynamic_alloc_tids:(Hike.Sections.dynamic_alloc_tids_of ~facts:top_facts sub) sub
  in
  Hike.Promote.promote_sub ~addr_bits:64 facts sub

(* Family 8: stack-arg promotion emission.  A promoted callee (two proven
   slots) and two callers — one resolved indirect site with the outgoing
   stores the slots feed, one unresolvable.  Returns the callee and the
   emitted IR for each caller. *)
(* Computed once: every pin reads the same emitted IR, nothing
   mutates the fixture. *)
let t4_fixture_ref = Lazy.from_fun (fun () ->
let t4_fixture () : sub term * string * string =
  let m = memv "prom_m" in
  let rsp = v64 "RSP" in
  let slot0 = ivar64 "hike_slot0" in
  let slot1 = ivar64 "hike_slot1" in
  let acc = v64 "prom_acc" in
  let rdi = v64 "RDI" in
  let rsi = v64 "RSI" in
  let ld0 =
    Def.create (v64 "prom_ld0")
      (Bil.Load (Bil.Var m, Bil.Var slot0, LittleEndian, `r64))
  in
  let callee, _ =
    sub_of "prom_callee"
      [ [ ld0;
          Def.create acc
            (Bil.BinOp (Bil.PLUS, Bil.Var rdi,
                        Bil.BinOp (Bil.PLUS, Bil.Var rsi,
                                   Bil.BinOp (Bil.PLUS, Bil.Var slot0, Bil.Var slot1)))) ],
        [ (1, mk_goto) ];
        [], [ (0, mk_ret) ] ]
  in
  let store1 =
    Def.create m
      (Bil.Store
         ( Bil.Var m,
           Bil.BinOp (Bil.MINUS, Bil.Var rsp, Bil.Int (Cbat_word.to_word (w64 24))),
           Bil.Int (Cbat_word.to_word (w64 7)),
           LittleEndian,
           `r64 ))
  in
  let store2 =
    Def.create m
      (Bil.Store
         ( Bil.Var m,
           Bil.BinOp (Bil.MINUS, Bil.Var rsp, Bil.Int (Cbat_word.to_word (w64 32))),
           Bil.Int (Cbat_word.to_word (w64 9)),
           LittleEndian,
           `r64 ))
  in
  let caller, _ =
    sub_of "prom_caller"
      [ [ store1; store2 ],
        [ (1, fun t -> Jmp.create (Call (Call.create ~return:(Direct t) ~target:(Indirect (Bil.Var (v64 "prom_tptr"))) ()))) ];
        [], [ (0, mk_ret) ] ]
  in
  let j = sub_jmp caller 0 0 in
  let callee_facts : Hike.Promote.facts = mk_facts ~prom_arity:2 () in
  let caller_facts : Hike.Promote.facts =
    mk_facts
      ~prom_resolved:(Tid.Map.singleton (Term.tid j) (Some (Term.tid callee)))
      ()
  in
  let callee = stamp callee_facts callee in
  let caller = stamp caller_facts caller in
  let ir = emit_ir [ caller; callee ] in
  let caller2, _ =
    sub_of "prom_caller2"
      [ [],
        [ (1,
           fun t ->
             Jmp.create
               (Call (Call.create ~return:(Direct t) ~target:(Indirect (Bil.Var (v64 "prom_tptr2"))) ()))) ];
        [], [ (0, mk_ret) ] ]
  in
  let j2 = sub_jmp caller2 0 0 in
  let caller2_facts : Hike.Promote.facts =
    mk_facts ~prom_resolved:(Tid.Map.singleton (Term.tid j2) None) ()
  in
  let caller2 = stamp caller2_facts caller2 in
  let ir2 = emit_ir [ caller2; callee ] in
  (callee, ir, ir2)
in
t4_fixture ())

(* Every pin reads the one computed fixture. *)
let t4_fixture () = Lazy.force t4_fixture_ref

(* Family 9: the promotion as a BIR rewrite — the sub's structure is the
   emitter's only input. *)

(* The promoted callee with one proven incoming-slot read.  Returns the
   original sub and its rewrite. *)
let t10_find_def sub' dtid =
  Term.enum blk_t sub'
  |> Seq.find_map ~f:(fun b ->
         Base.List.find_map
           (Term.enum def_t b |> Seq.to_list)
           ~f:(fun d -> if Tid.equal (Term.tid d) dtid then Some d else None))

(* The caller side: the site's store gains its call-arg def right after it
   (found through the chain replica's rewrite).  Returns the storing def
   and the bound call-arg def, when present. *)
let pr_a4_sub () : sub term =
  let m = memv "pr_m" in
  let a4_t = v64 "pr_a4_t" in
  let a4_st =
    Def.create m
      (Bil.Store
         ( Bil.Var m, plus_addr sp 8L, Bil.Int (Cbat_word.to_word (w64 5)),
           LittleEndian, `r64 ))
  in
  let a4_ld = Def.create a4_t (Bil.Load (Bil.Var m, plus_addr sp 8L, LittleEndian, `r64)) in
  let a4_ld1 =
    Def.create (v64 "pr_a4_t1")
      (Bil.Load (Bil.Var m, plus_addr sp 16L, LittleEndian, `r64))
  in
  let a4 = straight_sub "pr_a4_storing" [ a4_st; a4_ld; a4_ld1 ] in
  a4

(* The A4 sub's storage over [sec; lo, hi], read through its tree. *)
let pr_a4_storage (a4 : sub term) (sec : Hike.Stack_model.sec) (lo : int64) (hi : int64) :
    Hike.Sections.storage option =
  let ctx = fixture_ctx [ a4 ] in
  Base.Option.bind (Core.Map.find ctx.Hike.Sections.sub_trees (Term.tid a4))
    ~f:(fun tree ->
      Base.Option.map
        (Hike.Sections.storage_of_range tree (Hike.Sections.range sec lo hi))
        ~f:(fun rs -> rs.Hike.Sections.storage))

(* The A6 caller: two stores at [RSP+16] then an indirect call.  Returns the
   sub, its entry block, the call jmp, and the second (last) store def. *)
let pr_a6_sub () : sub term * blk term * jmp term * def term =
  let m = memv "pr_m" in
  let a6_st1 =
    Def.create m
      (Bil.Store
         ( Bil.Var m, plus_addr sp 16L, Bil.Int (Cbat_word.to_word (w64 7)),
           LittleEndian, `r64 ))
  in
  let a6_st2 =
    Def.create m
      (Bil.Store
         ( Bil.Var m, plus_addr sp 16L, Bil.Int (Cbat_word.to_word (w64 9)),
           LittleEndian, `r64 ))
  in
  let a6, _ =
    sub_of "pr_a6_caller"
      [ [ a6_st1; a6_st2 ],
        [ (1,
           fun t ->
             Jmp.create
               (Call (Call.create ~return:(Direct t) ~target:(Indirect (Bil.Var (v64 "pr_a6_tptr"))) ()))) ];
        [], [ (2, mk_goto) ];
        [], [ (0, mk_ret) ] ]
  in
  let body = Base.List.hd_exn (Term.enum blk_t a6 |> Seq.to_list) in
  let j = sub_jmp a6 0 0 in
  (a6, body, j, a6_st2)

(* Family 10: the window class's stored-value channel.  The fixture is the
   va_start triangle: the middle sub takes six GP args (no incoming
   stack-arg read), produces the overflow pointer (RAX := RBP + 8) and
   stores it (mem[RBP-0xC0] := RAX) in one straight-line block. *)
let prwc_mk_defs () : def term * def term * def term * def term * def term * var list =
  let m = memv "prwc_m" in
  let rsp = v64 "RSP" in
  let rbp = v64 "RBP" in
  let rax = v64 "RAX" in
  let gp_args = Base.List.map ~f:v64 [ "RDI"; "RSI"; "RDX"; "RCX"; "R8"; "R9" ] in
  ( Def.create rbp (Bil.Var rsp),
    Def.create rax (Bil.Var (List.nth gp_args 0)),
    Def.create rax (Bil.BinOp (Bil.PLUS, Bil.Var rbp, Bil.Int (Cbat_word.to_word (w64 8)))),
    Def.create (v64 "prwc_t") (Bil.Var (List.nth gp_args 1)),
    Def.create m
      (Bil.Store
         ( Bil.Var m,
           Bil.BinOp (Bil.MINUS, Bil.Var rbp, Bil.Int (Cbat_word.to_word (w64 0xc0))),
           Bil.Var rax,
           LittleEndian,
           `r64 )),
    gp_args )


(* Family RW: the one address map — a below-entry frame whose carved
   regions and reloaded pointers route every address def to its
   storage's base + displacement. *)

(* The -O0 frame shape: push rbp; mov rbp, rsp; sub rsp, 16 — one local
   store/load pair at [RBP-16] and an indexed store at [RBP-16+i*8]. *)
let rw_frame () : sub term =
  let m = memv "rw_m" in
  let rsp = v64 "RSP" in
  let rbp = v64 "RBP" in
  let i = v64 "rw_i" in
  let push =
    Def.create m
      (Bil.Store
         ( Bil.Var m, Bil.Var rsp, Bil.Var rbp, LittleEndian, `r64 ))
  in
  let k8 = Cbat_word.to_word (w64 8) |> fun w -> Bil.Int w in
  let k16 = Cbat_word.to_word (w64 16) |> fun w -> Bil.Int w in
  let defs =
    [ Def.create rsp (Bil.BinOp (Bil.MINUS, Bil.Var rsp, k8));
      push;
      Def.create rbp (Bil.Var rsp);
      Def.create rsp (Bil.BinOp (Bil.MINUS, Bil.Var rsp, k16));
      Def.create i (Bil.Int (Cbat_word.to_word (w64 0)));
      Def.create m
        (Bil.Store
           ( Bil.Var m,
             Bil.BinOp (Bil.MINUS, Bil.Var rbp, k16),
             Bil.Int (Cbat_word.to_word (w64 42)),
             LittleEndian, `r64 ));
      Def.create (v64 "rw_t")
        (Bil.Load
           ( Bil.Var m,
             Bil.BinOp (Bil.MINUS, Bil.Var rbp, k16),
             LittleEndian, `r64 ));
      Def.create m
        (Bil.Store
           ( Bil.Var m,
             Bil.BinOp
               ( Bil.PLUS,
                 Bil.BinOp (Bil.MINUS, Bil.Var rbp, k16),
                 Bil.BinOp (Bil.TIMES, Bil.Var i, k8) ),
             Bil.Int (Cbat_word.to_word (w64 7)),
             LittleEndian, `r64 )) ]
  in
  rewrite_one (straight_sub "rw_frame" defs)

(* The saved-then-reloaded pointer: the address of the local is stored
   into a cell and the through-pointer store dereferences the reload —
   the escaped cell write-closes into the residue, and the reloaded
   base still routes to the storage's base + displacement. *)
let rw_reload () : sub term =
  let m = memv "rw_m" in
  let rsp = v64 "RSP" in
  let rbp = v64 "RBP" in
  let p = v64 "rw_p" in
  let push =
    Def.create m
      (Bil.Store
         ( Bil.Var m, Bil.Var rsp, Bil.Var rbp, LittleEndian, `r64 ))
  in
  let k8 = Cbat_word.to_word (w64 8) |> fun w -> Bil.Int w in
  let k24 = Cbat_word.to_word (w64 24) |> fun w -> Bil.Int w in
  let k40 = Cbat_word.to_word (w64 40) |> fun w -> Bil.Int w in
  let defs =
    [ Def.create rsp (Bil.BinOp (Bil.MINUS, Bil.Var rsp, k8));
      push;
      Def.create rbp (Bil.Var rsp);
      Def.create rsp (Bil.BinOp (Bil.MINUS, Bil.Var rsp, k40));
      Def.create m
        (Bil.Store
           ( Bil.Var m,
             Bil.BinOp (Bil.MINUS, Bil.Var rbp, k24),
             Bil.BinOp (Bil.MINUS, Bil.Var rbp, k40),
             LittleEndian, `r64 ));
      Def.create (v64 "rw_q")
        (Bil.BinOp (Bil.MINUS, Bil.Var rbp, k40));
      Def.create p
        (Bil.Load
           ( Bil.Var m,
             Bil.BinOp (Bil.MINUS, Bil.Var rbp, k24),
             LittleEndian, `r64 ));
      Def.create m
        (Bil.Store
           ( Bil.Var m, Bil.Var p, Bil.Int (Cbat_word.to_word (w64 7)),
             LittleEndian, `r64 )) ]
  in
  rewrite_one (straight_sub "rw_reload" defs)

(* The defs of [sub] whose address expression references [name]. *)
let rw_accesses_named (sub : sub term) (name : string) : def term list =
  Term.enum blk_t sub |> Seq.concat_map ~f:(Term.enum def_t)
  |> Seq.filter ~f:(fun d ->
         match Cu.addr_of_rhs (Def.rhs d) with
         | Some (a, _) ->
             Core.Set.exists (Exp.free_vars a) ~f:(fun v ->
                 String.equal (Var.name (Var.base v)) name)
         | None -> false)
  |> Seq.to_list


(* The caller-window fixture: a callee whose above-entry (Args) read
   crosses slot cells (write-closed, never an Arg_slot) and a pure
   window-value def. *)
let rw_window () : sub term =
  let m = memv "rw_m" in
  let rsp = v64 "RSP" in
  let rbp = v64 "RBP" in
  let push =
    Def.create m
      (Bil.Store (Bil.Var m, Bil.Var rsp, Bil.Var rbp, LittleEndian, `r64))
  in
  let k8 = Cbat_word.to_word (w64 8) |> fun w -> Bil.Int w in
  (* +20 off RBP is +12 above the entry: the 8-byte read crosses the
     slot cells, so the Args binding is write-closed (never a slot). *)
  let k20 = Cbat_word.to_word (w64 20) |> fun w -> Bil.Int w in
  let defs =
    [ Def.create rsp (Bil.BinOp (Bil.MINUS, Bil.Var rsp, k8));
      push;
      Def.create rbp (Bil.Var rsp);
      Def.create (v64 "rw_w")
        (Bil.BinOp (Bil.PLUS, Bil.Var rbp, k20));
      Def.create (v64 "rw_t")
        (Bil.Load
           ( Bil.Var m,
             Bil.BinOp (Bil.PLUS, Bil.Var rbp, k20),
             LittleEndian, `r64 )) ]
  in
  rewrite_one (straight_sub "rw_window" defs)


(* The VLA fixture: a runtime-sized decrement (a guarded size join)
   seeds the allocation; the post-decrement SP copy carries the Vla
   origin and takes the allocation's base var. *)
let rw_vla () : sub term =
  let rsp = v64 "RSP" in
  let rax = v64 "RAX" in
  let c = v1 "rw_c" in
  let k16 = Cbat_word.to_word (w64 16) |> fun w -> Bil.Int w in
  let k32 = Cbat_word.to_word (w64 32) |> fun w -> Bil.Int w in
  let defs =
    [ Def.create rax
        (Bil.Ite (Bil.Var c, k16, k32));
      Def.create rsp (Bil.BinOp (Bil.MINUS, Bil.Var rsp, Bil.Var rax));
      Def.create (v64 "rw_t") (Bil.Var rsp) ]
  in
  rewrite_one (straight_sub "rw_vla" defs)


(* The lifted va_list construction: the incoming GP parameter registers
   stored into the frame (the reg_save_area) beside a pointer at/above
   the entry args base (the overflow_arg_area).  [overflow:false] drops
   the second half, leaving the register spills alone. *)
let rw_variadic ~(overflow : bool) () : sub term =
  let m = memv "rw_va_m" in
  let rsp = v64 "RSP" in
  let ov = v64 "rw_va_ov" in
  let k n = Cbat_word.to_word (w64 n) |> fun w -> Bil.Int w in
  let store reg off =
    Def.create m
      (Bil.Store
         ( Bil.Var m,
           Bil.BinOp (Bil.MINUS, Bil.Var rsp, k off),
           Bil.Var reg, LittleEndian, `r64 ))
  in
  let regs =
    [ store (v64 "RSI") 0x28; store (v64 "RDX") 0x20;
      store (v64 "RCX") 0x18; store (v64 "R8") 0x10 ]
  in
  let overflow_defs =
    if overflow then
      [ Def.create ov (Bil.BinOp (Bil.PLUS, Bil.Var rsp, k 0x10));
        Def.create m
          (Bil.Store
             ( Bil.Var m,
               Bil.BinOp (Bil.MINUS, Bil.Var rsp, k 0x40),
               Bil.Var ov, LittleEndian, `r64 )) ]
    else
      (* A frame-pointer store alone is not the overflow area. *)
      let p = v64 "rw_va_p" in
      [ Def.create p (Bil.BinOp (Bil.MINUS, Bil.Var rsp, k 0x30));
        Def.create m
          (Bil.Store
             ( Bil.Var m,
               Bil.BinOp (Bil.MINUS, Bil.Var rsp, k 0x50),
               Bil.Var p, LittleEndian, `r64 )) ]
  in
  straight_sub "rw_variadic" (regs @ overflow_defs)


(* The section-constant fixture: a def whose value is a .rodata
   constant address; the span owns it, so the value takes the
   component's base var. *)
let rw_sec () : sub term =
  let m = memv "rw_m" in
  let sub0 =
    straight_sub "rw_sec"
      [ (* the constant address (a .rodata word) *)
        Def.create (v64 "rw_c")
          (Bil.Int (Cbat_word.to_word (Cbat_word.of_int64 ~width:64 0x1000L)));
        (* an access through it: carves the component the value names *)
        Def.create (v64 "rw_t")
          (Bil.Load (Bil.Var m, Bil.Var (v64 "rw_c"), LittleEndian, `r64)) ]
  in
  let spans =
    [ { Hike.Sections.ds_sec = Hike.Stack_model.Rodata;
        Hike.Sections.ds_lo = 0x1000L;
        Hike.Sections.ds_hi = 0x1010L;
        Hike.Sections.ds_slots = [] } ]
  in
  let facts, subs, _ = fixture_facts [ sub0 ] in
  let prog = Program.create ~subs () in
  let prog =
    Term.map sub_t prog ~f:(fun sub ->
        Hike.Def_slots.stamp_dyn_allocs
          ~dynamic_alloc_tids:(Hike.Sections.dynamic_alloc_tids_of ~facts sub)
          sub)
  in
  let ctx =
    Hike.Sections.attribute ~facts ~word:8 ~entry:Hike.Stack_model.segment_base
      ~spans prog
  in
  let prog = Term.map sub_t prog ~f:(Hike.Sections.stamp_tags ctx) in
  let prog =
    Hike.Promote.rewrite_program ~word:8 ~entry:Hike.Stack_model.segment_base
      ~facts ~spans ~ctx prog
  in
  Term.first sub_t prog |> Base.Option.value_exn

(* The A7 fixture: a callee whose above-entry reads span several word
   cells (slots 0 and 2, so the arity is 3 and the gap is real). *)
let pr_slot_callee () : sub term * def term * def term =
  let m = memv "pr_slot_m" in
  let rbp = v64 "RBP" in
  let d_rbp = Def.create rbp (Bil.Var sp) in
  let ld0 =
    Def.create (v64 "pr_slot_l0")
      (Bil.Load (Bil.Var m, plus_addr rbp 8L, LittleEndian, `r64))
  in
  let ld2 =
    Def.create (v64 "pr_slot_l2")
      (Bil.Load (Bil.Var m, plus_addr rbp 24L, LittleEndian, `r64))
  in
  (straight_sub "pr_slot_callee" [ d_rbp; ld0; ld2 ], ld0, ld2)

(* The slot a promoted access addresses, by the slot var's name. *)
let slot_of_addr (d : def term) : string option =
  match Def.rhs d with
  | Bil.Load (_, a, _, _) -> (
      match a with
      | Bil.Var v -> Some (Var.name v)
      | Bil.BinOp (Bil.PLUS, Bil.Var v, _) -> Some (Var.name v)
      | _ -> None)
  | _ -> None

let tests : unit Alcotest.test list =
  [
    (* PR-01: the promoted signature carries the register lanes then the
       positional slots. *)


    (* PR-02: the resolved site is a DIRECT call through the promoted
       signature; the unpassed slots stay undef. *)


    (* PR-03: the memory-convention twin is internal. *)


    (* PR-04: the twin's synthetic indirect convention carries the window
       base, never SP. *)
    pin "PR-04"
      "the twin carries the synthetic indirect convention (the window base, never SP)"
      (fun () ->
        let _, ir, _ = t4_fixture () in
        check_ir "PR-04"
          ("_hike_thunk\"(i64 %RDI, i64 %RSI, i64 %RDX, i64 %RCX, i64 %R8, "
          ^ "i64 %R9, i256 %YMM0, i256 %YMM1, i256 %YMM2, i256 %YMM3, "
          ^ "i256 %YMM4, i256 %YMM5, i256 %YMM6, i256 %YMM7, ptr %hike_window)")
          ir);

    (* PR-05: the twin unpacks the window slots into the promoted body. *)


    (* PR-06: the twin reads the slots through the window pointer. *)


    (* PR-07: the unresolved site takes the pointer call through the
       synthetic signature. *)


    (* PR-08: the pointer call never lands on the promoted body directly. *)
    pin "PR-08" "the pointer call never lands on the promoted body directly" (fun () ->
        let _, _, ir2 = t4_fixture () in
        check "PR-08" (not (contains_substring ir2 "call { i64, i64 } @prom_callee(")));

    (* PR-09: the synthetic indirect signature carries the window base. *)
    pin "PR-09" "the synthetic indirect signature carries the window base" (fun () ->
        let _, _, ir2 = t4_fixture () in
        check_ir "PR-09"
          "@indirect_call(i64, i64, i64, i64, i64, i64, i256, i256, i256, i256, \
           i256, i256, i256, i256, ptr)"
          ir2);

    (* PR-10: the sub gains its promoted parameter as a real BIR arg. *)


    (* PR-11: the sub keeps its tid through the arg-term rewrite. *)


    (* PR-12: an identity access keeps its tag through the stamp. *)
    pin "PR-12" "an identity access keeps its tag through the stamp" (fun () ->
        let keep_m = memv "t10_km" in
        let keep =
          Def.create (v64 "t10_keep")
            (Bil.Load
               ( Bil.Var keep_m,
                 Bil.BinOp
                   ( Bil.PLUS,
                     Bil.Var (v64 "RSP"),
                     Cbat_word.to_word (w64 8) |> fun w -> Bil.Int w ),
                 LittleEndian,
                 `r64 ))
        in
        let keep_st =
          Def.create keep_m
            (Bil.Store
               ( Bil.Var keep_m,
                 Bil.BinOp
                   ( Bil.PLUS,
                     Bil.Var (v64 "RSP"),
                     Cbat_word.to_word (w64 8) |> fun w -> Bil.Int w ),
                 Bil.Int (Cbat_word.to_word (w64 3)),
                 LittleEndian,
                 `r64 ))
        in
        let keep_sub0 = straight_sub "t10_keep" [ keep; keep_st ] in
        let keep_ctx = fixture_ctx [ keep_sub0 ] in
        let keep_sub = Hike.Sections.stamp_tags keep_ctx keep_sub0 in
        let keep' = Ds.stamp_dyn_allocs ~dynamic_alloc_tids:Tid.Set.empty keep_sub in
        let keep_def = Base.Option.value_exn (t10_find_def keep' (Term.tid keep)) in
        check "PR-12" (Ds.sec_tag keep_def <> None));

    (* PR-13: the call-arg def is bound right after the storing def. *)


    (* PR-14: the call-arg def reads the storing def's written bytes (7). *)


    (* PR-15: the proven incoming-slot read promotes — the read's cell is
       Arg_slot 0 in the finalized tree (arity 1, no window). *)


    (* PR-16: the return-address cell ([RSP+0] load) dies into the retaddr
       set — it never forces a window parameter. *)
    pin "PR-16" "the [RSP+0] read is the retaddr cell (the retaddr set)" (fun () ->
        let m = memv "pr_m" in
        let a2_ra = v64 "pr_a2_ra" in
        let a2_ld =
          Def.create a2_ra (Bil.Load (Bil.Var m, Bil.Var sp, LittleEndian, `r64))
        in
        let a2 = straight_sub "pr_a2_retaddr" [ a2_ld ] in
        let a2_retaddr =
          let sol =
            Cbat_vsa.static_graph_vsa
              ~abi:Hike_abi.x86_64_sysv
              ~resolved:Tid.Map.empty (Program.create ~subs:[ a2 ] ()) a2
              (Cbat_vsa.init_sol ~abi:Hike_abi.x86_64_sysv a2)
          in
          Hike.Cfg_complete.retaddr_defs ~abi:Hike.Abi.x86_64_sysv ~sol a2
        in
        check "PR-16" (Core.Set.mem a2_retaddr (Term.tid a2_ld)));

    (* PR-17: a written cell promotes too — the pointer convention carries
       the store (no value to reconstruct, no demotion). *)
    pin "PR-17" "a written slot promotes (the pointer convention carries the store)"
      (fun () ->
        let a4 = pr_a4_sub () in
        check "PR-17"
          (pr_a4_storage a4 Sm.Args (pos 8L) (pos 15L) = Some Hike.Sections.Arg_slot));

    (* PR-18: the slot index is the ACCESS's own cell — the neighbouring
       cell is its own slot, never the binding's low end. *)
    pin "PR-18"
      "the neighbouring cell is its own slot (the binding is never the unit)"
      (fun () ->
        let a4 = pr_a4_sub () in
        check "PR-18"
          (pr_a4_storage a4 Sm.Args (pos 16L) (pos 23L)
          = Some Hike.Sections.Arg_slot));

    (* PR-19: the site's outgoing stores map to SysV slots, last store wins. *)
    pin "PR-19" "the site's outgoing stores map to SysV slots, last store wins"
      (fun () ->
        let a6, body, _, a6_st2 = pr_a6_sub () in
        check "PR-19"
          (let fa6, a6 = fixture_facts_sub a6 in
           let bindings =
             Hike.Promote.site_bindings_of_sub ~word:8 ~abi:Hike.Abi.x86_64_sysv ~sp
               ~denote:fa6.denote a6
           in
           match Core.Map.find bindings (Term.tid body) with
           | Some [ b ] ->
               Base.Int.equal b.Hike.Promote.sb_slot 1
               && Tid.equal (Term.tid b.Hike.Promote.sb_def) (Term.tid a6_st2)
           | _ -> false));

    (* PR-20: the unresolvable indirect target records no resolution. *)
    pin "PR-20" "the unresolvable indirect target records no resolution (symtab-free)"
      (fun () ->
        let a6, _, j, _ = pr_a6_sub () in
        check "PR-20"
          (let fa6, a6 = fixture_facts_sub a6 in
           let resolved =
             Hike.Promote.call_resolution ~denote:fa6.denote
               ~lookup:(fun _ -> None) a6
           in
           Core.Map.find resolved (Term.tid j) = Some None));

    (* PR-21: a pure window-value sub binds no Args cell: the window value
       carries the caller's pointer, so no slot and no residue is
       claimed. *)
    pin "PR-21" "a pure window-value sub binds no Args cell (the value carries it)"
      (fun () ->
        let prologue, al, ptr, filler, store, gp_args = prwc_mk_defs () in
        let mid, _ =
          sub_of
            ~args:(Base.List.map gp_args ~f:(fun v -> Arg.create v (Bil.Var v)))
            "prwc_va_middle"
            [ [ prologue; al; ptr; filler; store ], [ (1, mk_goto) ];
              [], [ (0, mk_ret) ] ]
        in
        check "PR-21"
          (let ctx = fixture_ctx [ mid ] in
           match Core.Map.find ctx.Hike.Sections.sub_trees (Term.tid mid) with
           | None -> false
           | Some tree ->
               not
                 (Base.List.exists
                    (Hike.Sections.Tree.to_sequence tree |> Seq.to_list)
                    ~f:(fun (k, _) ->
                      match k.Hike.Sections.lo.Hike.Sections.p_sec with
                      | Sm.Args -> true
                      | _ -> false))));

    (* PR-22: the boundary-visible twin — the window value is produced in
       a previous block and is stamped (the emitter re-bases it to the
       window parameter at its use). *)
    pin "PR-22" "the twin's window-value def is stamped (the window lane serves it)"
      (fun () ->
        let prologue, al, ptr, _filler, store, _gp_args = prwc_mk_defs () in
        let twin, _ =
          sub_of "prwc_va_twin"
            [ [ prologue; al; ptr ], [ (1, mk_goto) ];
              [ store ], [ (0, mk_ret) ] ]
        in
        let twin' = rewrite_one twin in
        check "PR-22"
          (match t10_find_def twin' (Term.tid ptr) with
           | Some d -> Ds.def_is_window_value d
           | None -> false));

    (* PR-23: a region address def's value is its storage's base plus the
       folded displacement (zero here — the base itself). *)
    pin "PR-23" "a region address def's value is its storage base + displacement"
      (fun () ->
        let sub' = rw_frame () in
        let find v =
          Term.enum blk_t sub' |> Seq.concat_map ~f:(Term.enum def_t)
          |> Seq.find ~f:(fun d -> Var.equal (Var.base (Def.lhs d)) v)
        in
        let st42 =
          Term.enum blk_t sub' |> Seq.concat_map ~f:(Term.enum def_t)
          |> Seq.find ~f:(fun d ->
                 match Cu.store_data_of_rhs (Def.rhs d) with
                 | Some (Bil.Int w) ->
                     (match Cbat_word.to_int64 (Cbat_word.of_word w) with
                      | Ok k -> Stdlib.Int64.equal k 42L
                      | Error _ -> false)
                 | _ -> false)
        in
        check "PR-23"
          (match
             ( Base.Option.map (find (v64 "RBP")) ~f:Def.rhs,
               Base.Option.bind st42 ~f:(fun d ->
                   Base.Option.map (Cu.addr_of_rhs (Def.rhs d)) ~f:fst) )
           with
           | Some (Bil.Var pv), Some (Bil.Var av) ->
               Cu.region_ptr_id_of pv = Some 2
               && Cu.region_ptr_id_of av = Some 1
           | _ -> false));

    (* PR-24: the emitter lowers the rewritten address as the storage's
       own alloca (or one GEP) — never a re-derived offset. *)


    (* PR-26: the residue's accesses and values take the same base +
       displacement form as a region's — the escaped cell write-closes
       into the residue and the pure address def over it names it. *)
    pin "PR-26" "a residue access and value name the residue base"
      (fun () ->
        let sub' = rw_reload () in
        let through = rw_accesses_named sub' "rw_p" in
        let addr_ok a =
          match a with
          | Bil.Var b -> Cu.region_ptr_id_of b = Some 0
          | Bil.BinOp (Bil.PLUS, Bil.Var b, _) ->
              Cu.region_ptr_id_of b = Some 0
          | _ -> false
        in
        let q =
          Term.enum blk_t sub' |> Seq.concat_map ~f:(Term.enum def_t)
          |> Seq.find ~f:(fun d ->
                 String.equal (Var.name (Var.base (Def.lhs d))) "rw_q")
          |> Base.Option.map ~f:Def.rhs
          |> Base.Option.map ~f:(function
               | Bil.Var b -> Some b
               | Bil.BinOp (Bil.PLUS, Bil.Var b, _) -> Some b
               | _ -> None)
          |> Base.Option.join
        in
        check "PR-26"
          (Base.List.for_all through ~f:(fun d ->
               match Cu.addr_of_rhs (Def.rhs d) with
               | Some (a, _) -> addr_ok a
               | None -> false)
          && Base.Option.value_map q ~default:false
               ~f:(fun b -> Cu.region_ptr_id_of b = Some 0)));

    (* PR-25: a reloaded-base access routes to its proven storage — the
       through-pointer store's address is the storage base plus the
       displacement over the reloaded pointer's offset, never the raw
       lane. *)
    pin "PR-25" "a reloaded-base access routes to its storage base" (fun () ->
        let sub' = rw_reload () in
        let through = rw_accesses_named sub' "rw_p" in
        let addr_base a =
          match a with
          | Bil.Var b -> Some b
          | Bil.BinOp (Bil.PLUS, Bil.Var b, _) -> Some b
          | _ -> None
        in
        check "PR-25"
          (Base.List.for_all through ~f:(fun d ->
               match Cu.addr_of_rhs (Def.rhs d) with
               | Some (a, _) ->
                   Base.Option.value_map (addr_base a) ~default:false
                     ~f:Cu.is_region_ptr
               | None -> false)));

    (* PR-27: a window access's address is the window parameter plus the
       entry-relative displacement. *)
    pin "PR-27" "a window access address is hike_window plus off" (fun () ->
        let sub' = rw_window () in
        let win_addr =
          Term.enum blk_t sub' |> Seq.concat_map ~f:(Term.enum def_t)
          |> Seq.filter_map ~f:(fun d ->
                 Base.Option.map (Cu.addr_of_rhs (Def.rhs d)) ~f:fst)
          |> Seq.exists ~f:(fun a ->
                 match a with
                 | Bil.BinOp (Bil.PLUS, Bil.Var b, _) ->
                     Cu.is_window_var b
                 | Bil.Var b -> Cu.is_window_var b
                 | _ -> false)
        in
        check "PR-27" win_addr);

    (* PR-28: a window value def (at/above the args base) takes the
       window parameter as its base. *)
    pin "PR-28" "a window value def value is hike_window plus off" (fun () ->
        let sub' = rw_window () in
        let w =
          Term.enum blk_t sub' |> Seq.concat_map ~f:(Term.enum def_t)
          |> Seq.find ~f:(fun d ->
                 String.equal (Var.name (Var.base (Def.lhs d))) "rw_w")
          |> Base.Option.map ~f:Def.rhs
        in
        check "PR-28"
          (match w with
           | Some (Bil.BinOp (Bil.PLUS, Bil.Var b, _)) -> Cu.is_window_var b
           | Some (Bil.Var b) -> Cu.is_window_var b
           | _ -> false));

    (* PR-29: a VLA address def's value is the allocation's base var
       (the offsets are frame-relative — byte zero is the base). *)
    pin "PR-29" "a VLA address def's value is its allocation base" (fun () ->
        let sub' = rw_vla () in
        ignore (install_fixture_envs [ sub' ]);
        let t =
          Term.enum blk_t sub' |> Seq.concat_map ~f:(Term.enum def_t)
          |> Seq.find ~f:(fun d ->
                 String.equal (Var.name (Var.base (Def.lhs d))) "rw_t")
          |> Base.Option.map ~f:Def.rhs
        in
        check "PR-29"
          (match t with
           | Some (Bil.Var pv) -> Cu.is_vla_ptr pv
           | Some (Bil.BinOp (Bil.PLUS, Bil.Var pv, _)) ->
               Cu.is_vla_ptr pv
           | _ -> false));

    (* PR-30: a constant address def's value is its component's base var
       (the displacement folds to zero at the component's low bound). *)
    pin "PR-30" "a constant address def's value is its component base" (fun () ->
        let sub' = rw_sec () in
        let c =
          Term.enum blk_t sub' |> Seq.concat_map ~f:(Term.enum def_t)
          |> Seq.find ~f:(fun d ->
                 String.equal (Var.name (Var.base (Def.lhs d))) "rw_c")
          |> Base.Option.map ~f:Def.rhs
        in
        check "PR-30"
          (match c with
           | Some (Bil.Var pv) -> Cu.is_sec_comp_ptr pv
           | Some (Bil.BinOp (Bil.PLUS, Bil.Var pv, _)) ->
               Cu.is_sec_comp_ptr pv
           | _ -> false));

    (* PR-31: the per-word-cell split — each access is its own cell's slot,
       never the binding's low end (the design's single-index form would
       give both accesses slot 0). *)
    pin "PR-31"
      "the per-word-cell split: a two-cell Args binding promotes each cell to its own slot"
      (fun () ->
        let sub, ld0, ld2 = pr_slot_callee () in
        let sub' = rewrite_one sub in
        check "PR-31"
          (match (t10_find_def sub' (Term.tid ld0), t10_find_def sub' (Term.tid ld2)) with
           | Some d0, Some d2 ->
               slot_of_addr d0 = Some "hike_slot0"
               && slot_of_addr d2 = Some "hike_slot2"
           | _ -> false));

    (* PR-32: the pointer convention — a promoted access is a REAL
       load/store whose address is the slot pointer (the memory node is
       kept, no value reconstruction). *)
    pin "PR-32" "a promoted access keeps its memory node, addressed at the slot pointer"
      (fun () ->
        let sub, ld0, _ = pr_slot_callee () in
        let sub' = rewrite_one sub in
        check "PR-32"
          (match t10_find_def sub' (Term.tid ld0) with
           | Some d -> (
               match Def.rhs d with
               | Bil.Load (_, Bil.Var v, LittleEndian, `r64) -> Cu.is_arg_slot v
               | _ -> false)
           | None -> false));

    (* PR-33: the promoted slot parameter is Mem-typed (a pointer), so the
       signature and the body agree on the address. *)
    pin "PR-33" "the promoted slot parameter is a pointer (Mem-typed)" (fun () ->
        let sub, _, _ = pr_slot_callee () in
        let sub' = rewrite_one sub in
        let slots =
          Term.enum arg_t sub' |> Base.Sequence.to_list
          |> Base.List.filter ~f:(fun a -> Cu.is_arg_slot (Arg.lhs a))
        in
        check "PR-33"
          (Base.List.length slots = 3
          && Base.List.for_all slots ~f:(fun a -> Cu.is_mem (Arg.lhs a))
          && Base.List.exists slots ~f:(fun a ->
                 String.equal (Var.name (Arg.lhs a)) "hike_slot2")));

    (* PR-34: the caller binds the slot ADDRESS — the store's own address,
       already re-pointed at the caller's storage — never the stored
       value. *)
    pin "PR-34" "the caller binds the slot address (the store's own address)"
      (fun () ->
        let m = memv "pr_sc_m" in
        let rsp = v64 "RSP" in
        let frame =
          Def.create rsp
            (Bil.BinOp
               ( Bil.MINUS,
                 Bil.Var rsp,
                 Bil.Int (Cbat_word.to_word (w64 24)) ))
        in
        let st0 =
          Def.create m
            (Bil.Store
               ( Bil.Var m,
                 plus_addr rsp 8L,
                 Bil.Int (Cbat_word.to_word (w64 0x2A)),
                 LittleEndian,
                 `r64 ))
        in
        let sub, _ =
          sub_of "pr_slot_caller"
            [ [ frame; st0 ],
              [ (1,
                 fun t ->
                   Jmp.create
                     (Call
                        (Call.create ~return:(Direct t)
                           ~target:(Indirect (Bil.Var (v64 "pr_sc_tptr")))
                           ()))) ];
              [], [ (0, mk_ret) ] ]
        in
        let sub' = rewrite_one sub in
        let arg0 =
          Term.enum blk_t sub' |> Seq.concat_map ~f:(Term.enum def_t)
          |> Seq.find ~f:(fun d ->
                 String.equal (Var.name (Var.base (Def.lhs d))) "hike_arg0")
        in
        check "PR-34"
          (match arg0 with
           | Some d -> (
               match Def.rhs d with
               (* The bound value is an ADDRESS, never the stored 0x2A. *)
               | Bil.Int _ -> false
               | rhs -> not (Core.Set.is_empty (Exp.free_vars rhs)))
           | None -> false));

    (* PR-35: the emitted slot parameter is an LLVM pointer and the
       access loads through it — the address IS the parameter. *)
    pin "PR-35"
      "the emitted slot parameter is an LLVM pointer and the access loads through it"
      (fun () ->
        let sub, _, _ = pr_slot_callee () in
        let sub' = rewrite_one sub in
        let ir = emit_ir [ sub' ] in
        check_ir "PR-35" "ptr %hike_slot0" ir);

    (* PR-36: the twin forwards the window GEP'd at the slot — a pointer,
       never a loaded value. *)
    pin "PR-36" "the twin forwards the window slot pointer (no load)"
      (fun () ->
        let _, ir, _ = t4_fixture () in
        check_ir "PR-36"
          ("getelementptr i8, ptr %hike_window, i64 "
          ^ Int64.to_string (Cu.slot_offset ~word:8 0))
          ir);

    (* PR-37: the lifted va_list construction — the reg-save spills
       beside the above-entry overflow pointer — stamps the sub
       variadic, and the emitted definition is a real LLVM variadic. *)
    pin "PR-37" "the va_list construction stamps the sub variadic"
      (fun () ->
        let sub' = rewrite_one (rw_variadic ~overflow:true ()) in
        check "PR-37a" (Cu.is_variadic sub');
        check_ir "PR-37b" ", ...)" (emit_ir [ sub' ]));

    (* PR-38: the same registers spilled into the frame with no
       overflow pointer are not the va_list construction. *)
    pin "PR-38" "the register spills alone are not variadic" (fun () ->
        let sub' = rewrite_one (rw_variadic ~overflow:false ()) in
        check "PR-38" (not (Cu.is_variadic sub')))
  ]

let () = run "promote" tests
