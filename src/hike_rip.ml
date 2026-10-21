open Bap.Std
module Synth = Hike_synth
module KB = Bap_knowledge.Knowledge

(* The one reader of the lifter's rip tag, run at the analysis entry:
   every tagged def's module-address literals become synthetic module
   addresses, which the VSA denotes with their [Rip] anchor.  The later
   storage bind turns every Load/Store into its storage form. *)

let prepare_def ~resolved addresses d =
  if not (KB.Value.get rip_relative_addr (Def.value d)) then d
  else begin
#ifdef VSA_DEBUG
    resolved := false;
#endif
    let d = Def.map_exp d ~f:addresses#map_exp in
#ifdef VSA_DEBUG
    Cbat_vsa.Cbat_kb_census.bump "rip.resolved.def";
    Cbat_vsa.Cbat_kb_census.bump
      (if not !resolved then "rip.resolved.unclassified"
       else if Option.is_some (Hike_stack_model.mem_node_of (Def.rhs d))
       then "rip.resolved.access" else "rip.resolved.value");
#endif
    d
  end

let prepare_block ~(synth : Hike_synth.table ref) ~addr_bits ~is_address
    (blk : blk term) : blk term =
  let resolved = ref false in
  let addresses =
    object (self)
      inherit Exp.mapper
      method! map_int w =
        match Word.to_int64 w with
        | Ok a when Word.bitwidth w = addr_bits && is_address a ->
#ifdef VSA_DEBUG
          resolved := true;
#endif
          Bil.Var (Synth.record synth (Synth.mint_module_addr ~addr_bits a))
        | _ -> Bil.Int w
      (* Only the address operand takes the synthetic form: a store's
         data is not an address, and its memory operand is the lifted
         memory-state var, never a tagged RIP expression. *)
      method! map_store ~mem ~addr ~exp endian size =
        Bil.Store (mem, self#map_exp addr, exp, endian, size)
    end
  in
  Term.map def_t blk
    ~f:(prepare_def ~resolved addresses)

let prepare_program ~synth ~addr_bits ~is_address program =
  let cell = ref synth in
  let program =
    Term.map sub_t program ~f:(fun sub ->
        Term.map blk_t sub
          ~f:(prepare_block ~synth:cell ~addr_bits ~is_address))
  in
  (!cell, program)

(* The finalized component layout exists after attribution.  Named
   accesses take their storage's byte offset; a generic access keeps its
   runtime address value. *)
let bind_program ~addr_bits ~synth ~regions ~slots ~named_only program =
  let cell = ref synth in
  let program =
    let bind =
      object
        inherit Term.mapper
        method! map_def d =
          Hike_synth_addr.rewrite_def ~addr_bits ~synth:cell ~regions ~slots
            ~named_only d
      end
    in
    Term.map sub_t program ~f:bind#map_sub
  in
  (!cell, program)

let resolve ~addr_bits ~named_only ~slots ~synth ~layout program =
  let program, regions, synth, result = layout ~synth program in
  let synth, program =
    bind_program ~addr_bits ~synth ~regions ~slots ~named_only program in
  (program, synth, result)

let resolve_with_layout ~addr_bits ~slots ~synth ~layout program =
  resolve ~addr_bits ~named_only:true ~slots ~synth ~layout program

let resolve_program ?(slots = []) ~addr_bits ~synth ~regions program =
  let program, synth, () =
    resolve ~addr_bits ~named_only:false ~slots ~synth
      ~layout:(fun ~synth program -> (program, regions, synth, ()))
      program
  in
  (synth, program)
