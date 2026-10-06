open Bap.Std
module Synth = Hike_synth
module KB = Bap_knowledge.Knowledge

(* The one reader of the lifter's rip tag.  The pass rewrites every
   tagged def's classified address literals into synthetic module
   addresses; the access rewrite itself belongs to Hike_synth, which
   turns every Load/Store into its storage form. *)

let prepare_program ~addr_bits ~is_address program =
#ifdef VSA_DEBUG
  let resolved = ref false in
#endif
  let addresses =
    object (self)
      inherit Exp.mapper
      method! map_int w =
        match Word.to_int64 w with
        | Ok a when Word.bitwidth w = addr_bits && is_address a ->
#ifdef VSA_DEBUG
          resolved := true;
#endif
          Bil.Var (Synth.module_addr ~addr_bits a)
        | _ -> Bil.Int w
      (* A store's data is not an address: only the address operand
         takes the synthetic form. *)
      method! map_store ~mem ~addr ~exp endian size =
        Bil.Store (mem, self#map_exp addr, exp, endian, size)
    end
  in
  (object
     inherit Term.mapper
     method! map_def d =
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
   end)#run program

(* The finalized component layout exists after attribution.  Named
   accesses take their storage's byte offset; a generic access keeps its
   runtime address value. *)
let bind_program ~addr_bits ~synth ~regions ~slots ~named_only program =
  (object
     inherit Term.mapper
     method! map_def d =
       Hike_synth_addr.rewrite_def ~addr_bits synth ~regions ~slots ~named_only d
   end)#run program

let resolve ~addr_bits ~is_address ~named_only ~slots ~layout program =
  let program = prepare_program ~addr_bits ~is_address program in
  let synth = Synth.empty in
  let program, regions, result = layout ~synth program in
  (bind_program ~addr_bits ~synth ~regions ~slots ~named_only program, result)

let resolve_with_layout ~addr_bits ~is_address ~slots ~layout program =
  resolve ~addr_bits ~is_address ~named_only:true ~slots ~layout program

let resolve_program ?(slots = []) ~addr_bits ~is_address ~regions program =
  fst
    (resolve ~addr_bits ~is_address ~named_only:false ~slots
       ~layout:(fun ~synth:_ program -> (program, regions, ()))
       program)
