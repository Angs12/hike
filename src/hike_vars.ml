(* Var-id pass: one int per variable, assigned in BIR order for the whole
   program; the environments key by that id.  Runs after the filter. *)

open Bap.Std

let intern_var (v : var) : unit = ignore (Cbat_var_id.intern v)
let intern_vars (vs : Var.Set.t) : unit = Core.Set.iter vs ~f:intern_var

(* The visitor walks every term once; the lhs and the free variables are
   the whole variable universe the analysis can meet. *)
class intern_visitor = object
  inherit [unit] Term.visitor
  method! enter_arg a () = intern_var (Arg.lhs a)
  method! enter_def d () =
    intern_var (Def.lhs d);
    intern_vars (Def.free_vars d)
  method! enter_phi p () =
    intern_var (Phi.lhs p);
    intern_vars (Phi.free_vars p)
  method! enter_jmp j () = intern_vars (Jmp.free_vars j)
end

let intern_abi target : unit =
  let abi = Hike_abi.of_target target in
  Base.List.iter (Hike_abi.param_regs abi) ~f:intern_var;
  Base.List.iter abi.Hike_abi.return_regs ~f:intern_var;
  Base.List.iter abi.Hike_abi.callee_saved ~f:intern_var;
  intern_var (Hike_abi.sp target)

let run (proj : project) : project =
  Cbat_var_id.reset ();
  intern_abi (Project.target proj);
  ignore ((new intern_visitor)#run (Project.program proj) ());
  proj
