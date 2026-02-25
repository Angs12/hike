module Solver = Z3.Solver
module Model = Z3.Model
open Monads.Std.Monad.Reader

let push solver =
  Solver.push solver;
  return solver

let pop solver ~times =
  Solver.pop solver times;
  return solver

let reset solver =
  Solver.reset solver;
  return solver

let add_assertions ~assertions solver : (Z3.Solver.solver, Z3.context) reader =
  let* assertions = all assertions in
  Solver.add solver assertions;
  return solver

let create_solver =
  let* ctx = read () in
  return (Solver.mk_solver ctx None)

let satisfiable ~l solver =
  let* l = all l in
  let status = Solver.string_of_status (Solver.check solver l) in
  if status = "satisfiable" then return true else return false

let print_check ~l solver : (Z3.Solver.solver, Z3.context) reader =
  let* l = all l in
  Stdio.printf "%s\n" (Solver.string_of_status (Solver.check solver l));
  return solver

let add_and_track_l solver ~constrains ~trackers =
  let* constrains = all constrains in
  let* trackers = all trackers in
  Solver.assert_and_track_l solver constrains trackers;
  return solver

let add_and_track solver ~constrain ~tracker =
  let* constrain = constrain in
  let* tracker = tracker in
  Solver.assert_and_track solver constrain tracker;
  return solver

let print_model solver : (Z3.Solver.solver, Z3.context) reader =
  match Solver.get_model solver with
  | Some m ->
      Stdio.printf "%s\n" (Model.to_string m);
      return solver
  | None ->
      Stdio.printf "no model\n";
      return solver

let print_proof solver : (Z3.Solver.solver, Z3.context) reader =
  try
    match Solver.get_proof solver with
    | Some p ->
        Stdio.printf "%s\n" (Z3.Expr.to_string p);
        return solver
    | None ->
        Stdio.printf "no proof\n";
        return solver
  with _ ->
    Stdio.printf "no proof\n";
    return solver

let print_unsat_core solver =
  Base.List.iter (Solver.get_unsat_core solver) ~f:(fun a ->
      Stdio.printf "%s\n" (Z3.Expr.to_string a));
  (* only p *)
  return solver

let simplify params expr = !$$Z3.Expr.simplify expr params

let check assertions =
  create_solver >>= add_assertions ~assertions >>= print_check ~l:[] >>| ignore

let solve assertions =
  create_solver >>= add_assertions ~assertions >>= print_check ~l:[]
  >>= print_model >>= print_proof >>| ignore

let prove assertions =
  create_solver >>= add_assertions ~assertions >>= print_check ~l:[]
  >>= print_model >>| ignore

let is_sat assertions =
  create_solver >>= add_assertions ~assertions >>= satisfiable ~l:[]

let create_params =
  let* ctx = read () in
  return @@ Some (Z3.Params.mk_params ctx)

let set_param_bool params name flag =
  let* ctx = read () in
  let param_sym = Z3.Symbol.mk_string ctx name in
  let* params = params in
  return
  @@ Option.bind params (fun params ->
         Some (Z3.Params.add_bool params param_sym flag))
