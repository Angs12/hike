(* T15 Q1 design check: does [Tid.for_addr] intern to the same label
   object as the primary lift when minted in the file's own package?
   This settles whether the address->sub map compensates for a package
   mismatch or for a genuine ownership fact.  Throwaway measurement. *)

open Bap.Std
open Bap_core_theory
module Kb = Bap_core_theory.KB
open Probe_common

let eval (type a) (k : a Kb.t) : a =
  let v : a Toplevel.var = Toplevel.var "t15-pkg" in
  Toplevel.put v k;
  Toplevel.get v

let () =
  init ();
  (match Array.to_list Sys.argv with
   | _ :: path :: _ -> (
     let proj = load_project path in
     let prog = Project.program proj in
     let file =
       match
         Term.enum sub_t prog
         |> Seq.filter_map ~f:(fun s -> Term.get_attr s filename)
         |> Seq.hd
       with
       | Some f -> f
       | None -> "(none)"
     in
     let pkg = eval Kb.Symbol.package in
     Printf.printf "path=%s\nfile=%s\ncurrent-package=%s\n" path file pkg;
     match Term.enum sub_t prog |> Seq.hd with
     | None -> Printf.printf "no subs\n%!"
     | Some sub -> (
       Printf.printf "sub tid=%s name=%s\n" (Tid.name (Term.tid sub))
         (Sub.name sub);
       match Term.first blk_t sub with
       | None -> Printf.printf "no blocks\n%!"
       | Some b -> (
         let tid = Term.tid b in
         match Term.get_attr b address with
         | None -> Printf.printf "no address\n%!"
         | Some a ->
           let ambient = Tid.for_addr a in
           let in_file = Tid.for_addr ~package:file a in
           Printf.printf "blk tid=%s addr=%s\n" (Tid.name tid)
             (Word.to_string a);
           Printf.printf "  ambient tid=%s eq=%b\n" (Tid.name ambient)
             (Tid.equal ambient tid);
           Printf.printf "  ~file   tid=%s eq=%b\n" (Tid.name in_file)
             (Tid.equal in_file tid))))
   | _ -> Printf.printf "usage: t15_pkg <binary>\n%!");
  flush stdout
