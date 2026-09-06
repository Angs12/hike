(* Scratch probe: why is the va_arg deref (mem[RAX] with RAX = the stored
   overflow_arg_area pointer) not tagged by today's VSA?
   Usage: vsa_ptr_diag.exe <binary> <subname>
   Follows audit02's loading shell; scratch-only (never installed). *)

open Bap.Std
open Bap_core_theory
open Probe_common

module AI = Cbat_vsa.AI
module Mem = Cbat_vsa.Mem
module Vsa = Cbat_vsa
module Ws = Cbat_clp_set_composite

let ws_str (w : Ws.t) : string =
  if Ws.is_top w then "TOP"
  else if Ws.is_bottom w then "BOTTOM"
  else
    let lo = match Ws.min_elem w with Some m -> Word.to_string m | None -> "?" in
    let hi = match Ws.max_elem w with Some m -> Word.to_string m | None -> "?" in
    if Ws.is_infinite w then Printf.sprintf "{%s..%s}^inf" lo hi
    else Printf.sprintf "{%s..%s}" lo hi

let exp_str (e : Bil.exp) : string = Format.asprintf "%a" Exp.pp e

(* Replica of the exported-neighborhood channel-2 test (is_seed is internal). *)
let neighborhood : int64 * int64 = (-65536L, 65536L)

let channel2_ok (ws : Ws.t) : bool =
  if Ws.is_top ws then false
  else if Ws.is_bottom ws then true
  else if Ws.is_infinite ws then false
  else
    match Ws.min_elem ws, Ws.max_elem ws with
    | Some lo, Some hi -> (
        match Word.to_int64 lo, Word.to_int64 hi with
        | Ok lo, Ok hi ->
            let nlo, nhi = neighborhood in
            Stdlib.Int64.compare lo nlo >= 0 && Stdlib.Int64.compare hi nhi <= 0
        | _ -> false)
    | _ -> false

let audit (sp : var) (target : Theory.Target.t) (sub : sub term) : unit =
  let prog' = Program.create ~subs:[ sub ] () in
  let sol = Vsa.static_graph_vsa [] prog' sub (Vsa.init_sol sub) in
  let info = Hike.Vsa.offsets_of_sub target sp sub in
  Printf.printf "sub %s: prod tags=%d\n"
    (Sub.name sub) (Core.Map.length info.Hike.Convutils.offsets);
  Term.enum blk_t sub
  |> Seq.iter ~f:(fun blk ->
      let st0 = Graphlib.Std.Solution.get sol (Term.tid blk) in
      let defs = Term.enum def_t blk |> Seq.to_list in
      ignore
        (Base.List.fold_left defs ~init:st0 ~f:(fun st d ->
             let st_before = st in
             let st = Vsa.denote_def d st in
             (match Vsa.Cbat_extraction.stack_address_of_rhs (Def.rhs d) with
              | Some addr ->
                  let frame = Vsa.frame_of_state st_before in
                  let addr' = Vsa.rewrite_addr frame addr in
                  let rewritten = not (Exp.equal addr addr') in
                  let ws =
                    match Vsa.denote_imm_exp addr' st_before with
                    | Ok w -> w
                    | Error _ -> Ws.top 64 in
                  let ws_s = ws_str ws in
                  (* Channel 1 proxy: rewrite_addr resolves the address's
                     frame-tracked base (a var-only address rewriting to an
                     offset expression means its base was frame-derived). *)
                  let ch1 = rewritten in
                  (* Channel 2: the denoted addr is bounded, finite, in-neighborhood. *)
                  let ch2 = channel2_ok ws in
                  let tag =
                    match Core.Map.find info.Hike.Convutils.offsets (Term.tid d) with
                    | Some k -> Probe_common.vsa_kind_to_string k
                    | None -> "(untagged)" in
                  (* The loaded-pointer lane: the deref's base var's value set. *)
                  let base_lane =
                    match Def.rhs d with
                    | Bil.Load (_, Bil.Var v, _, _)
                    | Bil.Store (_, Bil.Var v, _, _, _) ->
                        Some
                          (Printf.sprintf " base[%s]=%s"
                             (Var.name v)
                             (ws_str (AI.find_word 64 st_before v)))
                    | _ -> None in
                  Printf.printf
                    "  DEF %s: %-66s\n    addr=%s rewritten=%b ch1=%b ch2=%b(%s) tag=%s%s\n"
                    (Tid.to_string (Term.tid d))
                    (String.sub (exp_str (Def.rhs d)) 0
                       (Base.Int.min 64 (String.length (exp_str (Def.rhs d)))))
                    (exp_str addr) rewritten ch1 ch2 ws_s tag
                    (Base.Option.value ~default:"" base_lane);
                  st
              | _ -> st))))

let () =
  match Sys.argv with
  | [| _; bin; name |] ->
      Probe_common.init ();
      let proj = Probe_common.load_project bin in
      let prog = Project.program proj in
      let sp = Probe_common.sp_of proj in
      let target = Project.target proj in
      (match Probe_common.find_sub prog name with
       | Some sub -> audit sp target sub
       | None ->
           Printf.eprintf "sub %s not found\n" name;
           exit 1)
  | _ ->
      Printf.eprintf "usage: vsa_ptr_diag.exe <binary> <subname>\n";
      exit 2
