(* Pipeline BIR dump: prints a sub's blocks after chosen pass stages.
   Usage: bir_dump.exe <binary> <subname> <stage>  (stage: fp|split|ssa) *)

open Bap.Std
open Probe_common

let () =
  let args = List.tl (Array.to_list Sys.argv) in
  init ();
  match args with
  | [ path; "subs"; _ ] ->
    let proj = load_project path in
    Term.enum sub_t (production_input proj)
    |> Seq.iter ~f:(fun s ->
           let entry_addr =
             match Option.map fst (Term.enum blk_t s |> Seq.next) with
             | Some b -> (
               match Term.get_attr b address with
               | Some a -> (
                 match Addr.to_int64 a with
                 | Ok v -> v
                 | Error _ -> 0L)
               | None -> 0L)
             | None -> 0L
           in
           Printf.printf "sub %s entry-blk=%Lx\n" (Sub.name s) entry_addr);
    exit 0
  | [ path; "extrefs"; _ ] ->
    let proj = load_project path in
    List.iter (fun (a, n) -> Printf.printf "ext %Lx %s\n" a n)
      (Hike.Image.external_references proj);
    exit 0
  | [ path; "images"; _ ] ->
    let proj = load_project path in
    List.iter
      (fun (img : Cbat_vsa.section_image) ->
        Printf.printf "img %Lx..%Lx len=%d slots=%d bytes=%s\n"
          img.Cbat_vsa.img_lo img.Cbat_vsa.img_hi
          (Bytes.length img.Cbat_vsa.img_bytes)
          (Core.Set.length img.Cbat_vsa.img_slots)
          (if Bytes.length img.Cbat_vsa.img_bytes <= 8 then
             String.concat ""
               (List.init (Bytes.length img.Cbat_vsa.img_bytes) (fun i ->
                    Printf.sprintf "%02x"
                      (Char.code (Bytes.get img.Cbat_vsa.img_bytes i))))
           else "..."))
      (section_images proj);
    exit 0
  | [ path; "relvals"; _ ] ->
    let proj = load_project path in
    Printf.printf "bias=%Ld\n" (Hike.Image.get_bias proj);
    List.iter (fun (s, a) -> Printf.printf "rel %Lx -> %Lx\n" s a)
      (Hike.Image.relative_values proj ~bias:(Hike.Image.get_bias proj));
    ignore (find_sub (production_input proj) "main");
    exit 0
  | [ path; name; stage ] ->
    let proj = load_project path in
    let prog = production_input proj in
    let target = Project.target proj in
    let prog = Hike.Fp.run_program prog in
    let prog =
      match stage with
      | "fp" -> prog
      | _ ->
        (* the vsa/attribution stages run inside the plugin; the caller
           wants post-split/ssa shapes, which need the full solve *)
        failwith "stage needs the full pipeline; use fp"
    in
    (match find_sub prog name with
     | Some sub ->
       Term.enum blk_t sub
       |> Seq.iter ~f:(fun b ->
             Printf.printf "== blk %s ==\n%s" (Tid.name (Term.tid b))
               (blk_bil_to_string b))
     | None -> Printf.printf "sub %s not found\n" name);
    ignore target
  | _ -> usage Sys.argv.(0) "<binary> <subname> fp"
