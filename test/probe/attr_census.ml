(* Attribution census probe: per-sub fixpoint over the RAW subs (the
   audit02 population), classifying every top address by the mechanism
   that produced it and every word def by its precision bucket / band
   shape.  Prints `key=count` lines.
   Usage: attr_census.exe <binary> [<binary> ...]
   HIKE_ATTR_VERBOSE=1 adds per-address detail. *)

open Bap.Std
open Probe_common

module Vsa = Cbat_vsa
module AI = Vsa.AI
module Ws = Cbat_clp_set_composite
module Ext = Vsa.Cbat_extraction

module VarMap = Core.Map.Make (Var)

(* Current-sub base-var mechanism shadow: a top var's root cause, set at
   its def and read by the uses that follow. *)
let shadow : string VarMap.t ref = ref VarMap.empty

let verbose : bool =
  match Sys.getenv_opt "HIKE_ATTR_VERBOSE" with Some "1" -> true | _ -> false

let counts : (string, int) Core.Hashtbl.t =
  Core.Hashtbl.create (module Core.String)

let bump (key : string) : unit =
  let n = Core.Hashtbl.find counts key |> Core.Option.value ~default:0 in
  Core.Hashtbl.set counts ~key ~data:(n + 1)

let denote (e : exp) (env : AI.t) : Ws.t option =
  match Vsa.Test_seam.denote_imm_exp e env with Ok v -> Some v | Error _ -> None

let shape_retained (v : Ws.t) : bool = Core.Option.is_some (Ws.stack_offsets v)

let is_stack (v : Ws.t) : bool =
  shape_retained v || Ws.in_stack_segment v

let op_name : Bil.binop -> string = function
  | Bil.TIMES -> "mul"
  | Bil.DIVIDE -> "div"
  | Bil.SDIVIDE -> "sdiv"
  | Bil.MOD -> "mod"
  | Bil.SMOD -> "smod"
  | Bil.LSHIFT -> "lshift"
  | Bil.RSHIFT -> "rshift"
  | Bil.ARSHIFT -> "arshift"
  | Bil.AND -> "and"
  | Bil.OR -> "or"
  | Bil.XOR -> "xor"
  | Bil.PLUS -> "add"
  | Bil.MINUS -> "sub"
  | Bil.EQ -> "eq"
  | Bil.NEQ -> "neq"
  | Bil.LT -> "lt"
  | Bil.LE -> "le"
  | Bil.SLT -> "slt"
  | Bil.SLE -> "sle"

let blind_op : Bil.binop -> bool = function
  | Bil.TIMES | Bil.DIVIDE | Bil.SDIVIDE | Bil.MOD | Bil.SMOD
  | Bil.LSHIFT | Bil.RSHIFT | Bil.ARSHIFT
  | Bil.AND | Bil.OR | Bil.XOR -> true
  | _ -> false

(* The root mechanism of a top expression: the innermost bit-reading op
   on a stack operand, the memory root, or a shadowed var's cause. *)
let rec mech (env : AI.t) (e : exp) : string =
  match e with
  | Bil.Var v -> (
      match Core.Map.find !shadow (Var.base v) with
      | Some m -> m
      | None -> (
          match Var.typ v with
          | Type.Imm _ when not (Var.is_virtual v) -> "call_reg"
          | _ -> "var"))
  | Bil.BinOp (op, e1, e2) ->
    let v1 = denote e1 env and v2 = denote e2 env in
    let s1 = Core.Option.value_map v1 ~default:false ~f:is_stack in
    let s2 = Core.Option.value_map v2 ~default:false ~f:is_stack in
    if blind_op op && (s1 || s2) then "blind." ^ op_name op
    else (
      match v1, v2 with
      | Some v, _ when Ws.is_top v -> mech env e1
      | _, Some v when Ws.is_top v -> mech env e2
      | _ -> if s1 || s2 then "wide_offset" else "other")
  | Bil.UnOp (op, e1) -> (
      match op, denote e1 env with
      | Bil.NOT, Some v when is_stack v -> "blind.not"
      | Bil.NEG, Some v when is_stack v -> "blind.neg"
      | _, Some v when Ws.is_top v -> mech env e1
      | _ -> "other")
  | Bil.Load (_, a, _, _) | Bil.Store (_, a, _, _, _) -> (
      match denote a env with
      | Some va when Ws.is_top va -> mech env a
      | Some va when is_stack va -> "call_top"
      | Some _ -> "foreign"
      | None -> "other")
  | Bil.Cast (_, _, e1) -> (
      match denote e1 env with
      | Some v when is_stack v -> "blind.cast"
      | Some v when Ws.is_top v -> mech env e1
      | _ -> "other")
  | Bil.Extract (_, _, e1) -> (
      match denote e1 env with
      | Some v when is_stack v -> "blind.extract"
      | Some v when Ws.is_top v -> mech env e1
      | _ -> "other")
  | Bil.Concat (e1, e2) ->
    let s e = Core.Option.value_map (denote e env) ~default:false ~f:is_stack in
    if s e1 || s e2 then "blind.concat"
    else (
      match denote e1 env with
      | Some v when Ws.is_top v -> mech env e1
      | _ -> "other")
  | Bil.Ite (_, y, n) -> (
      match mech env y with "other" -> mech env n | m -> m)
  | Bil.Let (v, value, body) ->
    let env' =
      match denote value env with
      | Some w -> AI.add_word env ~key:v ~data:w
      | None -> env
    in
    mech env' body
  | Bil.Int _ -> "other"
  | Bil.Unknown _ -> "unknown"

let classify_top_addr (env : AI.t) (a : exp) : string =
  match denote a env with
  | None -> "denote_err"
  | Some v ->
    if not (Ws.is_top v) then "bounded"
    else if shape_retained v then "vla_wide." ^ mech env a
    else mech env a

let def_bucket (v : Ws.t) : string =
  if Ws.is_top v then "top"
  else if Ws.is_bottom v then "bottom"
  else
    match Cbat_word.to_int (Ws.cardinality v) with
    | Error _ -> "b65p"
    | Ok n ->
      if n = 1 then "exact"
      else if n <= 3 then "b2_3"
      else if n <= 8 then "b4_8"
      else if n <= 64 then "b9_64"
      else "b65p"

let band_shape (v : Ws.t) : string =
  if Ws.is_circular v then "circular"
  else if Ws.is_infinite v then "infinite"
  else
    match Ws.enumerate ~cap:80 v with
    | None -> "band.wide"
    | Some elems ->
      let ints =
        Core.List.filter_map elems ~f:(fun w ->
            match Cbat_word.to_int64 w with Ok x -> Some x | Error _ -> None)
      in
      if Core.List.length ints <> Core.List.length elems
         || Core.List.length ints < 3
      then "band"
      else
        let ds =
          Core.List.zip_exn (Core.List.drop_last_exn ints)
            (Core.List.drop ints 1)
          |> Core.List.map ~f:(fun (a, b) ->
                 Stdlib.Int64.abs (Stdlib.Int64.sub b a))
        in
        match ds with
        | d :: rest
          when Stdlib.Int64.compare d 1L > 0
               && Core.List.for_all rest ~f:(fun x -> Stdlib.Int64.equal x d)
          ->
          "gcd_hull"
        | _ -> "band"

(* The unsigned span of a finite value, None for top/bottom/wrap. *)
let band_span (v : Ws.t) : int64 option =
  if Ws.is_top v || Ws.is_bottom v then None
  else
    match Ws.min_elem v, Ws.max_elem v with
    | Some lo, Some hi -> (
        match Cbat_word.to_int64 lo, Cbat_word.to_int64 hi with
        | Ok a, Ok b -> Some (Stdlib.Int64.sub b a)
        | _ -> None)
    | _ -> None

let span_bucket (sp : int64) : string =
  if Stdlib.Int64.compare sp 0L < 0 then "ge_2m"
  else if Stdlib.Int64.compare sp 8388607L >= 0 then "8m"
  else if Stdlib.Int64.compare sp 1048575L >= 0 then "2m"
  else if Stdlib.Int64.compare sp 65535L >= 0 then "64k"
  else if Stdlib.Int64.compare sp 4095L >= 0 then "4k"
  else if Stdlib.Int64.compare sp 64L > 0 then "65p"
  else "b64"

(* gcc -O0's alignment spelling: (x >> k) << k, split across two defs. *)
let shift_pend : Word.t VarMap.t ref = ref VarMap.empty

let census_addr ~(sub : string) ~(env : AI.t) (a : exp) : unit =
  bump "ld.total";
  match denote a env with
  | None -> bump "ld.denote_err"
  | Some v ->
    if Ws.is_top v then begin
      bump "ld.top";
      let m = classify_top_addr env a in
      bump ("ld.top." ^ m);
      if verbose then
        Printf.printf "VERBOSE ld.top sub=%s addr=%s mech=%s\n" sub
          (Format.asprintf "%a" Exp.pp a) m
    end
    else bump "ld.bounded";
    let stackish = Ws.is_bottom v || Ws.in_stack_segment v in
    if stackish then begin
      bump "stack.def";
      (match Ext.caller_split (Ext.classify v) with
       | Ext.Infinite (lo, hi) when Ext.is_unbounded_span lo hi ->
         bump "stack.unbounded";
         let m = classify_top_addr env a in
         bump ("unbounded.stack." ^ m);
         bump ("unbounded.stack@" ^ sub);
         if verbose then
           Printf.printf "VERBOSE unbounded sub=%s addr=%s mech=%s\n" sub
             (Format.asprintf "%a" Exp.pp a) m
       | _ -> bump "stack.bounded")
    end
    else if Ws.is_top v then begin
      bump "stack.def";
      bump "stack.unbounded";
      let m = classify_top_addr env a in
      bump ("unbounded.stack." ^ m);
      bump ("unbounded.stack@" ^ sub);
      if verbose then
        Printf.printf "VERBOSE unbounded-plain sub=%s addr=%s mech=%s\n" sub
          (Format.asprintf "%a" Exp.pp a) m
    end

let census_sub (sub : sub term) : unit =
  try
    let sol = Probe_common.run_sub_fixpoint sub in
    let sname = Sub.name sub in
    shadow := VarMap.empty;
    shift_pend := VarMap.empty;
    Term.enum blk_t sub
    |> Seq.iter ~f:(fun b ->
        let st = ref (Graphlib.Std.Solution.get sol (Term.tid b)) in
        Term.enum def_t b
        |> Seq.iter ~f:(fun d ->
            let st_before = !st in
            (match Ext.stack_address_of_rhs (Def.rhs d) with
             | Some a -> census_addr ~sub:sname ~env:st_before a
             | None -> ());
            st := Vsa.Test_seam.denote_def d !st;
            match Var.typ (Def.lhs d) with
            | Type.Imm w ->
              let v = AI.find_word w !st (Def.lhs d) in
              let bucket = def_bucket v in
              bump ("value." ^ bucket);
              if Core.String.equal bucket "b65p" then begin
                bump ("b65p.shape." ^ band_shape v);
                (match band_span v with
                 | Some sp ->
                   let sb = span_bucket sp in
                   if shape_retained v then bump ("b65p.stack.span." ^ sb)
                   else bump ("b65p.plain.span." ^ sb)
                 | None -> ())
              end;
              (match band_span v with
               | Some sp ->
                 let sb = span_bucket sp in
                 bump ("def.span." ^ sb);
                 if Core.String.equal sb "8m" then
                   bump ("def.span.8m@" ^ sname)
               | None -> ());
              (* The alignment composition (x >> k) << k, split over two defs. *)
              let base = Var.base (Def.lhs d) in
              (match Def.rhs d with
               | Bil.BinOp (Bil.LSHIFT, Bil.Var sv, Bil.Int kw) -> (
                   match Core.Map.find !shift_pend (Var.base sv) with
                   | Some k when Word.equal k kw ->
                     bump "fullspan.shift_compose";
                     bump ("fullspan.shift_compose@" ^ sname);
                     (match band_span v with
                      | Some sp when Stdlib.Int64.compare sp 64L > 0 ->
                        bump "fullspan.shift_compose.wide"
                      | _ -> ());
                     shift_pend := Core.Map.remove !shift_pend base
                   | _ -> shift_pend := Core.Map.remove !shift_pend base)
               | Bil.BinOp (Bil.RSHIFT, _, Bil.Int kw) ->
                 shift_pend := Core.Map.set !shift_pend ~key:base ~data:kw
               | _ -> shift_pend := Core.Map.remove !shift_pend base);
              let base = Var.base (Def.lhs d) in
              if Ws.is_top v then
                shadow :=
                  Core.Map.set !shadow ~key:base
                    ~data:(mech st_before (Def.rhs d))
              else shadow := Core.Map.remove !shadow base
            | Type.Mem _ | Type.Unk -> ()))
  with
  | Vsa.Fixpoint_not_converged _ -> bump "backstop.sub"
  | _ -> bump "census.exception"

let dump () : unit =
  Core.Hashtbl.to_alist counts
  |> Core.List.sort ~compare:(fun (a, _) (b, _) -> Core.String.compare a b)
  |> Core.List.iter ~f:(fun (key, n) ->
         Printf.printf "hike-attr-census: %s=%d\n" key n);
  flush stdout

let () =
  let argv = Array.to_list Sys.argv in
  let paths = match argv with _ :: tl -> tl | [] -> [] in
  match paths with
  | [] -> ws_usage Sys.argv.(0)
  | _ ->
    ws_init "attr_census";
    Core.List.iter paths ~f:(fun path ->
        Printf.printf "### %s\n" (Filename.basename path);
        (match
           Project.create (Project.Input.file ~loader:"llvm" ~filename:path)
         with
         | Error e -> ws_load_fail path e
         | Ok proj ->
           let prog = Project.program proj in
           Term.enum sub_t prog |> Seq.iter ~f:census_sub);
        dump ();
        Core.Hashtbl.clear counts)
