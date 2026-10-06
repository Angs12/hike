(* The synthetic variable vocabulary, one ADT and one table.  A
   synthetic var names a value the emitter materializes — a text
   address, a global byte, an argument lane, a window cell, an alloca,
   an env register.  The rip pass rewrites the lifter's rip constants
   into these vars; the KB carries the table; the emitter resolves
   through [resolve] and renders the kind. *)

open Bap.Std

type kind =
  | Addr of int64 (* a module address: text or a section byte *)

let prefix = "hike_synth_"

let var (k : kind) : Var.t =
  match k with
  | Addr a ->
    Var.create ~is_virtual:true ~fresh:false
      (Printf.sprintf "%s%Lx" prefix a)
      (Type.Imm 64)

let kind_of_var (v : Var.t) : kind option =
  let n = Var.name v in
  if Base.String.is_prefix n ~prefix then
    Base.String.chop_prefix n ~prefix
    |> Base.Option.bind ~f:(fun h ->
           try Some (Addr (Stdlib.Int64.of_string ("0x" ^ h)))
           with _ -> None)
  else None

type table = kind Var.Map.t

let empty : table = Var.Map.empty

let resolve (tbl : table) (v : Var.t) : kind option =
  match Core.Map.find tbl v with Some k -> Some k | None -> kind_of_var v

(* The table over a program: every synthetic var's kind, recorded once
   so no consumer parses names. *)
let table_of_program (prog : program term) : table =
  Term.enum sub_t prog
  |> Seq.fold ~init:Var.Map.empty ~f:(fun acc sub ->
      Term.enum blk_t sub
      |> Seq.fold ~init:acc ~f:(fun acc blk ->
          Term.enum def_t blk
          |> Seq.fold ~init:acc ~f:(fun acc d ->
              match Def.rhs d with
              | Bil.Var v -> (
                  match kind_of_var v with
                  | Some k -> Core.Map.set acc ~key:v ~data:k
                  | None -> acc)
              | _ -> acc)))
