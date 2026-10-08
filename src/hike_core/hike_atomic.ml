(* Atomic intrinsics become ordinary analytical accesses with an explicit
   emission contract. Tags contain roles, never hidden expression operands. *)
open Bap.Std

let operations = [ "add"; "sub"; "and"; "or"; "xor"; "xchg"; "cmpxchg"; "neg" ]

let of_name name =
  let name = Hike_abi.strip_at name in
  let desc = Base.List.find_map operations ~f:(fun op ->
      Base.List.find_map [8;16;32;64] ~f:(fun bits ->
          if String.equal name (Printf.sprintf "intrinsic:x86:atomic_%s_%d" op bits)
          then Some (op,bits) else None)) in
  if Base.Option.is_none desc && Base.String.is_prefix name
      ~prefix:"intrinsic:x86:atomic_" then
    failwith "hike: unsupported atomic intrinsic";
  desc

let lane role bits =
  Var.create ~is_virtual:false ~fresh:false
    (Printf.sprintf "intrinsic:x86:atomic:%s:%d" role bits) (Type.Imm bits)

let operation : string Value.Tag.t =
  Value.Tag.register ~package:"hike" ~name:"atomic-operation"
    ~uuid:"7bdc2a2f-157a-4459-9420-d816351d7f10" (module Core.String)
let input : int Value.Tag.t =
  Value.Tag.register ~package:"hike" ~name:"atomic-input"
    ~uuid:"8bdc2a2f-157a-4459-9420-d816351d7f10" (module Core.Int)
let write : unit Value.Tag.t =
  Value.Tag.register ~package:"hike" ~name:"atomic-write"
    ~uuid:"9bdc2a2f-157a-4459-9420-d816351d7f10" (module Core.Unit)

let normalize ~addr_bits program =
  let mem = Var.create ~is_virtual:false ~fresh:false "mem"
      (Type.Mem (Size.addr_of_int_exn addr_bits,`r8)) in
  Term.map sub_t program ~f:(fun sub ->
      Term.map blk_t sub ~f:(fun blk ->
          let calls = Term.enum jmp_t blk |> Seq.filter_map ~f:(fun j ->
              match Jmp.kind j with
              | Call c -> (match Call.target c with
                  | Direct t -> Base.Option.map (of_name (Tid.name t))
                      ~f:(fun desc -> j,c,desc)
                  | _ -> None)
              | _ -> None) |> Seq.to_list in
          match calls with
          | [] -> blk
          | [j,c,(op,bits)] ->
            if not (Exp.equal (Jmp.cond j) Bil.(int (Word.one 1))) then
              failwith "hike: conditional atomic intrinsic";
            let continuation = match Call.return c with
              | Some (Direct t) -> t
              | _ -> failwith "hike: atomic intrinsic has no direct continuation" in
            let capture i =
              let v = Var.create ~is_virtual:true "atomic_input" (Type.Imm bits) in
              v, Term.set_attr
                (Def.create v (Bil.Var (lane (Printf.sprintf "input%d" i) bits))) input i in
            let arg,darg = capture 0 in
            let args,desired = if String.equal op "cmpxchg" then
                let v,d = capture 1 in [darg;d],Bil.Var v
              else (if String.equal op "neg" then [] else [darg]),Bil.Var arg in
            (* The producer captures the pure effective address before its input
               lanes. Keep its expression visible to TLS/storage attribution. *)
            let address_lane = lane "address" addr_bits in
            let addr = Term.enum def_t blk |> Seq.fold
                ~init:(Bil.Var address_lane) ~f:(fun addr d ->
                    if Var.same (Def.lhs d) address_lane then Def.rhs d else addr) in
            let old = lane "old" bits in
            let fresh = Var.create ~is_virtual:true "atomic_new" (Type.Imm bits) in
            let old_e = Bil.Var old in
            let operand = Bil.Var arg in
            let success = Bil.BinOp (Bil.EQ,old_e,operand) in
            let data = match op with
              | "add" -> Bil.BinOp (Bil.PLUS,old_e,operand)
              | "sub" -> Bil.BinOp (Bil.MINUS,old_e,operand)
              | "and" -> Bil.BinOp (Bil.AND,old_e,operand)
              | "or" -> Bil.BinOp (Bil.OR,old_e,operand)
              | "xor" -> Bil.BinOp (Bil.XOR,old_e,operand)
              | "xchg" -> operand
              | "cmpxchg" -> Bil.Ite (success,desired,old_e)
              | "neg" -> Bil.UnOp (Bil.NEG,old_e)
              | _ -> assert false in
            let defs = args @
              [Term.set_attr (Def.create old
                   (Bil.Load (Bil.Var mem,addr,LittleEndian,Size.of_int_exn bits))) operation op;
               Def.create fresh data] @
              (if String.equal op "cmpxchg" then
                 [Def.create (lane "success" 1) success] else []) @
              [Term.set_attr (Def.create mem
                  (Bil.Store (Bil.Var mem,addr,Bil.Var fresh,LittleEndian,Size.of_int_exn bits))) write ()] in
            let blk = Base.List.fold defs ~init:blk ~f:(Term.append def_t) in
            Term.map jmp_t blk ~f:(fun other ->
                if Tid.equal (Term.tid other) (Term.tid j) then
                  Jmp.with_kind j (Goto (Direct continuation))
                else other)
          | _ -> failwith "hike: multiple atomic intrinsics in one block"))
