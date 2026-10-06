(* The synthetic address layer: the leaf census and the base/displacement
   arithmetic of an address value.  The vocabulary (kinds, spans) lives
   in Hike_synth below the VSA; this layer needs the domain's word sets
   and the model's offset line, so it lives with the model. *)

open Bap.Std
module Model = Hike_stack_model

(* A leaf's kind: [`Static k] an address whose offset is provably k,
   [`Addr] an address whose offset is not static, [`Int] a visible
   non-address (a runtime piece).  A var the denotation cannot see is
   absent — unknown may be a pointer at emission, so it never enters a
   displacement. *)
type leaf = [ `Static of int64 | `Addr | `Int ]

let w64 (k : int64) : exp =
  Bil.Int (Cbat_word.to_word (Cbat_word.of_int64 ~width:64 k))

(* The entry-line arithmetic of an address exp: each [`Static] leaf
   folds to its constant, each [`Int] leaf (a value outside the stack
   segment) stays a runtime piece.  [None] when an address part is a
   pointer or invisible — the value then composes over its operands'
   own pointers. *)
let offset_of ~(leaves : leaf Var.Map.t) (e : exp) : exp option =
  Hike_exp_fold.fold
    (fun e child ->
      match e with
      | Bil.Int _ -> Some e
      | Bil.Var v -> (
          match Core.Map.find leaves v with
          | Some (`Static k) -> Some (w64 k)
          | Some `Int -> Some e
          | Some `Addr | None -> None)
      | Bil.BinOp ((Bil.PLUS | Bil.MINUS) as op, a, b) -> (
          match (child a, child b) with
          | Some a', Some b' -> (
              match (a', b') with
              | Bil.Int x, Bil.Int y -> (
                  match
                    (Cbat_word.to_int64 (Cbat_word.of_word x),
                     Cbat_word.to_int64 (Cbat_word.of_word y))
                  with
                  | Ok x', Ok y' ->
                      Some
                        (w64
                           ((if op = Bil.PLUS then Stdlib.Int64.add
                             else Stdlib.Int64.sub)
                              x' y'))
                  | _ -> Some (Bil.BinOp (op, a', b')))
              | _ -> Some (Bil.BinOp (op, a', b')))
          | _ -> None)
      | Bil.Cast (cast, width, a) ->
          Base.Option.map (child a) ~f:(fun a' -> Bil.Cast (cast, width, a'))
      | Bil.Ite (c, a, b) -> (
          match (child a, child b) with
          | Some a', Some b' -> Some (Bil.Ite (c, a', b'))
          | _ -> None)
      | _ ->
          if
            Core.Set.exists (Exp.free_vars e) ~f:(fun v ->
                match Core.Map.find leaves v with
                | Some `Int -> false
                | _ -> true)
          then None
          else Some e)
    e

(* [base + (disp − rel)] with the displacement folded: a static
   displacement folds to a constant (the base itself at zero). *)
let base_plus (base : var) ~(rel : int64) (disp : exp) : exp =
  match disp with
  | Bil.Int w -> (
      match Cbat_word.to_int64 (Cbat_word.of_word w) with
      | Ok k ->
          let k = Stdlib.Int64.sub k rel in
          if Stdlib.Int64.equal k 0L then Bil.Var base
          else Bil.BinOp (Bil.PLUS, Bil.Var base, w64 k)
      | Error _ -> Bil.BinOp (Bil.PLUS, Bil.Var base, disp))
  | _ ->
      Bil.BinOp
        (Bil.PLUS, Bil.Var base, Bil.BinOp (Bil.MINUS, disp, w64 rel))

(* Every var leaf's kind: a synthetic leaf's class is its kind's (a
   module address is an integer value, a stack storage's base is its
   allocated offset); a var with no synthetic identity asks the
   denotation. *)
let address_leaves ~(denote : blk:blk term -> ?def:def term -> exp ->
                     (Cbat_clp_set_composite.t, Type.error) Result.t)
    ~(storages : Hike_synth.storage_span list)
    ~(blk : blk term) ~(def : def term) (e : exp) : leaf Var.Map.t =
  (object
     inherit [ leaf Var.Map.t ] Exp.visitor
     method! visit_var v acc =
       let by_denotation () =
         match denote ~blk ~def (Bil.Var v) with
         | Ok ws
           when (not
                   (Cbat_clp_set_composite.is_top ws
                   || Cbat_clp_set_composite.is_bottom ws))
                && Cbat_clp_set_composite.in_stack_segment ws ->
           (* A Vla-origin value's offsets are frame-relative —
              read them off the value, never the entry-line hull. *)
           let off =
             match Cbat_clp_set_composite.origin ws with
             | Some (Cbat_clp_set_composite.Origin.Vla _) -> (
                 match Cbat_clp_set_composite.vla_offsets ws with
                 | Some offs -> Model.singleton_offset offs
                 | None -> None)
             | _ -> (
                 match Cbat_clp_set_composite.stack_offsets ws with
                 | Some offs -> Model.singleton_offset offs
                 | None -> None)
           in
           Core.Map.set acc ~key:v
             ~data:(match off with Some k -> `Static k | None -> `Addr)
         | Ok ws
           when not
                  (Cbat_clp_set_composite.is_top ws
                  || Cbat_clp_set_composite.is_bottom ws) ->
           Core.Map.set acc ~key:v ~data:`Int
         | Ok _ | Error _ -> acc
       in
       match Hike_synth.classify Hike_synth.empty v with
       | Some (Hike_synth.Module_addr _) ->
         Core.Map.set acc ~key:v ~data:`Int
       | Some (Hike_synth.Storage (Hike_synth.Stack id)) -> (
         match Hike_synth.span_of_storage storages (Hike_synth.Stack id) with
         | Some s ->
           Core.Map.set acc ~key:v
             ~data:
               (`Static
                  (Stdlib.Int64.sub s.Hike_synth.ss_lo Model.segment_base))
         | None -> by_denotation ())
       | _ -> by_denotation ()
   end)#visit_exp e Var.Map.empty

(* — Address interpretation. — *)

type region = { id : int; lo : int64; hi : int64 }

let contains r a =
  Int64.unsigned_compare r.lo a <= 0
  && Int64.unsigned_compare a r.hi <= 0

(* Both attribution and resolution use the owning byte span's base. *)
let of_address ~addr_bits ~regions a =
  Base.Option.map (Base.List.find regions ~f:(fun r -> contains r a))
    ~f:(fun r ->
      (Hike_synth.bytes ~addr_bits (Hike_synth.Global r.id),
       Bil.Int (Word.of_int64 ~width:addr_bits (Int64.sub a r.lo))))

let address_of_exp table e =
  Hike_exp_fold.fold
    (fun e child ->
       match e with
       | Bil.Int w -> Base.Result.ok (Word.to_int64 w)
       | Bil.Var v -> Hike_synth.module_addr_of table v
       | Bil.BinOp (Bil.PLUS, a, b) ->
         Base.Option.bind (child a) ~f:(fun a ->
             Base.Option.map (child b) ~f:(Int64.add a))
       | Bil.BinOp (Bil.MINUS, a, b) ->
         Base.Option.bind (child a) ~f:(fun a ->
             Base.Option.map (child b) ~f:(Int64.sub a))
       | _ -> None)
    e

let address_basis table e =
  (object
     inherit [int64 option] Exp.visitor
     method! visit_var v acc =
       Base.Option.first_some acc (Hike_synth.module_addr_of table v)
   end)#visit_exp e None

(* The inverse of [of_address] for every storage family: a base var's
   byte origin plus the access's constant index.  The origin map is the
   emitter's component table or the layout's regions; a plain memory var
   has no storage origin and keeps its index as the address. *)
let access_address ?origin table mem index =
  match address_of_exp table index with
  | None -> None
  | Some idx -> (
    match Hike_synth.storage_of table mem with
    | Some _ ->
      Base.Option.bind origin ~f:(fun origin ->
          Base.Option.map (origin (Var.base mem)) ~f:(Int64.add idx))
    | None -> Some idx)

(* — The general access rewriting: every Load/Store takes its storage's
     memory var and the storage-relative index. — *)

(* The access's general form: the memory operand and the storage-relative
   address.  A copy-relocated slot holds the object's address, so the
   access goes through the pointer the loader stores there: the memory
   operand stays and the address becomes a load at the slot's own
   absolute address (the emitter's section path renders it). *)
let access ?(slots = []) ~addr_bits ~regions ~named_only tbl mem addr ~size =
  let owner =
    match mem with Bil.Var mv -> Hike_synth.storage_of tbl mv | _ -> None
  in
  match address_of_exp tbl addr with
  | Some a when Base.List.exists slots ~f:(Int64.equal a) ->
    (* The slot's pointer read: the slot's own storage form, so the
       emitter resolves it through the one component map. *)
    Base.Option.map (of_address ~addr_bits ~regions a)
      ~f:(fun (slot_mem, slot_index) ->
        (mem, Bil.Load (Bil.Var slot_mem, slot_index, LittleEndian, `r64)))
  | addr_value -> (
    match owner, addr_value with
    | Some (Hike_synth.Global _ as storage), None ->
      (* A module-backed storage owns the whole range: subtract its
         runtime base once, including when the index is dynamic.  A
         runtime-backed storage (stack, window, slot, allocation)
         already carries its pointer-relative address and stays as it
         came. *)
      (match addr with
       | Bil.BinOp (Bil.MINUS, _, Bil.Var v)
         when Var.equal v (Hike_synth.base ~addr_bits storage) -> None
       | _ ->
         Some
           (Bil.Var (Hike_synth.bytes ~addr_bits storage),
            Bil.BinOp (Bil.MINUS, addr,
                       Bil.Var (Hike_synth.base ~addr_bits storage))))
    | Some _, None -> None
    | None, _ when named_only -> None
    | _, Some a ->
      Base.Option.bind (address_basis tbl addr) ~f:(fun _ ->
          let last = Int64.add a (Int64.of_int (size - 1)) in
          let regions =
            Base.List.filter regions ~f:(fun r ->
                Int64.unsigned_compare last a >= 0 && contains r last)
          in
          Base.Option.map (of_address ~addr_bits ~regions a)
            ~f:(fun (mv, index) -> (Bil.Var mv, index)))
    | None, None -> None)

(* The def's single memory node takes its general form; the rewrite does
   not descend into a node's own address (the generated slot pointer
   read is already in final form). *)
let rewrite_exp ?slots ~addr_bits tbl ~regions ~named_only e =
  (object
     inherit Exp.mapper as super
     method! map_load ~mem ~addr endian size =
       match
         access ?slots ~addr_bits ~regions ~named_only tbl mem addr
           ~size:(Size.in_bytes size)
       with
       | Some (mem', addr') -> Bil.Load (mem', addr', endian, size)
       | None -> Bil.Load (mem, addr, endian, size)
     method! map_store ~mem ~addr ~exp endian size =
       match
         access ?slots ~addr_bits ~regions ~named_only tbl mem addr
           ~size:(Size.in_bytes size)
       with
       | Some (mem', addr') ->
         Bil.Store (mem', addr', super#map_exp exp, endian, size)
       | None -> Bil.Store (mem, addr, super#map_exp exp, endian, size)
   end)#map_exp e

let rewrite_def ?slots ~addr_bits tbl ~regions ~named_only d =
  let memory = ref None in
  let mapper =
    object
      inherit Exp.mapper as super
      method! map_load ~mem ~addr endian size =
        match
          access ?slots ~addr_bits ~regions ~named_only tbl mem addr
            ~size:(Size.in_bytes size)
        with
        | Some (mem', addr') -> Bil.Load (mem', addr', endian, size)
        | None -> Bil.Load (mem, addr, endian, size)
      method! map_store ~mem ~addr ~exp endian size =
        match
          access ?slots ~addr_bits ~regions ~named_only tbl mem addr
            ~size:(Size.in_bytes size)
        with
        | Some (Bil.Var mv, addr') ->
          memory := Some mv;
          Bil.Store (Bil.Var mv, addr', super#map_exp exp, endian, size)
        | Some (mem', addr') ->
          Bil.Store (mem', addr', super#map_exp exp, endian, size)
        | None -> Bil.Store (mem, addr, super#map_exp exp, endian, size)
    end
  in
  let d = Def.map_exp d ~f:mapper#map_exp in
  match !memory with
  | Some mv -> (
    match Var.typ (Def.lhs d) with
    | Type.Mem _ -> Def.with_lhs d mv
    | _ -> d)
  | None -> d

(* The storage conversion an access def takes: decided by the
   attribution (its projection and finalized trees) and consumed by the
   rewrite below. *)
type conv =
  | Conv_region of int                    (* the region id *)
  | Conv_window                           (* the incoming window: the caller's world *)
  | Conv_slot of int * int                (* slot index, intra-slot byte *)
  | Conv_global of int                    (* the component id *)
  | Keep

let repoint_mapper ?(addr : exp option) (mem_var : var) =
  object
    inherit Exp.mapper as super
    method! map_load ~mem:_ ~addr:a rest s =
      Bil.Load
        ( Bil.Var mem_var,
          (match addr with Some e -> e | None -> super#map_exp a),
          rest, s )
    method! map_store ~mem:_ ~addr:a ~exp rest s =
      Bil.Store
        ( Bil.Var mem_var,
          (match addr with Some e -> e | None -> super#map_exp a),
          super#map_exp exp, rest, s )
  end

(* A slot access keeps its memory node and takes [addr] as its address:
   the load/store is real, through the caller's slot pointer. *)
let slot_addr_mapper (addr : exp) =
  object
    inherit Exp.mapper as super
    method! map_load ~mem ~addr:_ endian size =
      Bil.Load (mem, addr, endian, size)
    method! map_store ~mem ~addr:_ ~exp endian size =
      Bil.Store (mem, addr, super#map_exp exp, endian, size)
  end

(* One def's rewrite: re-point to the owning storage's mem var at the
   storage-relative address, or address its memory node at the caller's
   slot. *)
let rewrite_storage ~(addr_bits : int) ~(conv : conv) ~(bits : int)
    ?(addr : exp option) (d : def term) : def term =
  match conv with
  | Keep -> d
  | Conv_region id ->
      let mem_var = Model.region_mem ~addr_bits:bits id in

      let d =
        Def.map_exp d ~f:(fun e -> (repoint_mapper ?addr mem_var)#map_exp e)
      in

      if Model.is_mem (Def.lhs d) then Def.with_lhs d mem_var else d
  | Conv_window ->
      let mem_var = Model.window_mem ~addr_bits:bits in
      let d =
        Def.map_exp d ~f:(fun e -> (repoint_mapper ?addr mem_var)#map_exp e)
      in
      if Model.is_mem (Def.lhs d) then Def.with_lhs d mem_var else d
  | Conv_global id ->
      let mem_var = Model.sec_comp_mem ~addr_bits id in
      let d =
        Def.map_exp d ~f:(fun e -> (repoint_mapper mem_var)#map_exp e)
      in
      if Model.is_mem (Def.lhs d) then Def.with_lhs d mem_var else d
  | Conv_slot (i, byte_offset) ->
      let slot = Model.arg_slot ~addr_bits i in
      let addr =
        base_plus slot ~rel:0L
          (Bil.Int
             (Cbat_word.to_word
                (Cbat_word.of_int64 ~width:addr_bits
                   (Stdlib.Int64.of_int byte_offset))))
      in
      Def.map_exp d ~f:(fun e -> (slot_addr_mapper addr)#map_exp e)

