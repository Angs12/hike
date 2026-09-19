(* Forward transfer: value denotation over BIL. Pure; the walk and
   driver consume it (one-directional dep).  The entry RSP's word
   carries the symbolic segment base, SP-derived addresses denote
   [StackOff] directly, and memory cells key by their segment
   offsets. *)
include Core
open Bap.Std
open Graphlib.Std
open Cbat_vsa_utils
module AI = Cbat_ai_representation
module WordSet = Cbat_clp_set_composite
module Mem = Cbat_ai_memmap
module Word_ops = Cbat_word


(* Address size in bits; 0 falls back to BIL width. *)
let addr_bits_ref = ref 0
let set_addr_bits (n : int) : unit = addr_bits_ref := n

(* Memory index of a memory type. *)
let mem_idx addr_sz addressable_sz : Mem.idx =
  { Mem.addr_width =
      (if !addr_bits_ref > 0 then !addr_bits_ref else Size.in_bits addr_sz);
    Mem.addressable_width = Size.in_bits addressable_sz }

type wordset = WordSet.t





(* Widths of both inputs. *)
let denote_binop (op : Bil.binop) : wordset -> wordset -> wordset =
  let btrue = WordSet.singleton (Cbat_word.b1) in
  let bfalse = WordSet.singleton (Cbat_word.b0) in
  let wordset_of_bool b = if b then btrue else bfalse in
  let bool_top = WordSet.top 1 in
  let bool_bottom = WordSet.bottom 1 in
  (* Shared LT/LE/SLT/SLE endpoint test. *)
  let ordering ~(signed : bool) ~(le : bool) v1 v2 =
    let open Monads.Std.Monad.Option in
    let max_elem = if signed then WordSet.max_elem_signed else WordSet.max_elem in
    let min_elem = if signed then WordSet.min_elem_signed else WordSet.min_elem in
    let sgn = if signed then Cbat_word.signed else Fun.id in
    Option.value ~default:bool_top begin
      max_elem v1 >>= fun v1_max ->
      min_elem v1 >>= fun v1_min ->
      max_elem v2 >>= fun v2_max ->
      min_elem v2 >>= fun v2_min ->
      if le then
        if Cbat_word.(<=) (sgn v1_max) (sgn v2_min) then return btrue
        else if Cbat_word.(>) (sgn v1_min) (sgn v2_max) then return bfalse
        else return bool_top
      else
        if Cbat_word.(<) (sgn v1_max) (sgn v2_min) then return btrue
        else if Cbat_word.(>=) (sgn v1_min) (sgn v2_max) then return bfalse
        else return bool_top
    end in
  (* Shared EQ/NEQ decision. *)
  let compare_eq ~(negate : bool) v1 v2 =
    let v1Size = WordSet.cardinality v1 in
    let v2Size = WordSet.cardinality v2 in
    if Cbat_word.is_zero v1Size || Cbat_word.is_zero v2Size then bool_bottom
    else if Word_ops.is_one v1Size && Word_ops.is_one v2Size then
      wordset_of_bool
        (if negate then not (WordSet.equal v1 v2) else WordSet.equal v1 v2)
    else if WordSet.overlap v1 v2 then bool_top
    else if negate then btrue else bfalse
  in
  match op with
  | Bil.PLUS -> WordSet.add
  | Bil.MINUS -> WordSet.sub
  | Bil.TIMES -> WordSet.mul
  | Bil.LSHIFT -> WordSet.lshift
  | Bil.RSHIFT -> WordSet.rshift
  | Bil.ARSHIFT -> WordSet.arshift
  | Bil.DIVIDE -> WordSet.div
  | Bil.SDIVIDE -> WordSet.sdiv
  | Bil.MOD -> WordSet.modulo
  | Bil.SMOD -> WordSet.smodulo
  | Bil.AND -> WordSet.logand
  | Bil.OR -> WordSet.logor
  | Bil.XOR -> WordSet.logxor
  | Bil.EQ -> compare_eq ~negate:false
  | Bil.NEQ -> compare_eq ~negate:true
  | Bil.LT -> ordering ~signed:false ~le:false
  | Bil.LE -> ordering ~signed:false ~le:true
  | Bil.SLT -> ordering ~signed:true ~le:false
  | Bil.SLE -> ordering ~signed:true ~le:true

type val_t = [`Mem of Mem.t | `Word of wordset]

module Monad_type_error = Monads.Std.Monad.Result.Make(Type.Error)(Monads.Std.Monad.Ident)
type 'a or_type_error = ('a, Type.error) Result.t

let val_as_mem (v : val_t) : Mem.t or_type_error =
  match v with
  | `Mem m -> Ok m
  | `Word _ -> Error Type.Error.bad_mem

let val_as_imm (v : val_t) : wordset or_type_error =
  match v with
  | `Word p -> Ok p
  | `Mem _ -> Error Type.Error.bad_imm

let val_join (v1 : val_t) (v2 : val_t) : val_t or_type_error =
  let open Monad_type_error in
  match v1 with
  | `Word p1 -> val_as_imm v2 >>= fun p2 -> return @@ `Word (WordSet.join p1 p2)
  | `Mem m1 -> val_as_mem v2 >>= fun m2 -> return @@ `Mem (Mem.join m1 m2)

let val_top : typ -> val_t = function
  | Type.Imm i -> `Word (WordSet.top i)
  | Type.Mem (addr_sz, addressable_sz) ->
    let k = mem_idx addr_sz addressable_sz in
    `Mem (Mem.top k)
  | Type.Unk -> failwith "Error in val_top: typ is not representable by Type.t"

(* An image-backed section: [img_lo..img_hi] are the span's inclusive
   address bounds, [img_bytes] the section's static content.  The
   pass entry threads only sections whose runtime content IS the
   image. *)
type section_image =
  { img_lo : int64;
    img_hi : int64;
    img_bytes : int array }

let section_images_ref : section_image list ref = ref []

(* Threads the image-backed sections in. *)
let set_section_images (imgs : section_image list) : unit =
  section_images_ref := imgs

(* The image's [bits]-bit word at byte offset [off], assembled in the
   load's endianness; [None] when the bytes leave the array. *)
let image_word (bytes : int array) (off : int) ~(endian : endian)
    ~(bits : int) : Cbat_word.t option =
  let nb = bits / 8 in
  if
    bits <= 0 || bits > 64 || bits mod 8 <> 0 || off < 0
    || off + nb > Array.length bytes
  then None
  else
    let v =
      let rec go i acc =
        if i >= nb then acc
        else
          let b = Stdlib.Int64.of_int bytes.(off + i) in
          let acc' =
            match endian with
            | LittleEndian ->
              Stdlib.Int64.logor acc (Stdlib.Int64.shift_left b (8 * i))
            | BigEndian ->
              Stdlib.Int64.logor acc
                (Stdlib.Int64.shift_left b (8 * (nb - 1 - i)))
          in
          go (i + 1) acc'
      in
      go 0 0L
    in
    Some (Cbat_word.of_word (Word.of_int64 ~width:bits v))

(* An address set the image rule can enumerate exactly. *)
let image_load_card_cap = 64

(* The image-backed load: an address set fully bounded inside ONE
   threaded image reads the image's bytes — the exact value set, the
   image being the section's static content.  The premise is the whole
   rule: a plain (non-stack) bounded address whose entire access
   extent lies inside one image, no stored cell intersecting the
   extent (a store wins), and an enumerable address set.  Anything
   else keeps the abstract read — the sound identity. *)
let section_image_load ~(addr : wordset) ~(endian : endian) ~(bits : int)
    (mv : Mem.t) : wordset option =
  (* A live (non-bottom) memory reads top where no cell covers the
     bytes; a bottom memory — the unreached state's default — keeps
     the load's own abstract value. *)
  if not (Mem.is_bottom mv) then
    match !section_images_ref with
    | [] -> None
    | images ->
    if
      bits <= 0 || bits > 64
      || WordSet.is_top addr || WordSet.is_bottom addr
      || WordSet.is_infinite addr
      || Option.is_some (WordSet.stack_offsets addr)
      || WordSet.in_stack_segment addr
    then None
    else
      let i64 w =
        match Cbat_word.to_int64 w with Ok v -> Some v | Error _ -> None
      in
      let mn_w = WordSet.min_elem addr and mx_w = WordSet.max_elem addr in
      match
        Base.Option.bind mn_w ~f:i64, Base.Option.bind mx_w ~f:i64
      with
      | Some lo_a, Some hi_a -> (
          let nb = bits / 8 in
          let last = Stdlib.Int64.add hi_a (Stdlib.Int64.of_int (nb - 1)) in
          if Stdlib.Int64.unsigned_compare last hi_a < 0 then None
          else
            match
              Base.List.find images
                ~f:(fun { img_lo; img_hi; _ } ->
                  Stdlib.Int64.unsigned_compare lo_a img_lo >= 0
                  && Stdlib.Int64.unsigned_compare last img_hi <= 0)
            with
            | None -> None
            | Some { img_lo; img_bytes; _ } ->
              let last_w =
                Cbat_word.of_word (Word.of_int64 ~width:64 last)
              in
              if Mem.has_cell_in mv ~lo:(Option.value_exn mn_w) ~hi:last_w
              then None
              else if
                Cbat_word.gt_int (WordSet.cardinality addr) image_load_card_cap
              then None
              else
                (* Every enumerated address lies inside the hull, whose
                   whole extent the span check covered — the reads stay
                   in bounds; one unreadable word refuses the arm for
                   the whole set. *)
                Base.List.fold (WordSet.iter addr) ~init:(Some [])
                  ~f:(fun acc a ->
                      match acc with
                      | None -> None
                      | Some ws -> (
                          match i64 a with
                          | None -> None
                          | Some ai -> (
                              match
                                image_word img_bytes
                                  (Stdlib.Int64.to_int
                                     (Stdlib.Int64.sub ai img_lo))
                                  ~endian ~bits
                              with
                              | Some w -> Some (w :: ws)
                              | None -> None)))
                |> Option.map ~f:(fun words ->
                        WordSet.of_list ~width:bits words))
      | _ -> None
  else None

let rec denote_exp (e : exp) (env : AI.t) : val_t or_type_error =
  let open Monad_type_error in
  let monadic_assert (b : bool) (err : Type.error) =
    if b then !!() else fail err in
  let return_imm (v : wordset) = return @@ `Word v in
  let return_mem (v : Mem.t) = return @@ `Mem v in
  match e with
  | Bil.Var v -> begin match Var.typ v with
    | Type.Imm bitwidth -> return_imm @@ AI.find_word bitwidth env v
    | Type.Mem (addr_i, addressable_size) ->
      let k = mem_idx addr_i addressable_size in
      return_mem @@ AI.find_memory k env v
    | Type.Unk -> failwith "Error in denote_exp: var type is not representable by Type.t"
    end
  | Bil.Int bv -> return_imm @@ WordSet.singleton (Cbat_word.of_word bv)
  | Bil.BinOp (op, e1, e2) ->
    denote_exp e1 env >>= val_as_imm >>= fun v1 ->
    denote_exp e2 env >>= val_as_imm >>= fun v2 ->
    return_imm @@ denote_binop op v1 v2
  | Bil.Load (m, a, e, s) ->
    denote_exp a env >>= val_as_imm >>= fun addr ->
    denote_exp m env >>= val_as_mem >>= fun mv ->
    let resSize = Size.in_bits s in
    (match section_image_load ~addr ~endian:e ~bits:resSize mv with
    | Some ws -> return_imm ws
    | None ->
      if WordSet.splits_by addr (Cbat_word.of_int ~width:resSize (Size.in_bytes s))
      then Option.value_map ~default:(return_imm @@ WordSet.bottom resSize) (Mem.Key.of_wordset addr)
          ~f:(fun k -> Mem.find (resSize, e) mv k |> Mem.Val.data |> return_imm)
      else return_imm @@ WordSet.top resSize)
  | Bil.Store (m, a, u, e, s) ->
    Type.infer u >>= fun u_typ ->
    let sz = Size.in_bits s in
    let exp = Type.imm sz in
    let u_type_error = Type.Error.bad_type ~exp ~got:u_typ in
    monadic_assert Type.(exp = u_typ) u_type_error >>= fun () ->
    denote_exp a env >>= val_as_imm >>= fun addr ->
    denote_exp m env >>= val_as_mem >>= fun mv ->
    denote_exp u env >>= val_as_imm >>= fun v ->
    
    if WordSet.is_top addr
    (* The store may write any cell: whole-memory top. *)
    then return_mem @@ Mem.top (Mem.get_idx mv)
    else
    
    let v' = if WordSet.splits_by addr (Cbat_word.of_int ~width:sz (Size.in_bytes s))
      then v else WordSet.top sz in
    let data = Mem.Val.create v' e in
    return_mem @@ Option.value_map ~default:mv (Mem.Key.of_wordset addr)
      ~f:(fun key -> Mem.add mv ~key ~data)
  | Bil.Ite (cond, yes, no) ->
    denote_exp cond env >>= val_as_imm >>= fun condv ->
    denote_exp yes env >>= fun yesv ->
    denote_exp no env >>= fun nov ->
    if WordSet.is_top condv then val_join yesv nov
    else if WordSet.equal condv (WordSet.singleton (Cbat_word.b1)) then return yesv
    else if WordSet.equal condv (WordSet.singleton Cbat_word.b0) then return nov
    
    else val_join yesv nov
  | Bil.Extract (hi, lo, e) ->
    denote_exp e env >>= val_as_imm >>= fun v ->
    return_imm @@ WordSet.extract ~hi ~lo v
  | Bil.Concat (e1, e2) ->
    denote_exp e1 env >>= val_as_imm >>= fun v1 ->
    denote_exp e2 env >>= val_as_imm >>= fun v2 ->
    return_imm @@ WordSet.concat v1 v2
  | Bil.UnOp (Bil.NOT, e) ->
    denote_exp e env >>= val_as_imm >>| WordSet.lnot >>= return_imm
  | Bil.UnOp (Bil.NEG, e) ->
    denote_exp e env >>= val_as_imm >>| WordSet.neg >>= return_imm
  | Bil.Cast (ct, sz, e) ->
    denote_exp e env >>= val_as_imm >>| WordSet.cast ct sz >>= return_imm
  | Bil.Let (var, value, body) ->
    denote_exp value env >>= fun v ->
    let env' = match v with
      | `Word p -> AI.add_word ~key:var ~data:p env
      | `Mem m -> AI.add_memory ~key:var ~data:m env
    in
    denote_exp body env'
  | Bil.Unknown (_,typ) -> return @@ val_top typ

let denote_imm_exp (e : exp) (env : AI.t) : WordSet.t or_type_error =
  let open Monad_type_error in
  denote_exp e env >>= val_as_imm

(* Every def is denoted (spec §2.1): the denotation IS the transfer —
   SP-derived addresses arrive as [StackOff] words and memory ops key
   cells by their segment offsets. *)
let denote_def (df : def term) (env : AI.t) : AI.t =
  let v = Def.lhs df in
  let e = Def.rhs df in
  exn_on_err @@
  let open Monad_type_error in
  denote_exp e env >>| fun ev ->
  (match ev with
   | `Word p -> AI.add_word env ~key:v ~data:p
   | `Mem m -> AI.add_memory env ~key:v ~data:m)

(* Denotation of a block's defs. *)
let denote_defs (b : blk term) : AI.t -> AI.t =
  (* Phis are the identity. *)
  fun env0 ->
    Term.enum def_t b
    |> Seq.fold ~init:env0 ~f:(fun env df -> denote_def df env)

(* One per-block state replay: the block's defs fold [denote_def] from
   its solution entry state; [f] folds the accumulator over each def's
   (before, after) states.  A def-less block runs [f] zero times and
   the end state is the entry state. *)
let fold_block_states ~(sol : (tid, AI.t) Solution.t) (blk : blk term)
    ~(init : 'acc) ~(f : AI.t -> AI.t -> def term -> 'acc -> 'acc) :
    'acc * AI.t =
  let st_end, acc =
    Term.enum def_t blk
    |> Seq.fold ~init:(Solution.get sol (Term.tid blk), init)
         ~f:(fun (st_before, acc) d ->
             let st_after = denote_def d st_before in
             (st_after, f st_before st_after d acc))
  in
  (acc, st_end)

(* The block's last def per lhs var: the reaching def at the block's
   end (the defs run in order before the block's jmps). *)
let last_defs (blk : blk term) : def term Var.Map.t =
  Term.enum def_t blk
  |> Seq.fold ~init:Var.Map.empty ~f:(fun m d ->
      Core.Map.set m ~key:(Def.lhs d) ~data:d)



(* Jumps reachable in the env.  Guards evaluate on the words lane
   directly: an SP-derived var's word is the segment-smeared
   stack base, so bit tests on it stay undecided ([seg & 0xF] = [0,15])
   and comparisons against concrete addresses decide consistently with
   real pointer behavior. *)
let reachable_jumps (env : AI.t) (jmps : jmp term seq) : jmp term seq =
  Seq.unfold_with jmps  ~init:true ~f:begin fun reachable jmp ->
    let cond = exn_on_err @@ denote_imm_exp (Jmp.cond jmp) env in
    let can_fall_through = WordSet.elem Cbat_word.b0 cond in
    if not reachable then Seq.Step.Done
    else if WordSet.elem (Cbat_word.b1) cond then Seq.Step.Yield {value = jmp; state = can_fall_through}
    else Seq.Step.Skip {state = can_fall_through}
  end
