(* Forward transfer: value denotation over BIL.  The entry RSP's word
   carries the symbolic segment base, SP-derived addresses denote
   [StackOff], and memory cells key by their segment offsets. *)
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

let mem_idx addr_sz addressable_sz : Mem.idx =
  { Mem.addr_width =
      (if !addr_bits_ref > 0 then !addr_bits_ref else Size.in_bits addr_sz);
    Mem.addressable_width = Size.in_bits addressable_sz }

type wordset = WordSet.t

#ifdef VSA_DEBUG
(* The residual-mismatch log budget (the coercion pass should leave none). *)
let dbg_left = ref 256

let dbg_one_line (e : exp) : string =
  let bs = Buffer.create 128 in
  let fmt = Format.formatter_of_buffer bs in
  Format.pp_set_margin fmt 1_000_000;
  Format.fprintf fmt "%a" Exp.pp e;
  Format.pp_print_flush fmt ();
  Buffer.contents bs

(* B16 census: both operands are stack singletons.  The cardinality
   gate reads the saturated stack-span for a StackOff, so this shape
   can only reach the overlap fall-through. *)
let stack_singleton (v : wordset) : bool =
  match WordSet.stack_offsets v with
  | Some o -> Word_ops.is_one (WordSet.cardinality (WordSet.stack_word o))
  | None -> false

let debug_b16_eq (v1 : wordset) (v2 : wordset) : unit =
  if stack_singleton v1 && stack_singleton v2 && WordSet.equal v1 v2 then
    Format.eprintf "DBG B16 stack-singleton-eq GATE-FIRED\n%!"

let debug_b16_pair ~(negate : bool) (v1 : wordset) (v2 : wordset) : unit =
  if stack_singleton v1 && stack_singleton v2 then
    Format.eprintf "DBG B16 stack-singleton-pair %s %s\n%!"
      (if WordSet.equal v1 v2 then "equal-2reach" else "distinct")
      (if negate then "neq" else "eq")

(* The coercion pass promises uniform BIR widths; a hit here is a
   contract violation answered by top.  Bounded output: the first
   [dbg_left] hits carry the exp, then silence. *)
let debug_width_mismatch op e1 e2 (v1 : wordset) (v2 : wordset) : unit =
  let w1 = WordSet.bitwidth v1 and w2 = WordSet.bitwidth v2 in
  if w1 <> w2 && !dbg_left > 0 then begin
    decr dbg_left;
    Format.eprintf "DBG denote_binop width-mismatch w1=%d w2=%d e=%s\n%!" w1
      w2 (dbg_one_line (Bil.BinOp (op, e1, e2)))
  end

(* A def's value is stored at its lhs's declared width; a divergent
   store is the source of downstream mismatches. *)
let debug_store_width (v : var) (e : exp) (p : wordset) : unit =
  let lw = match Var.typ v with Type.Imm n -> n | _ -> 0 in
  let pw = WordSet.bitwidth p in
  if lw > 0 && pw <> lw && !dbg_left > 0 then begin
    decr dbg_left;
    Format.eprintf "DBG denote_def store-width lhs=%s:%d width=%d rhs=%s\n%!"
      (Var.name v) lw pw (dbg_one_line e)
  end
#endif

(* The binop's result width: a comparison answers one bit, every other op
   carries its operands' common width. *)
let binop_result_width (op : Bil.binop) (w1 : int) (w2 : int) : int =
  match op with
  | Bil.EQ | Bil.NEQ | Bil.LT | Bil.LE | Bil.SLT | Bil.SLE -> 1
  | _ -> Stdlib.max w1 w2

let b1_set = WordSet.singleton Cbat_word.b1
let b0_set = WordSet.singleton Cbat_word.b0

(* The width-1 shapes the comparison rows return, built once — the
   hottest solver function reads these on every row. *)
let bool_row = (b1_set, b0_set, WordSet.top 1, WordSet.bottom 1)

let denote_binop (op : Bil.binop) : wordset -> wordset -> wordset =
  let btrue, bfalse, bool_top, bool_bottom = bool_row in
  let wordset_of_bool b = if b then btrue else bfalse in
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
    (* Same-origin relatives compare by their offsets: a single offset on
       each side pins the one concrete address, so equality is decidable
       even though the saturated stack cardinality hides it (LT already
       reads the same line through plain_bounds). *)
    let rel_singleton (v : wordset) : (Hike_origin.t * Cbat_word.t) option =
      match WordSet.origin v, WordSet.relative_offsets v with
      | Some o, Some offs ->
        (match Cbat_clp.Pieces.min_elem_signed offs, Cbat_clp.Pieces.max_elem_signed offs with
         | Some lo, Some hi when Cbat_word.equal lo hi -> Some (o, lo)
         | _ -> None)
      | _ -> None in
    match rel_singleton v1, rel_singleton v2 with
    | Some (o1, a), Some (o2, b) when Hike_origin.equal o1 o2 ->
      wordset_of_bool (if negate then not (Cbat_word.equal a b) else Cbat_word.equal a b)
    | _ ->
    (let v1_size = WordSet.cardinality v1 in
    let v2_size = WordSet.cardinality v2 in
    if Cbat_word.is_zero v1_size || Cbat_word.is_zero v2_size then bool_bottom
    else if Word_ops.is_one v1_size && Word_ops.is_one v2_size then begin
#ifdef VSA_DEBUG
      debug_b16_eq v1 v2;
#endif
      wordset_of_bool
        (if negate then not (WordSet.equal v1 v2) else WordSet.equal v1 v2)
    end
    else if WordSet.overlap v1 v2 then begin
#ifdef VSA_DEBUG
      debug_b16_pair ~negate v1 v2;
#endif
      bool_top
    end
    else if negate then btrue else bfalse)
  in
  let op_fn : wordset -> wordset -> wordset =
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
  in
  fun v1 v2 ->
    (* The coercion pass makes every binop's operand widths uniform; a
       divergence is its contract violation, answered by the identity. *)
    let w1 = WordSet.bitwidth v1 in
    let w2 = WordSet.bitwidth v2 in
    if w1 <> w2 then WordSet.top (binop_result_width op w1 w2)
    else op_fn v1 v2

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

let val_top : typ -> val_t or_type_error = function
  | Type.Imm i -> Ok (`Word (WordSet.top i))
  | Type.Mem (addr_sz, addressable_sz) ->
    let k = mem_idx addr_sz addressable_sz in
    Ok (`Mem (Mem.top k))
  | Type.Unk -> Error Type.Error.bad_imm

(* An image-backed section: [img_lo..img_hi] are the span's inclusive
   address bounds, [img_bytes] the section's static content, [img_slots]
   the linker-owned slot addresses inside the span — a slot's value the
   dynamic linker writes at startup, so the file bytes there are not a
   value.  The pass entry threads only sections whose runtime content
   IS the image. *)
type section_image =
  { img_lo : int64;
    img_hi : int64;
    img_bytes : Bytes.t;
    img_slots : Int64.Set.t }

let section_images_ref : section_image list ref = ref []

(* Threads the image-backed sections in. *)
let set_section_images (imgs : section_image list) : unit =
  section_images_ref := imgs

(* Runs [f] with [imgs] armed, restoring the surrounding images on every exit. *)
let with_images (imgs : section_image list) (f : unit -> 'a) : 'a =
  let surrounding = !section_images_ref in
  section_images_ref := imgs;
  match f () with
  | v -> section_images_ref := surrounding; v
  | exception e -> section_images_ref := surrounding; raise e

(* The image's [bits]-bit word at byte offset [off], assembled in the
   load's endianness; [None] when the bytes leave the array. *)
let image_raw (bytes : Bytes.t) (off : int) ~(endian : endian)
    ~(bits : int) : int64 option =
  let nb = bits / 8 in
  if
    bits <= 0 || bits > 64 || bits mod 8 <> 0 || off < 0
    || off + nb > Bytes.length bytes
  then None
  else
    let v =
      let le = match endian with LittleEndian -> true | BigEndian -> false in
      match nb with
      | 1 -> Stdlib.Int64.of_int (Stdlib.Bytes.get_uint8 bytes off)
      | 2 ->
        Stdlib.Int64.of_int
          (if le then Stdlib.Bytes.get_uint16_le bytes off
           else Stdlib.Bytes.get_uint16_be bytes off)
      | 4 ->
        let x =
          if le then Stdlib.Bytes.get_int32_le bytes off
          else Stdlib.Bytes.get_int32_be bytes off in
        Stdlib.Int64.logand (Stdlib.Int64.of_int32 x) 0xFFFF_FFFFL
      | 8 ->
        if le then Stdlib.Bytes.get_int64_le bytes off
        else Stdlib.Bytes.get_int64_be bytes off
      | _ ->
        let rec go i acc =
          if i >= nb then acc
          else
            let b = Stdlib.Int64.of_int (Char.to_int (Bytes.get bytes (off + i))) in
            let sh = match endian with
              | LittleEndian -> 8 * i
              | BigEndian -> 8 * (nb - 1 - i) in
            go (i + 1) (Stdlib.Int64.logor acc (Stdlib.Int64.shift_left b sh))
        in
        go 0 0L
    in
    Some v

let image_word (bytes : Bytes.t) (off : int) ~(endian : endian)
    ~(bits : int) : Cbat_word.t option =
  Option.map (image_raw bytes off ~endian ~bits) ~f:(fun v ->
      Cbat_word.of_int64 ~width:bits v)

(* An address set the image rule can enumerate exactly; a dispatch table
   (wc, cksum: 109 entries) must fit. *)
let image_load_card_cap = 4096

(* The image-backed load: an address set fully bounded inside ONE
   threaded image, with no stored cell intersecting the access extent
   and an enumerable address set, reads the image's bytes — the exact
   value set.  Anything else keeps the abstract read. *)

(* The image arm's address preconditions: a bounded, non-stack,
   byte-width set the enumerate-and-read can walk. *)
let image_address_ok (addr : wordset) (bits : int) : bool =
  bits > 0 && bits <= 64
  && not (WordSet.is_top addr)
  && not (WordSet.is_bottom addr)
  && not (WordSet.is_infinite addr)
  && Option.is_none (WordSet.stack_offsets addr)
  && not (WordSet.in_stack_segment addr)

(* The enumerate-and-read: each enumerated address reads its image
   word; one unreadable word or one linker-owned slot address refuses
   the arm for the whole set — a slot's value is the loader's, never
   the file bytes. *)
let read_image_words ~(img_bytes : Bytes.t) ~(img_lo : int64)
    ~(slots : Int64.Set.t)
    ~(endian : endian) ~(bits : int) (addr : wordset) : wordset option =
  let exception Unreadable in
  try
    let words =
      Cbat_clp.Exact.of_iter ~width:bits ~iter:(fun emit ->
          List.iter (WordSet.iter addr) ~f:(fun a ->
              match Cbat_word.to_int64_opt a with
              | None -> raise Unreadable
              | Some ai ->
                if Core.Set.mem slots ai then raise Unreadable;
                match
                  image_word img_bytes
                    (Stdlib.Int64.to_int (Stdlib.Int64.sub ai img_lo))
                    ~endian ~bits
                with
                | None -> raise Unreadable
                | Some w -> emit w)) in
    Some (WordSet.of_exact words)
  with Unreadable -> None

let image_holding (img : section_image) ~(lo : int64) ~(last : int64) : bool =
  Stdlib.Int64.unsigned_compare lo img.img_lo >= 0
  && Stdlib.Int64.unsigned_compare last img.img_hi <= 0

(* The one image that backs the whole read span [lo_a, hi_a + nb - 1]
   when no stored cell intersects the access extent: [read] then runs on
   it.  [None] when the span wraps, no image holds it, or a cell
   intersects it. *)
let in_one_image ~(find : lo:int64 -> last:int64 -> section_image option)
    ~(mn_w : Cbat_word.t Lazy.t)
    ~(origin : Hike_origin.t option) ~(lo_a : int64) ~(hi_a : int64)
    ?(cell_free = false) ~(nb : int) (mv : Mem.t)
    ~(read : section_image -> 'a option) : 'a option =
  let last = Stdlib.Int64.add hi_a (Stdlib.Int64.of_int (nb - 1)) in
  if Stdlib.Int64.unsigned_compare last hi_a < 0 then None
  else
    match find ~lo:lo_a ~last with
    | None -> None
    | Some img ->
      let last_w = Cbat_word.of_int64 ~width:64 last in
      if
        (not cell_free)
        && Mem.has_cell_in mv
             ~origin:(Option.bind origin ~f:WordSet.key_line)
             ~lo:(Lazy.force mn_w) ~hi:last_w
      then None
      else read img

let section_image_load ~(addr : wordset) ~(endian : endian) ~(bits : int)
    (mv : Mem.t) : wordset option =
  (* A live (non-bottom) memory reads top where no cell covers the
     bytes; a bottom memory — the unreached state's default — keeps
     the load's own abstract value. *)
  if Mem.is_bottom mv then None
  else
    match !section_images_ref with
    | [] -> None
    | images ->
      if not (image_address_ok addr bits) then None
      else
        let mn_w = WordSet.min_elem addr and mx_w = WordSet.max_elem addr in
        match
          Base.Option.bind mn_w ~f:Cbat_word.to_int64_opt, Base.Option.bind mx_w ~f:Cbat_word.to_int64_opt
        with
        | Some lo_a, Some hi_a ->
          in_one_image
            ~find:(fun ~lo ~last ->
                Base.List.find images ~f:(image_holding ~lo ~last))
            ~mn_w:(Lazy.from_val (Option.value_exn mn_w))
            ~origin:(WordSet.origin addr) ~lo_a ~hi_a ~nb:(bits / 8) mv
            ~read:(fun { img_lo; img_bytes; img_slots; _ } ->
              if Cbat_word.gt_int (WordSet.cardinality addr) image_load_card_cap
              then None
              else
                (* Every enumerated address lies inside the hull, whose
                   whole extent the span check covered — the reads stay
                   in bounds. *)
                read_image_words ~img_bytes ~img_lo ~slots:img_slots
                  ~endian ~bits addr)
        | _ -> None

(* The reader of [section_image_load]'s raw image word at one plain
   address for a fixed memory and read shape: [None] where that arm
   refuses.  The point twin of the general read: it skips building the
   singleton set, and remembers the image the last read hit.  [cell_free]
   asserts that no stored cell touches the read's extent. *)
let image_point_reader ~(endian : endian) ~(bits : int) (mv : Mem.t) :
    cell_free:bool -> int64 -> int64 option =
  let images = !section_images_ref in
  if Mem.is_bottom mv || bits <= 0 || bits > 64 || List.is_empty images then
    fun ~cell_free:_ _ -> None
  else
    let hint = ref (List.hd_exn images) in
    let find ~lo ~last =
      if image_holding !hint ~lo ~last then Some !hint
      else
        match Base.List.find images ~f:(image_holding ~lo ~last) with
        | Some img as r -> hint := img; r
        | None -> None in
    fun ~cell_free a ->
      in_one_image ~find
        ~mn_w:(lazy (Cbat_word.of_int64 ~width:64 a))
        ~origin:None ~lo_a:a ~hi_a:a ~cell_free ~nb:(bits / 8) mv
        ~read:(fun { img_lo; img_bytes; img_slots; _ } ->
          if Core.Set.mem img_slots a then None
          else
            image_raw img_bytes
              (Stdlib.Int64.to_int (Stdlib.Int64.sub a img_lo))
              ~endian ~bits)

(* The value a read of [bits] at [addr] produces in [mv]: the image
   words where one image backs the whole set, else the join of the cells
   the bounded address set can touch — a strided set names its slots, a
   contiguous band's range key covers the read (find' expands the query
   by the size).  A bounded set no key names reads bottom on a bottom
   memory (the path is already dead) and top — the sound identity — on
   a live one; top also when nothing bounds the address.  The first
   cell's data seeds the fold: join's identity is the seed, so a stored
   relative value reads back with its origin, and multi-cell joins merge
   per the algebra. *)
let load_value ~(addr : wordset) ~(endian : endian) ~(bits : int) (mv : Mem.t) : wordset =
  (* The ABI TCB self cell holds the thread pointer, including after a
     foreign call has invalidated ordinary memory facts. *)
  if bits = WordSet.bitwidth addr
     && not (Mem.is_bottom mv)
     && Option.equal Hike_origin.equal (WordSet.origin addr) (Some Hike_origin.Fs)
     && Option.value_map (WordSet.relative_offsets addr) ~default:false
          ~f:(fun offs -> Cbat_clp.Pieces.equal offs
              (Cbat_clp.Pieces.singleton (Cbat_word.zero bits)))
     && not (Mem.has_cell_in mv ~origin:(Some Hike_origin.Fs)
               ~lo:(Cbat_word.zero bits)
               ~hi:(Cbat_word.of_int ~width:bits (bits / 8 - 1)))
  then addr else
  match section_image_load ~addr ~endian ~bits mv with
  | Some ws -> ws
  | None ->
    (match Mem.Key.of_wordset addr with
     | [] -> if Mem.is_bottom mv then WordSet.bottom bits else WordSet.top bits
     | k0 :: ks' ->
       Base.List.fold ks'
         ~init:(Mem.find (bits, endian) mv k0 |> Mem.Val.data)
         ~f:(fun acc k -> WordSet.join acc (Mem.find (bits, endian) mv k |> Mem.Val.data)))

(* The kind [e] denotes when its evaluation cannot fail: [`Word] or
   [`Mem], from the expression's shape and variable types alone.  [None]
   for anything that may fail or whose kind depends on values (Store,
   Ite, Let): those are evaluated in full. *)
let rec static_kind (e : exp) : [ `Word | `Mem ] option =
  let word e = match static_kind e with Some `Word -> true | _ -> false in
  match e with
  | Bil.Var v ->
    (match Var.typ v with
     | Type.Imm _ -> Some `Word
     | Type.Mem _ -> Some `Mem
     | Type.Unk -> None)
  | Bil.Int _ -> Some `Word
  | Bil.BinOp (_, a, b) | Bil.Concat (a, b) ->
    if word a && word b then Some `Word else None
  | Bil.UnOp (_, a) | Bil.Cast (_, _, a) | Bil.Extract (_, _, a) ->
    if word a then Some `Word else None
  | Bil.Load (m, a, _, _) ->
    (match static_kind m with
     | Some `Mem when word a -> Some `Word
     | _ -> None)
  | Bil.Unknown (_, Type.Imm _) -> Some `Word
  | Bil.Unknown (_, Type.Mem _) -> Some `Mem
  | Bil.Unknown (_, Type.Unk) | Bil.Store _ | Bil.Ite _ | Bil.Let _ -> None

(* Whether a stored address is provably inside the sub's own frame
   below entry: a Stack-origin value whose offset hull has a signed
   maximum below the entry word.  The caller's frame, a foreign or mixed
   address and TOP are outside. *)
let in_own_frame (addr : wordset) : bool =
  Option.equal Hike_origin.equal (WordSet.origin addr) (Some Hike_origin.Stack)
  && Option.value_map (WordSet.stack_offsets addr) ~default:false
       ~f:(fun hull ->
           Option.value_map (Cbat_clp.Pieces.max_elem_signed hull)
             ~default:false
             ~f:(fun hi ->
                 Option.value_map (Cbat_word.to_int64_opt hi) ~default:false
                   ~f:Int64.is_negative))

(* [escaped] is raised by a store that puts a stack address where a
   callee may reach it: the data has a stack leaf and the address is not
   in the sub's own frame below entry.  [denote_exp] discards it;
   [denote_def] folds it into the state. *)
(* The bit range a narrowing cast keeps; other casts keep none. *)
let narrowing_range (ct : Bil.cast) ~(sz : int) ~(width : int) : (int * int) option =
  if sz <= 0 || sz >= width then None
  else
    match ct with
    | Bil.LOW -> Some (sz - 1, 0)
    | Bil.HIGH -> Some (width - 1, width - sz)
    | Bil.UNSIGNED | Bil.SIGNED -> None

(* A read of bits [lo..hi] of a variable: the extract of its set met with
   the slice recorded for that range.  Both over-approximate the same
   bits; an empty meet is not read as an unreachable state. *)
let slice_read (env : AI.t) (e : exp) ~(hi : int) ~(lo : int) (r : WordSet.t) :
    WordSet.t =
  match e with
  | Bil.Var x ->
    let s = AI.find_slice env x ~hi ~lo in
    if WordSet.is_top s || WordSet.bitwidth s <> WordSet.bitwidth r then r
    else
      let m = WordSet.meet r s in
      if Cbat_word.is_zero (WordSet.cardinality m) then r else m
  | _ -> r

let rec denote_exp_escaping ~(synth : Hike_synth.table)
    ~(escaped : bool ref) (e : exp) (env : AI.t) :
    val_t or_type_error =
  let denote_exp = denote_exp_escaping ~synth ~escaped in
  let open Monad_type_error in
  let monadic_assert (b : bool) (err : Type.error) =
    if b then !!() else fail err in
  let return_imm (v : wordset) = return @@ `Word v in
  let return_mem (v : Mem.t) = return @@ `Mem v in
  match e with
  | Bil.Var v -> begin match Var.typ v with
    | Type.Imm bitwidth ->
      (match Hike_synth.module_addr_of synth v with
       | Some a when bitwidth = 64 -> return_imm (WordSet.module_address a)
       | Some a ->
         return_imm (WordSet.singleton
                       (Cbat_word.of_int64 ~width:bitwidth a))
       | None ->
         match Hike_synth.thread_addr_of synth v with
         | Some off -> return_imm (WordSet.set_origin Hike_origin.Fs
                                    (WordSet.stack_word_i64 off))
         | None -> return_imm @@ AI.find_word bitwidth env v)
    | Type.Mem (addr_i, addressable_size) ->
      let k = mem_idx addr_i addressable_size in
      return_mem @@ AI.find_memory k env v
    | Type.Unk -> Error Type.Error.bad_imm
    end
  | Bil.Int bv -> return_imm @@ WordSet.singleton (Cbat_word.of_word bv)
  | Bil.BinOp (op, e1, e2) ->
    denote_exp e1 env >>= val_as_imm >>= fun v1 ->
    denote_exp e2 env >>= val_as_imm >>= fun v2 ->
#ifdef VSA_DEBUG
    debug_width_mismatch op e1 e2 v1 v2;
#endif
    return_imm @@ denote_binop op v1 v2
  | Bil.Load (m, a, e, s) ->
    denote_exp a env >>= val_as_imm >>= fun addr ->
    denote_exp m env >>= val_as_mem >>= fun mv ->
    let res_size = Size.in_bits s in
    return_imm (load_value ~addr ~endian:e ~bits:res_size mv)
  | Bil.Store (m, a, u, e, s) ->
    Type.infer u >>= fun u_typ ->
    let sz = Size.in_bits s in
    let exp = Type.imm sz in
    let u_type_error = Type.Error.bad_type ~exp ~got:u_typ in
    monadic_assert Type.(exp = u_typ) u_type_error >>= fun () ->
    denote_exp a env >>= val_as_imm >>= fun addr ->
    denote_exp m env >>= val_as_mem >>= fun mv ->
    denote_exp u env >>= val_as_imm >>= fun v ->
    if (not (Base.List.is_empty (WordSet.stack_leaves v))) && not (in_own_frame addr)
    then escaped := true;

    if WordSet.is_top addr
    (* The store may write any cell: whole-memory top. *)
    then return_mem @@ Mem.top (Mem.get_idx mv)
    else
    
    (* One point address overwrites its cell; every key of a larger
       address set is a weak update (the store hits one of them). *)
    let data = Mem.Val.create v e in
    let keys = Mem.Key.of_wordset addr in
    let strong = match keys with [ _ ] -> true | _ -> false in
    return_mem
      @@ Base.List.fold keys ~init:mv
           ~f:(fun mv key -> Mem.store mv ~strong ~key ~data)
  | Bil.Ite (cond, yes, no) ->
    denote_exp cond env >>= val_as_imm >>= fun condv ->
    (* A decided condition evaluates the taken branch; the other runs
       only when it could fail, so its error still surfaces. *)
    let check b =
      if Option.is_some (static_kind b) then return ()
      else denote_exp b env >>| fun _ -> () in
    if WordSet.equal condv b1_set then
      denote_exp yes env >>= fun yesv -> check no >>= fun () -> return yesv
    else if WordSet.equal condv b0_set then
      check yes >>= fun () -> denote_exp no env
    else
      denote_exp yes env >>= fun yesv ->
      denote_exp no env >>= fun nov ->
      val_join yesv nov
  | Bil.Extract (hi, lo, e) ->
    denote_exp e env >>= val_as_imm >>= fun v ->
    return_imm @@ slice_read env e ~hi ~lo (WordSet.extract ~hi ~lo v)
  | Bil.Concat (e1, e2) ->
    denote_exp e1 env >>= val_as_imm >>= fun v1 ->
    denote_exp e2 env >>= val_as_imm >>= fun v2 ->
    return_imm @@ WordSet.concat v1 v2
  | Bil.UnOp (Bil.NOT, e) ->
    denote_exp e env >>= val_as_imm >>| WordSet.lnot >>= return_imm
  | Bil.UnOp (Bil.NEG, e) ->
    denote_exp e env >>= val_as_imm >>| WordSet.neg >>= return_imm
  | Bil.Cast (ct, sz, e) ->
    denote_exp e env >>= val_as_imm >>= fun v ->
    let r = WordSet.cast ct sz v in
    return_imm @@
    (match narrowing_range ct ~sz ~width:(WordSet.bitwidth v) with
     | Some (hi, lo) -> slice_read env e ~hi ~lo r
     | None -> r)
  | Bil.Let (var, value, body) ->
    denote_exp value env >>= fun v ->
    let env' = match v with
      | `Word p -> AI.add_word ~key:var ~data:p env
      | `Mem m -> AI.add_memory ~key:var ~data:m env
    in
    denote_exp body env'
  | Bil.Unknown (_,typ) -> val_top typ

let denote_exp ~(synth : Hike_synth.table) (e : exp) (env : AI.t) :
    val_t or_type_error =
  denote_exp_escaping ~synth ~escaped:(ref false) e env

let denote_imm_exp ~(synth : Hike_synth.table) (e : exp) (env : AI.t) :
    WordSet.t or_type_error =
  let open Monad_type_error in
  denote_exp ~synth e env >>= val_as_imm

(* Every def is denoted: SP-derived addresses arrive as [StackOff]
   words and memory ops key cells by their segment offsets.  A def the
   denotation cannot type adds nothing: its readers take the top
   identity. *)
let denote_def_escaping ~(synth : Hike_synth.table) ~(escaped : bool ref)
    (df : def term) (env : AI.t) :
    AI.t =
  let v = Def.lhs df in
  let e = Def.rhs df in
  match
    (let open Monad_type_error in
     denote_exp_escaping ~synth ~escaped e env >>| fun ev ->
     (match ev with
      | `Word p ->
        (* A partial-register write (EAX into RAX) zero-fills the base
           register's remaining bytes — the machine's narrow write.
           Wider-than-declared values keep their width. *)
        let p =
          match Var.typ (Var.base v) with
          | Type.Imm n when n > WordSet.bitwidth p ->
            WordSet.cast Bil.UNSIGNED n p
          | _ -> p
        in
#ifdef VSA_DEBUG
        debug_store_width v e p;
#endif
        AI.add_word env ~key:v ~data:p
      | `Mem m -> AI.add_memory env ~key:v ~data:m))
  with
  | Ok env' -> env'
  | Error err ->
    not_implemented ~top:env
      (Format.asprintf "denote_def %s: %s" (Var.name v)
         (Type.Error.to_string err))

let denote_def ~(synth : Hike_synth.table) (df : def term) (env : AI.t) : AI.t =
  let escaped = ref false in
  let env' = denote_def_escaping ~synth ~escaped df env in
  if !escaped then AI.escape_frame env' else env'

let denote_defs ~(synth : Hike_synth.table) (b : blk term) : AI.t -> AI.t =
  (* Phis are the identity. *)
  fun env0 ->
    Term.enum def_t b
    |> Seq.fold ~init:env0 ~f:(fun env df -> denote_def ~synth df env)

(* One per-block state replay: the block's defs fold [denote_def]
   from its entry state; [f] folds over each def's (before, after)
   states. *)
let fold_block_states ~(synth : Hike_synth.table)
    ~(sol : (tid, AI.t) Solution.t) (blk : blk term)
    ~(init : 'acc) ~(f : AI.t -> AI.t -> def term -> 'acc -> 'acc) :
    'acc * AI.t =
  let st_end, acc =
    Term.enum def_t blk
    |> Seq.fold ~init:(Solution.get sol (Term.tid blk), init)
         ~f:(fun (st_before, acc) d ->
             let st_after = denote_def ~synth d st_before in
             (st_after, f st_before st_after d acc))
  in
  (acc, st_end)

(* The block's last def per lhs var: the reaching def at the block's
   end. *)
let last_defs (blk : blk term) : def term Var.Map.t =
  Term.enum def_t blk
  |> Seq.fold ~init:Var.Map.empty ~f:(fun m d ->
      Core.Map.set m ~key:(Def.lhs d) ~data:d)



(* Jumps reachable in the env.  An SP-derived var's word is the
   segment base plus its exact offsets: bit tests and comparisons
   against concrete addresses decide consistently with real pointer
   behavior.  A cond whose denotation is the empty set is unreachable:
   no edge may run.  A live state that produces one is an analysis bug,
   and the decision seam says so loudly rather than widening the
   guard.  Jumps after one that always runs are not denoted. *)
let reachable_jumps_by (type a) ~(synth : Hike_synth.table)
    ~(jmp : a -> jmp term) (env : AI.t)
    (items : a seq) : a seq =
  Seq.unfold_with items ~init:true ~f:begin fun reachable item ->
    let jmp_term = jmp item in
    if not reachable then Seq.Step.Done
    else
    let cond =
      match denote_imm_exp ~synth (Jmp.cond jmp_term) env with
      | Ok c ->
          if WordSet.is_bottom c && not (AI.equal env AI.bottom) then
            failwith
              (Printf.sprintf
                 "vsa: bottom cond denotation in a live state (jmp %s)"
                 (Tid.name (Term.tid jmp_term)));
          c
      | Error _ -> WordSet.top 1
    in
    let can_fall_through = WordSet.elem Cbat_word.b0 cond in
    if WordSet.elem (Cbat_word.b1) cond then Seq.Step.Yield {value = item; state = can_fall_through}
    else Seq.Step.Skip {state = can_fall_through}
  end

let reachable_jumps ~(synth : Hike_synth.table) (env : AI.t)
    (jmps : jmp term seq) : jmp term seq =
  reachable_jumps_by ~synth ~jmp:Fn.id env jmps
