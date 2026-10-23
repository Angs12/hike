(* What survives a call: the one policy over the caller's words and
   frames at a call site. *)

open Core
open Bap.Std

module AI = Cbat_ai_representation
module Mem = Cbat_ai_memmap
module WordSet = Cbat_clp_set_composite

type site = {
  summary : Int.Set.t option;
  read_lanes : var list;
}

type callee =
  | Summary of Int.Set.t option
  | Declared of Int.Set.t option * Hike_signatures.record

(* An indirect call may name several code targets.  Every target is
   solved (or read from its final summary), and the call preserves only
   what every target preserves; one unknown target keeps the whole call
   conservative. *)
let indirect_callee ~(synth : Hike_synth.table) ~(lookup : int64 -> Tid.t option)
    ~(callee : Tid.t -> callee) ~(env : AI.t) (texp : exp) : callee =
  let written = function Summary s | Declared (s, _) -> s in
  let meet = function
    | [] -> None
    | c :: rest ->
      Base.List.fold rest ~init:(written c) ~f:(fun acc c' ->
          match acc, written c' with
          | None, _ | Some _, None -> None
          | Some a, Some b -> Some (Core.Set.inter a b))
  in
  match Cbat_transfer.denote_imm_exp ~synth texp env with
  | Error _ -> Summary None
  | Ok ws ->
    (match WordSet.enumerate ~cap:1024 ws with
     | Some [] | None -> Summary None
     | Some targets ->
       let summaries =
         Base.List.map targets ~f:(fun target ->
             match Cbat_word.to_int64_opt target with
             | None -> None
             | Some v -> Option.map (lookup v) ~f:callee)
       in
       if Base.List.exists summaries ~f:Option.is_none then Summary None
       else Summary (meet (Base.List.filter_opt summaries)))

(* Segment-relative bounds of a stack value; None when no bound exists.
   [key_extent] is the shared key-space clamp — the same rule the
   sections' attribution uses. *)
let range_of ~(width : int) (ws : WordSet.t) :
    (Cbat_word.t * Cbat_word.t) option =
  Hike_stack_bounds.key_extent ~width ws

(* The call block's bounded outgoing stack-argument hull.  The slot test
   is shared with promotion: only a singleton stack store beginning at a
   word-aligned slot above the call-time SP contributes. Store addresses
   use their before-states, before a later call push changes SP. *)
let stack_arg_ranges ~(synth : Hike_synth.table) ~(abi : Hike_abi.t) ~(block : blk term)
    ~(entry : AI.t) (env : AI.t) :
    (Cbat_word.t * Cbat_word.t) list =
  if not (Term.enum jmp_t block |> Seq.exists ~f:Hike_stack_model.machine_call)
  then []
  else
  let word_bits = Hike_abi.word_bits abi in
  let rsp = AI.find_word word_bits env abi.Hike_abi.sp in
  match Hike_stack_model.singleton_stack_position rsp with
  | None -> []
  | Some call_sp ->
    let ranges =
      Term.enum def_t block
      |> Seq.fold ~init:([], entry) ~f:(fun (acc, before) d ->
          let acc = match Hike_stack_model.addr_of_rhs (Def.rhs d),
                Hike_stack_model.store_data_of_rhs (Def.rhs d) with
          | Some (addr, size), Some _ ->
            (match Cbat_transfer.denote_imm_exp ~synth addr before with
             | Error _ -> acc
             | Ok address ->
               (match Hike_stack_model.singleton_stack_position address with
                | Some start
                  when Option.is_some
                         (Hike_stack_model.call_arg_slot ~word:abi.Hike_abi.word
                            ~call_sp ~start) ->
                  (match range_of ~width:word_bits address with
                   | None -> acc
                   | Some (lo, hi) ->
                     let extra =
                       Cbat_word.of_int ~width:word_bits
                         (Size.in_bytes size - 1)
                     in
                     let hi' = Cbat_word.add hi extra in
                     let hi' =
                       if Cbat_word.(hi' < hi) then Cbat_word.ones word_bits
                       else hi'
                     in
                     (lo, hi') :: acc)
                | _ -> acc))
          | _ -> acc in
          (acc, Cbat_transfer.denote_def ~synth d before))
      |> fst
    in
    (match ranges with
     | [] -> []
     | (lo, hi) :: rest ->
       let lo, hi =
         List.fold rest ~init:(lo, hi) ~f:(fun (lo, hi) (lo', hi') ->
             ((if Cbat_word.(lo' < lo) then lo' else lo),
              (if Cbat_word.(hi' > hi) then hi' else hi)))
       in
       [ lo, hi ])

(* The frame-keep boundary and outgoing stack-argument ranges are
   KEY-space: stack-derived cells key by segment offsets, foreign cells
   by their concrete addresses. The callee writes below its own RSP, so
   the keep boundary is the HIGHEST possible call-time SP's position —
   an unbounded-below SP still has a highest position, and the callee
   reaches below its entry only. An unbounded-above SP keeps nothing —
   the whole-memory top stays the sound fallback on any doubt.

   Only the Stack origin certifies a frame-keep boundary. An SP without
   that proof forces whole-memory top. *)
let frame_keep ~(preserved : Int.Set.t) ~(rsp : WordSet.t)
    ~(frame_escaped : bool) ~(clear_from : Cbat_word.t option)
    ~(foreign_cells : Mem.foreign_cells)
    ~(stack_args : (Cbat_word.t * Cbat_word.t) list) (env : AI.t) : AI.t =
#ifdef VSA_DEBUG
  Cbat_attr_census.bump "call.frame";
#endif
  let env = AI.top_words_except ~preserved env in
  let keep_lo =
    (* An ascending, circular, or wrapped SP hull names no highest
       position — nothing provably survives; the top fallback below is
       the sound answer. *)
    if WordSet.is_ascending rsp || WordSet.is_circular rsp then None
    else
      match WordSet.stack_offsets rsp with
      | Some offs -> WordSet.Clp.Pieces.max_elem offs
      | None -> None
  in
#ifdef VSA_DEBUG
  Format.eprintf "DBG frame_keep escaped=%b rsp=%a keep=%s@.%!"
    frame_escaped WordSet.pp rsp
    (match keep_lo with
     | None -> "none"
     | Some lo -> Cbat_word.to_string lo);
#endif
  match keep_lo with
  | Some lo ->
#ifdef VSA_DEBUG
    Cbat_attr_census.bump "call.frame.kept";
#endif
    AI.map_memories env ~f:(fun ~key:_ ~data ->
        Mem.call_keep data ~keep_lo:lo ~stack_args
          ~clear_frame:frame_escaped ~clear_from ~foreign_cells)
  | None ->
#ifdef VSA_DEBUG
    Cbat_attr_census.bump "call.frame.top.rsp";
#endif
    AI.top_memories env

let preserved_with_summary ~(abi : Hike_abi.t) ~(preserved : Int.Set.t)
    (ws : Int.Set.t) : Int.Set.t =
  Base.List.fold abi.Hike_abi.caller_saved_gprs
    ~init:preserved ~f:(fun acc v ->
        let id = Cbat_var_id.intern v in
        if Core.Set.mem ws id then acc
        else if
          Base.List.exists abi.Hike_abi.return_regs ~f:(Var.same v)
        then acc
        else Core.Set.add acc id)

(* The integer registers that may hold a pointer at the call, each with
   the parameter whose attributes govern it: a pointer parameter (or
   one containing a pointer, or passed by reference), the hidden pointer
   of a memory return, and for a variadic call every remaining integer
   register as a pointer the callee may write and keep.  [None] when a
   parameter travels on the stack. *)
let lane_params ~(abi : Hike_abi.t) (r : Hike_signatures.record) :
    (var * Hike_signatures.param) list option =
  let open Hike_signatures in
  let call = place ~abi r in
  let register index = integer_register ~abi index in
  let any_stack =
    List.exists call.arguments ~f:(fun a ->
        match a.location with Hike_sysv.Stack _ -> true | _ -> false) in
  if any_stack then None
  else
    let declared =
      List.concat
        (List.map2_exn r.params call.arguments ~f:(fun p a ->
             match a.location with
             | Hike_sysv.Registers parts when a.indirect || carries_pointer p.ty ->
               List.filter_map parts ~f:(function
                   | Hike_sysv.Integer_register i ->
                     Option.map (register i) ~f:(fun reg -> (reg, p))
                   | Vector_register _ -> None)
             | _ -> [])) in
    let hidden =
      match call.return with
      | Hike_sysv.Returned_in_memory ->
        Option.to_list
          (Option.map (register 0) ~f:(fun reg ->
               (reg, { ty = Scalar Pointer; access = May_write; captured = false })))
      | _ -> [] in
    let tail =
      if not r.variadic then []
      else
        List.init (List.length abi.Hike_abi.int_param_regs - call.integer_registers_used)
          ~f:(fun i -> register (call.integer_registers_used + i))
        |> List.filter_map ~f:(Option.map ~f:(fun reg ->
            (reg, { ty = Scalar Pointer; access = May_write; captured = true }))) in
    Some (hidden @ declared @ tail)

(* What the pointer arguments let the callee reach. *)
type reach = {
  sticky : bool;                   (* a stack pointer the callee may keep *)
  clear_now : bool;                (* the whole frame, at this call only *)
  clear_from : Cbat_word.t option; (* the frame from this offset up *)
  written : Hike_origin.t option list;
  (* the non-stack lines a writable pointer may name; [None] = any *)
}

let no_reach = { sticky = false; clear_now = false; clear_from = None;
                 written = [] }

(* What one pointer lane adds to the reach. *)
let reach_of_lane ~(word_bits : int) ~(env : AI.t)
    ~(memory : Hike_signatures.memory) (acc : reach) (v : var)
    (p : Hike_signatures.param) : reach =
  let open Hike_signatures in
  let access =
    match memory with
    | None_ | Reads_any | Argmem Read_only -> Read_only
    | Any | Argmem _ -> p.access in
  let writes = (match access with Read_only -> false | _ -> true) in
  let groups = WordSet.address_groups (AI.find_word word_bits env v) in
  List.fold groups ~init:acc ~f:(fun acc (origin, offsets) ->
      match origin with
      | Some o when Hike_origin.names_stack_line o ->
        if p.captured then { acc with sticky = true }
        else if not writes then acc
        else
          (match WordSet.Clp.Pieces.min_elem offsets with
           | None -> { acc with clear_now = true }
           | Some lo ->
             let from = match acc.clear_from with
               | Some f when Cbat_word.(f < lo) -> f
               | _ -> lo in
             { acc with clear_from = Some from })
      | _ when not writes -> acc
      | _ -> { acc with written = origin :: acc.written })

(* A call with no usable record: every lane it reads is a pointer the
   callee may write and keep, and it may touch any memory. *)
let unknown_pointer : Hike_signatures.param =
  { ty = Scalar Pointer; access = May_write; captured = true }

(* The reach of a call and the memory it may touch.  A record narrows the
   lanes read to the declared ones and bounds the memory; without one the
   call is the unknown callee above. *)
let reach_of_call ~(abi : Hike_abi.t) ~(site : site) ~(env : AI.t)
    ~(stack_args : (Cbat_word.t * Cbat_word.t) list)
    (signature : Hike_signatures.record option) :
    reach * Hike_signatures.memory =
  let word_bits = Hike_abi.word_bits abi in
  let declared =
    Option.bind signature ~f:(fun r ->
        Option.map (lane_params ~abi r) ~f:(fun lanes -> (r, lanes))) in
  let param_of_lane, memory, variadic =
    match declared with
    | Some (r, lanes) ->
      ((fun v ->
          Option.map ~f:snd (List.find lanes ~f:(fun (reg, _) -> Var.same v reg))),
       r.memory, r.variadic)
    | None -> ((fun _ -> Some unknown_pointer), Hike_signatures.Any, false) in
  let reach =
    List.fold site.read_lanes ~init:no_reach ~f:(fun acc v ->
        match param_of_lane v with
        | Some p -> reach_of_lane ~word_bits ~env ~memory acc v p
        | None -> acc) in
  (* A variadic call's outgoing stack area is read as pointers too. *)
  let area_pointers =
    variadic
    && AI.exists_memory env ~f:(fun m ->
        List.exists (Mem.stack_arg_vals m ~stack_args) ~f:(fun v ->
            not (Base.List.is_empty (WordSet.stack_leaves (Mem.Val.data v))))) in
  ({ reach with sticky = reach.sticky || area_pointers }, memory)

(* The non-stack cells a call leaves, from the memory it may touch and
   the lines its writable pointers name. *)
let foreign_cells_of ~(memory : Hike_signatures.memory) (reach : reach) :
    Mem.foreign_cells =
  match memory with
  | Hike_signatures.Any -> Mem.Drop_all
  | None_ | Reads_any | Argmem Read_only -> Mem.Keep_if (fun _ -> true)
  | Argmem _ ->
    if List.exists reach.written ~f:Option.is_none
    then Mem.Drop_all
    else
      (* An absolute cell may alias a module or thread address, so any
         named line drops it. *)
      Mem.Keep_if (fun o ->
          Base.List.is_empty reach.written
          || Option.exists o ~f:(fun o ->
              not (List.exists reach.written ~f:(fun w ->
                  Option.exists w ~f:(Hike_origin.equal o)))))

(* The call's result lane takes the value of the parameter the record
   says it returns. *)
let returned_value ~(abi : Hike_abi.t) ~(site : site) ~(env : AI.t)
    (signature : Hike_signatures.record option) (result : var option) :
    (var * WordSet.t) option =
  match signature, result with
  | Some ({ Hike_signatures.returned = Some k; _ } as r), Some rv
    when Option.is_some (lane_params ~abi r) ->
    let call = Hike_signatures.place ~abi r in
    let register =
      Option.bind (List.nth call.arguments k) ~f:(fun a ->
          match a.location with
          | Hike_sysv.Registers (Hike_sysv.Integer_register i :: _) ->
            Hike_signatures.integer_register ~abi i
          | _ -> None) in
    Option.bind register ~f:(fun reg ->
        List.find site.read_lanes ~f:(fun v -> Var.same v reg))
    |> Option.map ~f:(fun lane ->
        (rv, AI.find_word (Hike_abi.word_bits abi) env lane))
  | _ -> None

let transfer ?kept ?(stack_args = []) ?signature ?result ~(abi : Hike_abi.t)
    ~(preserved : Int.Set.t) ~(site : site) (env : AI.t) : AI.t =
  let word_bits = Hike_abi.word_bits abi in
  (* A callee's kill summary keeps the caller-saved GPRs it provably
     never writes; the return regs are the call's own lanes.  No
     summary keeps only the base set. *)
  let preserved =
    match kept, site.summary with
    | Some k, _ -> k
    | None, Some ws -> preserved_with_summary ~abi ~preserved ws
    | None, None -> preserved
  in
  let reach, memory = reach_of_call ~abi ~site ~env ~stack_args signature in
  let returned = returned_value ~abi ~site ~env signature result in
  (* Once raised, the sticky bit survives every later call in the sub. *)
  let frame_escaped = AI.frame_escaped env || reach.sticky in
  let env = if reach.sticky then AI.escape_frame env else env in
  (* Every call clears the outgoing stack-argument hull.  Once any frame
     address escaped, the simple rule clears the whole retained frame. *)
  let after =
    frame_keep ~preserved
      ~rsp:(AI.find_word word_bits env abi.Hike_abi.sp)
      ~frame_escaped:(frame_escaped || reach.clear_now)
      ~clear_from:reach.clear_from
      ~foreign_cells:(foreign_cells_of ~memory reach)
      ~stack_args env in
  match returned with
  | Some (rv, value) -> AI.add_word after ~key:rv ~data:value
  | None -> after
