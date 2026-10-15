(* Simon & King landmark widening: excluded boundaries are recorded at the
   enclosing cycle head; the head extrapolates toward them.  One table
   serves every key — a word at a head, or a memory cell at a head. *)

open Bap.Std
open Core

(* Per-(key, bound, is_upper) entry; smaller distance wins. *)
type lm_entry = {
  bound : Cbat_word.t;
  is_upper : bool;
  mutable dist : int option;   (* current distance *)
  mutable dist_p : int option;  (* previous distance *)
}

(* Distance readings cap at 2^40. *)
let max_landmark_distance = 1 lsl 40
let cap_distance (d : int) : int = min d max_landmark_distance
(* The distance from [a] to [b] on the counter's own (signed) line: a
   counter walking toward a negative boundary reads small, not as a
   2^width jump.  Unrepresentable distances cap. *)
let distance_words (a : Cbat_word.t) (b : Cbat_word.t) : int =
  match Cbat_word.to_int64 (Cbat_word.sub b a) with
  | Ok d ->
    (* [Int64.abs] overflows exactly at [min_int] (a 2^63 difference). *)
    let mag =
      if Int64.equal d Int64.min_value then Int64.max_value else Int64.abs d
    in
    if Int64.compare mag (Int64.of_int max_landmark_distance) < 0
    then Int64.to_int_exn mag
    else max_landmark_distance
  | Error _ -> max_landmark_distance

(* The cell a landmark is about: the memory key's byte hull (each end as
   width/value) and stride — per-stride cells keep their own rows. *)
type cell_desc = {
  origin : Hike_origin.t;
  lo_width : int;
  lo_value : int64;
  hi_width : int;
  hi_value : int64;
  stride : int;
}

let equal_cell (a : cell_desc) (b : cell_desc) : bool =
  Hike_origin.equal a.origin b.origin
  && Int.equal a.lo_width b.lo_width && Stdlib.Int64.equal a.lo_value b.lo_value
  && Int.equal a.hi_width b.hi_width && Stdlib.Int64.equal a.hi_value b.hi_value
  && Int.equal a.stride b.stride

(* What a landmark is about: a variable at the head, or a memory cell at
   the head.  The head is the table's outer key (the cycle owns its
   rows); the key is the base variable — a versioned var names the same
   abstract value. *)
type key = Word of var | Cell of cell_desc

let norm_key (k : key) : key =
  match k with Word v -> Word (Var.base v) | Cell _ -> k

let equal_key (a : key) (b : key) : bool =
  match norm_key a, norm_key b with
  | Word x, Word y -> Var.same x y
  | Cell x, Cell y -> equal_cell x y
  | Word _, Cell _ | Cell _, Word _ -> false

let kind_of_key (k : key) : string =
  match k with Word _ -> "word" | Cell _ -> "cell"

#ifdef VSA_DEBUG
let steps_census : (string, int) Hashtbl.t = Hashtbl.create (module String)

let bump_steps (k : string) : unit =
  Hashtbl.update steps_census k ~f:(function Some n -> n + 1 | None -> 1)

let () =
  at_exit (fun () ->
      Hashtbl.to_alist steps_census
      |> List.sort ~compare:(fun (a, _) (b, _) -> String.compare a b)
      |> List.iter ~f:(fun (k, n) -> Printf.eprintf "hike-lm-steps: %s=%d\n%!" k n))
#endif

(* One row per key at a head; a new entry appends, so the oldest entry is
   the list's head. *)
type row = { key : key; entries : lm_entry list }

(* The per-solve landmark table: one row list per head. *)
type t = {
  rows : (Tid.t, row list) Hashtbl.t;
  mutable widening_at_head : Tid.t option;  (* head currently widened; None outside a cycle *)
}

(* One fresh table per solve — the widening state is the run's, never
   the process's. *)
let create () : t =
  { rows = Hashtbl.create (module Tid); widening_at_head = None }

(* Run [f] with [head] widened; the previous head is restored. *)
let with_widening_head (t : t) (head : Tid.t option) (f : unit -> 'a) : 'a =
  let prev = t.widening_at_head in
  t.widening_at_head <- head;
  Fun.protect ~finally:(fun () -> t.widening_at_head <- prev) f

(* The row [key] holds at [head], if any. *)
let find_row (t : t) (h : Tid.t) (key : key) : row option =
  Option.bind (Hashtbl.find t.rows h)
    ~f:(List.find ~f:(fun r -> equal_key r.key key))

(* Entries recorded for [key] at [head]. *)
let entries (t : t) (h : Tid.t) (key : key) : lm_entry list =
  Option.value_map (find_row t h key) ~default:[] ~f:(fun r -> r.entries)

(* Every key recorded at [head], oldest row first. *)
let keys_at (t : t) (h : Tid.t) : key list =
  Option.value_map (Hashtbl.find t.rows h) ~default:[]
    ~f:(List.map ~f:(fun r -> r.key))

(* No entry cap.  The upsert keeps one entry per (bound, is_upper) with the
   smallest distance, so a row grows only with the distinct boundaries its
   key is measured against — and the same-line acquisition guard is what
   keeps those stable.  A head that grinds to the visit budget is bounded
   by that budget, not by a cap here. *)

(* The upsert: one entry per (bound, is_upper); a smaller distance wins and
   the history is preserved — only [advance] rotates it. *)
let upsert (entries : lm_entry list) (entry : lm_entry) : lm_entry list =
  let same (e : lm_entry) =
    Cbat_word.equal e.bound entry.bound && Bool.equal e.is_upper entry.is_upper
  in
  if List.exists entries ~f:same then
    List.map entries ~f:(fun e ->
        if not (same e) then e
        else
          let keep =
            match e.dist, entry.dist with
            | None, _ | _, None -> true
            | Some d1, Some d2 -> d2 < d1
          in
          if keep then { entry with dist_p = e.dist_p } else e)
  else entries @ [ entry ]

let record (t : t) ~(head : Tid.t) ~(key : key) ~(bound : Cbat_word.t)
    ~(is_upper : bool) ~(warmed : bool) ~(dist : int) : unit =
  (* A narrowed entry is never fresh: it carries its own reading as the
     prior, so it cannot hold a head in the non-widening [Zero] arm; a
     closer later reading pairs against it. *)
  let entry =
    { bound; is_upper; dist = Some dist;
      dist_p = if warmed then Some dist else None } in
  let rows = Option.value (Hashtbl.find t.rows head) ~default:[] in
  let rows =
    if Option.is_some (find_row t head key) then
      List.map rows ~f:(fun (r : row) ->
          if equal_key r.key key then { r with entries = upsert r.entries entry }
          else r)
    else rows @ [ { key; entries = [ entry ] } ]
  in
#ifdef VSA_DEBUG
  bump_steps (Printf.sprintf "recorded.%s" (kind_of_key key));
#endif
  Hashtbl.set t.rows ~key:head ~data:rows

(* Two values live on the same coordinate line: an excluded set from a
   different line is a category mismatch, not a disabled behavior. *)
let same_line (a : Cbat_clp_set_composite.t) (b : Cbat_clp_set_composite.t) :
    bool =
  match Cbat_clp_set_composite.origin a, Cbat_clp_set_composite.origin b with
  | Some oa, Some ob ->
    Hike_origin.equal (Cbat_clp_set_composite.key_line oa)
      (Cbat_clp_set_composite.key_line ob)
  | None, None -> true
  | Some _, None | None, Some _ -> false

(* The prior set lies wholly outside the constraint: the excluded boundary
   is the constraint's own edge, and the distance is the walk to it.  The
   same rule for every key. *)
let record_excluded (t : t) ~(head : Tid.t) ~(key : key)
    ~(p : Cbat_clp_set_composite.t) ~(cstr : Cbat_clp_set_composite.t) : bool =
  match Cbat_clp_set_composite.min_elem p, Cbat_clp_set_composite.max_elem p,
        Cbat_clp_set_composite.min_elem cstr, Cbat_clp_set_composite.max_elem cstr with
  | Some p_min, Some p_max, Some c_min, Some c_max ->
    if Cbat_word.(<) p_max c_min then begin
      (* Set below the boundary: upper landmark. *)
      let d = distance_words p_max c_min in
      record t ~head ~key ~bound:c_min ~is_upper:true ~warmed:false
        ~dist:(cap_distance d);
      true
    end else if Cbat_word.(>) p_min c_max then begin
      (* Set above the boundary: lower landmark. *)
      let d = distance_words c_max p_min in
      record t ~head ~key ~bound:c_max ~is_upper:false ~warmed:false
        ~dist:(cap_distance d);
      true
    end else false
  | _ -> false

(* The meet kept a proper subset: the discarded piece is the disabled
   behavior — its near boundary is the landmark. *)
let record_narrowed (t : t) ~(head : Tid.t) ~(key : key)
    ~(p : Cbat_clp_set_composite.t) ~(m : Cbat_clp_set_composite.t) : bool =
  match Cbat_clp_set_composite.min_elem p, Cbat_clp_set_composite.max_elem p,
        Cbat_clp_set_composite.min_elem m, Cbat_clp_set_composite.max_elem m with
  | Some p_min, Some p_max, Some m_min, Some m_max ->
#ifdef VSA_DEBUG
    bump_steps (Printf.sprintf "recorded.%s.narrowed" (kind_of_key key));
#endif
    if Cbat_word.(<) p_min m_min then begin
      let bound = Cbat_word.pred m_min in
      let d = distance_words p_min bound in
      record t ~head ~key ~bound ~is_upper:false ~dist:(cap_distance d) ~warmed:true;
      true
    end else if Cbat_word.(>) p_max m_max then begin
      let bound = Cbat_word.succ m_max in
      let d = distance_words bound p_max in
      record t ~head ~key ~bound ~is_upper:true ~dist:(cap_distance d) ~warmed:true;
      true
    end else false
  | _ -> false

(* Record an excluded behavior's boundary at the enclosing head.  The head
   check comes first — outside a cycle the meet below is pure computation
   whose result is discarded — then the line guard: an excluded set from a
   different coordinate line is a category mismatch, not a behavior, and
   its "boundary" travels with the state.  Then the discarded region is the
   landmark, whether the meet emptied the prior set or trimmed it.  [true]
   when one was recorded. *)
let observe_unsat (t : t) ~(key : key)
    ~(p : Cbat_clp_set_composite.t) ~(cstr : Cbat_clp_set_composite.t) : bool =
  if Cbat_clp_set_composite.bitwidth p <> Cbat_clp_set_composite.bitwidth cstr
  then false
  else
    match t.widening_at_head with
    | None ->
      (* Outside a cycle: no-op. *)
      false
    | Some h ->
      if not (same_line p cstr) then false
      else
        let m = Cbat_clp_set_composite.meet p cstr in
        if not (Cbat_clp_set_composite.is_bottom m) then
          record_narrowed t ~head:h ~key ~p ~m
        else record_excluded t ~head:h ~key ~p ~cstr

(* Steps until the closest landmark; Zero needs another measurement, Inf
   widens.  Only an entry holding a fresh measurement speaks: an entry
   already consumed by [advance] carries no reading, and a table keeps
   entries whose boundary the guard stopped reaching — neither may hold
   the head in [Zero], which never widens. *)
let steps_of_entries (lst : lm_entry list) :
    [> `Zero | `Finite of int | `Inf ] =
  let fresh = List.filter lst ~f:(fun e -> Option.is_some e.dist) in
  let steps =
    List.filter_map fresh ~f:(fun e ->
        match e.dist_p, e.dist with
        | Some dp, Some dc when dp > dc -> Some (dc / (dp - dc))
        | _ -> None)
  in
  if List.exists fresh ~f:(fun e -> Option.is_none e.dist_p) then `Zero
  else if List.is_empty steps then `Inf
  else `Finite (List.min_elt steps ~compare:Int.compare |> Option.value_exn)

#ifdef VSA_DEBUG
(* Which shape the entries are in — how many the row holds, how many carry
   a fresh reading, and whether the distances move — and which arm they
   answered for.  [kind] is the key kind, or "head" for the fold. *)
let note_steps (kind : string) (lst : lm_entry list)
    (answer : [ `Zero | `Finite of int | `Inf ]) : unit =
  let fresh = List.filter lst ~f:(fun e -> Option.is_some e.dist) in
  bump_steps
    (Printf.sprintf "table.%s.%d.%s" kind (List.length lst)
       (if List.is_empty lst then "empty"
        else if List.is_empty fresh then "stale"
        else if List.exists fresh ~f:(fun e -> Option.is_none e.dist_p) then "warm"
        else "live"));
  List.iter fresh ~f:(fun e ->
      match e.dist_p, e.dist with
      | Some dp, Some dc ->
        bump_steps
          (Printf.sprintf "%s.%s" kind
             (if dp > dc then "live.shrink" else "live.hold"))
      | _ -> ());
  match answer with
  | `Finite _ -> bump_steps (Printf.sprintf "fire.finite.%s" kind)
  | `Zero -> bump_steps (Printf.sprintf "fire.zero.%s" kind)
  | `Inf ->
    bump_steps
      (Printf.sprintf "fire.inf.%s.%s" kind
         (if List.is_empty fresh then "stale" else "held"))
#endif

let steps (t : t) (h : Tid.t) (key : key) :
    [> `Zero | `Finite of int | `Inf ] =
  let lst = entries t h key in
  let answer = steps_of_entries lst in
#ifdef VSA_DEBUG
  note_steps (kind_of_key key) lst answer;
#endif
  answer

(* The arm a key consumes: extrapolate by [Finite n] steps, advance and
   join on [Zero], plain-widen on [Inf]. *)
type arm = Finite of int | Zero | Inf

let equal_arm (a : arm) (b : arm) : bool =
  match a, b with
  | Zero, Zero | Inf, Inf -> true
  | Finite x, Finite y -> Int.equal x y
  | _ -> false

(* The head's own arm: its word keys' entries folded, so the caller's
   decision keeps the shape it had when the table was per head.  It is
   the FALLBACK a key consumes when its own arm is [Inf] — a
   computation of [n], never a scope change: consumption is always the
   key's own row. *)
let head_arm (t : t) (h : Tid.t) : arm =
  let lst =
    List.concat_map (keys_at t h) ~f:(fun k ->
        match k with Word _ -> entries t h k | Cell _ -> [])
  in
  let answer = steps_of_entries lst in
#ifdef VSA_DEBUG
  note_steps "head" lst answer;
#endif
  match answer with
  | `Finite n -> Finite n
  | `Zero -> Zero
  | `Inf -> Inf

(* The rotation: the current reading becomes the previous one.  An entry
   with no fresh reading keeps the history it holds — erasing it would
   drop a measurement the next reading must pair against. *)
let rotate (entries : lm_entry list) : unit =
  List.iter entries ~f:(fun entry ->
      (match entry.dist with
       | Some d -> entry.dist_p <- Some d
       | None -> ());
      entry.dist <- None)

(* Commit one key's current distances as previous. *)
let advance (t : t) (h : Tid.t) (key : key) : unit =
  Option.iter (find_row t h key) ~f:(fun r -> rotate r.entries)

(* Drop one key's entries. *)
let clear_key (t : t) (h : Tid.t) (key : key) : unit =
  match Hashtbl.find t.rows h with
  | None -> ()
  | Some rows ->
    let rows = List.filter rows ~f:(fun r -> not (equal_key r.key key)) in
    if List.is_empty rows then Hashtbl.remove t.rows h
    else Hashtbl.set t.rows ~key:h ~data:rows

(* The value's own line: [Some base] when its offsets are translatable — a
   fixed-base Stack/VLA line.  [None] defers (an unknown VLA base has no
   entry-line position). *)
let rel_line_base (o : Hike_origin.t) : Cbat_word.t option =
  let f = Cbat_clp_set_composite.base_facts o in
  if f.Hike_origin.certified > 0 then
    Some (Cbat_word.of_int64 ~width:64 f.Hike_origin.base)
  else None

(* Extend the grid [base + i*step] to cover [lo,hi], keeping the step and
   base congruence (the signed line).  None for a singleton (step 0). *)
let extend_grid ~(width : int) ~(base : Cbat_word.t) ~(step : Cbat_word.t)
    (lo : Cbat_word.t) (hi : Cbat_word.t) : Cbat_clp.t option =
  if Cbat_word.is_zero step then None
  else
    let diff = Cbat_word.sub lo base in
    let quot =
      match Cbat_word.to_int64 diff, Cbat_word.to_int64 step with
      | Ok di, Ok si when not (Stdlib.Int64.equal si 0L) ->
        let q = Stdlib.Int64.div di si in
        let q =
          if Stdlib.Int64.compare (Stdlib.Int64.rem di si) 0L < 0
          then Stdlib.Int64.pred q else q in
        Cbat_word.of_int64 ~width:(Cbat_word.bitwidth diff) q
      | _ -> Cbat_word.zero (Cbat_word.bitwidth diff) in
    let base' = Cbat_word.add base (Cbat_word.mul quot step) in
    let w1 = width + 1 in
    let cw w = Cbat_word.cast Bil.UNSIGNED w1 w in
    let cardn =
      Cbat_word.add
        (Cbat_word.div (cw (Cbat_word.sub hi base')) (cw step))
        (Cbat_word.one w1) in
    Some (Cbat_clp.create ~width ~step ~cardn base')

(* The value's translatable progression in its own space. *)
let value_progression (o : Hike_origin.t) (v : Cbat_clp_set_composite.t) :
    Cbat_clp.t option =
  match o with
  | Hike_origin.Vla _ -> Cbat_clp_set_composite.vla_offsets v
  | _ -> Cbat_clp_set_composite.stack_offsets v

(* Extrapolate bounds toward landmarks; clamp at landmark and current
   bound.  The translation works in the value's own line — a plain word's
   absolute words, or a relative value's offsets — so a stride is kept and
   a stack value stays on its key line. *)
let translate_to ~(steps : int) (data_old : Cbat_clp_set_composite.t)
    (data_new : Cbat_clp_set_composite.t)
    (entries : lm_entry list) : Cbat_clp_set_composite.t =
  let width = Cbat_clp_set_composite.bitwidth data_old in
  if width <> Cbat_clp_set_composite.bitwidth data_new then data_new
  else begin
    (* Growth per traversal times steps, clamped at landmark and bound. *)
    let delta_of (e : lm_entry) : int =
      Option.value ~default:0 (Option.map e.dist ~f:(fun dc ->
          let g = match e.dist_p with Some dp when dp > dc -> dp - dc | _ -> 0 in
          let d = g * steps in
          if d > max_landmark_distance then max_landmark_distance else d))
    in
    let rel =
      match Cbat_clp_set_composite.origin data_new with
      | Some o when Hike_origin.names_stack_line o -> rel_line_base o
      | _ -> None in
    let signed = Option.is_some rel in
    let sgn w = if signed then Cbat_word.signed w else w in
    let cmp a b = Cbat_word.compare (sgn a) (sgn b) in
    let min_e =
      if signed then Cbat_clp_set_composite.min_elem_signed
      else Cbat_clp_set_composite.min_elem in
    let max_e =
      if signed then Cbat_clp_set_composite.max_elem_signed
      else Cbat_clp_set_composite.max_elem in
    let lo_base = Option.value (min_e data_new) ~default:(Cbat_word.zero width) in
    let hi_base = Option.value (max_e data_new) ~default:(Cbat_word.zero width) in
    let extrap_lo =
      let lo' = List.filter entries ~f:(fun e -> not e.is_upper) in
      match lo' with
      | [] -> lo_base
      | _ ->
        let candidates = List.filter_map lo' ~f:(fun e ->
            let v = Cbat_word.sub lo_base (Cbat_word.of_int ~width (delta_of e)) in
            let v = if cmp v lo_base > 0 then lo_base else v in
            let v = if cmp v e.bound < 0 then e.bound else v in
            let v = if cmp v lo_base > 0 then lo_base else v in
            Some v)
        in
        List.fold candidates ~init:lo_base ~f:(fun acc v ->
            if cmp v acc < 0 then v else acc)
    in
    let extrap_hi =
      let hi' = List.filter entries ~f:(fun e -> e.is_upper) in
      match hi' with
      | [] -> hi_base
      | _ ->
        let candidates = List.filter_map hi' ~f:(fun e ->
            let v = Cbat_word.add hi_base (Cbat_word.of_int ~width (delta_of e)) in
            let v =
              if cmp v hi_base < 0 then
                (* Overflow saturates. *)
                Cbat_word.ones width
              else v in
            let v = if cmp v e.bound > 0 then e.bound else v in
            let v = if cmp v hi_base < 0 then hi_base else v in
            Some v)
        in
        List.fold candidates ~init:hi_base ~f:(fun acc v ->
            if cmp v acc > 0 then v else acc)
    in
    if cmp extrap_lo extrap_hi > 0 then data_new
    else
      match Cbat_clp_set_composite.origin data_new with
      | Some o when Hike_origin.names_stack_line o -> (
          match rel, value_progression o data_new with
          | Some b, Some p ->
            let lo_off = Cbat_word.sub extrap_lo b in
            let hi_off = Cbat_word.sub extrap_hi b in
            let base =
              Option.value (Cbat_clp.min_elem p) ~default:lo_off in
            (match
               extend_grid ~width ~base ~step:(Cbat_clp.step_of p) lo_off hi_off
             with
             | Some p' ->
               Cbat_clp_set_composite.set_origin o
                 (Cbat_clp_set_composite.stack_word p')
             | None -> data_new)
          | _ -> data_new)
      | _ ->
        (* A plain value: extend its grid in absolute words. *)
        let step =
          Cbat_word.of_int ~width (Cbat_clp_set_composite.stride data_new) in
        let base =
          Option.value (Cbat_clp_set_composite.min_elem data_new)
            ~default:(Cbat_word.zero width) in
        (match extend_grid ~width ~base ~step extrap_lo extrap_hi with
         | Some p' -> Cbat_clp_set_composite.of_clp p'
         | None -> data_new)
  end

(* The extrapolation's own answer: the landmark translation at [old]'s
   width, or the plain steps-extrapolation when no entry holds that width.
   An extrapolation that overflows to top is a property of the rule, not of
   a lane, so it answers [Widen] here. *)
let extrapolate ~(steps : int) ~(old : Cbat_clp_set_composite.t)
    ~(new_ : Cbat_clp_set_composite.t) ~(entries : lm_entry list) :
    [ `Extrapolated of Cbat_clp_set_composite.t | `Widen ] =
  let entries =
    List.filter entries ~f:(fun e ->
        Cbat_word.bitwidth e.bound = Cbat_clp_set_composite.bitwidth old)
  in
  (* A relative value with no translatable line (an unknown VLA base)
     defers to the plain widen. *)
  let unknown_line v =
    match Cbat_clp_set_composite.origin v with
    | Some o when Hike_origin.names_stack_line o -> Option.is_none (rel_line_base o)
    | _ -> false in
  match entries with
  | _ :: _ when unknown_line old || unknown_line new_ -> `Widen
  | [] ->
    `Extrapolated (Cbat_clp_set_composite.extrapolate_steps ~steps old new_)
  | _ ->
    let data = translate_to ~steps old new_ entries in
    if Cbat_clp_set_composite.is_top data then `Widen
    else `Extrapolated (Cbat_clp_set_composite.keep_section ~old ~new_ data)
