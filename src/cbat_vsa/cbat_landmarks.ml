(* Landmark-directed widening — the faithful port of Simon & King, "Widening
   Polyhedra with Landmarks" (APLAS 2006), per the grilling-settled design
   (Q1=C/Q2=B/Q3=C, 2026-08-30): the static threshold ladder is DELETED; the
   only precision mechanism is the landmark table (Listing 1 acquisition via
   the empty-meet path, Listing 3 closure-rate steps, Listing 4 growth×steps
   extrapolation clamped at the landmark). The paper's ∞-arm is plain
   [AI.widen_join] (Cousot-Halbwachs: unstable bounds → TOP); the Zero arm is
   a plain join. *)

open Bap.Std
open Core_kernel

(* per-(var, bound, is_upper) entry; smaller distance wins (updateLandmark) *)
type lm_entry = {
  bound : Word.t;
  is_upper : bool;
  mutable dist : int option;   (* dist_c — the current-iteration distance *)
  mutable dist_p : int option;  (* dist_p — the previous-iteration distance *)
}

let cap = 1 lsl 40
let cap_distance (d : int) : int = min d cap
let distance_words (a : Word.t) (b : Word.t) : int =
  let diff = Word.sub b a in
  try Word.to_int_exn diff with _ -> cap
  (* if word value > int range, cap *)

(* The landmark state is per-WTO-head: ONE table maps each head to a
   flat list of [lm_entry] values (one per (var_base, bound, is_upper)
   observation, deduped by the [add_smaller_dist] rule). Acquisition
   outside any WTO cycle is a sound no-op (Story 6/19); the AGENTS.md
   §3 NO-FALLBACKS doctrine forbids a global fallback that would mask
   the headless path's identity. Spec ticket S5: "a [landmark_env]
   holding the head→landmark-list table" — singular, not duplicated. *)

(* [widening_at_head]: the WTO SCC head whose widening point is currently
   being processed; bound by [cbat_vsa.process_vertex] around the block
   denotation so that [observe_unsat_var] attributes landmarks to the
   innermost enclosing cycle. None = acquisition outside any WTO cycle,
   which is a sound no-op. *)
let widening_at_head : Tid.t option ref = ref None

(* [lm_env] — head -> landmark list, the single per-cycle landmark table
   from Simon & King §4. Both acquisition ([record_landmark_for_head])
   and consumption ([lm_calc_steps], [lm_advance], [entries_for_head])
   read and write THIS table. *)
let lm_env : (Tid.t, lm_entry list) Hashtbl.t = Hashtbl.create (module Tid)

let clear () = Hashtbl.clear lm_env

(* [clear_head h blocks]: drop the landmark entries for head [h] AND every
   block in [blocks] (the head's full SCC — its inner-SCC members and
   any strict descendants of [h] in the WTO tree, per spec Q9). After
   consumption at [h], the inner-SCC landmarks are obsolete: Bourdoncle's
   WTO order is "inner before outer," so any inner cycle has already
   been stabilized by the time [h]'s widening fires, and its recorded
   measurements would be re-fired as the second measurement of [h]'s
   landmark table if not cleared. Called from the widening-point
   transition in [cbat_vsa.process_vertex]. *)
let clear_head (h : Tid.t) (blocks : Tid.Set.t) : unit =
  Hashtbl.remove lm_env h;
  Core.Set.iter blocks ~f:(fun btid -> Hashtbl.remove lm_env btid)

let add_smaller_dist (entries : lm_entry list) (entry : lm_entry) : lm_entry list =
  match List.find entries ~f:(fun e ->
      Word.equal e.bound entry.bound
      && Bool.equal e.is_upper entry.is_upper) with
  | None -> entry :: entries
  | Some existing ->
    let keep =
      match existing.dist, entry.dist with
      | None, _ | _, None -> true
      | Some d1, Some d2 -> d2 < d1
    in
    (* dist_p (history) is preserved by [add_smaller_dist] — only [lm_advance] rotates it *)
    (* dist_p stays whatever it was — add_smaller_dist never resets history *)
    (* The replacement PRESERVES the rotated history [existing.dist_p] —
       the second measurement updates [dist] while [dist_p] (committed by
       [lm_advance], Listing 2) survives; without this the re-acquisition
       after every advance resets the entry to a first-measurement state
       and [lm_calc_steps] returns `Zero forever — the Finite-never-fires
       bug (the entry record is rebuilt with dist_p = None; carry it). *)
    if keep then
      { entry with dist_p = existing.dist_p }
      :: List.filter entries ~f:(fun e -> not (
        Word.equal e.bound entry.bound
        && Bool.equal e.is_upper entry.is_upper))
    else entries

(* F2 — the ACQUISITION-FIRED LATCH.  [fired_count] is a bare int ref
   (NOT part of the landmark table): it counts
   [record_landmark_for_head] calls since the last reset — i.e., within
   the transfer the caller is about to run (the ORIGINAL transfer at
   memo-fill time, or the Q1 replay on a hit).  The C1 caller resets it
   around the transfer and reads the delta, so the memo entry can record
   whether the transfer it cached fired any acquisition.

   RE-ENTRANCY: a transfer cannot re-enter a nested run in the current
   tree — [denote_jump] never applies its [denote_call] parameter (the
   ON-path call abstraction [inspect_call] handles every Call jmp; the
   OFF-path recursion at [static_graph_vsa] is reached only from its own
   fold, never from inside a transfer) — so the process-global counter
   sees only the one transfer's firings.  The save/restore discipline is
   kept anyway ([start_fired_latch] returns the outer count,
   [end_fired_latch] restores it): it costs two int ops, and it keeps
   the latch exact if [denote_call] is ever wired back into the jump
   path (a nested run firing into its own tables would otherwise pollute
   the outer entry's flag). *)
let fired_count : int ref = ref 0
let start_fired_latch () : int = !fired_count
let end_fired_latch (base : int) : bool =
  let fired = !fired_count > base in
  fired_count := base;
  fired

let record_landmark_for_head ~(head:Tid.t) (v : var) ~(bound : Word.t) ~(is_upper : bool) ~(dist : int) : unit =
  (* F2 — the ACQUISITION-FIRED counter, bumped at this single choke
     point (every firing [observe_unsat_var] site funnels here — the
     fallthrough row, the gated env meet, and the jcc-decoder arm).  The
     record itself is written exactly as before, unconditionally — the
     replay decision belongs to the caller, never here. *)
  fired_count := !fired_count + 1;
  let entry = { bound; is_upper; dist = Some dist; dist_p = None } in
  let cur = Hashtbl.find lm_env head |> Option.value ~default:[] in
  let next = add_smaller_dist cur entry in
  Hashtbl.set lm_env ~key:head ~data:next

(* [entries_for_head head v]: every entry recorded for [head] (the
   single-table design — the consumption path filters by var internally
   via the entry's [lm_entry.bound] comparison if needed; here we
   return the head's full list for the caller's convenience). The
   [v] parameter is kept for API compatibility with the old per-var
   submap lookup but is unused. *)
let entries_for_head (head : Tid.t) (_v : var) : lm_entry list =
  Hashtbl.find lm_env head |> Option.value ~default:[]

(* Acquisition helper: called from meet_var when meet is empty. Records the
   disabled boundary (the cstr's extremum outside p) as a landmark for the
   INNERMOST ENCLOSING WTO CYCLE HEAD (the [widening_at_head] ref, bound by
   [cbat_vsa.process_vertex] around the block denotation — Simon & King §4
   "landmarks of the enclosing WTO cycle"). The recording goes to the head's
   per-head landmark table via [record_landmark_for_head]; the no-arg
   [record_landmark] is reserved for acquisition outside any WTO cycle (the
   sound no-op identity per the AGENTS.md §3 NO-FALLBACKS doctrine — a
   headless var carries no landmark, and we never fall back to a global
   landmark table). *)
let observe_unsat_var (v : var) ~(p : Cbat_clp_set_composite.t) ~(cstr : Cbat_clp_set_composite.t) : unit =
  if Cbat_clp_set_composite.bitwidth p <> Cbat_clp_set_composite.bitwidth cstr then ()
  else
    let m = Cbat_clp_set_composite.meet p cstr in
    if not (Cbat_clp_set_composite.is_bottom m) then ()
    else
      match !widening_at_head,
            Cbat_clp_set_composite.min_elem p, Cbat_clp_set_composite.max_elem p,
            Cbat_clp_set_composite.min_elem cstr, Cbat_clp_set_composite.max_elem cstr with
      | None, _, _, _, _ ->
        (* Acquisition outside any WTO cycle is a sound no-op (the AGENTS.md
           §3 NO-FALLBACKS identity; never bottom, never a global fallback). *)
        ()
      | Some h, Some p_min, Some p_max, Some c_min, Some c_max ->
        if Word.(<) p_max c_min then begin
          (* the set is entirely BELOW the constraint's boundary: the landmark
             caps the set from ABOVE (the loop-exit boundary of a growing
             counter) — [is_upper=true] so [translate_to]'s upper-extrapolation
             arm consumes it. *)
          let d = distance_words p_max c_min in
          record_landmark_for_head ~head:h v ~bound:c_min ~is_upper:true ~dist:(cap_distance d)
        end else if Word.(>) p_min c_max then begin
          (* the set is entirely ABOVE the constraint's boundary: the landmark
             floors the set from BELOW — [is_upper=false], the lower-
             extrapolation arm. *)
          let d = distance_words c_max p_min in
          record_landmark_for_head ~head:h v ~bound:c_max ~is_upper:false ~dist:(cap_distance d)
        end else ()
      | Some _, _, _, _, _ -> ()

(* [lm_calc_steps h]: Listing 3 — paper's "calc no. of iterations" arm.
   Three returns:
   - `Zero: a landmark still has no second measurement (dist_p is None).
     The "normal fixpoint computation" should resume so the landmark can
     acquire its second measurement on the next pass — the user's directive
     ("widen to the landmark, i.e K!") is satisfied when the FIRST
     extrapolation fires; this Zero return is the in-between state.
   - `Finite n: all landmarks have two measurements (dist_p finite).
     The minimum over landmarks of floor(dist_c / (dist_p - dist_c)) is
     the closest-landmark rank — the propagation rate that drives
     Listing 4's extrapolation.
   - `Inf: no landmarks at all (or no landmark with dist_p finite) —
     the paper's standard widening applies (the ∞-arm of Listing 4). *)
let lm_calc_steps (h : Tid.t) : [> `Zero | `Finite of int | `Inf] =
  match Hashtbl.find lm_env h with
  | None -> `Inf
  | Some lst ->
    let has_zero = List.exists lst ~f:(fun e -> Option.is_none e.dist_p) in
    if has_zero then `Zero
    else
      let finite =
        List.filter_map lst ~f:(fun e ->
          match e.dist_p, e.dist with
          | Some dp, Some dc when dp > dc -> Some (dc / (dp - dc))
          | _ -> None)
      in
      if List.is_empty finite then `Inf
      else `Finite (List.min_elt finite ~compare:Int.compare |> Option.value_exn)

(* [lm_advance h]: Listing 2 — commit the current distance as the previous
   ([dist_p := dist_c]) and reset [dist_c] to None so the next acquisition
   starts a fresh first measurement. *)
let lm_advance (h : Tid.t) : unit =
  match Hashtbl.find lm_env h with
  | None -> ()
  | Some lst ->
    List.iter lst ~f:(fun entry ->
      entry.dist_p <- entry.dist;
      entry.dist <- None)




(* [translate_to ~steps data_old data_new entries]: Listing 4 landmark
   consumption — for each landmark of the head (filtered to the var's width
   by the caller), translate the corresponding bound outward by the observed
   GROWTH per traversal (dist_p − dist) times [steps] — the product lands at
   (or one growth-step short of) the landmark. The candidate is CLAMPED at
   the landmark bound (never extrapolate past it — a landmark is a
   concretely-reachable value, so the clamp is sound) and at the current
   bound's outward side (a stale landmark can never NARROW the set).
   Overflow past the word grid -> the paper's infinite arm (word_max).
   The result is the interval [extrap_lo, extrap_hi]; if the two
   extrapolations cross (lo > hi) we fall back to [data_new]. *)
let translate_to ~(steps : int) (data_old : Cbat_clp_set_composite.t)
    (data_new : Cbat_clp_set_composite.t)
    (entries : lm_entry list) : Cbat_clp_set_composite.t =
  let width = Cbat_clp_set_composite.bitwidth data_old in
  if width <> Cbat_clp_set_composite.bitwidth data_new then data_new
  else begin
    (* Listing 4's translation rate: the observed GROWTH per traversal
       (dist_p - dist) times the traversal count [steps] — the product lands
       at (or one growth-step short of) the landmark. The candidate is
       CLAMPED at the landmark bound (never extrapolate past it — a landmark
       is a concretely-reachable value, so the clamp is sound) AND at the
       current bound's outward side (a stale landmark can never NARROW the
       set). Overflow past the word grid -> the paper's infinite arm. *)
    let cap = 1 lsl 40 in
    let delta_of (e : lm_entry) : int =
      match e.dist with
      | Some dc ->
        let g = match e.dist_p with Some dp when dp > dc -> dp - dc | _ -> 0 in
        let d = g * steps in
        if d > cap then cap else d
      | None -> 0
    in
    let lo_base = match Cbat_clp_set_composite.min_elem data_new with Some w -> w | None -> Word.zero width in
    let hi_base = match Cbat_clp_set_composite.max_elem data_new with Some w -> w | None -> Word.zero width in
    let extrap_lo =
      let lo' = List.filter entries ~f:(fun e -> not e.is_upper) in
      match lo' with
      | [] -> lo_base
      | _ ->
        let candidates = List.filter_map lo' ~f:(fun e ->
            let v = Word.sub lo_base (Word.of_int ~width (delta_of e)) in
            let v = if Word.compare v lo_base > 0 then lo_base else v in
            let v = if Word.compare v e.bound < 0 then e.bound else v in
            let v = if Word.compare v lo_base > 0 then lo_base else v in
            Some v)
        in
        List.fold candidates ~init:lo_base ~f:(fun acc v ->
            if Word.compare v acc < 0 then v else acc)
    in
    let extrap_hi =
      let hi' = List.filter entries ~f:(fun e -> e.is_upper) in
      match hi' with
      | [] -> hi_base
      | _ ->
        let candidates = List.filter_map hi' ~f:(fun e ->
            let v = Word.add hi_base (Word.of_int ~width (delta_of e)) in
            let v =
              if Word.compare v hi_base < 0 then
                (* overflow -> infinite arm (Listing 4): word_max *)
                Word.ones width
              else v in
            let v = if Word.compare v e.bound > 0 then e.bound else v in
            let v = if Word.compare v hi_base < 0 then hi_base else v in
            Some v)
        in
        List.fold candidates ~init:hi_base ~f:(fun acc v ->
            if Word.compare v acc > 0 then v else acc)
    in
    if Word.compare extrap_lo extrap_hi > 0 then data_new
    else Cbat_clp_set_composite.of_clp (Cbat_clp.interval ~width extrap_lo extrap_hi)
  end
