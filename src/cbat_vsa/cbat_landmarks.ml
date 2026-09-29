(* Simon & King landmark widening. Empty meets acquire landmarks; heads extrapolate toward them. *)

open Bap.Std
open Core

(* Per-(var, bound, is_upper) entry; smaller distance wins. *)
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
  let diff = Cbat_word.sub b a in
  match Cbat_word.to_int64 diff with
  | Ok d when Int64.compare (Int64.abs d) (Int64.of_int max_landmark_distance) < 0
    -> Option.value_exn (Int64.to_int (Int64.abs d))
  | Ok _ | Error _ -> max_landmark_distance

(* The cell an entry is keyed by: the memory key's byte hull (each
   end as width/value) and stride — per-stride cells keep their own
   landmark rows. *)
module Cell_key = struct
  type t = { origin : Hike_origin.t; lo_width : int; lo_value : int64;
             hi_width : int; hi_value : int64; stride : int }

  let equal a b =
    Hike_origin.equal a.origin b.origin
    && Int.equal a.lo_width b.lo_width && Stdlib.Int64.equal a.lo_value b.lo_value
    && Int.equal a.hi_width b.hi_width && Stdlib.Int64.equal a.hi_value b.hi_value
    && Int.equal a.stride b.stride
end

(* Per-head cell rows, oldest entry first. *)
type cell_rows = (Cell_key.t * lm_entry list) list

(* Per-head landmark tables: words keyed by width-filtered entry lists,
   cells by (head, cell). *)
type t = {
  lm_env : (Tid.t, lm_entry list) Hashtbl.t;
  cell_env : (Tid.t, cell_rows) Hashtbl.t;
  mutable widening_at_head : Tid.t option;  (* head currently widened; None outside a cycle *)
}

(* One fresh table per solve — the widening state is the run's, never
   the process's. *)
let create () : t =
  { lm_env = Hashtbl.create (module Tid);
    cell_env = Hashtbl.create (module Tid);
    widening_at_head = None }

(* Run [f] with [head] widened; the previous head is restored. *)
let with_widening_head (t : t) (head : Tid.t option) (f : unit -> 'a) : 'a =
  let prev = t.widening_at_head in
  t.widening_at_head <- head;
  Fun.protect ~finally:(fun () -> t.widening_at_head <- prev) f

(* Drop entries of [h] and its SCC. *)
let clear_head (t : t) (h : Tid.t) (blocks : Tid.Set.t) : unit =
  Hashtbl.remove t.lm_env h;
  Hashtbl.remove t.cell_env h;
  Core.Set.iter blocks ~f:(fun btid ->
      Hashtbl.remove t.lm_env btid;
      Hashtbl.remove t.cell_env btid)

let add_smaller_dist (entries : lm_entry list) (entry : lm_entry) : lm_entry list =
  match List.find entries ~f:(fun e ->
      Cbat_word.equal e.bound entry.bound
      && Bool.equal e.is_upper entry.is_upper) with
  | None -> entry :: entries
  | Some existing ->
    let keep =
      match existing.dist, entry.dist with
      | None, _ | _, None -> true
      | Some d1, Some d2 -> d2 < d1
    in
    (* Preserve [dist_p]; only [lm_advance] rotates history. *)
    if keep then
      { entry with dist_p = existing.dist_p }
      :: List.filter entries ~f:(fun e -> not (
        Cbat_word.equal e.bound entry.bound
        && Bool.equal e.is_upper entry.is_upper))
    else entries

let record_landmark_for_head (t : t) ~(head : Tid.t) ~(bound : Cbat_word.t) ~(is_upper : bool) ~(dist : int) : unit =
  let entry = { bound; is_upper; dist = Some dist; dist_p = None } in
  let cur = Hashtbl.find t.lm_env head |> Option.value ~default:[] in
  let next = add_smaller_dist cur entry in
  Hashtbl.set t.lm_env ~key:head ~data:next

(* Entries recorded for [head]. *)
let entries_for_head (t : t) (head : Tid.t) : lm_entry list =
  Hashtbl.find t.lm_env head |> Option.value ~default:[]

(* Two values live on the same coordinate line: an empty meet between
   different lines is a category mismatch, not a disabled behavior. *)
let same_line (a : Cbat_clp_set_composite.t) (b : Cbat_clp_set_composite.t) :
    bool =
  match Cbat_clp_set_composite.origin a, Cbat_clp_set_composite.origin b with
  | Some oa, Some ob ->
    Hike_origin.equal (Cbat_clp_set_composite.key_line oa)
      (Cbat_clp_set_composite.key_line ob)
  | None, None -> true
  | Some _, None | None, Some _ -> false

(* Record an empty meet's disabled boundary at the enclosing head. The
   head check comes first: outside a cycle the meet below is pure
   computation whose result is discarded. *)
let observe_unsat_var (t : t) (v : var) ~(p : Cbat_clp_set_composite.t)
    ~(cstr : Cbat_clp_set_composite.t)
    ~(meet : Cbat_clp_set_composite.t) : unit =
  if Cbat_clp_set_composite.bitwidth p <> Cbat_clp_set_composite.bitwidth cstr then ()
  else if not (same_line p cstr) then ()
  else
    match t.widening_at_head with
    | None ->
      (* Outside a cycle: no-op. *)
      ()
    | Some h ->
      if not (Cbat_clp_set_composite.is_bottom meet) then ()
      else
        match Cbat_clp_set_composite.min_elem p, Cbat_clp_set_composite.max_elem p,
              Cbat_clp_set_composite.min_elem cstr, Cbat_clp_set_composite.max_elem cstr with
        | Some p_min, Some p_max, Some c_min, Some c_max ->
          if Cbat_word.(<) p_max c_min then begin
            (* Set below the boundary: upper landmark. *)
            let d = distance_words p_max c_min in
            record_landmark_for_head t ~head:h ~bound:c_min ~is_upper:true ~dist:(cap_distance d)
          end else if Cbat_word.(>) p_min c_max then begin
            (* Set above the boundary: lower landmark. *)
            let d = distance_words c_max p_min in
            record_landmark_for_head t ~head:h ~bound:c_max ~is_upper:false ~dist:(cap_distance d)
          end else ()
        | _ -> ()

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

(* Steps until the closest landmark; Zero needs another measurement, Inf
   widens.  Only an entry holding a fresh measurement speaks: an entry
   already consumed by [lm_advance] carries no reading, and a table keeps
   entries whose boundary the guard stopped reaching — neither may hold
   the head in [Zero], which never widens. *)
let steps_of_entries (lst : lm_entry list) : [> `Zero | `Finite of int | `Inf] =
  let fresh = List.filter lst ~f:(fun e -> Option.is_some e.dist) in
  let steps =
    List.filter_map fresh ~f:(fun e ->
        match e.dist_p, e.dist with
        | Some dp, Some dc when dp > dc -> Some (dc / (dp - dc))
        | _ -> None)
  in
  let answer =
    if List.exists fresh ~f:(fun e -> Option.is_none e.dist_p) then `Zero
    else if List.is_empty steps then `Inf
    else `Finite (List.min_elt steps ~compare:Int.compare |> Option.value_exn)
  in
#ifdef VSA_DEBUG
  (* Which shape the head is in: how many entries the table holds, how
     many carry a fresh reading, and whether the distances move. *)
  bump_steps
    (Printf.sprintf "table.%d.%s" (List.length lst)
       (if List.is_empty lst then "empty"
        else if List.is_empty fresh then "stale"
        else if List.exists fresh ~f:(fun e -> Option.is_none e.dist_p) then "warm"
        else "live"));
  List.iter fresh ~f:(fun e ->
      match e.dist_p, e.dist with
      | Some dp, Some dc ->
        bump_steps (if dp > dc then "live.shrink" else "live.hold")
      | _ -> ());
  (match answer with
   | `Finite _ -> bump_steps "fire.finite"
   | `Zero -> bump_steps "fire.zero"
   | `Inf -> bump_steps ("fire.inf." ^ (if List.is_empty fresh then "stale" else "held")));
#endif
  answer

let lm_calc_steps (t : t) (h : Tid.t) : [> `Zero | `Finite of int | `Inf] =
  match Hashtbl.find t.lm_env h with
  | None -> `Inf
  | Some lst -> steps_of_entries lst

(* The rotation: the current reading becomes the previous one.  An entry
   with no fresh reading keeps the history it holds — erasing it would
   drop a measurement the next reading must pair against. *)
let rotate (entries : lm_entry list) : unit =
  List.iter entries ~f:(fun entry ->
      (match entry.dist with
       | Some d -> entry.dist_p <- Some d
       | None -> ());
      entry.dist <- None)

(* Commit current distances as previous. *)
let lm_advance (t : t) (h : Tid.t) : unit =
  Option.iter (Hashtbl.find t.lm_env h) ~f:rotate;
  Option.iter (Hashtbl.find t.cell_env h)
    ~f:(List.iter ~f:(fun (_, es) -> rotate es))




(* Extrapolate bounds toward landmarks; clamp at landmark and current bound. *)
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
    let lo_base = Option.value (Cbat_clp_set_composite.min_elem data_new) ~default:(Cbat_word.zero width) in
    let hi_base = Option.value (Cbat_clp_set_composite.max_elem data_new) ~default:(Cbat_word.zero width) in
    let extrap_lo =
      let lo' = List.filter entries ~f:(fun e -> not e.is_upper) in
      match lo' with
      | [] -> lo_base
      | _ ->
        let candidates = List.filter_map lo' ~f:(fun e ->
            let v = Cbat_word.sub lo_base (Cbat_word.of_int ~width (delta_of e)) in
            let v = if Cbat_word.compare v lo_base > 0 then lo_base else v in
            let v = if Cbat_word.compare v e.bound < 0 then e.bound else v in
            let v = if Cbat_word.compare v lo_base > 0 then lo_base else v in
            Some v)
        in
        List.fold candidates ~init:lo_base ~f:(fun acc v ->
            if Cbat_word.compare v acc < 0 then v else acc)
    in
    let extrap_hi =
      let hi' = List.filter entries ~f:(fun e -> e.is_upper) in
      match hi' with
      | [] -> hi_base
      | _ ->
        let candidates = List.filter_map hi' ~f:(fun e ->
            let v = Cbat_word.add hi_base (Cbat_word.of_int ~width (delta_of e)) in
            let v =
              if Cbat_word.compare v hi_base < 0 then
                (* Overflow saturates. *)
                Cbat_word.ones width
              else v in
            let v = if Cbat_word.compare v e.bound > 0 then e.bound else v in
            let v = if Cbat_word.compare v hi_base < 0 then hi_base else v in
            Some v)
        in
        List.fold candidates ~init:hi_base ~f:(fun acc v ->
            if Cbat_word.compare v acc > 0 then v else acc)
    in
    if Cbat_word.compare extrap_lo extrap_hi > 0 then data_new
    else Cbat_clp_set_composite.of_clp (Cbat_clp.interval ~width extrap_lo extrap_hi)
  end


(* ---- Cell entries: recorded at empty cell meets, consumed per cell. ---- *)

(* Per-head entry cap; the oldest entry drops when it overflows. *)
let cell_cap = 64

let record_landmark_for_cell (t : t) ~(head : Tid.t) ~(cell : Cell_key.t)
    ~(bound : Cbat_word.t) ~(is_upper : bool) ~(dist : int) : unit =
  let entry = { bound; is_upper; dist = Some dist; dist_p = None } in
  let same_bound (e : lm_entry) =
    Cbat_word.equal e.bound entry.bound && Bool.equal e.is_upper entry.is_upper in
  (* Same boundary updates in place — smaller distance wins, history
     kept; a new boundary appends (newest last). *)
  let upsert (es : lm_entry list) : lm_entry list =
    if List.exists es ~f:same_bound then
      List.map es ~f:(fun e ->
          if not (same_bound e) then e
          else
            let keep =
              match e.dist, entry.dist with
              | None, _ | _, None -> true
              | Some d1, Some d2 -> d2 < d1 in
            if keep then { entry with dist_p = e.dist_p } else e)
    else es @ [entry] in
  let rows = Option.value (Hashtbl.find t.cell_env head) ~default:[] in
  let rows =
    match List.find rows ~f:(fun (k, _) -> Cell_key.equal k cell) with
    | Some _ ->
      List.map rows ~f:(fun (k, es) ->
          if Cell_key.equal k cell then (k, upsert es) else (k, es))
    | None -> rows @ [(cell, [entry])] in
  let count = List.fold rows ~init:0 ~f:(fun n (_, es) -> n + List.length es) in
  let rec trim rows n =
    if n <= cell_cap then rows
    else
      match rows with
      | [] -> rows
      | (k, es) :: rest ->
        (match es with
         | [] -> trim rest n
         | [_] -> trim rest (n - 1)
         | _ :: tl -> trim ((k, tl) :: rest) (n - 1)) in
  Hashtbl.set t.cell_env ~key:head ~data:(trim rows count)

(* Record an empty cell meet's disabled boundary at the enclosing head;
   the same rule the words lane applies to vars. True when an entry was
   recorded. *)
let observe_unsat_cell (t : t) ~(cell : Cell_key.t)
    ~(p : Cbat_clp_set_composite.t) ~(cstr : Cbat_clp_set_composite.t) : bool =
  if Cbat_clp_set_composite.bitwidth p <> Cbat_clp_set_composite.bitwidth cstr then false
  else
    match t.widening_at_head with
    | None -> false
    | Some h ->
      let m = Cbat_clp_set_composite.meet p cstr in
      if not (Cbat_clp_set_composite.is_bottom m) then begin
        (* The meet kept a proper subset: the discarded piece is the
           disabled behavior — record its boundary. *)
        match Cbat_clp_set_composite.min_elem p, Cbat_clp_set_composite.max_elem p,
              Cbat_clp_set_composite.min_elem m, Cbat_clp_set_composite.max_elem m with
        | Some p_min, Some p_max, Some m_min, Some m_max ->
          if Cbat_word.(<) p_min m_min then begin
            let bound = Cbat_word.pred m_min in
            let d = distance_words p_min bound in
            record_landmark_for_cell t ~head:h ~cell ~bound ~is_upper:false ~dist:(cap_distance d);
            true
          end else if Cbat_word.(>) p_max m_max then begin
            let bound = Cbat_word.succ m_max in
            let d = distance_words bound p_max in
            record_landmark_for_cell t ~head:h ~cell ~bound ~is_upper:true ~dist:(cap_distance d);
            true
          end else false
        | _ -> false
      end
      else
        match Cbat_clp_set_composite.min_elem p, Cbat_clp_set_composite.max_elem p,
              Cbat_clp_set_composite.min_elem cstr, Cbat_clp_set_composite.max_elem cstr with
        | Some p_min, Some p_max, Some c_min, Some c_max ->
          if Cbat_word.(<) p_max c_min then begin
            (* Cell below the boundary: upper landmark. *)
            let d = distance_words p_max c_min in
            record_landmark_for_cell t ~head:h ~cell ~bound:c_min ~is_upper:true ~dist:(cap_distance d);
            true
          end else if Cbat_word.(>) p_min c_max then begin
            (* Cell above the boundary: lower landmark. *)
            let d = distance_words c_max p_min in
            record_landmark_for_cell t ~head:h ~cell ~bound:c_max ~is_upper:false ~dist:(cap_distance d);
            true
          end else false
        | _ -> false

(* The cell's own row, if recorded. *)
let find_row (t : t) (h : Tid.t) (cell : Cell_key.t) : lm_entry list option =
  let has_cell (k, _) = Cell_key.equal k cell in
  Option.bind (Hashtbl.find t.cell_env h) ~f:(fun rows ->
      Option.map ~f:snd (List.find rows ~f:has_cell))

let entries_for_cell (t : t) (h : Tid.t) (cell : Cell_key.t) : lm_entry list =
  Option.value ~default:[] (find_row t h cell)

let lm_calc_steps_for_cell (t : t) (h : Tid.t) (cell : Cell_key.t)
    : [> `Zero | `Finite of int | `Inf] =
  match entries_for_cell t h cell with
  | [] -> `Inf
  | es -> steps_of_entries es

(* Commit one cell's current distances; the next measurement yields steps. *)
let advance_cell (t : t) (h : Tid.t) (cell : Cell_key.t) : unit =
  Option.iter (find_row t h cell) ~f:rotate

(* Drop the cell's entries once its extrapolation consumed them; stale
   entries never narrow. *)
let clear_cell (t : t) (h : Tid.t) (cell : Cell_key.t) : unit =
  let lacks_cell (k, _) = not (Cell_key.equal k cell) in
  match Hashtbl.find t.cell_env h with
  | None -> ()
  | Some rows ->
    let rows = List.filter rows ~f:lacks_cell in
    if List.is_empty rows then Hashtbl.remove t.cell_env h
    else Hashtbl.set t.cell_env ~key:h ~data:rows

(* The head holds cell entries and no word entries: the memory arm runs
   its three-way on the cells' own entries. *)
let cell_driven (t : t) (h : Tid.t) : bool =
  not (Hashtbl.mem t.lm_env h) && Hashtbl.mem t.cell_env h
