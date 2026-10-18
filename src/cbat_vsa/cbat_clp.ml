(* ************************************************************************* *)
(*  *)
(* Copyright (C) Draper Laboratory. Licensed under project LICENSE. *)
(*  *)
(* This file is provided under the license found in the LICENSE file in *)
(* the top-level directory of this project. *)
(*  *)
(* This work is funded in part by ONR/NAWC Contract N6833518C0107. Its *)
(* content does not necessarily reflect the position or policy of the US *)
(* Government and no official endorsement should be inferred. *)
(*  *)
(* ************************************************************************* *)

(* The progression type and its constructors from the core; the set
   operations live in [Pieces]. *)

open Bap.Std
open Bin_prot.Std
open !Core

include Cbat_clp_core

let split_at_n = Cbat_clp_arith.split_at_n

(* The progression type, named for the [Pieces] signature. *)
type progression = t [@@deriving bin_io, sexp, compare]

(* The VSA_DEBUG census of the piece unions: canonical list lengths and
   cap events, dumped at exit. *)
#ifdef VSA_DEBUG
let census_len_counts = Stdlib.Array.make (Cbat_vsa_utils.max_pieces + 2) 0
let census_cap_hits = Stdlib.ref 0
let census_len (n : int) : unit =
  if n < Stdlib.Array.length census_len_counts then
    census_len_counts.(n) <- census_len_counts.(n) + 1
let census_cap () : unit = Stdlib.incr census_cap_hits
let () =
  Stdlib.at_exit (fun () ->
      Stdlib.Array.iteri
        (fun i n -> Printf.eprintf "hike-pieces-census: len.%d=%d\n%!" i n)
        census_len_counts;
      Printf.eprintf "hike-pieces-census: cap=%d\n%!" !census_cap_hits)
#endif

(* ====================== Pieces: the canonical progression union ======== *)

(* A canonical, capped union of progressions: sorted by unsigned minimum,
   disjoint, adjacent same-step runs merged, overlapping pieces hulled.
   The list is the set union; [] is bottom.  Smart constructors are the
   only way in; no raw list escapes except through [to_list].  The other
   fields are facts of the list, computed once when it is built: the
   circular hull (None when the union is its own hull; a hull is its own
   hull) and the four extrema.  Order, equality, sexp and bin_io are the
   list's alone. *)
module Pieces_base = struct
  type t =
    { pieces : progression list;
      hull : t option;
      min_u : Cbat_word.t option;
      max_u : Cbat_word.t option;
      min_s : Cbat_word.t option;
      max_s : Cbat_word.t option }

  module C = Cbat_clp_core
  module A = Cbat_clp_arith
  module U = Cbat_vsa_utils

  let extremum (f : C.t -> Cbat_word.t option)
      ~(better : Cbat_word.t -> Cbat_word.t -> Cbat_word.t)
      (ps : progression list) : Cbat_word.t option =
    List.fold ps ~init:None ~f:(fun acc p ->
        Cbat_word.keep_better ~better acc (f p))

  (* The smallest arc of the circle holding every piece, as a piece or
     the two arcs of one across the modulus; the empty union is its own
     hull. *)
  let hull_arcs (ps : progression list) : progression list =
    match ps with
    | [] | [ _ ] -> ps
    | p :: rest ->
      List.fold rest ~init:[ p ] ~f:(fun acc q -> C.union_arcs acc [ q ])

  (* A value with the given hull field and the extrema of its list. *)
  let with_hull (pieces : progression list) (hull : t option) : t =
    { pieces; hull;
      min_u = extremum C.min_elem ~better:(Cbat_word.min_by ~signed:false) pieces;
      max_u = extremum C.max_elem ~better:(Cbat_word.max_by ~signed:false) pieces;
      min_s =
        extremum C.min_elem_signed ~better:(Cbat_word.min_by ~signed:true) pieces;
      max_s =
        extremum C.max_elem_signed ~better:(Cbat_word.max_by ~signed:true) pieces }

  (* The one way to a value: derive the cached facts from the list.  A
     hull is its own hull, so a union that equals its hull, and the stored
     hull itself, keep none. *)
  let mk (pieces : progression list) : t =
    let arcs = hull_arcs pieces in
    if phys_equal arcs pieces
       || (List.length arcs = List.length pieces
           && List.for_all2_exn arcs pieces ~f:C.equal)
    then with_hull pieces None
    else with_hull pieces (Some (with_hull arcs None))

  let empty : t = mk []

  type repr = progression list [@@deriving bin_io, sexp, compare]

  let sexp_of_t (ps : t) : Sexp.t = sexp_of_repr ps.pieces
  let t_of_sexp (s : Sexp.t) : t = mk (repr_of_sexp s)
  let compare (a : t) (b : t) : int = compare_repr a.pieces b.pieces

  include Binable.Of_binable_with_uuid (struct
      type t = repr [@@deriving bin_io]
    end) (struct
      type nonrec t = t
      let to_binable (ps : t) : repr = ps.pieces
      let of_binable : repr -> t = mk
      let caller_identity = Bin_prot.Shape.Uuid.of_string "hike:cbat_clp.pieces/1"
    end)

  (* The union's bit width (its pieces' common width). *)
  let width_of (ps : t) : int =
    match ps.pieces with [] -> 0 | p :: _ -> C.bitwidth p

  let to_list (ps : t) : progression list = ps.pieces
  let fold (ps : t) ~(init : 'a) ~(f : 'a -> progression -> 'a) : 'a =
    List.fold ps.pieces ~init ~f
  let iter (ps : t) ~(f : progression -> unit) : unit = List.iter ps.pieces ~f
  let elements (ps : t) : Cbat_word.t list = List.concat_map ps.pieces ~f:C.iter

  let is_bottom (ps : t) : bool = List.is_empty ps.pieces
  let is_top (ps : t) : bool = List.exists ps.pieces ~f:C.is_top
  let bitwidth = width_of

  (* Cached per width, as [C.top] is. *)
  let top_cache : t array =
    Stdlib.Array.init 257 (fun i -> if i > 0 then mk [ C.top i ] else empty)

  let top (i : int) : t =
    if i > 0 && i < Stdlib.Array.length top_cache then top_cache.(i)
    else mk [ C.top i ]
  let bottom (_ : int) : t = empty

  (* The unsigned piece order: minimum, maximum, step, then the record. *)
  let compare_piece (p1 : progression) (p2 : progression) : int =
    let cmp_opt (a : Cbat_word.t option) (b : Cbat_word.t option) : int =
      match a, b with
      | None, None -> 0
      | None, Some _ -> -1
      | Some _, None -> 1
      | Some a, Some b -> Cbat_word.compare a b
    in
    let c = cmp_opt (C.min_elem p1) (C.min_elem p2) in
    if c <> 0 then c
    else
      let c = cmp_opt (C.max_elem p1) (C.max_elem p2) in
      if c <> 0 then c
      else
        let c = Cbat_word.compare (C.step_of p1) (C.step_of p2) in
        if c <> 0 then c else C.compare p1 p2

  (* The exact concatenation of two adjacent same-step finite pieces. *)
  let adjacent_merge (q : progression) (p : progression) : progression option =
    if C.is_infinite q || C.is_infinite p then None
    else
      (* A singleton continues its neighbour's run at the run's step. *)
      let step =
        if Cbat_word.is_one (C.cardn_of q) then C.step_of p else C.step_of q in
      let p_step =
        if Cbat_word.is_one (C.cardn_of p) then step else C.step_of p in
      if Cbat_word.is_zero step || not (Cbat_word.equal step p_step)
      then None
      else
        match C.finite_end q with
        | None -> None
        | Some q_end ->
          let expected_start = Cbat_word.add q_end step in
          let p_min =
            match C.min_elem p with Some m -> m | None -> C.base_of p in
          if not (Cbat_word.equal expected_start p_min) then None
          else
            let width = C.bitwidth q in
            let cardn = Cbat_word.add (C.cardn_of q) (C.cardn_of p) in
            match C.arcs ~width ~step ~cardn (C.base_of q), C.union q p with
            | [ merged ], [ u ] when C.equal merged u -> Some merged
            | _ -> None

  (* A piece small enough to enumerate exactly. *)
  let small_card (p : progression) : bool =
    (not (C.is_infinite p))
    && not (Cbat_word.gt_int (C.cardinality p) U.fin_set_size)

  (* The unsigned ranges are disjoint: no shared element is possible.
     A cheap pre-check that spares the exact machinery below. *)
  let range_disjoint (p : progression) (q : progression) : bool =
    match C.max_elem p, C.min_elem q with
    | Some pmax, Some qmin when Cbat_word.(<) pmax qmin -> true
    | _ -> (
      match C.max_elem q, C.min_elem p with
      | Some qmax, Some pmin -> Cbat_word.(<) qmax pmin
      | _ -> false)

  (* Exact shared-element test: enumeration when a side is small,
     same-step range arithmetic, else the conservative may-test (merging
     a non-overlapping pair is sound, only imprecise). *)
  let overlap_exact (p : progression) (q : progression) : bool =
    if C.is_bottom p || C.is_bottom q then false
    else if range_disjoint p q then false
    else if Cbat_word.is_one (C.cardn_of p) then C.elem (C.base_of p) q
    else if Cbat_word.is_one (C.cardn_of q) then C.elem (C.base_of q) p
    else if small_card p then List.exists (C.iter p) ~f:(fun x -> C.elem x q)
    else if small_card q then List.exists (C.iter q) ~f:(fun x -> C.elem x p)
    else if
      C.is_circular p || C.is_circular q || C.is_infinite p || C.is_infinite q
    then not (C.is_bottom (C.intersection p q))
    else
      let s_p = C.step_of p and s_q = C.step_of q in
      if Cbat_word.equal s_p s_q then begin
        let d = Cbat_word.sub (C.base_of q) (C.base_of p) in
        if not (Cbat_word.is_zero (Cbat_word.modulo d s_p)) then false
        else
          match C.finite_end p, C.finite_end q with
          | Some e_p, Some e_q ->
            let lo = Cbat_word.max (C.base_of p) (C.base_of q) in
            let hi = Cbat_word.min e_p e_q in
            Cbat_word.(<=) lo hi
          | _ -> not (C.is_bottom (C.intersection p q))
      end
      else not (C.is_bottom (C.intersection p q))

  (* [merge_arc acc a] is the canonical union of a canonical ascending
     disjoint list [acc] and one piece [a].  Overlaps hull, adjacent
     same-step runs join, contained pieces drop; a hull that crosses the
     modulus is two arcs, re-placed from the high one.  The accumulator
     stays ascending, disjoint, single width. *)
  let rec merge_arc (acc : progression list) (a : progression)
    : progression list =
    (* [same]: [left] is still the untouched prefix of [acc]. *)
    let rec scan same left = function
      | [] -> List.rev (a :: left)
      | (q :: rest) as cur ->
        if C.subset a q then (if same then acc else List.rev_append left cur)
        else if C.subset q a then scan false left rest
        else
          let hull =
            if overlap_exact a q then Some (C.union a q)
            else
              Option.map ~f:(fun r -> [ r ])
                (if compare_piece a q < 0 then adjacent_merge a q
                 else adjacent_merge q a)
          in
          (match hull with
           | None ->
             if compare_piece a q < 0 then List.rev_append left (a :: q :: rest)
             else scan same (q :: left) rest
           | Some arcs ->
             List.fold (List.rev arcs)
               ~init:(List.rev_append left rest) ~f:merge_arc)
    in
    scan true [] acc

  (* The streaming combine of an ascending stream.  While hulls stay
     disjoint a piece can only meet the tail.  Once its minimum reaches
     the largest placed maximum (kept with each placed piece), an
     overlap can hide behind an interleaved tail, so it is checked against
     every placed piece.  A hull across the modulus or a hidden overlap
     marks the stream [general]: the inputs ([raw], newest first) are
     then re-placed by [merge_arc] at [close].  No sort runs here. *)
  type acc =
    { placed : (progression * Cbat_word.t option) list;
      raw : progression list;
      n : int;
      general : bool }

  let empty_acc = { placed = []; raw = []; n = 0; general = false }

  (* [push acc p]: [p] is not below the last pushed piece; an exact
     repeat is dropped. *)
  let push (acc : acc) (p : progression) : acc =
    match acc.raw with
    | q :: _ when compare_piece q p = 0 -> acc
    | _ ->
#ifdef VSA_DEBUG
      assert (match acc.raw with q :: _ -> compare_piece q p <= 0 | [] -> true);
#endif
      let acc = { acc with raw = p :: acc.raw } in
      if acc.general then acc
      else
        let place x placed =
          let hi =
            match placed, C.max_elem x with
            | [], m -> m
            | (_, Some a) :: _, Some b -> Some (Cbat_word.max a b)
            | _ -> None
          in
          (x, hi) :: placed
        in
        let hidden x = function
          | [] -> false
          | (_, hi) :: _ as placed ->
            (match hi, C.min_elem x with
             | Some hi, Some lo -> Cbat_word.(<=) lo hi
             | _ -> true)
            && List.exists placed ~f:(fun (q, _) -> overlap_exact x q)
        in
        match acc.placed with
        | [] -> { acc with placed = place p []; n = 1 }
        | (q, _) :: tl ->
          let join r =
            if hidden r tl then { acc with general = true }
            else { acc with placed = place r tl }
          in
          if overlap_exact p q then begin
            match C.union p q with
            | [ r ] -> join r
            | _ -> { acc with general = true }
          end
          else (
            match adjacent_merge q p with
            | Some r -> join r
            | None ->
              if hidden p acc.placed then { acc with general = true }
              else { acc with placed = place p acc.placed; n = acc.n + 1 })

  (* The combined pieces, ascending. *)
  let combined (acc : acc) : progression list =
    if acc.general then List.fold (List.rev acc.raw) ~init:[] ~f:merge_arc
    else List.rev_map acc.placed ~f:fst

  (* Mixed widths collapse to top at the widest — a producer's rule; a
     canonical value is single width. *)
  let collapse_width (ps : progression list) : progression list =
    match ps with
    | [] | [ _ ] -> ps
    | p :: rest ->
      let w = C.bitwidth p in
      if List.for_all rest ~f:(fun q -> Stdlib.Int.equal (C.bitwidth q) w)
      then ps
      else
        [ C.top
            (List.fold rest ~init:w
               ~f:(fun a q -> Stdlib.max a (C.bitwidth q))) ]

  (* The cap hull of two ascending disjoint pieces: one piece the
     canonicalizer cannot split back apart.  A union across the modulus
     circulates to its circular grid; otherwise the plain union. *)
  let coalesce (pi : progression) (pj : progression) : progression =
    match C.union pi pj with
    | [ r ] -> r
    | arcs ->
      (match A.unit_of arcs with
       | Some (base, step, _) -> C.infinite (base, step)
       | None -> C.top (C.bitwidth pi))

  (* A union of at most [U.max_pieces] pieces is kept as it is; a larger
     one is a single hull piece. *)
  let within_budget (ps : progression list) : bool =
    List.length ps <= U.max_pieces

  (* The one-piece hull of a union that leaves the budget.  A hull that
     traverses the wrap circulates to its circular grid. *)
  let hull (ps : progression list) : progression list =
    match ps with
    | [] -> []
    | p :: rest ->
#ifdef VSA_DEBUG
      census_cap ();
#endif
      [ List.fold rest ~init:p ~f:coalesce ]

  let cap (ps : progression list) : progression list =
    if within_budget ps then ps else hull ps

  (* The streaming consumer's end: a union past the budget collapses to
     its hull. *)
  let fallbacks = ref 0
  let fallback_count () : int = !fallbacks

  let close (acc : acc) : t =
    if acc.general then incr fallbacks;
    let r =
      if (not acc.general) && acc.n <= U.max_pieces then combined acc
      else cap (combined acc) in
#ifdef VSA_DEBUG
    census_len (List.length r);
#endif
    mk r

  (* The producer finish for an already-ordered list. *)
  let finish (ps : progression list) : t =
    close (List.fold ps ~init:empty_acc ~f:push)

  (* The pieces of a result: its arcs, ascending and disjoint. *)
  let of_arcs (arcs : progression list) : t =
    finish (List.filter arcs ~f:(fun a -> not (C.is_bottom a)))

  let of_progression (p : progression) : t = of_arcs [ p ]

  module Image = Map.Make (struct
      type t = progression [@@deriving sexp]
      let compare = compare_piece
    end)

  (* General progression images can move their minima independently.
     Their producer maintains the result index as each arc is computed. *)
  let produce (iter : (progression -> unit) -> unit) : t =
    let image = ref Image.empty in
    iter (fun p ->
        if not (C.is_bottom p) then image := Map.set !image ~key:p ~data:());
    finish (collapse_width (Map.keys !image))

  (* Merge two producers' ascending streams without combining or capping. *)
  let merge_progressions a b = List.merge a b ~compare:compare_piece

  (* The producer supplies disjoint, ascending, live pieces. *)
  let of_progressions (ps : progression list) : t =
#ifdef VSA_DEBUG
    assert (List.is_sorted ps ~compare:compare_piece);
    assert (List.for_all ps ~f:(fun p -> not (C.is_bottom p || C.crosses p)));
#endif
    finish ps

  (* Maximal constant-difference runs of a sorted element list; each run
     is one exact progression (a run too sparse to stay finite
     over-approximates). *)
  let runs_from_sorted_elements ~(width : int) (els : Cbat_word.t list)
    : progression list =
#ifdef VSA_DEBUG
    let () = assert (List.is_sorted els ~compare:Cbat_word.compare) in
#endif
    (* One run as a progression when the progression is exactly the run
       (the cardinality check rejects a circular over-approximation), else
       as its singletons. *)
    let of_run start step count (run_els : Cbat_word.t list) : progression list =
      match step with
      | None -> [ C.singleton start ]
      | Some s ->
        let piece =
          C.create ~width ~step:s
            ~cardn:(Cbat_word.of_int ~width:(width + 1) count) start in
        let exact =
          match Cbat_word.to_int (C.cardinality piece) with
          | Ok n -> n = count
          | Error _ -> false
        in
        if exact then [ piece ] else List.map run_els ~f:C.singleton
    in
    let rec go acc start prev step count run_els = function
      | [] -> List.rev_append (of_run start step count run_els) acc
      | x :: rest ->
        let d = Cbat_word.sub x prev in
        (match step with
         | None -> go acc start x (Some d) 2 (x :: run_els) rest
         | Some s ->
           if Cbat_word.equal d s then
             go acc start x (Some s) (count + 1) (x :: run_els) rest
           else
             go
               (List.rev_append (of_run start step count run_els) acc)
               x x None 1 [ x ] rest)
    in
    match els with
    | [] -> []
    | x :: rest -> go [] x x None 1 [ x ] rest

  (* [of_list] requires an ascending, deduped word list — a precondition,
     not a sort.  The run builder consumes it directly. *)
  let of_list ~(width : int) (l : Cbat_word.t list) : t =
    if width <= 0 then empty
    else
      match l with
      (* A point address, the common key: its one run is its singleton. *)
      | [ w ] -> mk [ C.singleton (Cbat_word.extract_exn ~hi:(width - 1) ~lo:0 w) ]
      | _ ->
        let l = List.map l ~f:(Cbat_word.extract_exn ~hi:(width - 1) ~lo:0) in
        finish (List.rev (runs_from_sorted_elements ~width l))

  let singleton (w : Cbat_word.t) : t = mk [ C.singleton w ]

  let min_elem (ps : t) : Cbat_word.t option = ps.min_u
  let max_elem (ps : t) : Cbat_word.t option = ps.max_u
  let min_elem_signed (ps : t) : Cbat_word.t option = ps.min_s
  let max_elem_signed (ps : t) : Cbat_word.t option = ps.max_s

  (* Saturating sum of the pieces' cardinalities. *)
  let cardinality (ps : t) : Cbat_word.t =
    match ps.pieces with
    | [ p ] -> C.cardinality p
    | pieces ->
    let width = width_of ps in
    if width = 0 then Cbat_word.zero 1
    else
      let w1 = width + 1 in
      List.fold pieces ~init:(Cbat_word.zero w1) ~f:(fun acc p ->
          let c = Cbat_word.cast Bil.UNSIGNED w1 (C.cardinality p) in
          let s = Cbat_word.add acc c in
          if Cbat_word.(<) s acc then Cbat_word.ones w1 else s)

  (* [gt_int (cardinality ps) n] without building the sum. *)
  let card_exceeds (n : int) (ps : t) : bool =
    let rec go (left : int) = function
      | [] -> false
      | p :: rest ->
        let c = Cbat_word.to_int_sat (C.cardinality p) in
        c > left || go (left - c) rest
    in
    go n ps.pieces

  let elem (w : Cbat_word.t) (ps : t) : bool =
    List.exists ps.pieces ~f:(fun p -> C.elem w p)

  let equal (a : t) (b : t) : bool =
    phys_equal a b
    ||
    (match a.pieces, b.pieces with
     | [ x ], [ y ] -> C.equal x y
     | a, b ->
       List.length a = List.length b && List.for_all2_exn a b ~f:C.equal)

  let overlap (a : t) (b : t) : bool =
    List.exists a.pieces ~f:(fun pa ->
        List.exists b.pieces ~f:(fun pb -> overlap_exact pa pb))

  let splits_by (ps : t) (w : Cbat_word.t) : bool =
    List.for_all ps.pieces ~f:(fun p -> C.splits_by p w)

  let is_ascending (ps : t) : bool = List.for_all ps.pieces ~f:C.is_ascending
  let is_descending (ps : t) : bool = List.for_all ps.pieces ~f:C.is_descending
  let is_circular (ps : t) : bool = List.for_all ps.pieces ~f:C.is_circular

  (* Union-order coverage: every piece of [a] is contained in [b]'s union
     (a single covering piece, or a small piece covered element-wise). *)
  let precedes (a : t) (b : t) : bool =
    List.for_all a.pieces ~f:(fun pa ->
        List.exists b.pieces ~f:(fun pb -> C.subset pa pb)
        || (small_card pa
            && List.for_all (C.iter pa) ~f:(fun x ->
                List.exists b.pieces ~f:(fun pb -> C.elem x pb))))

  (* Union's own construction: both operands are ascending and disjoint,
     so a two-way merge by minimum gives an ascending stream each of whose
     pieces can only meet the placed tail — combine tail-only, in order,
     with no scan and no sort.  A width mismatch (a producer's rule)
     collapses to top at the widest; only a hull across the modulus falls
     back. *)
  let union (a : t) (b : t) : t =
    match a.pieces, b.pieces with
    | [], _ -> b
    | _, [] -> a
    | _ when equal a b -> a
    | _ when not (Stdlib.Int.equal (width_of a) (width_of b)) ->
      finish (collapse_width (List.append a.pieces b.pieces))
    | ap, bp ->
      (* [b] ascends, so each piece can only meet the placed tail; place
         it exactly. *)
      let merged = List.fold bp ~init:ap ~f:merge_arc in
      (* Every piece of [b] sat inside [a]'s pieces: [a] is the union. *)
      if phys_equal merged ap then a else finish merged

  (* Exact meet of one pair: a small side enumerates element-wise, else
     the CLP meet (sound over-approximation). *)
  let pair_intersection (pa : progression) (pb : progression)
    : progression list =
    if C.is_bottom pa || C.is_bottom pb then []
    else
      if small_card pa || small_card pb then begin
        let small_p, big_p = if small_card pa then pa, pb else pb, pa in
        let els = List.filter (C.iter small_p) ~f:(fun x -> C.elem x big_p) in
        runs_from_sorted_elements ~width:(C.bitwidth small_p) els
      end
      else
        let r = C.intersection pa pb in
        if C.is_bottom r then [] else [ r ]

  let intersection (a : t) (b : t) : t =
    if is_bottom a || is_bottom b then empty
    else if equal a b then a
    else
      produce (fun emit ->
          List.iter a.pieces ~f:(fun pa ->
              List.iter b.pieces ~f:(fun pb ->
                  List.iter (pair_intersection pa pb) ~f:emit)))

  (* The survivors of one finite non-wrapping grid after removing [es]
     (sorted ascending, all on the grid). *)
  let finite_survivors (a : progression) (es : Cbat_word.t list)
    : progression list =
    let width = C.bitwidth a in
    let step = C.step_of a in
    let end_of_a =
      match C.finite_end a with Some e -> e | None -> C.base_of a in
    let seg lo hi =
      if Cbat_word.(>) lo hi then None
      else
        Some
          (C.create ~width ~step
             ~cardn:(C.cardn_from_bounds lo step hi) lo)
    in
    let rec go acc start = function
      | [] ->
        (match seg start end_of_a with
         | Some s -> List.rev (s :: acc)
         | None -> List.rev acc)
      | r :: rest ->
        let acc =
          if Cbat_word.(<=) (Cbat_word.add start step) r then
            match seg start (Cbat_word.sub r step) with
            | Some s -> s :: acc
            | None -> acc
          else acc
        in
        let start' = Cbat_word.add r step in
        if Cbat_word.(<) start' r then List.rev acc else go acc start' rest
    in
    go [] (C.base_of a) es

  (* The survivors of an ascending ray. *)
  let ascending_survivors (a : progression) (es : Cbat_word.t list)
    : progression list =
    let width = C.bitwidth a in
    let step = C.step_of a in
    let seg lo hi =
      if Cbat_word.(>) lo hi then None
      else
        Some
          (C.create ~width ~step
             ~cardn:(C.cardn_from_bounds lo step hi) lo)
    in
    let rec go acc start = function
      | [] ->
        List.rev (C.create_ascending ~width ~base:start ~step :: acc)
      | r :: rest ->
        let acc =
          if Cbat_word.(<=) (Cbat_word.add start step) r then
            match seg start (Cbat_word.sub r step) with
            | Some s -> s :: acc
            | None -> acc
          else acc
        in
        let start' = Cbat_word.add r step in
        if Cbat_word.(<) start' r then List.rev acc else go acc start' rest
    in
    go [] (C.base_of a) es

  (* The survivors of a descending ray; [es] arrives ascending. *)
  let descending_survivors (a : progression) (es : Cbat_word.t list)
    : progression list =
    let width = C.bitwidth a in
    let step = C.step_of a in
    let es = List.rev es in
    let seg lo hi =
      if Cbat_word.(>) lo hi then None
      else
        Some
          (C.create ~width ~step
             ~cardn:(C.cardn_from_bounds lo step hi) lo)
    in
    let rec go acc start = function
      | [] ->
        List.rev (C.create_descending ~width ~base:start ~step :: acc)
      | r :: rest ->
        let acc =
          if Cbat_word.(>=) start (Cbat_word.add r step) then
            match seg (Cbat_word.add r step) start with
            | Some s -> s :: acc
            | None -> acc
          else acc
        in
        let start' = Cbat_word.sub r step in
        if Cbat_word.(>) start' r then List.rev acc else go acc start' rest
    in
    go [] (C.base_of a) es

  let small_total (ps : progression list) : bool =
    List.for_all ps ~f:(fun p -> not (C.is_infinite p))
    && (let budget = U.fin_set_size in
        let sum =
          List.fold ps ~init:0 ~f:(fun acc p ->
              if acc > budget then acc
              else
                acc
                + (match Cbat_word.to_int (C.cardinality p) with
                   | Ok n -> n
                   | Error _ -> budget + 1))
        in
        sum <= budget)

  (* The subtrahend pieces' hulls may interleave, so their enumerations
     are merged, not concatenated. *)
  let merge_distinct =
    Cbat_vsa_utils.merge_dedup ~compare:Cbat_word.compare

  (* The CLP difference of [a] and each of [bs] in turn. *)
  let minus_all (a : progression) (bs : progression list) : progression list =
    List.fold bs ~init:[ a ] ~f:(fun acc b ->
        List.concat_map acc ~f:(fun x -> C.diff x b))

  (* [a] minus the union of [bs]: exact when the cheap side enumerates,
     the sound CLP identity otherwise. *)
  let rec diff_piece (a : progression) (bs : progression list)
    : progression list =
    if C.is_bottom a then []
    else if small_card a then
      let survivors =
        List.filter (C.iter a) ~f:(fun x ->
            not (List.exists bs ~f:(fun b -> C.elem x b)))
      in
      runs_from_sorted_elements ~width:(C.bitwidth a) survivors
    else if small_total bs then begin
      let es =
        List.fold bs ~init:[] ~f:(fun acc b ->
            merge_distinct acc (List.filter (C.iter b) ~f:(fun x -> C.elem x a)))
      in
      if Cbat_word.is_one (C.cardn_of a) then (if es = [] then [ a ] else [])
      else if C.is_ascending a then ascending_survivors a es
      else if C.is_descending a then descending_survivors a es
      else if not (C.is_infinite a) then finite_survivors a es
      else minus_all a bs
    end
    else minus_all a bs

  let diff (a : t) (b : t) : t =
    if is_bottom a || equal a b then empty
    else if is_bottom b then a
    else produce (fun emit ->
        List.iter a.pieces ~f:(fun pa ->
            List.iter (diff_piece pa b.pieces) ~f:emit))

  (* Unary images enter their ordered index as they are produced; an
     image is a piece or the two arcs of one across the modulus. *)
  let map (f : progression -> progression list) (ps : t) : t =
    match ps.pieces with
    | [] -> empty
    | [ p ] -> of_arcs (f p)
    | pieces ->
      produce (fun emit -> List.iter pieces ~f:(fun p -> List.iter (f p) ~f:emit))

  let lift2 (f : progression -> progression -> progression list) (a : t) (b : t)
    : t =
    match a.pieces, b.pieces with
    | [ pa ], [ pb ] -> of_arcs (f pa pb)
    | ap, bp -> produce (fun emit ->
        List.iter ap ~f:(fun pa ->
            List.iter bp ~f:(fun pb -> List.iter (f pa pb) ~f:emit)))

  (* Each piece produces any number of result pieces directly into the
     ordered image. *)
  let map_parts (f : progression -> progression list) (ps : t) : t =
    produce (fun emit ->
        List.iter ps.pieces ~f:(fun q -> List.iter (f q) ~f:emit))

  (* Each pair likewise. *)
  let lift2_parts (f : progression -> progression -> progression list)
      (a : t) (b : t) : t =
    produce (fun emit ->
        List.iter a.pieces ~f:(fun qa ->
            List.iter b.pieces ~f:(fun qb -> List.iter (f qa qb) ~f:emit)))

  let point_pieces (ps : progression list) : bool =
    List.for_all ps ~f:(fun p -> Cbat_word.is_one (C.cardn_of p))

  let finite_pieces (ps : progression list) : bool =
    List.for_all ps ~f:(fun p -> not (C.is_infinite p))

  (* [ps] shifted by [c], ascending.  Pieces and high arcs that stay below
     2^w keep their order; whatever wraps lands below [c], ahead of all of
     them.  Whole-wrapped pieces stay ordered; a low arc of a crossing piece
     (or a two-element piece the wrap reorders) is out of place and is the
     only thing sorted. *)
  let shifted (ps : progression list) (c : Cbat_word.t) : progression list =
    let above, whole, partial =
      List.fold_right ps ~init:([], [], []) ~f:(fun p (u, w, x) ->
          let base = C.base_of p in
          let wraps = Cbat_word.(<) (Cbat_word.add base c) base in
          List.fold_right (C.translate p c) ~init:(u, w, x)
            ~f:(fun q (u, w, x) ->
                if not (Cbat_word.(<) (C.base_of q) c) then (q :: u, w, x)
                else if wraps then (u, q :: w, x)
                else (u, w, q :: x)))
    in
    List.append
      (merge_progressions (List.sort partial ~compare:compare_piece) whole)
      above

  (* Ascending rows pushed in merged order, the lowest head first. *)
  let stream (rows : progression list list) : t =
    let rec go acc = function
      | [] -> close acc
      | rows ->
        let best =
          List.reduce_exn rows ~f:(fun x y ->
              if compare_piece (List.hd_exn x) (List.hd_exn y) <= 0 then x
              else y) in
        let acc = push acc (List.hd_exn best) in
        go acc
          (List.filter_map rows ~f:(fun r ->
               if phys_equal r best then
                 (match r with _ :: (_ :: _ as tl) -> Some tl | _ -> None)
               else Some r))
    in
    go empty_acc rows

  (* Each piece of [ps] shifted by each delta: one row per delta. *)
  let shift_all (ps : progression list) (deltas : Cbat_word.t list) : t =
    stream (List.map deltas ~f:(shifted ps))

  (* A shift by constants: one operand all single points, the other all
     finite pieces of the same width.  [None]: general pairs. *)
  let shift_operands (a : t) (b : t) : (progression list * progression list) option =
    match a.pieces, b.pieces with
    | [], _ | _, [] -> None
    | _ when not (Stdlib.Int.equal (width_of a) (width_of b)) -> None
    | ap, bp ->
      if point_pieces bp && finite_pieces ap then Some (ap, bp)
      else if point_pieces ap && finite_pieces bp then Some (bp, ap)
      else None

  let add (a : t) (b : t) : t =
    match a.pieces, b.pieces with
    | [ _ ], [ _ ] -> lift2 A.add a b
    | _ ->
      (match shift_operands a b with
       | Some (ps, pts) -> shift_all ps (List.map pts ~f:C.base_of)
       | None -> lift2 A.add a b)

  let sub (a : t) (b : t) : t =
    match a.pieces, b.pieces with
    | [ _ ], [ _ ] -> lift2 A.sub a b
    | (_ :: _ as ap), (_ :: _ as bp)
      when point_pieces bp && finite_pieces ap
           && Stdlib.Int.equal (width_of a) (width_of b) ->
      shift_all ap (List.map bp ~f:(fun p -> Cbat_word.neg (C.base_of p)))
    | _ -> lift2 A.sub a b
  let mul = lift2 A.mul
  let div = lift2 A.div
  let sdiv = lift2 A.sdiv
  let modulo = lift2 A.modulo
  let smodulo = lift2 A.smodulo
  let arshift = lift2_parts (fun a b -> List.concat (A.arshift_parts a b))
  let rshift = lift2_parts (fun a b -> List.concat (A.rshift_parts a b))
  let lshift = lift2_parts (fun a b -> List.concat (A.lshift_parts a b))
  let logand = lift2 A.logand
  let logor = lift2 A.logor
  let concat = lift2 A.concat

  (* Each operand's derived values are built once, not once per pair. *)
  let logxor (a : t) (b : t) : t =
    match a.pieces, b.pieces with
    | [ pa ], [ pb ] -> of_arcs (A.logxor pa pb)
    | [], _ | _, [] -> empty
    | ap, bp ->
      let ob = List.map bp ~f:(fun pb -> A.xor_operand pb) in
      produce (fun emit ->
          List.iter ap ~f:(fun pa ->
              let oa = A.xor_operand pa in
              List.iter ob ~f:(fun ob ->
                  List.iter (A.logxor_ops oa ob) ~f:emit)))

  let lnot = map (fun p -> [ C.lnot p ])
  (* Negation reverses disjoint finite ranges.  Only a piece holding 0
     wraps: 0 comes first, the rest of its image last. *)
  let neg (ps : t) : t =
    let rec disjoint = function
      | p :: (q :: _ as rest) ->
        (match C.max_elem p, C.min_elem q with
         | Some hi, Some lo -> Cbat_word.(<) hi lo && disjoint rest
         | _ -> false)
      | _ -> true
    in
    match ps.pieces with
    | [] | [ _ ] -> map A.neg ps
    | pieces when finite_pieces pieces && disjoint pieces ->
      let head, tail =
        match pieces with
        | p :: rest when Cbat_word.is_zero (C.base_of p) -> Some p, rest
        | _ -> None, pieces
      in
      let rest = List.concat (List.rev_map tail ~f:A.neg) in
      stream
        [ (match Option.map head ~f:A.neg with
           | None -> rest
           | Some [ low; high ] -> (low :: rest) @ [ high ]
           | Some arcs -> arcs @ rest) ]
    | _ -> map A.neg ps

  let extract ?hi ?lo (ps : t) : t =
    let w = bitwidth ps in
    let full =
      (match hi with None -> true | Some h -> Stdlib.Int.equal h (w - 1))
      && (match lo with None | Some 0 -> true | Some _ -> false) in
    if full then ps
    else map_parts (A.extract_parts ?hi ?lo) ps

  let cast c sz (ps : t) : t =
    if Stdlib.Int.equal sz (bitwidth ps) then ps
    else map_parts (A.cast_parts c sz) ps

  let translate (ps : t) (delta : Cbat_word.t) : t =
    if Cbat_word.is_zero delta then ps
    else map (fun p -> C.translate p delta) ps

  (* The widening pairing: the two sorted atom lists merge with an origin
     tag, then one pass pairs the corresponding atoms.  An overlapping
     couple is a pair; otherwise the nearer couple pairs (a strictly
     smaller gap to the next opposite-side atom holds the left atom for
     it), ties keeping the lower minimum.  An atom without a counterpart
     stays its own atom — no excess hull, no growth attribution.  A top
     couple collapses the whole value (the studied termination escape). *)
  let positional (f : progression -> progression -> progression list) (a : t)
      (b : t) : t =
    match a.pieces, b.pieces with
    | [], [] -> empty
    | [], _ -> b
    | _, [] -> a
    | _ ->
      (* A successor may drop old elements or split its covering piece.
         Pair against the cumulative value so growth reaches the widener. *)
      let b = union a b in
      (* The origin tag: [true] is the old iterate [a]. *)
      let rec merge xs ys =
        match xs, ys with
        | [], ys -> ys
        | xs, [] -> xs
        | ((_, p) as xp) :: xt, ((_, q) as yp) :: yt ->
          if compare_piece p q <= 0 then xp :: merge xt ys
          else yp :: merge xs yt
      in
      let merged =
        merge
          (List.map a.pieces ~f:(fun p -> (true, p)))
          (List.map b.pieces ~f:(fun p -> (false, p)))
      in
      (* The unsigned distance from [p]'s upper end to [q]'s lower end,
         zero when the spans meet, unbounded when [p] has no maximum. *)
      let gap (p : progression) (q : progression) : Cbat_word.t =
        let w1 = Stdlib.max (C.bitwidth p) (C.bitwidth q) + 1 in
        match C.max_elem p, C.min_elem q with
        | Some hi, Some lo ->
          if Cbat_word.(<=) lo hi then Cbat_word.zero w1
          else Cbat_word.sub lo hi
        | _ -> Cbat_word.ones w1
      in
      let top_hit = Stdlib.ref false in
      let rec pass emit = function
        | [] -> ()
        | [ (_, p) ] -> emit p
        | (s1, p1) :: ((s2, p2) :: rest as tl) ->
          if s1 = s2 then begin emit p1; pass emit tl end
          else begin
            (* [f] is directional: the old iterate is the left operand. *)
            let old, new_ = if s1 then p1, p2 else p2, p1 in
            if overlap_exact p1 p2 then pair emit old new_ rest
            else
              let nearer =
                List.find_map rest ~f:(fun (s, q) ->
                    if s <> s2 then Some q else None)
              in
              match nearer with
              | Some q when Cbat_word.(<) (gap p2 q) (gap p1 p2) ->
                emit p1; pass emit tl
              | _ -> pair emit old new_ rest
          end
      and pair emit old new_ rest =
        let r = f old new_ in
        if List.exists r ~f:C.is_top then top_hit := true
        else List.iter r ~f:emit;
        pass emit rest
      in
      let pieces = produce (fun emit -> pass emit merged) in
      if !top_hit then top (width_of b) else pieces

  let widen_join = positional C.widen_join
  let extrapolate_steps ~steps a b = positional (C.extrapolate_steps ~steps) a b

  (* ---- the circular hull: one arc of the circle ---- *)

  let circular_hull (ps : t) : t =
    match ps.hull with None -> ps | Some h -> h

  (* The hull of two hulls. *)
  let hull_union (a : t) (b : t) : t = of_arcs (C.union_arcs a.pieces b.pieces)

  (* Sum and difference of two hulls, each result joined into one hull. *)
  let hull_add (a : t) (b : t) : t = of_arcs (A.add_l a.pieces b.pieces)
  let hull_sub (a : t) (b : t) : t = of_arcs (A.sub_l a.pieces b.pieces)

  (* [p] met with a hull: the hull of its meets with the hull's pieces. *)
  let hull_intersection (p : progression) (r : t) : t =
    of_arcs
      (List.fold r.pieces ~init:[] ~f:(fun acc a ->
           let i = C.intersection p a in
           if C.is_bottom i then acc else C.union_arcs acc [ i ]))

  (* The step of a hull: the progression it denotes (0 for a singleton). *)
  let hull_step (h : t) : Cbat_word.t =
    match h.pieces with
    | [] -> Cbat_word.zero 1
    | [ p ] -> C.step_of p
    | pieces ->
      (match A.unit_of pieces with
       | Some (_, step, _) -> step
       | None -> C.step_of (List.hd_exn pieces))

  (* The hull of an ascending, deduplicated word list. *)
  let hull_of_list ~(width : int) (l : Cbat_word.t list) : t =
    of_arcs (C.of_list ~width l)

  (* The step-1 interval [lo, hi] (a pair with [hi < lo] is the circular
     interval across the modulus). *)
  let interval ~(width : int) (lo : Cbat_word.t) (hi : Cbat_word.t) : t =
    of_arcs (C.interval ~width lo hi)

  (* Widening of two hulls by the progression rule [f].  A hull across
     the modulus widens to its circular grid unless it is stable. *)
  let widen_hulls (f : progression -> progression -> progression list)
      (a : t) (b : t) : t =
    match a.pieces, b.pieces with
    | [ x ], [ y ] -> of_arcs (f x y)
    | [], _ -> b
    | _ when equal a b -> a
    | ap, bp ->
      let u = C.union_arcs ap bp in
      match u, A.unit_of u with
      | _ :: _ :: _, Some (base, step, _) when precedes a b ->
        mk [ C.infinite (base, step) ]
      | _ -> of_arcs u

  let pp ppf (ps : t) =
    match ps.pieces with
    | [] -> ()
    | [ p ] -> C.pp ppf p
    | (low :: _) as pieces ->
      (match A.unit_of pieces, C.finite_end low with
       | Some (base, step, cardn), Some last ->
         C.pp_span ppf ~width:(C.bitwidth low) ~base ~step ~cardn ~last
       | _ -> ())
  let join = union
  let meet = intersection
end

let interval = Pieces_base.interval

(* ==================== Exact: the uncapped flat element array ========== *)

(* The exact finite tier as a flat array: the elements as words at the
   declared width, unsigned, strictly ascending.  The array is the
   canonical form, so structural equality is set equality; the empty
   array is bottom and the width survives in the record.  It is never
   mutated after its producer builds it.  Unlike [Pieces], the set is
   uncapped and unbudgeted; the caller's canonical promotion applies the
   budget.  Ordered images write their array directly; other images
   maintain an ordered bit-prefix set while computing their elements. *)
module Exact_base = struct
  module W = Cbat_word

  type t = { width : int; words : W.t array }
  [@@deriving bin_io, sexp, compare]

  let count (t : t) : int = Array.length t.words

  let is_bottom (t : t) : bool = Array.is_empty t.words

  let nth (t : t) (i : int) : W.t = t.words.(i)

  let elements (t : t) : W.t list = Array.to_list t.words
  let iter = elements

  (* An element at [width], unsigned: a narrower or wider word is
     zero-extended or truncated, as [W.extract_exn] slices. *)
  let at_width (width : int) (w : W.t) : W.t =
    if W.bitwidth w <> width then W.extract_exn ~hi:(width - 1) w
    else if W.is_signed w then W.unsigned w else w

  (* An image producer's local Patricia set. Branch bits decrease along
     each path; the zero branch precedes the one branch unsigned. *)
  type image =
    | Empty
    | Point of W.t
    | Branch of {
        sample : W.t;
        bit : int;
        mutable low : image;
        mutable high : image;
      }

  let bit_set (w : W.t) (bit : int) : bool =
    match w with
    | W.Small (v, _, _) -> bit < 62 && v land (1 lsl bit) <> 0
    | W.W64 (v, _, _) ->
      not (Stdlib.Int64.equal
             (Stdlib.Int64.logand v (Stdlib.Int64.shift_left 1L bit)) 0L)
    | W.Big (v, _, _) -> Z.testbit v bit

  let of_iter ~(width : int) ~(iter : (W.t -> unit) -> unit) : t =
    let size = ref 0 in
    let branch w tree sample bit =
      incr size;
      let low, high =
        if bit_set w bit then tree, Point w else Point w, tree in
      Branch { sample; bit; low; high } in
    let rec add tree w =
      match tree with
      | Empty -> incr size; Point w
      | Point sample ->
        (match W.lead_1_bit (W.logxor sample w) with
         | None -> tree
         | Some bit -> branch w tree sample bit)
      | Branch b ->
        (match W.lead_1_bit (W.logxor b.sample w) with
         | None -> tree
         | Some bit when bit > b.bit -> branch w tree b.sample bit
         | Some _ ->
           if bit_set w b.bit then b.high <- add b.high w
           else b.low <- add b.low w;
           tree) in
    let tree = ref Empty in
    iter (fun w -> tree := add !tree (at_width width w));
    let words = Array.create ~len:!size (W.zero width) in
    let next = ref 0 in
    let rec emit = function
      | Empty -> ()
      | Point w -> words.(!next) <- w; incr next
      | Branch b -> emit b.low; emit b.high in
    emit !tree;
    { width; words }

  let of_list ~(width : int) (l : W.t list) : t =
    of_iter ~width ~iter:(fun emit -> List.iter l ~f:emit)

  (* The producer has already normalized, ordered and deduplicated [l]. *)
  let of_sorted_list ~(width : int) (l : W.t list) : t =
    let words = Array.of_list l in
#ifdef VSA_DEBUG
    assert (Array.for_all words ~f:(fun w -> W.bitwidth w = width));
    assert (Array.is_sorted_strictly words ~compare:W.compare);
#endif
    { width; words }

  let bottom (width : int) : t = { width; words = [||] }

  (* The survivors of one ascending pass, calling [f] once per element;
     the source itself when every element survives. *)
  let filter (t : t) ~(f : W.t -> bool) : t =
    let n = count t in
    let rec first_drop i =
      if i = n then n else if f t.words.(i) then first_drop (i + 1) else i in
    let d = first_drop 0 in
    if d = n then t
    else begin
      let out = Array.create ~len:(n - 1) t.words.(0) in
      Array.blit ~src:t.words ~src_pos:0 ~dst:out ~dst_pos:0 ~len:d;
      let k = ref d in
      for i = d + 1 to n - 1 do
        if f t.words.(i) then (out.(!k) <- t.words.(i); incr k)
      done;
      { t with words = Array.sub out ~pos:0 ~len:!k }
    end

  let singleton (w : W.t) : t = { width = W.bitwidth w; words = [| W.unsigned w |] }

  (* The runs in ascending order, as [Pieces.runs_from_sorted_elements]
     builds them. *)
  let to_pieces (t : t) : progression list =
    if is_bottom t then []
    else List.rev (Pieces_base.runs_from_sorted_elements ~width:t.width (elements t))

  (* The same elements as a canonical piece union.  The array is strictly
     ascending at [width], so its runs are ascending, disjoint and
     non-wrapping: only the budget combines. *)
  let pieces (t : t) : Pieces_base.t =
    let runs = to_pieces t in
    Pieces_base.mk (Pieces_base.cap runs)

  (* Piece minima ascend, but strided pieces can interleave.  Merge their
     ascending element streams to preserve the array's order. *)
  let of_pieces ~(width : int) (ps : Pieces_base.t) : t =
#ifdef VSA_DEBUG
    assert (List.for_all (Pieces_base.to_list ps) ~f:(fun p -> Cbat_clp_core.bitwidth p = width));
#endif
    of_sorted_list ~width
      (List.fold_right (Pieces_base.to_list ps) ~init:[] ~f:(fun p acc ->
           List.merge (Cbat_clp_core.iter p) acc ~compare:W.compare)
       |> List.remove_consecutive_duplicates ~equal:W.equal)

  let bitwidth (t : t) : int = t.width
  let get_idx (t : t) : int = t.width

  let cardinality (t : t) : W.t = W.of_int ~width:(t.width + 1) (count t)

  let card_exceeds (n : int) (t : t) : bool = count t > n

  let elem (w : W.t) (t : t) : bool =
    W.bitwidth w = t.width
    && (let w = W.unsigned w in
        let rec search lo hi =
          lo < hi
          && (let mid = (lo + hi) / 2 in
              let c = W.compare t.words.(mid) w in
              c = 0 || if c < 0 then search (mid + 1) hi else search lo mid)
        in
        search 0 (count t))

  (* The linear merge over two equal-width arrays, keeping the elements
     only in [a], in both, or only in [b] as asked. *)
  let merge ~(left : bool) ~(both : bool) ~(right : bool) (a : t) (b : t) : t =
    let na = count a and nb = count b in
    let out = Array.create ~len:(na + nb) (W.zero 1) in
    let n = ref 0 in
    let add x = out.(!n) <- x; incr n in
    let rec go i j =
      if i = na then (if right then for j' = j to nb - 1 do add b.words.(j') done)
      else if j = nb then (if left then for i' = i to na - 1 do add a.words.(i') done)
      else
        let c = W.compare a.words.(i) b.words.(j) in
        if c < 0 then (if left then add a.words.(i); go (i + 1) j)
        else if c > 0 then (if right then add b.words.(j); go i (j + 1))
        else (if both then add a.words.(i); go (i + 1) (j + 1))
    in
    go 0 0;
    { width = a.width; words = Array.sub out ~pos:0 ~len:!n }

  let rewiden (width : int) (t : t) : t =
    if t.width = width then t
    else { width; words = Array.map t.words ~f:(at_width width) }

  let equal (a : t) (b : t) : bool =
    a.width = b.width && Array.equal W.equal a.words b.words

  (* A width mismatch follows the finite tier: the union holds both
     element sets at the wider width; the meet of distinct widths is
     empty; [diff] keeps the left set. *)
  let union (a : t) (b : t) : t =
    let w = Stdlib.max a.width b.width in
    merge ~left:true ~both:true ~right:true (rewiden w a) (rewiden w b)

  let intersection (a : t) (b : t) : t =
    if a.width <> b.width then bottom (Stdlib.max a.width b.width)
    else merge ~left:false ~both:true ~right:false a b

  let diff (a : t) (b : t) : t =
    if a.width <> b.width then a
    else merge ~left:true ~both:false ~right:false a b

  (* A common element: one linear pass that stops at the first. *)
  let overlap (a : t) (b : t) : bool =
    let na = count a and nb = count b in
    a.width = b.width
    && (let rec go i j =
          i < na && j < nb
          && (let c = W.compare a.words.(i) b.words.(j) in
              c = 0 || if c < 0 then go (i + 1) j else go i (j + 1))
        in
        go 0 0)

  (* [a] is a subset of [b]: one linear pass over the sorted arrays. *)
  let precedes (a : t) (b : t) : bool =
    let na = count a and nb = count b in
    a.width = b.width && na <= nb
    && (let rec go i j =
          i = na
          || (j < nb
              && (let c = W.compare a.words.(i) b.words.(j) in
                  if c = 0 then go (i + 1) (j + 1)
                  else c > 0 && go i (j + 1)))
        in
        go 0 0)

  (* The pointwise element image at [width]. *)
  let lift1 ~(width : int) (f : W.t -> W.t) (a : t) : t =
    of_iter ~width ~iter:(fun emit -> Array.iter a.words ~f:(fun w -> emit (f w)))

  (* The Cartesian element image; [width] is the finite tier's per-op width
     rule: the wider side, or the left side for the shifts. *)
  let lift2 ?(width = fun w1 w2 -> Stdlib.max w1 w2)
      (f : W.t -> W.t -> W.t) (a : t) (b : t) : t =
    of_iter ~width:(width a.width b.width) ~iter:(fun emit ->
        Array.iter a.words ~f:(fun x ->
            Array.iter b.words ~f:(fun y -> emit (f x y))))

  let add = lift2 W.add
  let sub = lift2 W.sub
  let mul = lift2 W.mul
  let div = lift2 W.div
  let sdiv = lift2 (fun w1 w2 -> W.div (W.signed w1) (W.signed w2))
  let modulo = lift2 W.modulo
  let smodulo = lift2 (fun w1 w2 -> W.modulo (W.signed w1) (W.signed w2))

  let arshift = lift2 ~width:(fun w1 _ -> w1) W.arshift
  let rshift = lift2 ~width:(fun w1 _ -> w1) W.rshift
  let lshift = lift2 ~width:(fun w1 _ -> w1) W.lshift

  let logand = lift2 W.logand
  let logor = lift2 W.logor
  let logxor = lift2 W.logxor

  let lnot (t : t) : t =
    { t with words = Array.init (count t) ~f:(fun i -> W.lnot t.words.(count t - i - 1)) }

  let neg (t : t) : t =
    let zero_first = count t > 0 && W.is_zero t.words.(0) in
    { t with words = Array.init (count t) ~f:(fun i ->
          if zero_first && i = 0 then t.words.(0)
          else W.neg t.words.(count t - i - (if zero_first then 0 else 1))) }

  let extract ?hi ?(lo = 0) (t : t) : t =
    let new_bw =
      let hi = Option.value ~default:(t.width - 1) hi in
      hi - lo + 1 in
    if new_bw <= 0 || (lo = 0 && new_bw = t.width) then t
    else lift1 ~width:new_bw (W.extract_exn ?hi ~lo) t

  let cast (c : Bil.cast) (sz : int) (t : t) : t =
    if sz <= 0 || sz = t.width then t
    else if sz > t.width && c <> Bil.HIGH then
      { width = sz; words = Array.map t.words ~f:(fun w -> at_width sz (W.cast c sz w)) }
    else lift1 ~width:sz (W.cast c sz) t

  let concat (a : t) (b : t) : t =
    let nb = count b in
    { width = a.width + b.width;
      words = Array.init (count a * nb) ~f:(fun i -> W.concat a.words.(i / nb) b.words.(i mod nb)) }

  (* True when consecutive elements are spaced by a multiple of [w]. *)
  let splits_by (t : t) (w : W.t) : bool =
    let rec go i =
      i >= count t
      || (W.is_zero (W.modulo (W.sub t.words.(i) t.words.(i - 1)) w)
          && go (i + 1))
    in
    go 1

  let min_elem (t : t) : W.t option =
    if is_bottom t then None else Some (nth t 0)

  let max_elem (t : t) : W.t option =
    if is_bottom t then None else Some (nth t (count t - 1))

  (* The index of the first element with its sign bit set: the array
     ascends unsigned, so the sign bit is monotone along it. *)
  let first_negative (t : t) : int =
    let rec search lo hi =
      if lo >= hi then lo
      else
        let mid = (lo + hi) / 2 in
        if W.msb t.words.(mid) then search lo mid else search (mid + 1) hi
    in
    search 0 (count t)

  let min_elem_signed (t : t) : W.t option =
    if is_bottom t then None
    else
      let i = first_negative t in
      Some (W.signed t.words.(if i < count t then i else 0))

  let max_elem_signed (t : t) : W.t option =
    if is_bottom t then None
    else
      let i = first_negative t in
      Some (W.signed t.words.(if i > 0 then i - 1 else count t - 1))

  (* [elem] tests one element of the other operand, which has width
     [width]; a width mismatch answers may-overlap. *)
  let overlap_elem ~(width : int) ~(elem : W.t -> bool) (t : t) : bool =
    if width <> t.width then not (is_bottom t)
    else Array.exists t.words ~f:elem

  (* An exact value is never a top; a growing widen is the caller's
     promotion signal, so the union is the sound answer if it arrives. *)
  let widen_join = union
  let join = union
  let meet = intersection

  let pp ppf (t : t) =
    Format.fprintf ppf "@[{@ ";
    List.iter (elements t) ~f:(Format.fprintf ppf "%a@ " W.pp);
    Format.fprintf ppf "}@]"
end

module Exact_backward = Cbat_preimage.Make (struct
  include Exact_base

  let parts t = if is_bottom t then [] else [ t ]

  let assemble ~width = function
    | [] -> bottom width
    | [ t ] -> t
    | ts ->
        of_iter ~width ~iter:(fun emit ->
            List.iter ts ~f:(fun t -> List.iter (iter t) ~f:emit))

  let unary op ~arg ~result =
    filter arg ~f:(fun x -> elem (Cbat_preimage.word1 op x) result)

  let binary op ~left ~right ~result =
    let accepts x y =
      Option.value_map (Cbat_preimage.word2 op x y) ~default:true ~f:(fun z ->
          elem z result)
    in
    let xs = iter left and ys = iter right in
    ( filter left ~f:(fun x -> List.exists ys ~f:(accepts x)),
      filter right ~f:(fun y -> List.exists xs ~f:(fun x -> accepts x y)) )
end)

module Piece_backward = struct
  module P = Pieces_base
  module W = Cbat_word
  module I = Cbat_preimage

  let width = P.bitwidth
  let empty a = P.bottom (width a)
  let bounds a = Option.both (P.min_elem a) (P.max_elem a)
  let iv w lo hi = if W.(lo > hi) then P.bottom w else P.interval ~width:w lo hi

  let union _w xs =
    P.produce (fun emit -> List.iter xs ~f:(fun p -> P.iter p ~f:emit))

  let singleton a = if W.is_one (P.cardinality a) then P.min_elem a else None
  let finite a cap = if P.card_exceeds cap a then None else Some (P.elements a)

  let image1 op a =
    match op with
    | I.Lnot -> P.lnot a
    | I.Neg -> P.neg a
    | I.Cast (c, n) -> P.cast c n a
    | I.Extract (hi, lo) -> P.extract ?hi ~lo a

  (* The output window repeats only inside this input progression. *)
  let low arg result =
    let w = width arg and n = width result in
    if n >= w then P.intersection arg (P.cast Bil.LOW w result)
    else
      match bounds arg with
      | None -> arg
      | Some (alo, ahi) ->
          let count = W.of_int ~width:w n in
          let k0 = W.rshift alo count and k1 = W.rshift ahi count in
          if W.gt_int (W.sub k1 k0) Cbat_vsa_utils.max_pieces then
            match bounds result with
            | None -> arg
            | Some (lo, hi) -> (
                let lo = W.cast Bil.UNSIGNED w lo
                and hi = W.cast Bil.UNSIGNED w hi in
                let period = W.pow2 ~width:w n in
                let step =
                  if W.equal lo hi then Some period
                  else
                    match P.to_list result with
                    | [ p ] ->
                        let step = W.cast Bil.UNSIGNED w (step_of p) in
                        if
                          (not (W.is_zero step))
                          && W.is_zero (W.modulo period step)
                          && W.(lo < step)
                          && W.equal hi (W.add lo (W.sub period step))
                        then Some step
                        else None
                    | _ -> None
                in
                let first = W.add (W.lshift k0 count) lo in
                let last = W.add (W.lshift k1 count) hi in
                match step with
                | Some step ->
                    let distance =
                      W.cast Bil.UNSIGNED (w + 1) (W.sub last first)
                    in
                    let cardn =
                      W.succ (W.div distance (W.cast Bil.UNSIGNED (w + 1) step))
                    in
                    P.intersection arg
                      (P.of_progression (create ~width:w ~step ~cardn first))
                | None -> P.intersection arg (iv w first last))
          else
            let r = P.cast Bil.UNSIGNED w result in
            let rec windows k acc =
              let base = W.lshift k count in
              let p = P.intersection arg (P.translate r base) in
              let acc = p :: acc in
              if W.equal k k1 then union w acc else windows (W.succ k) acc
            in
            windows k0 []

  let extend signed arg result =
    let n = width arg and w = width result in
    let z = W.zero w and maxn = W.pred (W.pow2 ~width:w n) in
    let image =
      if not signed then P.intersection result (iv w z maxn)
      else
        let half = W.pow2 ~width:w (n - 1) in
        P.intersection result
          (union w [ iv w z (W.pred half); iv w (W.sub z half) (W.ones w) ])
    in
    P.intersection arg (P.cast Bil.LOW n image)

  let extract arg result ~hi ~lo =
    let w = width arg in
    if hi < lo || lo < 0 || hi >= w then arg
    else
      let shifted = P.rshift arg (P.singleton (W.of_int ~width:w lo)) in
      let narrowed = low shifted result in
      if P.is_bottom narrowed then empty arg
      else
        let base = P.lshift narrowed (P.singleton (W.of_int ~width:w lo)) in
        let lows = iv w (W.zero w) (W.pred (W.pow2 ~width:w lo)) in
        P.intersection arg (P.add base lows)

  let unary op ~arg ~result =
    match finite arg 64 with
    | Some xs ->
        P.of_list ~width:(width arg)
          (List.filter xs ~f:(fun x -> P.elem (I.word1 op x) result))
    | None -> (
        if not (P.overlap (image1 op arg) result) then empty arg
        else
          match op with
          | I.Lnot -> P.intersection arg (P.lnot result)
          | I.Neg -> P.intersection arg (P.neg result)
          | I.Cast (c, n) when n = width arg -> P.intersection arg result
          | I.Cast (Bil.HIGH, n) when n < width arg ->
              extract arg result ~hi:(width arg - 1) ~lo:(width arg - n)
          | I.Cast (_, n) when n < width arg -> low arg result
          | I.Cast (Bil.SIGNED, _) -> extend true arg result
          | I.Cast (Bil.UNSIGNED, _) -> extend false arg result
          | I.Cast _ -> arg
          | I.Extract (hi, lo) ->
              extract arg result
                ~hi:(Option.value hi ~default:(width arg - 1))
                ~lo)

  (* Order projections use signed endpoints on the signed number line. *)
  let order ~signed ~strict left right =
    let w = width left in
    let mn = if signed then P.min_elem_signed else P.min_elem in
    let mx = if signed then P.max_elem_signed else P.max_elem in
    let first = if signed then W.pow2 ~width:w (w - 1) else W.zero w in
    let last = if signed then W.pred first else W.ones w in
    let less x y = if signed then W.(signed x < signed y) else W.(x < y) in
    match (mn left, mx right) with
    | Some x, Some y when less x y || ((not strict) && W.equal x y) ->
        let upper = if strict then W.pred y else y in
        let lower = if strict then W.succ x else x in
        ( P.intersection left (P.interval ~width:w first upper),
          P.intersection right (P.interval ~width:w lower last) )
    | Some _, Some _ -> (empty left, empty right)
    | _ -> (left, right)

  let compare op left right truth =
    match op with
    | Bil.EQ | Bil.NEQ -> (
        if Bool.equal truth (Poly.equal op Bil.EQ) then
          let meet = P.intersection left right in
          (meet, meet)
        else
          ( (match singleton right with
            | Some k -> P.diff left (P.singleton k)
            | None -> left),
            match singleton left with
            | Some k -> P.diff right (P.singleton k)
            | None -> right ))
    | Bil.LT | Bil.LE | Bil.SLT | Bil.SLE ->
        let signed = Poly.equal op Bil.SLT || Poly.equal op Bil.SLE in
        let strict = Poly.equal op Bil.LT || Poly.equal op Bil.SLT in
        if truth then order ~signed ~strict left right
        else
          let b, a = order ~signed ~strict:(not strict) right left in
          (a, b)
    | _ -> (left, right)

  let ceil_div a b =
    let q = W.div a b in
    if W.is_zero (W.modulo a b) then q else W.succ q

  let arithmetic op left right result =
    let w = width left in
    let keep a b = (P.intersection left a, P.intersection right b) in
    match op with
    | Bil.PLUS -> keep (P.sub result right) (P.sub result left)
    | Bil.MINUS -> keep (P.add result right) (P.sub left result)
    | Bil.TIMES ->
        let project a b =
          match (singleton b, bounds a, bounds result) with
          | Some k, Some (_, amax), Some (lo, hi)
            when (not (W.is_zero k)) && W.(amax <= div (ones w) k) ->
              P.intersection a (iv w (ceil_div lo k) (W.div hi k))
          | _ -> a
        in
        (project left right, project right left)
    | Bil.DIVIDE -> (
        match (bounds right, bounds result) with
        | Some (kmin, kmax), Some (lo, hi) when not (W.is_zero kmin) ->
            let wide x = W.cast Bil.UNSIGNED ((2 * w) + 1) x in
            let low = W.mul (wide lo) (wide kmin) in
            let high = W.pred (W.mul (W.succ (wide hi)) (wide kmax)) in
            let maxw = wide (W.ones w) in
            if W.(low > maxw) then (empty left, empty right)
            else
              keep
                (iv w (W.cast Bil.LOW w low)
                   (W.cast Bil.LOW w (W.min high maxw)))
                right
        | _ -> (left, right))
    | Bil.SDIVIDE -> (
        match
          (singleton right, P.min_elem_signed result, P.max_elem_signed result)
        with
        | Some k, Some lo, Some hi when not (W.msb k || W.is_zero k) ->
            let signed_z x =
              let z = W.to_z x in
              if W.msb x then Z.sub z (Z.shift_left Z.one w) else z
            in
            let k = W.to_z k and lo = signed_z lo and hi = signed_z hi in
            let extra = Z.pred k in
            let lower =
              Z.sub (Z.mul lo k) (if Z.sign lo <= 0 then extra else Z.zero)
            in
            let upper =
              Z.add (Z.mul hi k) (if Z.sign hi >= 0 then extra else Z.zero)
            in
            let half = Z.shift_left Z.one (w - 1) in
            let lower = Z.max lower (Z.neg half)
            and upper = Z.min upper (Z.pred half) in
            if Z.compare lower upper > 0 then (empty left, empty right)
            else
              keep (P.interval ~width:w (W.of_z lower w) (W.of_z upper w)) right
        | _ -> (left, right))
    | Bil.AND | Bil.OR | Bil.XOR ->
        let project a b =
          match singleton b with
          | Some k ->
              let constraint_ =
                match op with
                | Bil.XOR -> P.logxor result (P.singleton k)
                | Bil.AND when W.equal k (W.ones w) -> result
                | Bil.OR when W.is_zero k -> result
                | Bil.AND -> (
                    match bounds result with
                    | None -> a
                    | Some (lo, hi) ->
                        let rec submask i acc =
                          if i < 0 then acc
                          else
                            let bit = W.pow2 ~width:w i in
                            let cand = W.logor acc bit in
                            submask (i - 1)
                              (if
                                 (not (W.is_zero (W.logand k bit)))
                                 && W.(cand <= hi)
                               then cand
                               else acc)
                        in
                        iv w lo
                          (W.logor (submask (w - 1) (W.zero w)) (W.lnot k)))
                | _ -> a
              in
              P.intersection a constraint_
          | None -> a
        in
        (project left right, project right left)
    | Bil.LSHIFT | Bil.RSHIFT | Bil.ARSHIFT -> (
        match finite right 64 with
        | None -> (left, right)
        | Some counts ->
            let pairs =
              List.filter_map counts ~f:(fun k ->
                  match W.to_int k with
                  | Error _ -> Some (left, P.singleton k)
                  | Ok n ->
                      let candidate =
                        if n >= w then
                          if Poly.equal op Bil.ARSHIFT then left
                          else if P.elem (W.zero w) result then left
                          else empty left
                        else if n < 0 then left
                        else if n = 0 then P.intersection left result
                        else if Poly.equal op Bil.LSHIFT then
                          let valid =
                            P.intersection result
                              (P.of_progression
                                 (create ~width:w ~step:(W.pow2 ~width:w n)
                                    ~cardn:(W.pow2 ~width:(w + 1) (w - n))
                                    (W.zero w)))
                          in
                          low left
                            (P.cast Bil.LOW (w - n)
                               (P.rshift valid (P.singleton k)))
                        else
                          let valid =
                            if Poly.equal op Bil.RSHIFT then
                              P.intersection result
                                (iv w (W.zero w) (W.rshift (W.ones w) k))
                            else
                              let half = W.pow2 ~width:w (w - 1) in
                              P.intersection result
                                (union w
                                   [
                                     iv w (W.zero w) (W.rshift (W.pred half) k);
                                     iv w (W.arshift half k) (W.ones w);
                                   ])
                          in
                          let reduced =
                            P.cast Bil.UNSIGNED w (P.cast Bil.LOW (w - n) valid)
                          in
                          let bases = P.lshift reduced (P.singleton k) in
                          P.intersection left
                            (P.add bases
                               (iv w (W.zero w) (W.pred (W.pow2 ~width:w n))))
                      in
                      if P.is_bottom candidate then None
                      else Some (candidate, P.singleton k))
            in
            ( union w (List.map pairs ~f:fst),
              union (width right) (List.map pairs ~f:snd) ))
    | _ -> (left, right)

  let binary op ~left ~right ~result =
    match (finite left 64, finite right 64) with
    | Some xs, Some ys when List.length xs * List.length ys <= 4096 ->
        let accepts x y =
          Option.value_map (I.word2 op x y) ~default:true ~f:(fun z ->
              P.elem z result)
        in
        ( P.of_list ~width:(width left)
            (List.filter xs ~f:(fun x -> List.exists ys ~f:(accepts x))),
          P.of_list ~width:(width right)
            (List.filter ys ~f:(fun y ->
                 List.exists xs ~f:(fun x -> accepts x y))) )
    | _ -> (
        match op with
        | I.Concat ->
            let rw = width right in
            ( P.intersection left
                (P.extract ~hi:(width result - 1) ~lo:rw result),
              P.intersection right (P.extract ~hi:(rw - 1) ~lo:0 result) )
        | I.Op ((Bil.EQ | Bil.NEQ | Bil.LT | Bil.LE | Bil.SLT | Bil.SLE) as cmp)
          ->
            let has0 = P.elem W.b0 result and has1 = P.elem W.b1 result in
            if has0 && has1 then (left, right)
            else if has0 || has1 then compare cmp left right has1
            else (empty left, empty right)
        | I.Op op -> arithmetic op left right result)
end

module Pieces_backward = Cbat_preimage.Make (struct
  include Pieces_base

  let parts t = List.map (to_list t) ~f:of_progression

  let assemble ~width:_ = function
    | [] -> empty
    | [ p ] -> p
    | ts -> produce (fun emit -> List.iter ts ~f:(fun p -> iter p ~f:emit))

  let unary = Piece_backward.unary
  let binary = Piece_backward.binary
end)

module Pieces = struct
  include Pieces_base

  let backward1 = Pieces_backward.backward1
  let backward2 = Pieces_backward.backward2
end

module Exact = struct
  include Exact_base

  let backward1 = Exact_backward.backward1
  let backward2 = Exact_backward.backward2
end
