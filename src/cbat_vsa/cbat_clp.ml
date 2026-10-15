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

(* The frozen seam: core from the include below, arithmetic one line
   per op. *)

open Bap.Std
open Bin_prot.Std
open !Core

include Cbat_clp_core

let add = Cbat_clp_arith.add
let sub = Cbat_clp_arith.sub
let mul = Cbat_clp_arith.mul
let div = Cbat_clp_arith.div
let sdiv = Cbat_clp_arith.sdiv
let modulo = Cbat_clp_arith.modulo
let smodulo = Cbat_clp_arith.smodulo
let neg = Cbat_clp_arith.neg
let logand = Cbat_clp_arith.logand
let split_at_n = Cbat_clp_arith.split_at_n
let logor = Cbat_clp_arith.logor
let logxor = Cbat_clp_arith.logxor
let lshift = Cbat_clp_arith.lshift
let rshift = Cbat_clp_arith.rshift
let arshift = Cbat_clp_arith.arshift
let extract = Cbat_clp_arith.extract
let cast = Cbat_clp_arith.cast
let concat = Cbat_clp_arith.concat

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
   only way in; no raw list escapes except through [to_list]. *)
module Pieces = struct
  type t = progression list [@@deriving bin_io, sexp, compare]

  module C = Cbat_clp_core
  module A = Cbat_clp_arith
  module U = Cbat_vsa_utils

  (* The union's bit width (its pieces' common width). *)
  let width_of (ps : t) : int =
    match ps with [] -> 0 | p :: _ -> C.bitwidth p

  let to_list (ps : t) : progression list = ps
  let fold (ps : t) ~(init : 'a) ~(f : 'a -> progression -> 'a) : 'a =
    List.fold ps ~init ~f
  let iter (ps : t) ~(f : progression -> unit) : unit = List.iter ps ~f
  let elements (ps : t) : Cbat_word.t list = List.concat_map ps ~f:C.iter

  let is_bottom (ps : t) : bool = ps = []
  let is_top (ps : t) : bool = List.exists ps ~f:C.is_top
  let bitwidth = width_of

  (* Cached per width, as [C.top] is. *)
  let top_cache : t array = Stdlib.Array.init 257 (fun i -> if i > 0 then [ C.top i ] else [])

  let top (i : int) : t =
    if i > 0 && i < Stdlib.Array.length top_cache then top_cache.(i) else [ C.top i ]
  let bottom (_ : int) : t = []

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
            let merged = C.create ~width ~step ~cardn (C.base_of q) in
            if C.equal merged (C.union q p) then Some merged else None

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
          | Some e_p, Some e_q
            when Cbat_word.(>=) e_p (C.base_of p)
                 && Cbat_word.(>=) e_q (C.base_of q) ->
            let lo = Cbat_word.max (C.base_of p) (C.base_of q) in
            let hi = Cbat_word.min e_p e_q in
            Cbat_word.(<=) lo hi
          | _ -> not (C.is_bottom (C.intersection p q))
      end
      else not (C.is_bottom (C.intersection p q))

  (* The non-bottom, non-wrapping arcs of a produced piece.  Splitting at
     the producer is [shape]'s arc rule, kept where wrapping can arise. *)
  let split_arcs (p : progression) : progression list =
    if C.is_bottom p then []
    else List.filter (C.split_wrapped p) ~f:(fun a -> not (C.is_bottom a))

  (* [merge_arc acc a] is the canonical union of a canonical ascending
     disjoint list [acc] and one non-wrapping piece [a].  Overlaps hull,
     adjacent same-step runs join, contained pieces drop; a hull that
     wraps is split into its arcs and re-placed.  The accumulator stays
     ascending, disjoint, non-wrapping, single width. *)
  let rec merge_arc (acc : progression list) (a : progression)
    : progression list =
    let rec scan left = function
      | [] -> List.rev (a :: left)
      | q :: rest ->
        if C.subset a q then List.rev_append left (q :: rest)
        else if C.subset q a then scan left rest
        else
          let hull =
            if overlap_exact a q then Some (C.union a q)
            else
              (if compare_piece a q < 0 then adjacent_merge a q
               else adjacent_merge q a)
          in
          (match hull with
           | None ->
             if compare_piece a q < 0 then List.rev_append left (a :: q :: rest)
             else scan (q :: left) rest
           | Some r ->
             List.fold (split_arcs r)
               ~init:(List.rev_append left rest) ~f:merge_arc)
    in
    scan [] acc

  (* [assemble] combines an already-ascending, non-wrapping stream.  While
     hulls stay disjoint a piece can only meet the tail.  Once its minimum
     reaches the largest placed maximum (kept with each placed piece), an
     overlap can hide behind an interleaved tail, so it is checked against
     every placed piece.  A wrapped hull or a hidden overlap falls back to
     the general placement.  No sort runs here. *)
  let assemble (ps : progression list) : t =
    let push x acc =
      let hi =
        match acc, C.max_elem x with
        | [], m -> m
        | (_, Some a) :: _, Some b -> Some (Cbat_word.max a b)
        | _ -> None
      in
      (x, hi) :: acc
    in
    let hidden x = function
      | [] -> false
      | (_, hi) :: _ as placed ->
        (match hi, C.min_elem x with
         | Some hi, Some lo -> Cbat_word.(<=) lo hi
         | _ -> true)
        && List.exists placed ~f:(fun (q, _) -> overlap_exact x q)
    in
    let rec go acc = function
      | [] -> `Done (List.rev_map acc ~f:fst)
      | p :: rest -> (
        match acc with
        | [] -> go (push p acc) rest
        | (q, _) :: tl ->
          let join r = if hidden r tl then `General else go (push r tl) rest in
          if overlap_exact p q then begin
            let r = C.union p q in
            if C.is_wrapped r then `General else join r
          end
          else (
            match adjacent_merge q p with
            | Some r -> join r
            | None -> if hidden p acc then `General else go (push p acc) rest))
    in
    match go [] ps with
    | `Done ps -> ps
    | `General -> List.fold ps ~init:[] ~f:merge_arc

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
     canonicalizer cannot split back apart.  A wrap-traversing union
     circulates to its circular grid; otherwise the plain union. *)
  let coalesce (pi : progression) (pj : progression) : progression =
    let r = C.union pi pj in
    if C.is_wrapped r then C.infinite (C.base_of r, C.step_of r) else r

  (* A union of at most [U.max_pieces] pieces is kept as it is; a larger
     one is a single hull piece. *)
  let within_budget (ps : progression list) : bool =
    List.length ps <= U.max_pieces

  (* The one-piece hull of a union that leaves the budget.  A hull that
     traverses the wrap circulates to its circular grid. *)
  let hull (ps : progression list) : t =
    match ps with
    | [] -> []
    | p :: rest ->
#ifdef VSA_DEBUG
      census_cap ();
#endif
      [ List.fold rest ~init:p ~f:coalesce ]

  let cap (ps : t) : t = if within_budget ps then ps else hull ps

  (* The producer finish: combine the already-ordered stream, then
     collapse a union past the budget to its hull.  No sort: the caller
     ordered its own output. *)
  let finish (ps : progression list) : t =
    let r = cap (assemble ps) in
#ifdef VSA_DEBUG
    census_len (List.length r);
#endif
    r

  let of_progression (p : progression) : t =
    match split_arcs p with
    | [ hi; lo ] -> finish [ lo; hi ]
    | arcs -> finish arcs

  module Image = Map.Make (struct
      type t = progression [@@deriving sexp]
      let compare = compare_piece
    end)

  (* General progression images can move their minima independently.
     Their producer maintains the result index as each arc is computed. *)
  let produce (iter : (progression -> unit) -> unit) : t =
    let image = ref Image.empty in
    iter (fun p ->
        List.iter (split_arcs p) ~f:(fun arc ->
            image := Map.set !image ~key:arc ~data:()));
    finish (collapse_width (Map.keys !image))

  (* Merge two producers' ascending streams without combining or capping. *)
  let merge_progressions a b = List.merge a b ~compare:compare_piece

  (* The producer supplies disjoint, ascending, non-wrapping live pieces. *)
  let of_progressions (ps : progression list) : t =
#ifdef VSA_DEBUG
    assert (List.is_sorted ps ~compare:compare_piece);
    assert (List.for_all ps ~f:(fun p -> not (C.is_bottom p || C.is_wrapped p)));
#endif
    finish ps

  (* Maximal constant-difference runs of a sorted element list; each run
     is one exact progression (a wrapped run over-approximates). *)
  (* The runs of an already ascending element list. *)
  let runs_from_sorted_elements ~(width : int) (els : Cbat_word.t list)
    : progression list =
#ifdef VSA_DEBUG
    let () = assert (List.is_sorted els ~compare:Cbat_word.compare) in
#endif
    (* One run as a progression when the progression is exactly the run
       (the cardinality check rejects a wrapped over-approximation), else
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
    if width <= 0 then []
    else
      match l with
      (* A point address, the common key: its one run is its singleton. *)
      | [ w ] -> [ C.singleton (Cbat_word.extract_exn ~hi:(width - 1) ~lo:0 w) ]
      | _ ->
        let l = List.map l ~f:(Cbat_word.extract_exn ~hi:(width - 1) ~lo:0) in
        finish (List.rev (runs_from_sorted_elements ~width l))

  let singleton (w : Cbat_word.t) : t = [ C.singleton w ]

  let min_elem (ps : t) : Cbat_word.t option =
    List.fold ps ~init:None ~f:(fun acc p ->
        match C.min_elem p, acc with
        | None, acc -> acc
        | Some m, None -> Some m
        | Some m, Some a -> Some (if Cbat_word.compare m a < 0 then m else a))

  let max_elem (ps : t) : Cbat_word.t option =
    List.fold ps ~init:None ~f:(fun acc p ->
        match C.max_elem p, acc with
        | None, acc -> acc
        | Some m, None -> Some m
        | Some m, Some a -> Some (if Cbat_word.compare m a > 0 then m else a))

  let min_elem_signed (ps : t) : Cbat_word.t option =
    List.fold ps ~init:None ~f:(fun acc p ->
        match C.min_elem_signed p, acc with
        | None, acc -> acc
        | Some m, None -> Some m
        | Some m, Some a ->
          Some
            (if Cbat_word.compare (Cbat_word.signed m) (Cbat_word.signed a) < 0
             then m else a))

  let max_elem_signed (ps : t) : Cbat_word.t option =
    List.fold ps ~init:None ~f:(fun acc p ->
        match C.max_elem_signed p, acc with
        | None, acc -> acc
        | Some m, None -> Some m
        | Some m, Some a ->
          Some
            (if Cbat_word.compare (Cbat_word.signed m) (Cbat_word.signed a) > 0
             then m else a))

  (* Saturating sum of the pieces' cardinalities. *)
  let cardinality (ps : t) : Cbat_word.t =
    match ps with
    | [ p ] -> C.cardinality p
    | _ ->
    let width = width_of ps in
    if width = 0 then Cbat_word.zero 1
    else
      let w1 = width + 1 in
      List.fold ps ~init:(Cbat_word.zero w1) ~f:(fun acc p ->
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
    go n ps

  let elem (w : Cbat_word.t) (ps : t) : bool =
    List.exists ps ~f:(fun p -> C.elem w p)

  let equal (a : t) (b : t) : bool =
    phys_equal a b
    ||
    (match a, b with
     | [ x ], [ y ] -> C.equal x y
     | _ ->
       List.length a = List.length b && List.for_all2_exn a b ~f:C.equal)

  let overlap (a : t) (b : t) : bool =
    List.exists a ~f:(fun pa -> List.exists b ~f:(fun pb -> overlap_exact pa pb))

  let splits_by (ps : t) (w : Cbat_word.t) : bool =
    List.for_all ps ~f:(fun p -> C.splits_by p w)

  let is_ascending (ps : t) : bool = List.for_all ps ~f:C.is_ascending
  let is_descending (ps : t) : bool = List.for_all ps ~f:C.is_descending
  let is_circular (ps : t) : bool = List.for_all ps ~f:C.is_circular

  (* Union-order coverage: every piece of [a] is contained in [b]'s union
     (a single covering piece, or a small piece covered element-wise). *)
  let precedes (a : t) (b : t) : bool =
    List.for_all a ~f:(fun pa ->
        List.exists b ~f:(fun pb -> C.subset pa pb)
        || ((not (C.is_infinite pa))
            && not (Cbat_word.gt_int (C.cardinality pa) U.fin_set_size)
            && List.for_all (C.iter pa) ~f:(fun x ->
                List.exists b ~f:(fun pb -> C.elem x pb))))

  (* Union's own construction: both operands are ascending and disjoint,
     so a two-way merge by minimum gives an ascending stream each of whose
     pieces can only meet the placed tail — combine tail-only, in order,
     with no scan and no sort.  A width mismatch (a producer's rule)
     collapses to top at the widest; only a wrapped hull falls back. *)
  let union (a : t) (b : t) : t =
    match a, b with
    | [], _ -> b
    | _, [] -> a
    | _ when equal a b -> a
    | _ when not (Stdlib.Int.equal (width_of a) (width_of b)) ->
      finish (collapse_width (List.append a b))
    | _ ->
      (* [b] ascends, so each produced arc can only meet the placed tail;
         split every arc and place it exactly. *)
      finish
        (List.fold b ~init:a ~f:(fun acc p ->
             List.fold (split_arcs p) ~init:acc ~f:merge_arc))

  (* Exact meet of one pair: a small side enumerates element-wise, else
     the CLP meet (sound over-approximation). *)
  let pair_intersection (pa : progression) (pb : progression)
    : progression list =
    if C.is_bottom pa || C.is_bottom pb then []
    else
      let small p =
        (not (C.is_infinite p))
        && not (Cbat_word.gt_int (C.cardinality p) U.fin_set_size)
      in
      if small pa || small pb then begin
        let small_p, big_p = if small pa then pa, pb else pb, pa in
        let els = List.filter (C.iter_ascending small_p) ~f:(fun x -> C.elem x big_p) in
        runs_from_sorted_elements ~width:(C.bitwidth small_p) els
      end
      else
        let r = C.intersection pa pb in
        if C.is_bottom r then [] else [ r ]

  let intersection (a : t) (b : t) : t =
    if is_bottom a || is_bottom b then []
    else if equal a b then a
    else
      produce (fun emit ->
          List.iter a ~f:(fun pa ->
              List.iter b ~f:(fun pb ->
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

  (* Merge two ascending word lists, dropping repeats.  The subtrahend
     pieces' hulls may interleave, so their enumerations are merged, not
     concatenated. *)
  let merge_distinct (xs : Cbat_word.t list) (ys : Cbat_word.t list)
    : Cbat_word.t list =
    let rec go acc xs ys =
      match xs, ys with
      | [], rest | rest, [] -> List.rev_append acc rest
      | x :: xt, y :: yt ->
        let c = Cbat_word.compare x y in
        if c < 0 then go (x :: acc) xt ys
        else if c > 0 then go (y :: acc) xs yt
        else go (x :: acc) xt yt
    in
    go [] xs ys

  (* [a] minus the union of [bs]: exact when the cheap side enumerates,
     the sound CLP identity otherwise. *)
  let rec diff_piece (a : progression) (bs : progression list)
    : progression list =
    if C.is_bottom a then []
    else if small_card a then
      let survivors =
        List.filter (C.iter_ascending a) ~f:(fun x ->
            not (List.exists bs ~f:(fun b -> C.elem x b)))
      in
      runs_from_sorted_elements ~width:(C.bitwidth a) survivors
    else if small_total bs then begin
      let es =
        List.fold bs ~init:[] ~f:(fun acc b ->
            merge_distinct acc (List.filter (C.iter_ascending b) ~f:(fun x -> C.elem x a)))
      in
      if Cbat_word.is_one (C.cardn_of a) then (if es = [] then [ a ] else [])
      else if C.is_ascending a then ascending_survivors a es
      else if C.is_descending a then descending_survivors a es
      else if
        (not (C.is_infinite a)) && not (C.is_circular a)
        && (match C.finite_end a with
            | Some e -> Cbat_word.(>=) e (C.base_of a)
            | None -> false)
      then finite_survivors a es
      else [ List.fold bs ~init:a ~f:C.diff ]
    end
    else [ List.fold bs ~init:a ~f:C.diff ]

  let diff (a : t) (b : t) : t =
    if is_bottom a || equal a b then []
    else if is_bottom b then a
    else produce (fun emit ->
        List.iter a ~f:(fun pa -> List.iter (diff_piece pa b) ~f:emit))

  (* Unary images enter their ordered index as they are produced. *)
  let map (f : progression -> progression) (ps : t) : t =
    match ps with
    | [] -> []
    | [ p ] -> of_progression (f p)
    | _ -> produce (fun emit -> List.iter ps ~f:(fun p -> emit (f p)))

  let lift2 (f : progression -> progression -> progression) (a : t) (b : t)
    : t =
    match a, b with
    | [ pa ], [ pb ] -> of_progression (f pa pb)
    | _ -> produce (fun emit ->
        List.iter a ~f:(fun pa -> List.iter b ~f:(fun pb -> emit (f pa pb))))

  (* Each pair produces its result arcs directly into the ordered image. *)
  let lift2_parts (f : progression -> progression -> progression list)
      (a : t) (b : t) : t =
    produce (fun emit ->
        List.iter a ~f:(fun pa ->
            List.iter (C.split_wrapped pa) ~f:(fun qa ->
                List.iter b ~f:(fun pb ->
                    List.iter (C.split_wrapped pb) ~f:(fun qb ->
                        List.iter (f qa qb) ~f:emit)))))

  let add = lift2 A.add
  let sub = lift2 A.sub
  let mul = lift2 A.mul
  let div = lift2 A.div
  let sdiv = lift2 A.sdiv
  let modulo = lift2 A.modulo
  let smodulo = lift2 A.smodulo
  let arshift = lift2_parts A.arshift_parts
  let rshift = lift2_parts A.rshift_parts
  let lshift = lift2_parts A.lshift_parts
  let logand = lift2 A.logand
  let logor = lift2 A.logor
  let logxor = lift2 A.logxor
  let concat = lift2 A.concat

  let lnot = map C.lnot
  let neg = map A.neg

  let extract ?hi ?lo (ps : t) : t =
    let w = bitwidth ps in
    let full =
      (match hi with None -> true | Some h -> Stdlib.Int.equal h (w - 1))
      && (match lo with None | Some 0 -> true | Some _ -> false) in
    if full then ps
    else
      produce (fun emit ->
          List.iter ps ~f:(fun p ->
              List.iter (C.split_wrapped p) ~f:(fun q ->
                  List.iter (A.extract_parts ?hi ?lo q) ~f:emit)))

  let cast c sz (ps : t) : t =
    if Stdlib.Int.equal sz (bitwidth ps) then ps
    else
      produce (fun emit ->
          List.iter ps ~f:(fun p ->
              List.iter (C.split_wrapped p) ~f:(fun q ->
                  List.iter (A.cast_parts c sz q) ~f:emit)))

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
  let positional (f : progression -> progression -> progression) (a : t)
      (b : t) : t =
    match a, b with
    | [], [] -> []
    | [], _ -> b
    | _, [] -> a
    | _ ->
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
          (List.map a ~f:(fun p -> (true, p)))
          (List.map b ~f:(fun p -> (false, p)))
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
        if C.is_top r then top_hit := true else emit r;
        pass emit rest
      in
      let pieces = produce (fun emit -> pass emit merged) in
      if !top_hit then [ C.top (width_of b) ] else pieces

  let widen_join = positional C.widen_join
  let extrapolate_steps ~steps a b = positional (C.extrapolate_steps ~steps) a b
  let join = union
  let meet = intersection
end

(* ==================== Exact: the uncapped flat element array ========== *)

(* The exact finite tier as a flat array: the elements as words at the
   declared width, unsigned, strictly ascending.  The array is the
   canonical form, so structural equality is set equality; the empty
   array is bottom and the width survives in the record.  It is never
   mutated after its producer builds it.  Unlike [Pieces], the set is
   uncapped and unbudgeted; the caller's canonical promotion applies the
   budget.  Ordered images write their array directly; other images
   maintain an ordered bit-prefix set while computing their elements. *)
module Exact = struct
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
    else List.rev (Pieces.runs_from_sorted_elements ~width:t.width (elements t))

  let point_pieces (t : t) : Pieces.t option =
    if count t = 1 then Some (to_pieces t) else None

  (* The same elements as a canonical piece union.  The array is strictly
     ascending at [width], so its runs are ascending, disjoint and
     non-wrapping: only the budget combines. *)
  let pieces (t : t) : Pieces.t =
    let runs = to_pieces t in
    if List.length runs <= Cbat_vsa_utils.max_pieces then runs
    else Pieces.hull runs

  (* Piece minima ascend, but strided pieces can interleave.  Merge their
     ascending element streams to preserve the array's order. *)
  let of_pieces ~(width : int) (ps : Pieces.t) : t =
#ifdef VSA_DEBUG
    assert (List.for_all ps ~f:(fun p -> Cbat_clp_core.bitwidth p = width));
#endif
    of_sorted_list ~width
      (List.fold_right ps ~init:[] ~f:(fun p acc ->
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

  let overlap (a : t) (b : t) : bool =
    a.width = b.width && not (is_bottom (intersection a b))

  let precedes (a : t) (b : t) : bool =
    a.width = b.width && is_bottom (diff a b)

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

  let overlap_generic (type ws)
      (module WS : Cbat_wordset_intf.S with type t = ws)
      (t : t) (s' : ws) : bool =
    (* Width mismatch answers may-overlap. *)
    if WS.bitwidth s' <> t.width then not (is_bottom t)
    else Array.exists t.words ~f:(fun w -> WS.elem w s')

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
