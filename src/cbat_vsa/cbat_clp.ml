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

  let max_pieces : int = U.max_pieces

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

  let top (i : int) : t = [ C.top i ]
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

  (* Exact shared-element test: enumeration when a side is small,
     same-step range arithmetic, else the conservative may-test (merging
     a non-overlapping pair is sound, only imprecise). *)
  let overlap_exact (p : progression) (q : progression) : bool =
    if C.is_bottom p || C.is_bottom q then false
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

  (* Insert one piece into the reverse-sorted accumulator. *)
  let rec insert (acc : progression list) (p : progression) : progression list =
    match acc with
    | [] -> [ p ]
    | q :: rest ->
      if C.subset p q then acc
      else if C.subset q p then insert rest p
      else if overlap_exact p q then insert rest (C.union q p)
      else
        (match adjacent_merge q p with
         | Some merged -> insert rest merged
         | None -> p :: acc)

  (* Two pieces interleave when each sits below the other across the
     wrap: their exact union is two arcs, which the cap cannot use (it
     would split back apart and never reduce the count).  The cap hull
     takes the aligned circular grid instead — sound, and one piece. *)
  let interleaved (pi : progression) (pj : progression) : bool =
    match C.max_elem pi, C.min_elem pj, C.max_elem pj, C.min_elem pi with
    | Some hi_i, Some lo_j, Some hi_j, Some lo_i ->
      Cbat_word.(<) hi_i lo_j && Cbat_word.(<) hi_j lo_i
    | _ -> false

  (* The cap hull: one piece the canonicalizer cannot split back apart.
     Interleaved pairs and wrap-traversing unions circulate to the
     aligned circular grid (the grid dividing both steps and the modular
     base difference — it covers both pieces); everything else takes the
     plain union. *)
  let coalesce (pi : progression) (pj : progression) : progression =
    if interleaved pi pj then
      let g =
        Cbat_word.bounded_gcd
          (Cbat_word.bounded_gcd (C.step_of pi) (C.step_of pj))
          (Cbat_word.sub (C.base_of pj) (C.base_of pi)) in
      C.infinite (C.base_of pi, g)
    else
      let r = C.union pi pj in
      if C.is_wrapped r then C.infinite (C.base_of r, C.step_of r) else r

  (* The pair-hull cost: cardinality growth of the cap hull when all
     three are finite, the unsigned gap otherwise. *)
  let pair_growth (hull : progression) (pi : progression) (pj : progression)
    : Cbat_word.t =
    let width = C.bitwidth pi in
    let w1 = width + 1 in
    let finite p = not (C.is_infinite p) && not (C.is_bottom p) in
    if finite pi && finite pj && finite hull then begin
      let sum = Cbat_word.add (C.cardinality pi) (C.cardinality pj) in
      let h = Cbat_word.cast Bil.UNSIGNED w1 (C.cardinality hull) in
      if Cbat_word.(<) h sum then Cbat_word.zero w1
      else Cbat_word.sub h sum
    end
    else
      match C.min_elem pj, C.max_elem pi with
      | Some lo_j, Some hi_i ->
        if Cbat_word.(<=) lo_j hi_i then Cbat_word.zero w1
        else Cbat_word.cast Bil.UNSIGNED w1 (Cbat_word.sub lo_j hi_i)
      | _ -> Cbat_word.ones w1

  (* The smallest-growth pair, same-step preferred on ties. *)
  let choose_pair (ps : progression list)
    : (progression * progression list) option =
    let arr = Stdlib.Array.of_list ps in
    let n = Stdlib.Array.length arr in
    let best = Stdlib.ref None in
    for i = 0 to n - 1 do
      for j = i + 1 to n - 1 do
        let g = pair_growth (coalesce arr.(i) arr.(j)) arr.(i) arr.(j) in
        let same_step =
          Cbat_word.equal (C.step_of arr.(i)) (C.step_of arr.(j)) in
        let better =
          match !best with
          | None -> true
          | Some (_, _, gb, sb) ->
            let c = Cbat_word.compare g gb in
            c < 0 || (c = 0 && same_step && not sb)
        in
        if better then best := Some (i, j, g, same_step)
      done
    done;
    match !best with
    | None -> None
    | Some (i, j, _, _) ->
      let hull = coalesce arr.(i) arr.(j) in
      let rest = List.filteri ps ~f:(fun k _ -> k <> i && k <> j) in
      Some (hull, rest)

  (* A union of at most [U.fin_set_size] elements stays exact: the cap
     bounds large unions, never a set the exact tier keeps. *)
  let within_exact_budget (ps : progression list) : bool =
    let budget = U.fin_set_size in
    let rec go n = function
      | [] -> true
      | p :: rest ->
        (not (C.is_infinite p))
        && (match Cbat_word.to_int (C.cardinality p) with
            | Ok k -> n + k <= budget && go (n + k) rest
            | Error _ -> false)
    in
    go 0 ps

  (* Two-way merge of two ascending [compare_piece] lists.  The left
     operand wins ties, matching the stable sort it replaces. *)
  let rec merge_sorted (xs : progression list) (ys : progression list)
    : progression list =
    match xs, ys with
    | [], ys -> ys
    | xs, [] -> xs
    | x :: xt, y :: yt ->
      if compare_piece x y <= 0 then x :: merge_sorted xt ys
      else y :: merge_sorted xs yt

  (* The cap repair over a merged list: hull the smallest-growth pair and
     re-merge the hull, never re-sorting. *)
  let rec cap (ps : t) : t =
    let ps =
      if List.length ps > max_pieces && not (within_exact_budget ps) then begin
#ifdef VSA_DEBUG
        census_cap ();
#endif
        match choose_pair ps with
        | Some (hull, rest) ->
          cap
            (List.rev
               (List.fold (merge_sorted [ hull ] rest) ~init:[] ~f:insert))
        | None -> ps
      end
      else ps
    in
#ifdef VSA_DEBUG
    census_len (List.length ps);
#endif
    ps

  (* The insert fold and cap over an ascending list.  [canonical_of_list] is this
     after [shape] and its merges; [union] feeds it a merge. *)
  let canonical_of_sorted (ps : progression list) : t =
    cap (List.rev (List.fold ps ~init:[] ~f:insert))

  (* The shape phase: split wrapped pieces into their arcs, drop bottoms,
     and collapse mixed widths to top at the widest.  A canonical value
     never wraps and never mixes widths, so canonical inputs skip it. *)
  let shape (ps : progression list) : progression list =
    let ps =
      match ps with
      | [ p ] when not (C.is_bottom p) && not (C.is_wrapped p) -> [ p ]
      | _ ->
        List.filter
          (List.concat_map ps ~f:C.split_wrapped)
          ~f:(fun p -> not (C.is_bottom p)) in
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

  (* The same canonicalization for an output list of unknown order:
     bottom-up adjacent merges (stable), then the insert fold.  No
     [List.sort]. *)
  let canonical_of_list (ps : progression list) : t =
    let rec merge_runs = function
      | [] -> []
      | [ x ] -> [ x ]
      | x :: y :: rest -> merge_sorted x y :: merge_runs rest
    in
    let rec merge_sort = function
      | [] | [ _ ] as l -> l
      | l -> merge_sort (merge_runs l)
    in
    canonical_of_sorted
      (List.concat (merge_sort (List.map (shape ps) ~f:(fun p -> [ p ]))))

  let of_progression (p : progression) : t = canonical_of_list [ p ]

  (* Maximal constant-difference runs of a sorted element list; each run
     is one exact progression (a wrapped run over-approximates). *)
  (* The runs of an already ascending element list. *)
  let runs_from_sorted_elements ~(width : int) (els : Cbat_word.t list)
    : progression list =
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

  let runs_from_elements ~(width : int) (els : Cbat_word.t list)
    : progression list =
    runs_from_sorted_elements ~width
      (List.sort els ~compare:Cbat_word.compare)

  let of_list ~(width : int) (l : Cbat_word.t list) : t =
    if width <= 0 then []
    else
      let l = List.map l ~f:(Cbat_word.extract_exn ~hi:(width - 1) ~lo:0) in
      canonical_of_list (runs_from_elements ~width l)

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

  let elem (w : Cbat_word.t) (ps : t) : bool =
    List.exists ps ~f:(fun p -> C.elem w p)

  let equal (a : t) (b : t) : bool =
    match a, b with
    | [ x ], [ y ] -> C.equal x y
    | _ ->
      List.length a = List.length b && List.for_all2_exn a b ~f:C.equal

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

  (* Union of canonical values: one linear merge, then the insert fold
     and cap.  The emitted order matches the stable sort this replaces;
     a width mismatch (unreachable for canonical values) falls back to
     the full canonicalization. *)
  let union (a : t) (b : t) : t =
    match a, b with
    | [], _ -> b
    | _, [] -> a
    | _ when Stdlib.Int.equal (width_of a) (width_of b) ->
      canonical_of_sorted (merge_sorted a b)
    | _ -> canonical_of_list (List.append a b)

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
        let els = List.filter (C.iter small_p) ~f:(fun x -> C.elem x big_p) in
        runs_from_elements ~width:(C.bitwidth small_p) els
      end
      else
        let r = C.intersection pa pb in
        if C.is_bottom r then [] else [ r ]

  let intersection (a : t) (b : t) : t =
    canonical_of_list
      (List.concat_map a ~f:(fun pa ->
           List.concat_map b ~f:(fun pb -> pair_intersection pa pb)))

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
    let es = List.sort es ~compare:(fun x y -> Cbat_word.compare y x) in
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
      runs_from_elements ~width:(C.bitwidth a) survivors
    else if small_total bs then begin
      let es =
        List.sort
          (List.filter (List.concat_map bs ~f:C.iter)
             ~f:(fun x -> C.elem x a))
          ~compare:Cbat_word.compare
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
    canonical_of_list (List.concat_map a ~f:(fun pa -> diff_piece pa b))

  (* Pointwise map for the elementwise unary ops. *)
  let map (f : progression -> progression) (ps : t) : t =
    canonical_of_list (List.map ps ~f)

  (* Cross product with empty pair results dropped. *)
  let lift2 (f : progression -> progression -> progression) (a : t) (b : t)
    : t =
    canonical_of_list
      (List.concat_map a ~f:(fun pa ->
           List.filter_map b ~f:(fun pb ->
               let r = f pa pb in
               if C.is_bottom r then None else Some r)))

  (* Cross product where a pair yields several pieces; a wrapped operand
     is split into its arcs first (the parts producers are
     progression-level). *)
  let lift2_parts (f : progression -> progression -> progression list)
      (a : t) (b : t) : t =
    canonical_of_list
      (List.concat_map a ~f:(fun pa ->
           List.concat_map (C.split_wrapped pa) ~f:(fun qa ->
               List.concat_map b ~f:(fun pb ->
                   List.concat_map (C.split_wrapped pb) ~f:(fun qb ->
                       f qa qb)))))

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
    canonical_of_list
      (List.concat_map ps ~f:(fun p ->
           List.concat_map (C.split_wrapped p) ~f:(fun q ->
               A.extract_parts ?hi ?lo q)))

  let cast c sz (ps : t) : t =
    canonical_of_list
      (List.concat_map ps ~f:(fun p ->
           List.concat_map (C.split_wrapped p) ~f:(fun q ->
               A.cast_parts c sz q)))

  let translate (ps : t) (delta : Cbat_word.t) : t =
    canonical_of_list (List.map ps ~f:(fun p -> C.translate p delta))

  (* Hull excess pieces into their side's last pair before widening, so
     growth in an excess piece is extrapolated too. *)
  let positional (f : progression -> progression -> progression) (a : t)
      (b : t) : t =
    match a, b with
    | [], [] -> []
    | [], _ -> [ C.top (width_of b) ]
    | _, [] -> a
    | _ ->
      let n = Stdlib.min (List.length a) (List.length b) in
      let aa = Stdlib.Array.of_list a and ba = Stdlib.Array.of_list b in
      let top_hit = Stdlib.ref false in
      let out = Stdlib.ref [] in
      for i = 0 to n - 1 do
        let tail arr =
          let p = Stdlib.ref arr.(i) in
          if i = n - 1 then
            for j = n to Stdlib.Array.length arr - 1 do
              p := coalesce !p arr.(j)
            done;
          !p in
        let w = f (tail aa) (tail ba) in
        if C.is_top w then top_hit := true else out := w :: !out
      done;
      if !top_hit then [ C.top (width_of b) ]
      else canonical_of_list (List.rev !out)

  let widen_join = positional C.widen_join
  let extrapolate_steps ~steps a b = positional (C.extrapolate_steps ~steps) a b
  let join = union
  let meet = intersection
end

(* ==================== Exact: the uncapped exact run list =============== *)

(* The exact finite tier as a [progression] run list: the small-set
   tier's element set, carried as the runs [Pieces.runs_from_elements] builds.
   Unlike [Pieces], the list is uncapped and unbudgeted; the caller's
   canonical promotion applies [fin_set_size].  Every constructor rebuilds
   the runs, so the list is canonical: sorted by [compare_piece], disjoint,
   non-wrapping, exactly the element set.  [] is bottom; the width survives
   in the record. *)
module Exact = struct
  module C = Cbat_clp_core
  module W = Cbat_word

  type t = { width : int; pieces : progression list }
  [@@deriving bin_io, sexp, compare]

  let is_bottom (t : t) : bool = t.pieces = []

  (* The raw run list. *)
  let to_pieces (t : t) : progression list = t.pieces

  let elements (t : t) : W.t list = List.concat_map t.pieces ~f:C.iter
  let iter = elements

  (* The exact runs of an element list.  Elements are grouped by their own
     width (a run's width is the words'), deduplicated and kept in the set
     order, so mixed-width operands keep the finite tier's semantics. *)
  let of_elements ~(width : int) (els : W.t list) : progression list =
    let els = List.dedup_and_sort els ~compare:W.compare in
    let groups =
      List.group els ~break:(fun a b -> W.bitwidth a <> W.bitwidth b) in
    List.sort
      (List.concat_map groups ~f:(fun g ->
           Pieces.runs_from_sorted_elements
             ~width:(W.bitwidth (List.hd_exn g)) g))
      ~compare:Pieces.compare_piece

  let make ~(width : int) (els : W.t list) : t =
    { width; pieces = of_elements ~width els }

  (* The finite tier's element equality: distinct words, width included. *)
  let word_mem (w : W.t) (els : W.t list) : bool =
    List.exists els ~f:(fun x -> W.equal x w)

  let bottom (width : int) : t = { width; pieces = [] }
  let of_list ~(width : int) (l : W.t list) : t = make ~width l

  let singleton (w : W.t) : t =
    { width = W.bitwidth w; pieces = [ C.singleton w ] }

  let bitwidth (t : t) : int = t.width
  let get_idx (t : t) : int = t.width

  let cardinality (t : t) : W.t =
    List.length (elements t) |> W.of_int ~width:(t.width + 1)

  let elem (w : W.t) (t : t) : bool =
    (* The bitwidth gates membership; the piece guard keeps [C.elem]'s
       equal-width assertion for mixed-width values. *)
    W.bitwidth w = t.width
    && List.exists t.pieces ~f:(fun p ->
           W.bitwidth w = C.bitwidth p && C.elem w p)

  let equal (a : t) (b : t) : bool =
    a.width = b.width && List.equal C.equal a.pieces b.pieces

  let overlap (a : t) (b : t) : bool =
    a.width = b.width
    && (let eb = elements b in
        List.exists (elements a) ~f:(fun w -> word_mem w eb))

  (* The width mismatch follows the finite tier: the declared width is the
     wider side and the elements keep their own width; [diff] keeps the
     left set. *)
  let union (a : t) (b : t) : t =
    make ~width:(Stdlib.max a.width b.width)
      (List.append (elements a) (elements b))

  let intersection (a : t) (b : t) : t =
    let eb = elements b in
    make ~width:(Stdlib.max a.width b.width)
      (List.filter (elements a) ~f:(fun w -> word_mem w eb))

  let diff (a : t) (b : t) : t =
    if a.width <> b.width then a
    else
      let eb = elements b in
      make ~width:a.width
        (List.filter (elements a) ~f:(fun w -> not (word_mem w eb)))

  (* The pointwise element map, at the same width. *)
  let lift (f : W.t -> W.t) (a : t) : t =
    make ~width:a.width (List.map (elements a) ~f)

  (* The Cartesian element image; [width] is the finite tier's per-op width
     rule: the wider side, or the left side for the shifts. *)
  let lift2 ?(width = fun w1 w2 -> Stdlib.max w1 w2)
      (f : W.t -> W.t -> W.t) (a : t) (b : t) : t =
    let eb = elements b in
    make ~width:(width a.width b.width)
      (List.concat_map (elements a) ~f:(fun w1 ->
           List.map eb ~f:(fun w2 -> f w1 w2)))

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

  let lnot = lift W.lnot
  let neg = lift W.neg

  let extract ?hi ?(lo = 0) (t : t) : t =
    let new_bw =
      let hi = Option.value ~default:(t.width - 1) hi in
      hi - lo + 1 in
    if new_bw <= 0 then t
    else make ~width:new_bw (List.map (elements t) ~f:(W.extract_exn ?hi ~lo))

  let cast (c : Bil.cast) (sz : int) (t : t) : t =
    if sz <= 0 then t
    else make ~width:sz (List.map (elements t) ~f:(W.cast c sz))

  let concat = lift2 ~width:(fun w1 w2 -> w1 + w2) W.concat

  (* True when consecutive elements are spaced by a multiple of [w]. *)
  let splits_by (t : t) (w : W.t) : bool =
    let rec go prev = function
      | [] -> true
      | x :: rest -> W.is_zero (W.modulo (W.sub x prev) w) && go x rest
    in
    match elements t with [] -> true | x :: rest -> go x rest

  let min_elem (t : t) : W.t option =
    List.min_elt (elements t) ~compare:W.compare

  let max_elem (t : t) : W.t option =
    List.max_elt (elements t) ~compare:W.compare

  let min_elem_signed (t : t) : W.t option =
    List.min_elt (List.map (elements t) ~f:W.signed) ~compare:W.compare

  let max_elem_signed (t : t) : W.t option =
    List.max_elt (List.map (elements t) ~f:W.signed) ~compare:W.compare

  let precedes (a : t) (b : t) : bool =
    a.width = b.width
    && (let eb = elements b in
        List.for_all (elements a) ~f:(fun w -> word_mem w eb))

  let overlap_generic (type ws)
      (module WS : Cbat_wordset_intf.S with type t = ws)
      (t : t) (s' : ws) : bool =
    (* Width mismatch answers may-overlap. *)
    if WS.bitwidth s' <> t.width then not (is_bottom t)
    else List.exists (elements t) ~f:(fun w -> WS.elem w s')

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
