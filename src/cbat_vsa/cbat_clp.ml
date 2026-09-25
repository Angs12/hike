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
      let step = C.step_of q in
      if Cbat_word.is_zero step || not (Cbat_word.equal step (C.step_of p))
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

  (* Canonicalize and cap: split wrapped pieces into their arcs, sort,
     merge, then hull the smallest-growth pair until the list fits.  No
     piece in a canonical list wraps. *)
  let rec normalize (ps : progression list) : t =
    let ps =
      List.filter
        (List.concat_map ps ~f:C.split_wrapped)
        ~f:(fun p -> not (C.is_bottom p)) in
    let ps = List.sort ps ~compare:compare_piece in
    let ps = List.rev (List.fold ps ~init:[] ~f:insert) in
    let ps =
      if List.length ps > max_pieces then begin
#ifdef VSA_DEBUG
        census_cap ();
#endif
        match choose_pair ps with
        | Some (hull, rest) -> normalize (hull :: rest)
        | None -> ps
      end
      else ps
    in
#ifdef VSA_DEBUG
    census_len (List.length ps);
#endif
    ps

  let of_progression (p : progression) : t = normalize [ p ]

  (* Maximal constant-difference runs of a sorted element list; each run
     is one exact progression (a wrapped run over-approximates). *)
  let runs_from_elements ~(width : int) (els : Cbat_word.t list)
    : progression list =
    let els = List.sort els ~compare:Cbat_word.compare in
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

  let of_list ~(width : int) (l : Cbat_word.t list) : t =
    if width <= 0 then []
    else
      let l = List.map l ~f:(Cbat_word.extract_exn ~hi:(width - 1) ~lo:0) in
      normalize (runs_from_elements ~width l)

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

  let union (a : t) (b : t) : t = normalize (List.append a b)

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
    normalize
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
    normalize (List.concat_map a ~f:(fun pa -> diff_piece pa b))

  (* Pointwise map for the elementwise unary ops. *)
  let map (f : progression -> progression) (ps : t) : t =
    normalize (List.map ps ~f)

  (* Cross product with empty pair results dropped. *)
  let lift2 (f : progression -> progression -> progression) (a : t) (b : t)
    : t =
    normalize
      (List.concat_map a ~f:(fun pa ->
           List.filter_map b ~f:(fun pb ->
               let r = f pa pb in
               if C.is_bottom r then None else Some r)))

  (* Cross product where a pair yields several pieces; a wrapped operand
     is split into its arcs first (the parts producers are
     progression-level). *)
  let lift2_parts (f : progression -> progression -> progression list)
      (a : t) (b : t) : t =
    normalize
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
    normalize
      (List.concat_map ps ~f:(fun p ->
           List.concat_map (C.split_wrapped p) ~f:(fun q ->
               A.extract_parts ?hi ?lo q)))

  let cast c sz (ps : t) : t =
    normalize
      (List.concat_map ps ~f:(fun p ->
           List.concat_map (C.split_wrapped p) ~f:(fun q ->
               A.cast_parts c sz q)))

  let translate (ps : t) (delta : Cbat_word.t) : t =
    normalize (List.map ps ~f:(fun p -> C.translate p delta))

  (* Positional widening: sorted pairs, excess hulled into the last pair,
     a top pair collapsing the whole list. *)
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
        let w = f aa.(i) ba.(i) in
        if C.is_top w then top_hit := true else out := w :: !out
      done;
      if !top_hit then [ C.top (width_of b) ]
      else begin
        let out = List.rev !out in
        let excess =
          if List.length a > n then List.drop a n
          else if List.length b > n then List.drop b n
          else []
        in
        let out =
          match List.rev out, excess with
          | _, [] -> out
          | last :: rev_rest, _ ->
            List.rev (List.fold excess ~init:last ~f:coalesce :: rev_rest)
          | [], _ -> excess
        in
        normalize out
      end

  let widen_join = positional C.widen_join
  let extrapolate_steps ~steps a b = positional (C.extrapolate_steps ~steps) a b
  let join = union
  let meet = intersection
end
