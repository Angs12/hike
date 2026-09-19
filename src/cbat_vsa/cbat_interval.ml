(* The interval-components algebra: the partition engine over closed
   intervals (see the .mli for the sweep invariant). *)

let connected_components
    ~(key : 'a -> 'a -> int)
    ~(span : 'a -> int64 * int64)
    (items : 'a list) : 'a list list =
  let before x y =
    let lo1, hi1 = span x and lo2, hi2 = span y in
    let c = Stdlib.Int64.compare lo1 lo2 in
    if c <> 0 then c
    else
      let c = Stdlib.Int64.compare hi1 hi2 in
      if c <> 0 then c else key x y
  in
  match List.sort before items with
  | [] -> []
  | x0 :: tl ->
    let rec sweep cur max_hi rest =
      match rest with
      | [] -> [ List.rev cur ]
      | x :: tl ->
        let lo, hi = span x in
        if Stdlib.Int64.compare lo max_hi <= 0 then
          sweep (x :: cur)
            (if Stdlib.Int64.compare hi max_hi > 0 then hi else max_hi)
            tl
        else List.rev cur :: sweep [ x ] hi tl
    in
    let _, hi0 = span x0 in
    sweep [ x0 ] hi0 tl

let hull ~(span : 'a -> int64 * int64) (members : 'a list) : int64 * int64 =
  match members with
  | [] -> (0L, 0L)
  | x0 :: rest ->
    let lo0, hi0 = span x0 in
    List.fold_left
      (fun (l, h) x ->
        let lo, hi = span x in
        (Stdlib.Int64.min l lo, Stdlib.Int64.max h hi))
      (lo0, hi0) rest
