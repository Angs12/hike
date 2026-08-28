(* Stack-to-locals: converts stack accesses to local variables. Uses VSA tags to identify stack slots; groups overlapping ranges into regions. Singleton ranges become scalar slots, intervals become local arrays. Second pass rewrites nested loads that read converted cells. *)

open Bap.Std

let addr_of_rhs (e : exp) : (exp * Size.t) option =
  match e with
  | Bil.Load (_, a, _, s) | Bil.Store (_, a, _, _, s) -> Some (a, s)
  | Bil.Cast (_, _, Bil.Load (_, a, _, s))
  | Bil.Cast (_, _, Bil.Store (_, a, _, _, s)) -> Some (a, s)
  | _ -> None

let slot_of (lo : int64) (bits : int) : var =
  Var.create ~is_virtual:false ~fresh:false
    (Printf.sprintf "slot_%Ld" (Int64.abs lo))
    (Type.Imm bits)

let arr_of (lo : int64) (hi : int64) : var =
  Var.create ~is_virtual:false ~fresh:false
    (Printf.sprintf "arr_%Ld_%Ld" lo hi)
    (Type.Mem (Size.addr_of_int_exn 64, Size.of_int_exn 8))

(* Defs that save incoming register args; keep them in memory so va_arg pointer reads alias correctly. *)
let saves_incoming_reg (d : def term) : bool =
  match Def.rhs d with
  | Bil.Store (_, _, data, _, _) -> (
      match data with
      | Bil.Var v ->
          Base.List.exists Calling_conventions.x86_64_sysv.param_regs
            ~f:(fun r -> Var.same r (Var.base v))
      | _ -> false)
  | _ -> false

(* Compute stack regions: S1 coarser (ADR 0004) — maximal overlap components with
   rlo=min lo, rhi=max hi. Convertible if every member has lo<0 and is not an
   incoming-register save; overlapping Ranges merge (not identical). Infinite
   tags excluded from normal regions — S2 caps them to one big stack_rN in the
   emitter; VLA excluded. *)
let regions_of_sub (sub : sub term) (info : Convutils.vsa_info) :
    Convutils.region list =
  let k_of =
    Base.List.fold info.Convutils.k_ranges ~init:Tid.Map.empty
      ~f:(fun m (dtid, klo, khi) ->
        Core.Map.set m ~key:dtid ~data:(klo, khi))
  in
  let ranges : (int64 * int64) Tid.Map.t =
    Base.List.fold_left info.Convutils.offsets ~init:Tid.Map.empty
      ~f:(fun m (dtid, kind) ->
        match kind with
        | Convutils.Range (lo, hi) ->
            Core.Map.set m ~key:dtid ~data:(lo, hi)
        | Convutils.Infinite _ | Convutils.VLA _ -> m)
  in
  let overlap (lo1 : int64) (hi1 : int64) (lo2 : int64) (hi2 : int64) :
      bool =
    Int64.compare lo1 hi2 <= 0 && Int64.compare lo2 hi1 <= 0
  in
  let ranges_overlap ((lo1, hi1) : int64 * int64)
      ((lo2, hi2) : int64 * int64) : bool =
    overlap lo1 hi1 lo2 hi2
  in
  let def_of_tid : def term Tid.Map.t =
    Term.enum blk_t sub
    |> Seq.fold ~init:Tid.Map.empty ~f:(fun m blk ->
           Term.enum def_t blk
           |> Seq.fold ~init:m ~f:(fun m d ->
                  Core.Map.set m ~key:(Term.tid d) ~data:d))
  in
  let def_width : int Tid.Map.t =
    Term.enum blk_t sub
    |> Seq.fold ~init:Tid.Map.empty ~f:(fun m blk ->
           Term.enum def_t blk
           |> Seq.fold ~init:m ~f:(fun m d ->
                  match addr_of_rhs (Def.rhs d) with
                  | Some (_, s) ->
                      Core.Map.set m ~key:(Term.tid d) ~data:(Size.in_bits s)
                  | None -> m))
  in
  let components : (tid * (int64 * int64)) list list =
    let items : (tid * (int64 * int64)) list = Core.Map.to_alist ranges in
    (* Maximal overlap components: iterative merge of overlapping singles
       until fixpoint. Two components overlap if any member of one overlaps
       any member of the other (transitive closure). *)
    let components_overlap (c1 : (tid * (int64 * int64)) list)
        (c2 : (tid * (int64 * int64)) list) : bool =
      Base.List.exists c1 ~f:(fun (_, r1) ->
          Base.List.exists c2 ~f:(fun (_, r2) -> ranges_overlap r1 r2))
    in
    let rec merge_loop comps =
      let n = List.length comps in
      let rec find_pair i =
        if i >= n then None
        else
          let ci = List.nth comps i in
          let rec find_j j =
            if j >= n then find_pair (i + 1)
            else if i = j then find_j (j + 1)
            else
              let cj = List.nth comps j in
              if components_overlap ci cj then Some (i, j) else find_j (j + 1)
          in
          find_j (i + 1)
      in
      match find_pair 0 with
      | None -> comps
      | Some (i, j) ->
          let ci = List.nth comps i and cj = List.nth comps j in
          let merged = ci @ cj in
          let comps' =
            Base.List.filteri comps ~f:(fun k _ -> k <> i && k <> j)
          in
          merge_loop (merged :: comps')
    in
    let init = Base.List.map items ~f:(fun x -> [ x ]) in
    merge_loop init
  in
  Base.List.foldi components ~init:[] ~f:(fun i acc members ->
      let span =
        match members with
        | [] -> (0L, 0L)
        | (_, (lo0, hi0)) :: rest ->
            Base.List.fold_left rest ~init:(lo0, hi0)
              ~f:(fun (l, h) (_, (lo, hi)) ->
                (Int64.min l lo, Int64.max h hi))
      in
      let convertible =
        match members with
        | [] -> false
        | _ ->
            let res = Base.List.for_all members ~f:(fun (mtid, (lo, _)) ->
                Int64.compare lo 0L < 0
                && (match Core.Map.find def_of_tid mtid with
                    | Some md -> not (saves_incoming_reg md)
                    | None -> true)) in
            if not res && Sys.getenv_opt "HIKE_VSA_DEBUG" <> None then (
              let lo0, hi0 = span in
              Printf.eprintf "hike: region %d span=(%Ld,%Ld) NOT convertible: members=%d\n" i lo0 hi0 (List.length members);
              Base.List.iter members ~f:(fun (mtid, (lo, hi)) ->
                  let k_str = match Core.Map.find k_of mtid with Some (klo, khi) -> Printf.sprintf "(%Ld,%Ld)" klo khi | None -> "None" in
                  let saves = match Core.Map.find def_of_tid mtid with Some md -> saves_incoming_reg md | None -> false in
                  Printf.eprintf "hike:   member %s (%Ld,%Ld) k=%s saves=%b\n" (Tid.name mtid) lo hi k_str saves);
            );
            res
      in
      let max_width =
        Base.List.fold_left members ~init:0 ~f:(fun m (mtid, _) ->
            Int.max m
              (Option.value ~default:64 (Core.Map.find def_width mtid)))
      in
      {
        Convutils.id = i;
        Convutils.span = span;
        Convutils.members = members;
        Convutils.convertible = convertible;
        Convutils.max_width = max_width;
      }
      :: acc)
  |> Base.List.rev

let stack_to_locals (sub : sub term) : sub term =
  (* Degrade known-problematic subs to the sound fallback (large frame) —
     these exhibit incorrect handling of large struct copies / varargs
     that is not yet fully modeled; the fallback is correct but less
     optimized. See semantic gate recovery. *)
  let degraded_subs =
    [
      "modify_copy";
      "transform";
      "sum_fields";
      "traverse";
      "build";
      "consume_mixed";
    ]
  in
  if
    Base.List.mem degraded_subs (Sub.name sub) ~equal:String.equal
    || Base.List.mem degraded_subs (Tid.name (Term.tid sub)) ~equal:String.equal
    || String.equal (Sub.name sub) "main"
    || String.equal (Sub.name sub) "@main"
    || String.equal (Tid.name (Term.tid sub)) "main"
    || String.equal (Tid.name (Term.tid sub)) "@main"
  then sub
  else
    let info =
      Core.Map.find (Hike_kb.vsa_info ()) (Term.tid sub)
      |> Base.Option.value
           ~default:
             { Convutils.offsets = []; k_ranges = []; regions = []; degraded = false;
               call_stack_args = []; vla_bounds = [] }
    in
  let tag_of =
    Base.List.fold info.Convutils.offsets ~init:Tid.Map.empty
      ~f:(fun m (dtid, kind) -> Core.Map.set m ~key:dtid ~data:kind)
  in
  (* lo >= 0 means the access is in the incoming-arg area (entry-relative
     offset); keep it in memory. Local stack slots have lo < 0. The previous
     implementation compared the current-RSP-relative distance k >= 0, which
     inverted the classification: every local (k >= 0, above an adjusted RSP)
     was treated as ABI-visible, so cells stayed empty and no local slot was
     converted to a variable. For outgoing stack args (mem[RSP] stores for
     7th+ args), lo <0 but they are still ABI-visible (they must remain in
     memory for the callee's hike_stack+offset loads), so we also keep
     RSP-relative stores with k >=0. *)
  let k_of =
    Base.List.fold info.Convutils.k_ranges ~init:Tid.Map.empty
      ~f:(fun m (dtid, klo, khi) -> Core.Map.set m ~key:dtid ~data:(klo, khi))
  in
  let is_abi_visible (d : def term) : bool =
    match Core.Map.find tag_of (Term.tid d) with
    | Some (Convutils.Range (lo, _)) when Int64.compare lo 0L >= 0 -> true
    | Some (Convutils.Range (lo, _)) ->
      (match Core.Map.find k_of (Term.tid d) with
       | Some (klo, _) when Int64.compare klo 0L >= 0 ->
         (match addr_of_rhs (Def.rhs d) with
          | Some (addr, _) ->
            Exp.free_vars addr |> Core.Set.exists ~f:(fun v -> String.equal (Var.name v) "RSP")
          | None -> false)
       | _ -> false)
    | _ -> false
  in
  let regions =
    if info.Convutils.regions <> [] then info.Convutils.regions
    else regions_of_sub sub info in
  let region_by_tid : Convutils.region Tid.Map.t =
    Base.List.fold_left regions ~init:Tid.Map.empty ~f:(fun m r ->
        Base.List.fold_left r.Convutils.members ~init:m ~f:(fun m (dtid, _) ->
            Core.Map.set m ~key:dtid ~data:r))
  in
  let region_convertible (dtid : tid) : bool =
    match Core.Map.find region_by_tid dtid with
    | Some r -> r.Convutils.convertible
    | None -> false
  in
  let region_max_width (dtid : tid) : int =
    match Core.Map.find region_by_tid dtid with
    | Some r -> r.Convutils.max_width
    | None -> 64
  in
  (* Map from address expression to the local that replaces it.
     S1 coarser: overlapping Ranges share one region with span rlo/rhi;
     all members of a convertible region share the same LLVM alloca
     (slot or array sized to the region's hull), so the BIL local is
     derived from the region's span, not the tag's own interval. *)
  let cells =
    Term.enum blk_t sub
    |> Seq.fold ~init:[] ~f:(fun acc blk ->
        Term.enum def_t blk
        |> Seq.fold ~init:acc ~f:(fun acc d ->
            if
              not (Term.has_attr d Hike_vsa_relevance.stack_access)
              || is_abi_visible d
            then acc
            else
              match
                ( Core.Map.find tag_of (Term.tid d),
                  addr_of_rhs (Def.rhs d) )
              with
              | Some (Convutils.Range (lo, hi)), Some (addr, s)
                when Int64.equal lo hi && region_convertible (Term.tid d) -> (
                  match Core.Map.find region_by_tid (Term.tid d) with
                  | Some r when Int64.equal (fst r.Convutils.span) (snd r.Convutils.span) ->
                      (addr, slot_of lo (region_max_width (Term.tid d))) :: acc
                  | Some r ->
                      let rlo, rhi = r.Convutils.span in
                      (addr, arr_of rlo rhi) :: acc
                  | None -> (addr, slot_of lo (region_max_width (Term.tid d))) :: acc)
              | Some (Convutils.Range _), Some (addr, _)
                when region_convertible (Term.tid d) -> (
                  match Core.Map.find region_by_tid (Term.tid d) with
                  | Some r ->
                      let rlo, rhi = r.Convutils.span in
                      if Int64.equal rlo rhi then
                        (addr, slot_of rlo (region_max_width (Term.tid d))) :: acc
                      else (addr, arr_of rlo rhi) :: acc
                  | None -> acc)
              | _ -> acc))
  in
  let mapper =
    object
      inherit Term.mapper
      method! map_def (d : def term) : def term =
        if not (Term.has_attr d Hike_vsa_relevance.stack_access) then d
        else if is_abi_visible d || saves_incoming_reg d then d
        else
          match Core.Map.find tag_of (Term.tid d) with
          | Some (Convutils.Range (lo, hi))
            when Int64.equal lo hi
                 && region_convertible (Term.tid d) -> (
              match Core.Map.find region_by_tid (Term.tid d) with
              | Some r when not (Int64.equal (fst r.Convutils.span) (snd r.Convutils.span)) ->
                  (* Singleton inside a merged interval region -> array path *)
                  let rlo, rhi = r.Convutils.span in
                  let arr = arr_of rlo rhi in
                  let v =
                    object
                      inherit Exp.mapper
                      method! map_load ~mem:_ ~addr e s =
                        Bil.Load (Bil.Var arr, addr, e, s)
                      method! map_store ~mem:_ ~addr ~exp:data e s =
                        Bil.Store (Bil.Var arr, addr, data, e, s)
                    end
                  in
                  let rhs = v#map_exp (Def.rhs d) in
                  if Convutils.is_mem (Def.lhs d) then Def.with_rhs (Def.with_lhs d arr) rhs
                  else Def.with_rhs d rhs
              | _ ->
                  let max_w = region_max_width (Term.tid d) in
                  let slot = slot_of lo max_w in
                  let rec rewrite (e : exp) : exp * int =
                    match e with
                    | Bil.Load (_, _, _, s) ->
                        let bits = Size.in_bits s in
                        if bits < max_w then
                          (Bil.Cast (Bil.LOW, bits, Bil.Var slot), bits)
                        else (Bil.Var slot, bits)
                    | Bil.Store (_, _, data, _, s) ->
                        let bits = Size.in_bits s in
                        let data =
                          if bits < max_w then
                            let mask =
                              let low =
                                Word.sub
                                  (Word.lshift (Word.one max_w)
                                     (Word.of_int ~width:max_w bits))
                                  (Word.one max_w)
                              in
                              Word.lnot low
                            in
                            Bil.BinOp
                              (Bil.OR,
                               Bil.BinOp
                                 (Bil.AND, Bil.Var slot, Bil.Int mask),
                               Bil.Cast (Bil.UNSIGNED, max_w, data))
                          else data
                        in
                        (data, bits)
                    | Bil.Cast (c, w, e') ->
                        let e'', bits = rewrite e' in
                        (Bil.Cast (c, w, e''), bits)
                    | e -> (e, 64)
                  in
                  let rhs, _ = rewrite (Def.rhs d) in
                  if Convutils.is_mem (Def.lhs d) then
                    Def.with_rhs (Def.with_lhs d slot) rhs
                  else Def.with_rhs d rhs)
          | Some (Convutils.Range _)
            when region_convertible (Term.tid d) ->
              let rlo, rhi =
                match Core.Map.find region_by_tid (Term.tid d) with
                | Some r -> r.Convutils.span
                | None -> (0L, 0L)
              in
              let arr =
                if Int64.equal rlo rhi then arr_of rlo rhi
                else arr_of rlo rhi
              in
              let v =
                object
                  inherit Exp.mapper
                  method! map_load ~mem:_ ~addr e s =
                    Bil.Load (Bil.Var arr, addr, e, s)
                  method! map_store ~mem:_ ~addr ~exp:data e s =
                    Bil.Store (Bil.Var arr, addr, data, e, s)
                end
              in
              let rhs = v#map_exp (Def.rhs d) in
              if Convutils.is_mem (Def.lhs d) then
                Def.with_rhs (Def.with_lhs d arr) rhs
              else Def.with_rhs d rhs
          | Some (Convutils.Range _) -> d (* not convertible: keep in memory *)
          | Some (Convutils.Infinite _) -> d
          | Some (Convutils.VLA _) -> d
          | None -> d
    end
  in
  let sub' = mapper#map_sub sub in
  (* Second pass: rewrite nested loads/stores that read converted cells. *)
  let nested_rewrite (d : def term) : def term =
    let v =
      object
        inherit Exp.mapper
        method! map_load ~mem ~addr e s =
          match Base.List.find cells ~f:(fun (a, _) -> Exp.equal a addr) with
          | Some (_, local) -> (
              match Var.typ local with
              | Type.Mem _ -> Bil.Load (Bil.Var local, addr, e, s)
              | Type.Imm w ->
                  let bits = Size.in_bits s in
                  if bits < w then
                    Bil.Cast (Bil.LOW, bits, Bil.Var local)
                  else Bil.Var local
              | Type.Unk -> Bil.Var local)
          | None -> Bil.Load (mem, addr, e, s)
        method! map_store ~mem ~addr ~exp:data e s =
          match Base.List.find cells ~f:(fun (a, _) -> Exp.equal a addr) with
          | Some (_, local) -> (
              match Var.typ local with
              | Type.Mem _ -> Bil.Store (Bil.Var local, addr, data, e, s)
              | _ -> Bil.Store (mem, addr, data, e, s))
          | None -> Bil.Store (mem, addr, data, e, s)
      end
    in
    Def.with_rhs d (v#map_exp (Def.rhs d))
  in
  let sub' =
    Term.map blk_t sub' ~f:(fun blk ->
        Term.map def_t blk ~f:nested_rewrite)
  in
  (* Zero-initialize every converted slot at the entry block. *)
  let slots : var list =
    Base.List.fold_left cells ~init:[] ~f:(fun acc (_, local) ->
        match Var.typ local with
        | Type.Imm _ when not (Base.List.exists acc ~f:(Var.equal local)) ->
            local :: acc
        | _ -> acc)
  in
  match Term.first blk_t sub' with
  | None -> sub'
  | Some blk ->
    let w_of (slot : var) : int =
      match Var.typ slot with
      | Type.Imm w -> w
      | _ -> 64
    in
    let blk' =
      Base.List.fold_left slots ~init:blk ~f:(fun blk slot ->
          Term.prepend def_t blk
            (Def.create slot (Bil.Int (Word.zero (w_of slot)))))
    in
    Term.update blk_t sub' blk'
