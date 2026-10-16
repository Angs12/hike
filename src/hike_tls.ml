(* FS-relative values use the same origin algebra as stack and module
   addresses. Resolve them before attribution changes their expressions. *)
open Bap.Std
module Ws = Cbat_vsa.WordSet
module P = Cbat_clp.Pieces

let rewrite_program ~addr_bits ~(tls : Hike_spec.tls_spec option)
    ~(denote : Hike_kb.denote) program =
  let int n = Bil.Int (Word.of_int64 ~width:addr_bits n) in
  let address off = Bil.Var (Hike_synth.thread_addr ~addr_bits off) in
  let own lo hi = match tls with
    | Some t -> lo >= t.tls_base && hi < Int64.add t.tls_base t.tls_memsz
    | None -> false in
  let native lo hi = match tls with
    | Some t -> hi < t.tls_base || lo >= Int64.add t.tls_base t.tls_memsz
    | None -> true in
  Term.map sub_t program ~f:(fun sub ->
      Term.map blk_t sub ~f:(fun blk ->
          Term.map def_t blk ~f:(fun def ->
              let bounds exp =
                match denote ~blk ~def exp with
                | Ok ws when Base.Option.equal Hike_origin.equal (Ws.origin ws)
                               (Some Hike_origin.Fs) ->
                  Base.Option.bind (Ws.relative_offsets ws) ~f:(fun offs ->
                      if P.is_bottom offs then None else
                      Some (Base.Option.value
                        (Base.Option.bind (P.min_elem_signed offs) ~f:(fun lo ->
                          Base.Option.bind (P.max_elem_signed offs) ~f:(fun hi ->
                              Cbat_word.int64_pair lo hi)))
                        ~default:(Int64.min_int, Int64.max_int)))
                | _ -> None in
              let mapper = object (self)
                inherit Exp.mapper as super

                (* Recover an operand's input TP offset from its emitted
                   storage. A single known offset needs no runtime read. *)
                method offset original rendered =
                  match bounds original with
                  | Some (lo, hi) when Int64.equal lo hi -> int lo
                  | Some (lo, hi) when own lo hi ->
                    let t = Base.Option.value_exn tls in
                    Bil.BinOp (Bil.PLUS,
                      Bil.BinOp (Bil.MINUS, rendered, address t.tls_base),
                      int t.tls_base)
                  | Some (lo, hi) when native lo hi ->
                    Bil.BinOp (Bil.MINUS, rendered, address 0L)
                  | _ -> failwith
                      "hike-tls: cannot recover an offset spanning program TLS and native TCB storage"

                method! map_exp exp =
                  let rendered = super#map_exp exp in
                  match bounds exp with
                  | Some (lo, hi) when Int64.equal lo hi -> address lo
                  | Some (lo, hi) -> (
                    match exp, rendered with
                    | Bil.BinOp ((Bil.PLUS | Bil.MINUS) as op, a, b),
                      Bil.BinOp (_, a', b') ->
                      let operand original rendered =
                        match bounds original with
                        | Some _ -> self#offset original rendered
                        | None -> rendered in
                      let off = Bil.BinOp (op, operand a a', operand b b') in
                      let native_value = Bil.BinOp (Bil.PLUS, address 0L, off) in
                      (match tls with
                       | None -> native_value
                       | Some t ->
                         let owned = Hike_synth_addr.base_plus
                             (Hike_synth.thread_addr ~addr_bits t.tls_base)
                             ~rel:t.tls_base off in
                         if own lo hi then owned
                         else if native lo hi then native_value
                         else Bil.Ite
                             (Bil.BinOp (Bil.AND,
                                Bil.BinOp (Bil.SLE, int t.tls_base, off),
                                Bil.BinOp (Bil.SLT, off,
                                  int (Int64.add t.tls_base t.tls_memsz))),
                              owned, native_value))
                    | _ -> rendered)
                  | None -> (
                    match exp, rendered with
                    | Bil.BinOp (Bil.MINUS, a, b), Bil.BinOp (_, a', b')
                      when Base.Option.is_some (bounds a)
                           && Base.Option.is_some (bounds b) ->
                      Bil.BinOp (Bil.MINUS, self#offset a a', self#offset b b')
                    | _ -> rendered)
              end in
              Def.map_exp def ~f:mapper#map_exp)))
