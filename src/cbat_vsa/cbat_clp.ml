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

(* The frozen seam (cbat_clp.mli): core comes from the include
   below; arithmetic is one line per op behind it. *)

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
let of_list = Cbat_clp_arith.of_list
